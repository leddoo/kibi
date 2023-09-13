use sti::traits::CopyIt;
use sti::arena::Arena;
use sti::vec::Vec;
use sti::string::String;
use sti::boks::Box;
use sti::rc::Rc;
use sti::keyed::{KVec, KFreeVec};
use sti::hash::HashMap;

use crate::string_table::StringTable;
use crate::diagnostics::{Diagnostics, Diagnostic};
use crate::ast::{SourceId, ParseId, SourceRange, UserSourcePos, UserSourceRange};
use crate::parser::{self, Parse};
use crate::env::{Env, SymbolId};
use crate::traits::Traits;
use crate::elab::{Elaborator, Elab};
use crate::vfs::Vfs;


pub struct Compiler {
    #[allow(dead_code)]
    persistent: Box<Arena>,

    inner: Inner<'static>,
}

struct Inner<'c> {
    vfs: Rc<dyn Vfs>,

    dirty: bool,

    path_to_source: HashMap<String, SourceId>,
    sources: KVec<SourceId, OptSourceDataId>,
    source_datas: KFreeVec<SourceDataId, SourceData>,
    parses: KVec<ParseId, OptParseDataId>,
    parse_datas: KFreeVec<ParseDataId, ParseData>,
    elab_datas: KFreeVec<ElabDataId, ElabData>,

    strings: StringTable<'c>,
}

sti::define_key!(u32, SourceDataId, opt: OptSourceDataId);

struct SourceData {
    dirty: bool,
    path: String,
    data: Vec<u8>,
    parse: OptParseDataId,
    elab: OptElabDataId,
}


sti::define_key!(u32, ParseDataId, opt: OptParseDataId);

struct ParseData {
    #[allow(dead_code)]
    arena: Arena,

    parse: Parse<'static>,
}


sti::define_key!(u32, ElabDataId, opt: OptElabDataId);

struct ElabData {
    #[allow(dead_code)]
    arena: Arena,

    env: Env<'static>,
    traits: Traits,
    elab: Elab<'static>,
}

impl Compiler {
    pub fn new(vfs: &Rc<impl 'static + Vfs>) -> Self {
        let persistent = Box::new(Arena::new());

        let inner = Inner {
            vfs: unsafe { vfs.clone().cast(|p| p as *mut sti::rc::RcInner<dyn Vfs>) },
            dirty: false,
            path_to_source: HashMap::new(),
            sources: KVec::new(),
            source_datas: KFreeVec::new(),
            parses: KVec::new(),
            parse_datas: KFreeVec::new(),
            elab_datas: KFreeVec::new(),
            strings: StringTable::new(&*persistent),
        };
        let inner = unsafe { core::mem::transmute(inner) };

        Self { persistent, inner }
    }

    pub fn add_source(&mut self, path: &str) -> SourceId {
        self.inner.add_source(path)
    }

    pub fn remove_source(&mut self, path: &str) -> bool {
        self.inner.remove_source(path)
    }

    pub fn file_changed(&mut self, path: &str) {
        self.inner.file_changed(path)
    }

    pub fn update(&mut self) {
        spall::trace_scope!("kibi/update");
        self.inner.update()
    }


    pub fn query_semantic_tokens(&mut self, path: &str) -> Vec<SemanticToken> {
        spall::trace_scope!("kibi/query_semantic_tokens"; "{}", path);
        self.inner.query_semantic_tokens(path)
    }

    pub fn query_diagnostics<'out>(&mut self, alloc: &'out Arena) -> Vec<FileDiagnostics<'out>> {
        spall::trace_scope!("kibi/query_diagnostics");
        self.inner.query_diagnostics(alloc)
    }
}

impl<'c> Inner<'c> {
    pub fn add_source(&mut self, path: &str) -> SourceId {
        *self.path_to_source.get_or_insert_with_key(path, |_| {
            let data_id = self.source_datas.alloc(SourceData {
                dirty: true,
                path: path.into(),
                data: Vec::new(),
                parse: None.into(),
                elab: None.into(),
            });
            self.dirty = true;
            (path.into(), self.sources.push(data_id.some()))
        })
    }

    pub fn remove_source(&mut self, path: &str) -> bool {
        let Some(source_id) = self.path_to_source.remove_value(path) else {
            return false;
        };

        let data_id = self.sources[source_id].take().unwrap();

        // @todo: kfreevec drop & unwrap.
        let source = &mut self.source_datas[data_id];
        if let Some(parse_id) = source.parse.take() {
            self.parse_datas.free(parse_id);
        }
        if let Some(elab_id) = source.elab.take() {
            self.elab_datas.free(elab_id);
        }
        // @todo: string free.
        source.path = String::new();
        source.data.free();

        self.source_datas.free(data_id);
        self.dirty = true;

        return true;
    }

    pub fn file_changed(&mut self, path: &str) {
        if let Some(id) = self.path_to_source.get(path).copied() {
            let data_id = self.sources[id].unwrap();
            self.source_datas[data_id].dirty = true;
            self.dirty = true;
        }
    }


    pub fn update(&mut self) {
        if !self.dirty { return }
        self.dirty = false;

        for source_id in self.sources.range() {
            if let Some(data_id) = self.sources[source_id].to_option() {
                self.update_source(source_id, data_id);
            }
        }
    }

    fn update_source(&mut self, source_id: SourceId, source: SourceDataId) {
        let source = &mut self.source_datas[source];
        if !source.dirty { return }
        source.dirty = false;

        spall::trace_scope!("kibi/update_source"; "{}", source.path);

        source.data = match self.vfs.read(&source.path) {
            Ok(data) => {
                if source.data.len() > u32::MAX as usize {
                    // @todo: error.
                    return;
                }
                data
            }

            Err(_) => {
                // @todo: error.
                return;
            }
        };


        if let Some(parse_id) = source.parse.take() {
            self.parse_datas.free(parse_id);
        }
        if let Some(elab_id) = source.elab.take() {
            self.elab_datas.free(elab_id);
        }


        let parse_arena = Arena::new();

        let mut parse = Parse {
            source: source_id,
            source_range: SourceRange {
                begin: 0,
                end: source.data.len() as u32,
            },
            diagnostics: Diagnostics::new(),
            numbers: KVec::new(),
            strings: KVec::new(),
            tokens:  KVec::new(),
            items:  KVec::new(),
            levels: KVec::new(),
            exprs:  KVec::new(),
        };

        parser::parse_file(&source.data, &mut parse,
            &mut self.strings, &parse_arena);


        let elab_arena = Arena::new();

        let mut elab = Elab {
            diagnostics: Diagnostics::new(),
        };

        let mut env = Env::new();
        let mut traits = Traits::new();

        for item in parse.items.range() {
            let mut elaborator = Elaborator::new(
                &mut elab,
                &mut env,
                &mut traits,
                &parse,
                SymbolId::ROOT,
                &mut self.strings,
                &elab_arena,
                &elab_arena);
            if elaborator.elab_item(item).is_none() {
                break;
            }
        }

        // @todo: make this safer.
        let parse = unsafe { core::mem::transmute(parse) };
        let parse_id = self.parse_datas.alloc(ParseData { arena: parse_arena, parse });
        source.parse = parse_id.some();

        // @todo: make this safer.
        let (env, elab) = unsafe { core::mem::transmute((env, elab)) };
        let elab_id = self.elab_datas.alloc(ElabData { arena: elab_arena, env, traits, elab });
        source.elab = elab_id.some();
    }
}


#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum TokenClass {
    Error,
    Comment,
    Keyword,
    Punctuation,
    Operator,
    String,
    Number,
    Type,
    Parameter,
    Variable,
    Property,
    Function,
    Method,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SemanticToken {
    pub delta_line: u32,
    pub delta_col:  u32,
    pub len: u32,
    pub class: TokenClass,
}

impl<'c> Inner<'c> {
    pub fn query_semantic_tokens(&mut self, path: &str) -> Vec<SemanticToken> {
        self.update();

        let Some(id) = self.path_to_source.get(path).copied() else {
            // @todo: diagnostic.
            return Vec::new();
        };

        let source = &self.source_datas[self.sources[id].unwrap()];
        debug_assert!(!source.dirty);

        let parse = &self.parse_datas[source.parse.unwrap()].parse;
        debug_assert_eq!(parse.source_range.begin, 0);
        debug_assert_eq!(parse.source_range.end,   source.data.len() as u32);


        // @todo: line table thing.
        let code = source.data.as_slice();
        let mut next_newline =
            code.copy_it().position(|x| x == b'\n')
            .unwrap_or(code.len());

        let mut line = 0;
        let mut prev_begin = 0;

        let mut result = Vec::with_cap(parse.tokens.len());
        for token in parse.tokens.inner().copy_it() {
            let mut next_line = line;
            let mut delta_col = token.source.begin - prev_begin;
            while token.source.begin > next_newline as u32 {
                delta_col = token.source.begin - next_newline as u32 - 1;

                next_newline += 1;
                while next_newline < code.len() {
                    if code[next_newline] == b'\n' {
                        break;
                    }
                    next_newline += 1;
                }
                next_line += 1;
            }

            let delta_line = next_line - line;

            line = next_line;
            prev_begin = token.source.begin;

            let len = token.source.end - token.source.begin;

            let class = {
                use crate::ast::TokenKind as T; 
                match token.kind {
                    T::Error => TokenClass::Error,
                    T::EndOfFile => TokenClass::Punctuation,
                    T::Hole => TokenClass::Variable,
                    T::Ident(_) => TokenClass::Variable,
                    T::Bool(_) => TokenClass::Variable,
                    T::Number(_) => TokenClass::Number,
                    T::String(_) => TokenClass::String,
                    T::KwSort => TokenClass::Type,
                    T::KwProp => TokenClass::Type,
                    T::KwType => TokenClass::Type,
                    T::KwLam => TokenClass::Keyword,
                    T::KwPi => TokenClass::Type,
                    T::KwInductive => TokenClass::Keyword,
                    T::KwStruct => TokenClass::Keyword,
                    T::KwEnum => TokenClass::Keyword,
                    T::KwDef => TokenClass::Keyword,
                    T::KwTrait => TokenClass::Keyword,
                    T::KwImpl => TokenClass::Keyword,
                    T::KwLet => TokenClass::Keyword,
                    T::KwVar => TokenClass::Keyword,
                    T::KwDo => TokenClass::Keyword,
                    T::KwIf => TokenClass::Keyword,
                    T::KwElif => TokenClass::Keyword,
                    T::KwElse => TokenClass::Keyword,
                    T::KwWhile => TokenClass::Keyword,
                    T::KwFor => TokenClass::Keyword,
                    T::KwIn => TokenClass::Keyword,
                    T::KwBreak => TokenClass::Keyword,
                    T::KwContinue => TokenClass::Keyword,
                    T::KwReturn => TokenClass::Keyword,
                    T::KwFn => TokenClass::Keyword,
                    T::KwAnd => TokenClass::Keyword,
                    T::KwOr => TokenClass::Keyword,
                    T::KwNot => TokenClass::Keyword,
                    T::LParen => TokenClass::Punctuation,
                    T::RParen => TokenClass::Punctuation,
                    T::LBracket => TokenClass::Punctuation,
                    T::RBracket => TokenClass::Punctuation,
                    T::LCurly => TokenClass::Punctuation,
                    T::RCurly => TokenClass::Punctuation,
                    T::Dot => TokenClass::Punctuation,
                    T::Comma => TokenClass::Punctuation,
                    T::Semicolon => TokenClass::Punctuation,
                    T::Colon => TokenClass::Punctuation,
                    T::ColonColon => TokenClass::Punctuation,
                    T::ColonEq => TokenClass::Punctuation,
                    T::Arrow => TokenClass::Punctuation,
                    T::FatArrow => TokenClass::Punctuation,
                    T::Add => TokenClass::Operator,
                    T::AddAssign => TokenClass::Operator,
                    T::Minus => TokenClass::Operator,
                    T::SubAssign => TokenClass::Operator,
                    T::Star => TokenClass::Operator,
                    T::MulAssign => TokenClass::Operator,
                    T::Div => TokenClass::Operator,
                    T::DivAssign => TokenClass::Operator,
                    T::FloorDiv => TokenClass::Operator,
                    T::FloorDivAssign => TokenClass::Operator,
                    T::Rem => TokenClass::Operator,
                    T::RemAssign => TokenClass::Operator,
                    T::Eq => TokenClass::Operator,
                    T::EqEq => TokenClass::Operator,
                    T::Not => TokenClass::Operator,
                    T::NotEq => TokenClass::Operator,
                    T::Le => TokenClass::Operator,
                    T::Lt => TokenClass::Operator,
                    T::Ge => TokenClass::Operator,
                    T::Gt => TokenClass::Operator,
                }
            };

            result.push(SemanticToken { delta_line, delta_col, len, class });
        }
        return result;
    }
}


#[derive(Debug)]
pub struct FileDiagnostics<'a> {
    pub path: &'a str,
    pub diagnostics: Vec<FileDiagnostic<'a>>,
}

#[derive(Clone, Copy, Debug)]
pub struct FileDiagnostic<'a> {
    pub range: UserSourceRange,
    pub message: &'a str,
}

impl<'c> Inner<'c> {
    pub fn query_diagnostics<'out>(&mut self, alloc: &'out Arena) -> Vec<FileDiagnostics<'out>> {
        self.update();

        let mut result = Vec::new();
        for source_id in self.sources.range() {
            let Some(data_id) = self.sources[source_id].to_option() else { continue };
            let source = &self.source_datas[data_id];

            let mut file_diagnostics = Vec::new();

            let parse_id = source.parse.unwrap();
            let parse = &self.parse_datas[parse_id].parse;
            for d in parse.diagnostics.diagnostics.iter() {
                file_diagnostics.push(mk_file_diagnostic(d, source, parse, alloc));
            }

            let elab_id = source.elab.unwrap();
            let elab = &self.elab_datas[elab_id].elab;
            for d in elab.diagnostics.diagnostics.iter() {
                file_diagnostics.push(mk_file_diagnostic(d, source, parse, alloc));
            }

            result.push(FileDiagnostics {
                path: alloc.alloc_str(&source.path),
                diagnostics: file_diagnostics,
            });
        }
        return result;


        fn mk_file_diagnostic<'out>(d: &Diagnostic, source: &SourceData, parse: &Parse, alloc: &'out Arena) -> FileDiagnostic<'out> {
            use core::fmt::Write;
            use crate::diagnostics::*;

            let range = d.source.resolve_source_range(parse);

            let range = {
                let code = &source.data;
                // @temp: line table.
                let mut line = 0;
                let mut line_begin = 0;
                let mut i = 0;
                loop {
                    while i < code.len() && code[i] != b'\n' {
                        i += 1;
                    }
                    if range.begin as usize <= i {
                        break;
                    }
                    if i < code.len() {
                        i += 1;
                        line += 1;
                        line_begin = i;
                    }
                }
                let begin = UserSourcePos { line, col: range.begin - line_begin as u32 };
                // @temp: line table.
                let mut line = 0;
                let mut line_begin = 0;
                let mut i = 0;
                loop {
                    while i < code.len() && code[i] != b'\n' {
                        i += 1;
                    }
                    if range.end as usize <= i {
                        break;
                    }
                    if i < code.len() {
                        i += 1;
                        line += 1;
                        line_begin = i;
                    }
                }
                let end = UserSourcePos { line, col: range.end - line_begin as u32 };
                UserSourceRange { begin, end }
            };

            let message = match d.kind {
                DiagnosticKind::ParseError(e) => {
                    // @cleanup: sti temp formatting.
                    let mut buf = String::new_in(alloc);
                    match e {
                        ParseError::Expected(what) => {
                            sti::write!(&mut buf, "expected: {what}");
                        }

                        ParseError::Unexpected(what) => {
                            sti::write!(&mut buf, "unexpected: {what}");
                        }
                    }
                    buf.leak()
                }

                DiagnosticKind::ElabError(e) => {
                    // @cleanup: sti temp formatting.
                    let mut buf = String::new_in(alloc);
                    match e {
                        ElabError::SymbolShadowedByLocal(name) => {
                            sti::write!(&mut buf, "symbol {name:?} shadowed");
                        }

                        ElabError::UnresolvedName { base: _, name } => {
                            sti::write!(&mut buf, "unknown symbol {name:?}");
                        }

                        ElabError::UnresolvedLevel(name) => {
                            sti::write!(&mut buf, "unknown level {name:?}");
                        }

                        ElabError::LevelCountMismatch { expected, found } => {
                            sti::write!(&mut buf, "expected {expected} levels, found {found}");
                        }

                        ElabError::TypeMismatch { expected, found } => {
                            let pp = crate::pp::PP::new(alloc);
                            // @cleanup: sti temp formatting.
                            sti::write!(&mut buf, "expected ");
                            pp.render(expected, 50).layout_into_string(&mut buf);
                            sti::write!(&mut buf, ", found ");
                            pp.render(found, 50).layout_into_string(&mut buf);
                        }

                        ElabError::TypeExpected { found } => {
                            let pp = crate::pp::PP::new(alloc);
                            sti::write!(&mut buf, "type expected, found ");
                            pp.render(found, 50).layout_into_string(&mut buf);
                        }

                        ElabError::TooManyArgs => {
                            sti::write!(&mut buf, "too many args");
                        }

                        ElabError::UnassignedIvars => {
                            sti::write!(&mut buf, "unassigned ivars");
                        }

                        ElabError::TypeFormerHasIvars => {
                            sti::write!(&mut buf, "type former has ivars");
                        }

                        ElabError::CtorTypeHasIvars => {
                            sti::write!(&mut buf, "ctor type has ivars");
                        }

                        ElabError::CtorNeedsTypeCauseIndices => {
                            sti::write!(&mut buf, "ctor needs type, because type has indices");
                        }

                        ElabError::CtorArgLevelTooLarge => {
                            sti::write!(&mut buf, "arg level too large");
                        }

                        ElabError::CtorInvalidRecursion => {
                            sti::write!(&mut buf, "invalid recursion");
                        }

                        ElabError::CtorRecArgUsed => {
                            sti::write!(&mut buf, "recursive arg used");
                        }

                        ElabError::CtorNotRetSelf => {
                            sti::write!(&mut buf, "ctor must return Self");
                        }

                        ElabError::TraitResolutionFailed { trayt } => {
                            sti::write!(&mut buf, "trait resolution failed for trait {trayt:?}");
                        }

                        ElabError::ImplTypeIsNotTrait => {
                            sti::write!(&mut buf, "impl type is not a trait");
                        }

                        ElabError::TempTBD => {
                            sti::write!(&mut buf, "(temp): not entirely sure what went wrong here");
                        }

                        ElabError::TempArgFailed => {
                            sti::write!(&mut buf, "(temp): arg failed");
                        }

                        ElabError::TempCtorArgLevelCouldBeTooLarge => {
                            sti::write!(&mut buf, "(temp): maybe ctor arg level too large");
                        }

                        ElabError::TempUnimplemented => {
                            sti::write!(&mut buf, "(temp): unimplemented");
                        }
                    }
                    buf.leak()
                }
            };

            FileDiagnostic { range, message }
        }
    }
}

