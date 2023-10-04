use core::fmt::Write;

use sti::traits::CopyIt;
use sti::arena::Arena;
use sti::arena_pool::ArenaPool;
use sti::vec::Vec;
use sti::string::String;
use sti::boks::Box;
use sti::rc::Rc;
use sti::keyed::{KVec, KFreeVec};
use sti::hash::HashMap;

use crate::string_table::{StringTable, Atom};
use crate::diagnostics::{Diagnostics, Diagnostic};
use crate::ast::{SourceId, SourceRange, UserSourcePos, UserSourceRange, TokenId, AstId, ItemId};
use crate::parser::{self, Parse};
use crate::env::{Env, SymbolId};
use crate::traits::Traits;
use crate::elab::{self, Elab};
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
    parse_datas: KFreeVec<ParseDataId, ParseData>,
    elab_datas: KFreeVec<ElabDataId, ElabData>,

    strings: StringTable<'c>,
}

sti::define_key!(u32, SourceDataId, opt: OptSourceDataId);

struct SourceData {
    dirty: bool,
    path: String,
    code: Vec<u8>,
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
    #[allow(dead_code)]
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

    pub fn query_hover_info<'out>(&mut self, path: &str, line: u32, col: u32, alloc: &'out Arena) -> Vec<HoverInfo<'out>> {
        spall::trace_scope!("kibi/query_hover_info");
        self.inner.query_hover_info(path, line, col, alloc)
    }

    pub fn query_info_panel<'out>(&mut self, path: &str, line: u32, col: u32, width: u32, alloc: &'out Arena) -> InfoPanel<'out> {
        spall::trace_scope!("kibi/query_info_panel");
        self.inner.query_info_panel(path, line, col, width, alloc)
    }
}

impl<'c> Inner<'c> {
    pub fn add_source(&mut self, path: &str) -> SourceId {
        *self.path_to_source.get_or_insert_with_key(path, |_| {
            let data_id = self.source_datas.alloc(SourceData {
                dirty: true,
                path: path.into(),
                code: Vec::new(),
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
        source.code.free();

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

        source.code = match self.vfs.read(&source.path) {
            Ok(data) => {
                if source.code.len() > u32::MAX as usize {
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
                end: source.code.len() as u32,
            },
            diagnostics: Diagnostics::new(),
            numbers: KVec::new(),
            strings: KVec::new(),
            tokens:  KVec::new(),
            items:   KVec::new(),
            stmts:   KVec::new(),
            levels:  KVec::new(),
            exprs:   KVec::new(),
            tactics: KVec::new(),
            root_items: Vec::new(),
        };
        parser::parse_file(&source.code, &mut parse, &mut self.strings, &parse_arena);


        let elab_arena = Arena::new();

        let mut elab = Elab {
            diagnostics: Diagnostics::new(),
            token_infos: HashMap::new(),
            item_infos:   KVec::new(),
            item_ctxs:    KVec::new(),
            expr_infos:   KVec::new(),
            tactic_infos: KVec::new(),
        };
        let mut env = Env::new();
        let mut traits = Traits::new();
        elab::elab_file(&parse, &mut elab, &mut env, &mut traits, &mut self.strings, &elab_arena);


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

        let Some(source_id) = self.path_to_source.get(path).copied() else {
            // @todo: diagnostic.
            return Vec::new();
        };

        let source = &self.source_datas[self.sources[source_id].unwrap()];
        debug_assert!(!source.dirty);

        let parse = &self.parse_datas[source.parse.unwrap()].parse;
        debug_assert_eq!(parse.source_range.begin, 0);
        debug_assert_eq!(parse.source_range.end,   source.code.len() as u32);


        // @todo: line table thing.
        let code = source.code.as_slice();
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
                    T::Label(_) => TokenClass::Keyword,
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
                    T::KwIn => TokenClass::Keyword,
                    T::KwBy => TokenClass::Keyword,
                    T::KwDo => TokenClass::Keyword,
                    T::KwIf => TokenClass::Keyword,
                    T::KwThen => TokenClass::Keyword,
                    T::KwWhile => TokenClass::Keyword,
                    T::KwLoop => TokenClass::Keyword,
                    T::KwElse => TokenClass::Keyword,
                    T::KwBreak => TokenClass::Keyword,
                    T::KwContinue => TokenClass::Keyword,
                    T::KwReturn => TokenClass::Keyword,
                    T::KwFn => TokenClass::Keyword,
                    T::Ampersand => TokenClass::Operator,
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
                    T::LeftArrow => TokenClass::Punctuation,
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
                file_diagnostics.push(self.mk_file_diagnostic(d, source, parse, alloc));
            }

            let elab_id = source.elab.unwrap();
            let elab = &self.elab_datas[elab_id].elab;
            for d in elab.diagnostics.diagnostics.iter() {
                file_diagnostics.push(self.mk_file_diagnostic(d, source, parse, alloc));
            }

            result.push(FileDiagnostics {
                path: alloc.alloc_str(&source.path),
                diagnostics: file_diagnostics,
            });
        }
        return result;
    }


    fn mk_file_diagnostic<'out>(&self, d: &Diagnostic, source: &SourceData, parse: &Parse, alloc: &'out Arena) -> FileDiagnostic<'out> {
        use crate::diagnostics::*;

        let range = d.source.resolve_source_range(parse);

        let range = {
            let code = &source.code;
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

        let mut msg = String::new_in(alloc);
        match &d.kind {
            DiagnosticKind::ParseError(e) => {
                match e {
                    ParseError::Expected(what) => {
                        sti::write!(&mut msg, "expected: {what}");
                    }

                    ParseError::Unexpected(what) => {
                        sti::write!(&mut msg, "unexpected: {what}");
                    }

                    ParseError::TempStr(str) => {
                        sti::write!(&mut msg, "(temp) msg: {}", str);
                    }
                }
            }

            DiagnosticKind::ElabError(e) => {
                match e {
                    ElabError::UnresolvedName (name) => {
                        sti::write!(&mut msg, "unknown symbol {name:?}");
                    }

                    ElabError::UnresolvedLevel (name) => {
                        sti::write!(&mut msg, "unknown level {name:?}");
                    }

                    ElabError::LevelCountMismatch { expected, found } => {
                        sti::write!(&mut msg, "expected {expected} levels, found {found}");
                    }

                    ElabError::TypeMismatch { expected, found } => {
                        let pp = crate::pp::PP::new(alloc);
                        sti::write!(&mut msg, "expected ");
                        pp.render(expected, 50).layout_into_string(&mut msg);
                        sti::write!(&mut msg, ", found ");
                        pp.render(found, 50).layout_into_string(&mut msg);
                    }

                    ElabError::TypeExpected { found } => {
                        let pp = crate::pp::PP::new(alloc);
                        sti::write!(&mut msg, "type expected, found ");
                        pp.render(found, 50).layout_into_string(&mut msg);
                    }

                    ElabError::TooManyArgs => {
                        sti::write!(&mut msg, "too many args");
                    }

                    ElabError::UnassignedIvars => {
                        sti::write!(&mut msg, "unassigned ivars");
                    }

                    ElabError::TypeFormerHasIvars => {
                        sti::write!(&mut msg, "type former has ivars");
                    }

                    ElabError::CtorTypeHasIvars => {
                        sti::write!(&mut msg, "ctor type has ivars");
                    }

                    ElabError::CtorNeedsTypeCauseIndices => {
                        sti::write!(&mut msg, "ctor needs type, because type has indices");
                    }

                    ElabError::CtorArgLevelTooLarge => {
                        sti::write!(&mut msg, "arg level too large");
                    }

                    ElabError::CtorInvalidRecursion => {
                        sti::write!(&mut msg, "invalid recursion");
                    }

                    ElabError::CtorRecArgUsed => {
                        sti::write!(&mut msg, "recursive arg used");
                    }

                    ElabError::CtorNotRetSelf => {
                        sti::write!(&mut msg, "ctor must return Self");
                    }

                    ElabError::TraitResolutionFailed { trayt } => {
                        sti::write!(&mut msg, "trait resolution failed for trait {trayt:?}");
                    }

                    ElabError::ImplTypeIsNotTrait => {
                        sti::write!(&mut msg, "impl type is not a trait");
                    }

                    ElabError::TempTBD => {
                        sti::write!(&mut msg, "(temp): not entirely sure what went wrong here");
                    }

                    ElabError::TempArgFailed => {
                        sti::write!(&mut msg, "(temp): arg failed");
                    }

                    ElabError::TempCtorArgLevelCouldBeTooLarge => {
                        sti::write!(&mut msg, "(temp): maybe ctor arg level too large");
                    }

                    ElabError::TempUnimplemented => {
                        sti::write!(&mut msg, "(temp): unimplemented");
                    }

                    ElabError::TempStr(str) => {
                        sti::write!(&mut msg, "(temp) msg: {}", str);
                    }
                }
            }

            DiagnosticKind::TyCkError(e) => {
                let elab = &self.elab_datas[source.elab.unwrap()];
                let env = &elab.env;

                let mut pp = crate::tt::TermPP::new(env, &self.strings, &e.lctx, alloc);

                use crate::tt::tyck::ErrorKind as EK;
                match e.err.kind {
                    EK::LooseBVar => todo!(),
                    EK::LooseLocal => todo!(),
                    EK::TermIVar => todo!(),
                    EK::GlobalNotReady => todo!(),
                    EK::GlobalLevelMismatch => todo!(),
                    EK::TypeExpected { found: _ } => todo!(),

                    EK::TypeInvalid { found: _, expected: _ } => todo!(),

                    EK::LetValTypeInvalid { found: _ } => todo!(),

                    EK::AppArgTypeInvalid { found, expected } => {
                        sti::write!(&mut msg, "[tyck type invalid] ");
                        sti::write!(&mut msg, "expected ");
                        let expected = pp.pp_term(expected);
                        pp.render(expected, 50).layout_into_string(&mut msg);
                        sti::write!(&mut msg, ", found ");
                        let found = pp.pp_term(found);
                        pp.render(found, 50).layout_into_string(&mut msg);
                    }

                    EK::LevelParamIndexInvalid => todo!(),

                    EK::LevelIVar => todo!(),
                }

                sti::write!(&mut msg, " at:\n");
                let at = pp.pp_term(e.err.at);
                pp.render(at, 120).layout_into_string(&mut msg);
            }
        };
        let message = msg.leak();

        FileDiagnostic { range, message }
    }
}


pub struct HoverInfo<'a> {
    pub lang: Option<&'a str>,
    pub content: &'a str,
}

impl<'c> Inner<'c> {
    pub fn query_hover_info<'out>(&mut self, path: &str, line: u32, col: u32, alloc: &'out Arena) -> Vec<HoverInfo<'out>> {
        self.update();

        let Some(source_id) = self.path_to_source.get(path).copied() else {
            // @todo: diagnostic.
            return Vec::new();
        };

        let source = &self.source_datas[self.sources[source_id].unwrap()];
        debug_assert!(!source.dirty);

        let parse = &self.parse_datas[source.parse.unwrap()].parse;
        debug_assert_eq!(parse.source_range.begin, 0);
        debug_assert_eq!(parse.source_range.end,   source.code.len() as u32);

        let elab_data = &self.elab_datas[source.elab.unwrap()];
        let elab = &elab_data.elab;


        let Some((token_id, is_hit)) = hit_test_token(line, col, source, parse) else {
            return Vec::new();
        };

        if is_hit { if let Some(info) = elab.token_infos.get(&token_id) {
            let mut buf = String::new_in(alloc);
            match *info {
                elab::TokenInfo::Local(item_id, id) => {
                    let ctx = elab.item_ctxs[item_id].as_ref().unwrap();

                    let local = ctx.local_ctx.lookup(id);
                    let name = if local.name == Atom::NULL { "_" } else { &self.strings[local.name] };
                    sti::write!(&mut buf, "{name}: ");

                    let mut pp = crate::tt::TermPP::new(&elab_data.env, &self.strings, &ctx.local_ctx, alloc);
                    let ty = ctx.ivar_ctx.instantiate_term_vars(local.ty, alloc);
                    let ty = pp.pp_term(ty);
                    let ty = pp.render(ty, 50);
                    ty.layout_into_string(&mut buf);
                }

                elab::TokenInfo::Symbol(id) => {
                    let temp = ArenaPool::tls_get_temp();
                    let mut parts = Vec::new_in(&*temp);
                    let mut at = id;
                    while at != SymbolId::ROOT {
                        let symbol = elab_data.env.symbol(at);
                        parts.push(symbol.name);
                        at = symbol.parent;
                    }
                    for (i, part) in parts.copy_it().rev().enumerate() {
                        if i != 0 { sti::write!(&mut buf, "::"); }
                        sti::write!(&mut buf, "{}", &self.strings[part]);
                    }
                }
            }
            return sti::vec![HoverInfo { lang: Some("kibi"), content: buf.leak() }];
        }}

        let Some((hit_item, hit)) = hit_test_items(token_id, parse) else {
            return Vec::new();
        };
        let Some(ctx) = &elab.item_ctxs[hit_item] else {
            return Vec::new();
        };

        let mut buf = String::new_in(alloc);
        match hit {
            AstId::Item(id) => {
                if let Some(info) = elab.item_infos[id] {
                    match info {
                        elab::ItemInfo::Symbol(_) => (),
                        elab::ItemInfo::Reduce(value) => {
                            let mut pp = crate::tt::TermPP::new(&elab_data.env, &self.strings, &ctx.local_ctx, alloc);
                            let v = ctx.ivar_ctx.instantiate_term_vars(value, alloc);
                            let v = pp.pp_term(v);
                            let v = pp.render(v, 50);
                            v.layout_into_string(&mut buf);
                        }
                    }
                }
            }

            AstId::Stmt(_) => (),

            AstId::Level(_) => (),

            AstId::Expr(id) => {
                if let Some(info) = elab.expr_infos[id] {
                    let term_begin = buf.len();
                    let mut pp = crate::tt::TermPP::new(&elab_data.env, &self.strings, &ctx.local_ctx, alloc);
                    let term = ctx.ivar_ctx.instantiate_term_vars(info.term, alloc);
                    let term = pp.pp_term(term);
                    let term = pp.render(term, 50);
                    term.layout_into_string(&mut buf);

                    if buf.len() - term_begin > 40 {
                        sti::write!(&mut buf, "\n");
                    }
                    sti::write!(&mut buf, ": ");

                    let ty = ctx.ivar_ctx.instantiate_term_vars(info.ty, alloc);
                    let ty = pp.pp_term(ty);
                    let ty = pp.render(ty, 50);
                    ty.layout_into_string(&mut buf);

                    // @todo: keep?
                    if let Some(local) = info.term.try_local() {
                        let entry = ctx.local_ctx.lookup(local);
                        if let crate::tt::ScopeKind::Local(val) = entry.kind {
                            sti::write!(&mut buf, " := ");
                            let val = ctx.ivar_ctx.instantiate_term_vars(val, alloc);
                            let val = pp.pp_term(val);
                            let val = pp.render(val, 50);
                            val.layout_into_string(&mut buf);
                        }
                    }
                }
            }

            AstId::Tactic(id) => {
                if let Some(info) = elab.tactic_infos[id] {
                    let mut pp = crate::tt::TermPP::new(&elab_data.env, &self.strings, &ctx.local_ctx, alloc);

                    match info.kind {
                        elab::TacticInfoKind::None => (),

                        elab::TacticInfoKind::Term(term) => {
                            sti::write!(&mut buf, "term: ");
                            let term = ctx.ivar_ctx.instantiate_term_vars(term, alloc);
                            let term = pp.pp_term(term);
                            let term = pp.render(term, 60);
                            term.layout_into_string(&mut buf);
                        }
                    }
                }
            }
        }

        if buf.len() > 0 {
            return sti::vec![HoverInfo { lang: Some("kibi"), content: buf.leak() }];
        }
        else { return Vec::new() }
    }
}


pub struct InfoPanel<'a> {
    pub lines: &'a [&'a str],
}

impl<'c> Inner<'c> {
    pub fn query_info_panel<'out>(&mut self, path: &str, line: u32, col: u32, width: u32, alloc: &'out Arena) -> InfoPanel<'out> {
        self.update();

        let Some(source_id) = self.path_to_source.get(path).copied() else {
            return InfoPanel {
                lines: alloc.alloc_new([
                    sti::format_in!(alloc, "invalid uri {:?}", path).leak(),
                ]),
            };
        };

        let source = &self.source_datas[self.sources[source_id].unwrap()];
        debug_assert!(!source.dirty);

        let parse = &self.parse_datas[source.parse.unwrap()].parse;
        debug_assert_eq!(parse.source_range.begin, 0);
        debug_assert_eq!(parse.source_range.end,   source.code.len() as u32);

        let elab_data = &self.elab_datas[source.elab.unwrap()];
        let elab = &elab_data.elab;


        let Some((hit_token, _)) = hit_test_token(line, col, source, parse) else {
            return InfoPanel { lines: &[] };
        };
        let Some((hit_item, hit)) = hit_test_items(hit_token, parse) else {
            return InfoPanel { lines: &[] };
        };
        let Some(ctx) = &elab.item_ctxs[hit_item] else {
            return InfoPanel { lines: &[] };
        };

        match hit {
            AstId::Tactic(it) => {
                let Some(info) = &elab.tactic_infos[it] else {
                    return InfoPanel { lines: &[] };
                };

                let mut lines = Vec::with_cap_in(alloc, 32);

                let mut pp = crate::tt::TermPP::new(&elab_data.env, &self.strings, &ctx.local_ctx, alloc);

                let mut buf = String::with_cap_in(alloc, 1024);

                // locals
                for local in info.locals.copy_it() {
                    let local = ctx.local_ctx.lookup(local);
                    let ty = ctx.ivar_ctx.instantiate_term_vars(local.ty, alloc);
                    let ty = pp.pp_term(ty);
                    let local = pp.cat(
                        pp.text(sti::format_in!(alloc, "{}: ",
                            &self.strings[local.name]).leak()),
                        ty);
                    let local = pp.render(local, width as i32);
                    local.layout_into_string(&mut buf);
                    buf.push_char('\n');
                }
                if info.locals.len() > 0 {
                    buf.push_char('\n');
                }

                for goal in info.goals.copy_it() {
                    let goal = ctx.ivar_ctx.instantiate_term_vars(goal, alloc);
                    let goal = pp.pp_term(goal);
                    let goal = pp.cat(pp.text("goal: "), goal);
                    let goal = pp.render(goal, width as i32);
                    goal.layout_into_string(&mut buf);
                    buf.push_char('\n');
                }
                let buf = buf.leak();

                // this is kinda dumb. whatever.
                for line in buf.lines() {
                    lines.push(line);
                }

                InfoPanel { lines: lines.leak() }
            }

            _ => {
                InfoPanel { lines: &[] }
            }
        }
    }
}



use crate::ast::{ItemKind, StmtKind, LevelKind, ExprKind, TacticKind, Binder};

fn hit_test_token(line: u32, col: u32, source: &SourceData, parse: &Parse) -> Option<(TokenId, bool)> {
    // convert to offset.
    // @temp line table.
    let mut lines_i = 0;
    let code = &*source.code;
    let mut lines = core::iter::from_fn(|| {
        let start = lines_i;
        while lines_i < code.len() {
            if code[lines_i] == b'\n' {
                lines_i += 1;
                return Some(lines_i - start);
            }
            lines_i += 1;
        }
        None
    });
    let mut offset = col;
    for _ in 0..line {
        let Some(len) = lines.next() else {
            // error?
            return None;
        };
        offset += len as u32;
    }

    // find token.
    for (id, token) in parse.tokens.iter() {
        if offset < token.source.end {
            let is_hit = offset >= token.source.begin;
            return Some((id, is_hit));
        }
    }
    return None;
}

// @cleanup: visit children.
fn hit_test_ast(node: AstId, pos: TokenId, parse: &Parse) -> Option<AstId> {
    match node {
        AstId::Item(id) => {
            let item = &parse.items[id];
            if !item.source.contains(pos) { return None }

            let hit = match &item.kind {
                ItemKind::Error => None,

                ItemKind::Axiom(it) =>
                    hit_test_binders(it.params, pos, parse).or_else(||
                    hit_test_ast(it.ty.into(), pos, parse)),

                ItemKind::Def(it) =>
                    hit_test_binders(it.params, pos, parse).or_else(||
                    it.ty.to_option().and_then(|ty|
                        hit_test_ast(ty.into(), pos, parse))).or_else(||
                    hit_test_ast(it.value.into(), pos, parse)),

                ItemKind::Reduce(it) =>
                    hit_test_ast((*it).into(), pos, parse),

                ItemKind::Inductive(_) =>
                    None,

                ItemKind::Trait(_) =>
                    None,

                ItemKind::Impl(_) =>
                    None,
            };
            Some(hit.unwrap_or(id.into()))
        }

        AstId::Stmt(id) => {
            let stmt = parse.stmts[id];
            if !stmt.source.contains(pos) { return None }

            let hit = match stmt.kind {
                StmtKind::Error => None,

                StmtKind::Let(it) =>
                    it.ty.to_option().and_then(|ty|
                        hit_test_ast(ty.into(), pos, parse)).or_else(||
                    it.val.to_option().and_then(|val|
                        hit_test_ast(val.into(), pos, parse))),

                StmtKind::Assign(lhs, rhs) =>
                    hit_test_ast(lhs.into(), pos, parse).or_else(||
                    hit_test_ast(rhs.into(), pos, parse)),

                StmtKind::Expr(it) =>
                    hit_test_ast(it.into(), pos, parse)
            };
            Some(hit.unwrap_or(id.into()))
        }

        AstId::Level(id) => {
            let level = parse.levels[id];
            if !level.source.contains(pos) { return None }

            let hit = match level.kind {
                LevelKind::Error => None,
                LevelKind::Hole => None,
                LevelKind::Ident(_) => None,
                LevelKind::Nat(_) => None,

                LevelKind::Add((lhs, _)) =>
                    hit_test_ast(lhs.into(), pos, parse),

                LevelKind::Max((lhs, rhs)) |
                LevelKind::IMax((lhs, rhs)) =>
                    hit_test_ast(lhs.into(), pos, parse).or_else(||
                    hit_test_ast(rhs.into(), pos, parse)),
            };
            Some(hit.unwrap_or(id.into()))
        }

        AstId::Expr(id) => {
            let expr = parse.exprs[id];
            if !expr.source.contains(pos) { return None }

            let hit = match expr.kind {
                ExprKind::Error => None,
                ExprKind::Hole => None,
                ExprKind::Ident(_) => None,
                ExprKind::DotIdent(_) => None,
                ExprKind::Path(_) => None,
                ExprKind::Levels(_) => None,
                ExprKind::Sort(_) => None,
                ExprKind::Bool(_) => None,
                ExprKind::Number(_) => None,
                ExprKind::String(_) => None,

                ExprKind::Parens(it) => hit_test_ast(it.into(), pos, parse),

                ExprKind::Forall(it) |
                ExprKind::Lambda(it) =>
                    hit_test_binders(it.binders, pos, parse).or_else(||
                    hit_test_ast(it.value.into(), pos, parse)),

                ExprKind::Let(it) =>
                    it.ty.to_option().and_then(|ty|
                        hit_test_ast(ty.into(), pos, parse)).or_else(||
                    hit_test_ast(it.val.into(), pos, parse).or_else(||
                    hit_test_ast(it.body.into(), pos, parse))),

                ExprKind::By(it) => {
                    let mut result = None;
                    for id in it.copy_it() {
                        if let Some(hit) = hit_test_ast(id.into(), pos, parse) {
                            result = Some(hit);
                            break;
                        }
                    }
                    result
                }

                ExprKind::Ref(it) =>
                    hit_test_ast(it.expr.into(), pos, parse),

                ExprKind::Deref(it) =>
                    hit_test_ast(it.into(), pos, parse),

                ExprKind::Eq(lhs, rhs) =>
                    hit_test_ast(lhs.into(), pos, parse).or_else(||
                    hit_test_ast(rhs.into(), pos, parse)),

                ExprKind::Op1(it) =>
                    hit_test_ast(it.expr.into(), pos, parse),

                ExprKind::Op2(it) =>
                    hit_test_ast(it.lhs.into(), pos, parse).or_else(||
                    hit_test_ast(it.rhs.into(), pos, parse)),

                ExprKind::Field(it) =>
                    hit_test_ast(it.base.into(), pos, parse),

                ExprKind::Index(it) =>
                    hit_test_ast(it.base.into(), pos, parse).or_else(||
                    hit_test_ast(it.index.into(), pos, parse)),

                ExprKind::Call(it) =>
                    hit_test_ast(it.func.into(), pos, parse).or_else(||
                    it.args.copy_it().find_map(|arg|
                        hit_test_ast(arg.into(), pos, parse))),

                ExprKind::Do(it) => {
                    let mut result = None;
                    for stmt in it.stmts.copy_it() {
                        if let Some(hit) = hit_test_ast(stmt.into(), pos, parse) {
                            result = Some(hit);
                            break;
                        }
                    }
                    result
                }

                ExprKind::If(it) =>
                    hit_test_ast(it.cond.into(), pos, parse).or_else(||
                    hit_test_ast(it.then.into(), pos, parse).or_else(||
                    it.els.to_option().and_then(|els|
                        hit_test_ast(els.into(), pos, parse)))),

                ExprKind::While(it) =>
                    hit_test_ast(it.cond.into(), pos, parse).or_else(||
                    hit_test_ast(it.body.into(), pos, parse).or_else(||
                    it.els.to_option().and_then(|els|
                        hit_test_ast(els.into(), pos, parse)))),

                ExprKind::Loop(it) => {
                    let mut result = None;
                    for stmt in it.stmts.copy_it() {
                        if let Some(hit) = hit_test_ast(stmt.into(), pos, parse) {
                            result = Some(hit);
                            break;
                        }
                    }
                    result
                }

                ExprKind::Break(it) =>
                    it.value.to_option().and_then(|value|
                        hit_test_ast(value.into(), pos, parse)),

                ExprKind::Continue(_) => None,

                ExprKind::ContinueElse(_) => None,

                ExprKind::Return(it) =>
                    it.to_option().and_then(|value|
                        hit_test_ast(value.into(), pos, parse)),

                ExprKind::TypeHint(it) =>
                    hit_test_ast(it.expr.into(), pos, parse).or_else(||
                    hit_test_ast(it.ty.into(), pos, parse)),
            };
            Some(hit.unwrap_or(id.into()))
        }

        AstId::Tactic(id) => {
            let tactic = parse.tactics[id];
            if !tactic.source.contains(pos) { return None }

            let hit = match tactic.kind {
                TacticKind::Error => None,

                TacticKind::Goal => None,
                TacticKind::Sorry => None,
                TacticKind::Assumption => None,
                TacticKind::Refl => None,

                TacticKind::Rewrite(it) =>
                    hit_test_ast(it.with.into(), pos, parse),

                TacticKind::By(it) => {
                    let mut result = None;
                    for id in it.copy_it() {
                        if let Some(hit) = hit_test_ast(id.into(), pos, parse) {
                            result = Some(hit);
                            break;
                        }
                    }
                    result
                }

                TacticKind::Intro(_) => None,

                TacticKind::Unfold(_) => None,

                TacticKind::Exact(it) => hit_test_ast(it.into(), pos, parse),

                TacticKind::Apply(it) => hit_test_ast(it.into(), pos, parse),
            };
            Some(hit.unwrap_or(id.into()))
        }
    }
}

fn hit_test_binders(binders: &[Binder], pos: TokenId, parse: &Parse) -> Option<AstId> {
    for binder in binders {
        let hit = match binder {
            Binder::Ident(_) => None,

            Binder::Typed(it) =>
                hit_test_ast(it.ty.into(), pos, parse)
        };
        if hit.is_some() {
            return hit;
        }
    }
    None
}

fn hit_test_items(pos: TokenId, parse: &Parse) -> Option<(ItemId, AstId)> {
    for item in parse.root_items.copy_it() {
        if let Some(hit) = hit_test_ast(item.into(), pos, parse) {
            return Some((item, hit));
        }
    }
    None
}


