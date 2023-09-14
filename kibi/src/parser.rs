use sti::arena::Arena;
use sti::arena_pool::ArenaPool;
use sti::vec::Vec;
use sti::keyed::KVec;
use sti::reader::Reader;

use crate::string_table::{StringTable, Atom, atoms};
use crate::diagnostics::*;
use crate::ast::*;



pub struct Parse<'a> {
    pub source: SourceId,
    pub source_range: SourceRange,

    pub diagnostics: Diagnostics<'a>,

    pub numbers: KVec<ParseNumberId, &'a str>,
    pub strings: KVec<ParseStringId, &'a str>,
    pub tokens:  KVec<TokenId, Token>,

    pub items:  KVec<ItemId,  Item<'a>>,
    pub levels: KVec<LevelId, Level>,
    pub exprs:  KVec<ExprId,  Expr<'a>>,

    pub root_items: Vec<ItemId>,
}

impl<'a> Parse<'a> {
    #[inline]
    pub fn resolve_parse_range(&self, range: ParseRange) -> SourceRange {
        debug_assert!(range.begin <= range.end);
        debug_assert!(range.end <= self.source_range.end - self.source_range.begin);
        SourceRange {
            begin: self.source_range.begin + range.begin,
            end:   self.source_range.begin + range.end,
        }
    }

    #[inline]
    pub fn resolve_token_range(&self, range: TokenRange) -> SourceRange {
        let first = range.idx(0);
        let last  = range.rev(0);
        SourceRange {
            begin: self.source_range.begin + self.tokens[first].source.begin,
            end:   self.source_range.begin + self.tokens[last].source.end,
        }
    }
}



// @todo: return `ItemId`.
pub fn parse_file<'out>(input: &[u8], parse: &mut Parse<'out>, strings: &mut StringTable, alloc: &'out Arena) {
    tokenize(input, parse, strings, alloc);

    spall::trace_scope!("kibi/parse_file");
    let mut parser = Parser { parse, strings, alloc, token_cursor: 0 };

    while parser.peek().0.kind != TokenKind::EndOfFile {
        if let Some(item) = parser.parse_item(crate::ast::AstParent::None) {
            parser.parse.root_items.push(item);
        }
        else { break }
    }
}


pub fn tokenize<'out>(input: &[u8], parse: &mut Parse<'out>, strings: &mut StringTable, alloc: &'out Arena) {
    spall::trace_scope!("kibi/tok");

    let mut tok = Tokenizer {
        alloc,
        strings,
        parse,
        reader: Reader::new(input),
    };
    while tok.next() {}
    debug_assert_eq!(tok.reader.remaining(), 0);

    parse.tokens.push(Token {
        source: ParseRange { begin: input.len() as u32, end: input.len() as u32 },
        kind: TokenKind::EndOfFile,
    });
}


pub struct Tokenizer<'me, 'c, 'i, 'out> {
    pub alloc: &'out Arena,

    pub strings: &'me mut StringTable<'c>,
    pub parse: &'me mut Parse<'out>,

    pub reader: Reader<'i, u8>,
}

impl<'me, 'c, 'i, 'out> Tokenizer<'me, 'c, 'i, 'out> {
    pub fn next(&mut self) -> bool {
        loop {
            self.skip_ws();

            if self.reader.starts_with(b"--") {
                self.reader.consume(2);
                self.reader.consume_while(|at| *at != b'\n');
                continue;
            }

            break;
        }

        let begin_offset = self.reader.offset();
        let Some(at) = self.reader.next() else {
            return false;
        };

        let kind = 'kind: {
            // operators & punctuation.
            'next: { break 'kind match at as char {
                '(' => TokenKind::LParen,
                ')' => TokenKind::RParen,
                '[' => TokenKind::LBracket,
                ']' => TokenKind::RBracket,
                '{' => TokenKind::LCurly,
                '}' => TokenKind::RCurly,

                '.' => TokenKind::Dot,
                ',' => TokenKind::Comma,
                ';' => TokenKind::Semicolon,

                ':' => {
                    if self.reader.consume_if_eq(&b':') {
                        TokenKind::ColonColon
                    }
                    else if self.reader.consume_if_eq(&b'=') {
                        TokenKind::ColonEq
                    }
                    else { TokenKind::Colon }
                }

                '+' => {
                    if self.reader.consume_if_eq(&b'=') {
                        TokenKind::AddAssign
                    }
                    else { TokenKind::Add }
                }

                '-' => {
                    if self.reader.consume_if_eq(&b'=') {
                        TokenKind::SubAssign
                    }
                    else if self.reader.consume_if_eq(&b'>') {
                        TokenKind::Arrow
                    }
                    else { TokenKind::Minus }
                }

                '*' => {
                    if self.reader.consume_if_eq(&b'=') {
                        TokenKind::MulAssign
                    }
                    else { TokenKind::Star }
                }

                '/' => {
                    if self.reader.consume_if_eq(&b'=') {
                        TokenKind::DivAssign
                    }
                    else if self.reader.consume_if_eq(&b'/') {
                        if self.reader.consume_if_eq(&b'=') {
                            TokenKind::FloorDivAssign
                        }
                        else { TokenKind::FloorDiv }
                    }
                    else { TokenKind::Div }
                }

                '%' => {
                    if self.reader.consume_if_eq(&b'=') {
                        TokenKind::RemAssign
                    }
                    else { TokenKind::Rem }
                }

                '=' => {
                    if self.reader.consume_if_eq(&b'=') {
                        TokenKind::EqEq
                    }
                    else if self.reader.consume_if_eq(&b'>') {
                        TokenKind::FatArrow
                    }
                    else { TokenKind::Eq }
                }

                '!' => {
                    if self.reader.consume_if_eq(&b'=') {
                        TokenKind::NotEq
                    }
                    else { TokenKind::Not }
                }

                '<' => {
                    if self.reader.consume_if_eq(&b'=') {
                        TokenKind::Le
                    }
                    else { TokenKind::Lt }
                }

                '>' => {
                    if self.reader.consume_if_eq(&b'=') {
                        TokenKind::Ge
                    }
                    else { TokenKind::Gt }
                }

                '\u{CE}' => {
                    // Π
                    if self.reader.consume_if_eq(&0xA0) {
                        TokenKind::KwPi
                    }
                    // λ
                    else if self.reader.consume_if_eq(&0xBB) {
                        TokenKind::KwLam
                    }
                    else { break 'next }
                }

                _ => break 'next
            }}

            // strings.
            if at == '"' as u8 {
                let mut is_escaped = false;
                let (value, no_eoi) = self.reader.consume_while_slice(|at| {
                    let done = !is_escaped && *at == b'"';
                    is_escaped = *at == b'\\' as u8 && !is_escaped;
                    return !done;
                });
                if no_eoi { self.reader.consume(1) }
                // else: @todo: error.

                let value = unsafe { core::str::from_utf8_unchecked(value) };

                let value = self.alloc.alloc_str(value);
                TokenKind::String(self.parse.strings.push(value))
            }
            // f-strings.
            /*
            else if at == 'f' as u8 && self.reader.next_if(|at| at == '"' as u8).is_some() {
                unimplemented!()
            }
            */
            // idents & keywords.
            else if at.is_ascii_alphabetic() || at == b'_' {
                let (value, _) = self.reader.consume_while_slice_from(begin_offset, |at|
                    at.is_ascii_alphanumeric() || *at == b'_');

                let value = unsafe { core::str::from_utf8_unchecked(value) };

                // keywords.
                match value {
                    "_" => TokenKind::Hole,

                    "Sort" => TokenKind::KwSort,
                    "Prop" => TokenKind::KwProp,
                    "Type" => TokenKind::KwType,
                    "lam"  => TokenKind::KwLam,
                    "Pi"   => TokenKind::KwPi,

                    "inductive" => TokenKind::KwInductive,
                    "struct" => TokenKind::KwStruct,
                    "enum" => TokenKind::KwEnum,
                    "def" => TokenKind::KwDef,

                    "trait" => TokenKind::KwTrait,
                    "impl" => TokenKind::KwImpl,

                    "let" => TokenKind::KwLet,
                    "var" => TokenKind::KwVar,

                    "do" => TokenKind::KwDo,

                    "if" => TokenKind::KwIf,
                    "elif" => TokenKind::KwElif,
                    "else" => TokenKind::KwElse,

                    "while" => TokenKind::KwWhile,
                    "for" => TokenKind::KwFor,
                    "in" => TokenKind::KwIn,

                    "break" => TokenKind::KwBreak,
                    "continue" => TokenKind::KwContinue,
                    "return" => TokenKind::KwReturn,

                    "fn" => TokenKind::KwFn,

                    "and" => TokenKind::KwAnd,
                    "or"  => TokenKind::KwOr,
                    "not" => TokenKind::KwNot,

                    _ => {
                        let atom = self.strings.insert(value);
                        TokenKind::Ident(atom)
                    }
                }
            }
            // numbers.
            else if at.is_ascii_digit() {
                // before decimal.
                self.reader.consume_while(|at| at.is_ascii_digit());

                // decimal.
                if let Some(b'.') = self.reader.get(0) {
                    if let Some(after_decimal) = self.reader.get(1) {
                        if after_decimal.is_ascii_digit() {
                            self.reader.consume(1);

                            // after decimal.
                            self.reader.consume_while(|at| at.is_ascii_digit());
                        }
                    }
                }

                let value = &self.reader.consumed_slice()[begin_offset..];
                let value = unsafe { core::str::from_utf8_unchecked(value) };

                let value = self.alloc.alloc_str(value);
                TokenKind::Number(self.parse.numbers.push(value))
            }
            // error.
            else {
                TokenKind::Error
            }
        };

        let end_offset = self.reader.offset();
        let source = ParseRange {
            begin: begin_offset as u32,
            end:   end_offset as u32,
        };
        self.parse.tokens.push(Token { source, kind });

        return true;
    }


    fn skip_ws(&mut self) {
        self.reader.consume_while(|at|
            *at == b' ' || *at == b'\n' || *at == b'\r');
    }
}


pub struct Parser<'me, 'c, 'out> {
    pub alloc:  &'out Arena,
    pub strings: &'me StringTable<'c>,

    pub parse: &'me mut Parse<'out>,
    pub token_cursor: usize,
}

impl<'me, 'c, 'out> Parser<'me, 'c, 'out> {
    pub fn parse_item(&mut self, parent: AstParent) -> Option<ItemId> {
        let (at, source_begin) = self.next();

        let this_item = self.parse.items.push(Item {
            parent,
            source: TokenRange::ZERO,
            kind: ItemKind::Error,
        });
        let this_parent = Some(AstId::Item(this_item));

        let kind = match at.kind {
            TokenKind::Ident(atoms::axiom) => {
                let name = self.expect_ident()?;
                let name = self.parse_ident_or_path(name)?;

                let mut levels = &mut [][..];
                if self.consume_if_eq(TokenKind::Dot) {
                    self.expect(TokenKind::LCurly)?;
                    levels = self.sep_by(TokenKind::Comma, TokenKind::RCurly, |this| {
                        this.expect_ident()
                    })?;
                }

                let params = self.parse_binders(this_parent, false)?;

                self.expect(TokenKind::Colon)?;
                let ty = self.parse_type(this_parent)?;

                ItemKind::Axiom(item::Axiom { name, levels, params, ty })
            }

            TokenKind::KwInductive => {
                ItemKind::Inductive(self.parse_inductive(this_parent)?)
            }

            TokenKind::KwDef => {
                let name = self.expect_ident()?;
                let name = self.parse_ident_or_path(name)?;

                let mut levels = &mut [][..];
                if self.consume_if_eq(TokenKind::Dot) {
                    self.expect(TokenKind::LCurly)?;
                    levels = self.sep_by(TokenKind::Comma, TokenKind::RCurly, |this| {
                        this.expect_ident()
                    })?;
                }

                let params = self.parse_binders(this_parent, false)?;

                let mut ty = None.into();
                if self.consume_if_eq(TokenKind::Colon) {
                    ty = self.parse_type(this_parent)?.some();
                }

                self.expect(TokenKind::ColonEq)?;

                let value = self.parse_expr(this_parent)?;

                ItemKind::Def(item::Def { name, levels, params, ty, value })
            }

            TokenKind::KwTrait => {
                self.expect(TokenKind::KwInductive)?;
                ItemKind::Trait(item::Trait::Inductive(self.parse_inductive(this_parent)?))
            }

            TokenKind::KwImpl => {
                //let name = self.expect_ident()?;
                //let name = self.parse_ident_or_path(name)?;

                let mut levels = &mut [][..];
                if self.consume_if_eq(TokenKind::Dot) {
                    self.expect(TokenKind::LCurly)?;
                    levels = self.sep_by(TokenKind::Comma, TokenKind::RCurly, |this| {
                        this.expect_ident()
                    })?;
                }

                let params = self.parse_binders(this_parent, false)?;

                self.expect(TokenKind::Colon)?;
                let ty = self.parse_type(this_parent)?;

                self.expect(TokenKind::ColonEq)?;

                let value = self.parse_expr(this_parent)?;

                ItemKind::Impl(item::Impl { levels, params, ty, value })
            }

            TokenKind::Ident(atoms::reduce) => {
                let expr = self.parse_expr(this_parent)?;
                ItemKind::Reduce(expr)
            }

            _ => {
                self.error_unexpected(at, source_begin);
                return None;
            }
        };

        let source = self.token_range_from(source_begin);

        let this = &mut self.parse.items[this_item];
        this.source = source;
        this.kind = kind;

        return Some(this_item);
    }


    pub fn parse_expr(&mut self, parent: AstParent) -> Option<ExprId> {
        self.parse_expr_exw(parent, ParseExprFlags::default(), 0)
    }

    pub fn parse_expr_ex(&mut self, parent: AstParent, prec: u32) -> Option<ExprId> {
        self.parse_expr_exw(parent, ParseExprFlags::default(), prec)
    }

    pub fn parse_type(&mut self, parent: AstParent) -> Option<ExprId> {
        self.parse_expr_exw(parent, ParseExprFlags::default().with_ty(), 0)
    }

    pub fn parse_type_ex(&mut self, parent: AstParent, prec: u32) -> Option<ExprId> {
        self.parse_expr_exw(parent, ParseExprFlags::default().with_ty(), prec)
    }

    pub fn parse_expr_exw(&mut self, parent: AstParent, flags: ParseExprFlags, prec: u32) -> Option<ExprId> {
        let token_begin = self.current_token_id();

        let mut result = self.parse_leading_expr(parent, flags, prec)?;

        loop {
            let (at, _) = self.peek();

            // equality type.
            if flags.ty && at.kind == TokenKind::Eq && PREC_EQ >= prec {
                self.consume(1);

                let (this_expr, this_parent) = self.new_expr_uninit(parent);
                self.parse.exprs[result].parent = this_parent;

                let lhs = result;
                let rhs = self.parse_expr_ex(this_parent, PREC_EQ)?;

                let kind = ExprKind::Eq(lhs, rhs);

                self.expr_init_from(this_expr, token_begin, kind);

                result = this_expr;
                continue;
            }

            // infix operators.
            if let Some(op) = InfixOp::from_token(at) {
                let allowed = !flags.no_cmp || (
                       op != InfixOp::Op2(expr::Op2Kind::CmpLt)
                    && op != InfixOp::Op2(expr::Op2Kind::CmpGt)
                );

                if allowed && op.lprec() >= prec {
                    self.consume(1);

                    let (this_expr, this_parent) = self.new_expr_uninit(parent);
                    self.parse.exprs[result].parent = this_parent;

                    let lhs = result;
                    let rhs = self.parse_expr_ex(this_parent, op.rprec())?;

                    let kind = match op {
                        InfixOp::Assign =>
                            ExprKind::Assign(expr::Assign { lhs, rhs }),

                        InfixOp::Op2Assign(op) =>
                            ExprKind::Op2Assign(expr::Op2 { op, lhs, rhs }),

                        InfixOp::Op2(op) =>
                            ExprKind::Op2(expr::Op2 { op, lhs, rhs }),
                    };

                    self.expr_init_from(this_expr, token_begin, kind);

                    result = this_expr;
                    continue;
                }
            }

            // arrow function.
            // @speed: merge multiple arrows.
            if at.kind == TokenKind::Arrow && PREC_ARROW >= prec {
                self.consume(1);

                let (this_expr, this_parent) = self.new_expr_uninit(parent);
                self.parse.exprs[result].parent = this_parent;

                let lhs = result;
                let rhs = self.parse_type_ex(this_parent, PREC_ARROW)?;

                // @arrow_uses_null_ident
                let name = OptIdent {
                    source: self.parse.exprs[lhs].source.first(),
                    value: Atom::NULL.some(),
                };
                let kind = ExprKind::Forall(expr::Forall {
                    binders: &self.alloc.alloc_new([
                        Binder::Typed(TypedBinder {
                            implicit: false,
                            names: &self.alloc.alloc_new([name])[..],
                            ty: lhs,
                            default: None.into(),
                        }),
                    ])[..],
                    ret: rhs,
                });

                self.expr_init_from(this_expr, token_begin, kind);

                result = this_expr;
                continue;
            }

            // postfix operators.
            if PREC_POSTFIX < prec {
                break;
            }

            if at.kind == TokenKind::Dot {
                self.consume(1);

                let (this_expr, this_parent) = self.new_expr_uninit(parent);
                self.parse.exprs[result].parent = this_parent;

                let (at, at_src) = self.next();
                let kind = match at.kind {
                    // field.
                    TokenKind::Ident(name) => {
                        ExprKind::Field(expr::Field {
                            name: Ident { source: at_src, value: name },
                            base: result,
                        })
                    }

                    // levels
                    TokenKind::LCurly => {
                        let r = self.parse.exprs[result];
                        let symbol = match r.kind {
                            ExprKind::Ident(name) => IdentOrPath::Ident(name),
                            ExprKind::Path(path)  => IdentOrPath::Path(path),
                            _ => {
                                self.error_expect_expr(result, "ident | path");
                                return None;
                            }
                        };

                        let levels = self.sep_by(TokenKind::Comma, TokenKind::RCurly, |this| {
                            this.parse_level(this_parent)
                        })?;

                        ExprKind::Levels(expr::Levels { symbol, levels })
                    }

                    _ => {
                        self.error_expect(at_src, "ident | '{'");
                        return None;
                    }
                };
                self.expr_init_from(this_expr, token_begin, kind);

                result = this_expr;
                continue;
            }

            if at.kind == TokenKind::LParen {
                self.consume(1);

                let (this_expr, this_parent) = self.new_expr_uninit(parent);
                self.parse.exprs[result].parent = this_parent;


                let args = self.sep_by(TokenKind::Comma, TokenKind::RParen, |this| {
                    this.parse_expr(this_parent)
                })?;

                self.expr_init_from(this_expr, token_begin,
                    ExprKind::Call(expr::Call {
                        func: result,
                        args,
                    }));

                result = this_expr;
                continue;
            }

            break;
        }

        return Some(result);
    }

    fn parse_leading_expr(&mut self, parent: AstParent, flags: ParseExprFlags, prec: u32) -> Option<ExprId> {
        let (at, source_begin) = self.next();

        let (this_expr, this_parent) = self.new_expr_uninit(parent);

        let kind = 'kind: {
            'next: { break 'kind match at.kind {
                TokenKind::Hole => {
                    ExprKind::Hole
                }

                TokenKind::Ident(ident) => {
                    match self.parse_ident_or_path(Ident { source: source_begin, value: ident })? {
                        IdentOrPath::Ident(ident) => ExprKind::Ident(ident),
                        IdentOrPath::Path(path) => ExprKind::Path(path),
                    }
                }

                TokenKind::Dot => {
                    let ident = self.expect_ident()?;
                    ExprKind::DotIdent(ident)
                }


                TokenKind::KwSort => {
                    self.expect(TokenKind::LParen)?;
                    let level = self.parse_level(this_parent)?;
                    self.expect(TokenKind::RParen)?;
                    ExprKind::Sort(level)
                }

                TokenKind::KwProp => {
                    let source = self.token_range_from(source_begin);
                    let level = self.parse.levels.push(Level {
                        parent: this_parent,
                        source,
                        kind: LevelKind::Nat(0),
                    });
                    ExprKind::Sort(level)
                }

                TokenKind::KwType => {
                    let source = self.token_range_from(source_begin);
                    let level = self.parse.levels.push(Level {
                        parent: this_parent,
                        source,
                        kind: LevelKind::Nat(1),
                    });
                    ExprKind::Sort(level)
                }

                TokenKind::KwPi => {
                    let binders = self.parse_binders(this_parent, true)?;

                    self.expect(TokenKind::Arrow)?;

                    let ret = self.parse_type(this_parent)?;
                    ExprKind::Forall(expr::Forall { binders, ret })
                }

                TokenKind::KwLam => {
                    let binders = self.parse_binders(this_parent, true)?;

                    self.expect(TokenKind::FatArrow)?;

                    let value = self.parse_expr(this_parent)?;
                    ExprKind::Lambda(expr::Lambda { binders, value })
                }


                TokenKind::Bool(value) => ExprKind::Bool(value),

                TokenKind::Number(value) => {
                    // @temp: analyze compatible types.
                    // maybe convert to value.
                    // or structured repr, maybe in tok.
                    ExprKind::Number(value)
                }

                TokenKind::String(value) => {
                    // @temp: remove escapes.
                    ExprKind::String(value)
                }


                // subexpr.
                TokenKind::LParen => {
                    let inner =
                        self.parse_expr_exw(
                            this_parent,
                            ParseExprFlags::default()
                                .with_tuple()
                                .with_type_hint(),
                            0)?;

                    self.expect(TokenKind::RParen)?;

                    ExprKind::Parens(inner)
                }

                // list & list type.
                TokenKind::LBracket => {
                    let (children, last_had_sep, had_error) =
                        self.sep_by_ex(TokenKind::Comma, TokenKind::RBracket, |this| {
                            this.parse_expr(this_parent)
                        });

                    if had_error {
                        return None;
                    }

                    // list type.
                    if !last_had_sep && children.len() == 1 && flags.ty {
                        ExprKind::ListType(children[0])
                    }
                    // list.
                    else {
                        ExprKind::List(children)
                    }
                }

                _ => break 'next
            }}

            // prefix operators.
            if let Some(PrefixOp(op)) = PrefixOp::from_token(at) {
                if PREC_PREFIX < prec {
                    unimplemented!()
                }

                let expr = self.parse_expr_ex(this_parent, PREC_PREFIX)?;

                break 'kind ExprKind::Op1(expr::Op1 { op, expr });
            }


            self.error_unexpected(at, source_begin);
            return None;
        };

        self.expr_init_from(this_expr, source_begin, kind);

        return Some(this_expr);
    }


    fn parse_inductive(&mut self, this_parent: AstParent) -> Option<adt::Inductive<'out>> {
        let name = self.expect_ident()?;

        // @cleanup: parse_level_params.
        let mut levels = &mut [][..];
        if self.consume_if_eq(TokenKind::Dot) {
            self.expect(TokenKind::LCurly)?;
            levels = self.sep_by(TokenKind::Comma, TokenKind::RCurly, |this| {
                this.expect_ident()
            })?;
        }

        let params = self.parse_binders(this_parent, false)?;

        let mut ty = None.into();
        if self.consume_if_eq(TokenKind::Colon) {
            ty = self.parse_expr(this_parent)?.some();
        }

        self.expect(TokenKind::LCurly)?;
        let ctors = self.sep_by(TokenKind::Semicolon, TokenKind::RCurly, |this| {
            this.parse_ctor(this_parent)
        })?;

        Some(adt::Inductive { name, levels, params, ty, ctors })
    }

    fn parse_ctor(&mut self, this_parent: AstParent) -> Option<adt::Ctor<'out>> {
        let name = self.expect_ident()?;

        let args = self.parse_binders(this_parent, false)?;

        let mut ty = None.into();
        if self.consume_if_eq(TokenKind::Colon) {
            ty = self.parse_expr(this_parent)?.some();
        }

        Some(adt::Ctor { name, args, ty })
    }


    fn parse_level(&mut self, parent: AstParent) -> Option<LevelId> {
        let (at, source_begin) = self.next();

        let this_level = self.parse.levels.push(Level {
            parent,
            source: TokenRange::ZERO,
            kind: LevelKind::Error,
        });
        let this_parent = Some(AstId::Level(this_level));

        let kind = match at.kind {
            TokenKind::Hole => {
                LevelKind::Hole
            }

            TokenKind::Ident(name) => {
                if name == atoms::max || name == atoms::imax {
                    self.expect(TokenKind::LParen)?;
                    let lhs = self.parse_level(this_parent)?;
                    self.expect(TokenKind::Comma)?;
                    let rhs = self.parse_level(this_parent)?;
                    self.expect(TokenKind::RParen)?;

                    if name == atoms::max {
                        LevelKind::Max((lhs, rhs))
                    }
                    else if name == atoms::imax {
                        LevelKind::IMax((lhs, rhs))
                    }
                    else { unreachable!() }
                }
                else {
                    LevelKind::Ident(Ident { source: source_begin, value: name })
                }
            }

            TokenKind::Number(v) => {
                let v = self.parse.numbers[v];
                let v = u32::from_str_radix(v, 10).ok()?;
                LevelKind::Nat(v)
            }

            _ => {
                self.error_unexpected(at, source_begin);
                return None;
            }
        };

        let source = self.token_range_from(source_begin);
        let this = &mut self.parse.levels[this_level];
        this.source = source;
        this.kind = kind;


        let mut result = this_level;

        if self.consume_if_eq(TokenKind::Add) {
            let (at, at_src) = self.next();

            let TokenKind::Number(v) = at.kind else {
                self.error_expect(at_src, "number");
                return None;
            };
            let v = self.parse.numbers[v];
            let v = u32::from_str_radix(v, 10).ok()?;

            let this_level = self.parse.levels.push(Level {
                parent,
                source,
                kind: LevelKind::Add((result, v))
            });

            self.parse.levels[result].parent = Some(AstId::Level(this_level));

            result = this_level;
        }

        return Some(result);
    }

    fn parse_binders(&mut self, this_parent: AstParent, allow_ident: bool) -> Option<BinderList<'out>> {
        let temp = ArenaPool::tls_get_rec();
        let mut binders = Vec::new_in(&*temp);
        loop {
            if allow_ident {
                if let Some(ident) = self.parse_ident_or_hole() {
                    binders.push(Binder::Ident(ident));
                    continue;
                }
            }

            if self.consume_if_eq(TokenKind::LParen) {
                self.parse_typed_binders(this_parent, TokenKind::RParen, &mut binders)?;
                continue;
            }
            if self.consume_if_eq(TokenKind::Lt) {
                self.parse_typed_binders(this_parent, TokenKind::Gt, &mut binders)?;
                continue;
            }

            break;
        }
        return Some(binders.move_into(self.alloc).leak());
    }

    fn parse_typed_binders<'res>(&mut self, this_parent: AstParent, terminator: TokenKind, binders: &mut Vec<Binder<'out>, &'res Arena>) -> Option<()> {
        let implicit = match terminator {
            TokenKind::RParen => false,
            TokenKind::Gt => true,
            _ => unreachable!()
        };

        let mut last_had_sep = true;
        let mut last_end = TokenId::ZERO;

        loop {
            if self.consume_if_eq(terminator) {
                return Some(());
            }

            if !last_had_sep {
                debug_assert!(last_end != TokenId::ZERO);
                self.error_expect(last_end, "','");
            }

            let names = {
                let temp = ArenaPool::tls_get_temp();
                let mut names = Vec::new_in(&*temp);
                while let Some(ident) = self.parse_ident_or_hole() {
                    names.push(ident);
                }
                if names.len() == 0 {
                    self.error_expect(self.current_token_id(), "ident | hole");
                }
                names.clone_in(self.alloc).leak()
            };

            self.expect(TokenKind::Colon)?;
            let flags = ParseExprFlags::default().with_no_cmp().with_ty();
            let ty = self.parse_expr_exw(this_parent, flags, 0)?;

            let mut default = None.into();
            if self.consume_if_eq(TokenKind::ColonEq) {
                default = self.parse_expr(this_parent)?.some();
            }

            binders.push(Binder::Typed(TypedBinder { implicit, names, ty, default }));

            last_end = self.current_token_id();
            last_had_sep = self.consume_if_eq(TokenKind::Comma);
        }
    }

    #[inline(always)]
    fn expect_ident(&mut self) -> Option<Ident> {
        let (at, at_src) = self.next();
        if let TokenKind::Ident(value) = at.kind {
            return Some(Ident { source: at_src, value });
        }
        self.error_expect(at_src, "ident");
        return None;
    }

    fn parse_ident_or_hole(&mut self) -> Option<OptIdent> {
        let (at, at_src) = self.peek();
        if let TokenKind::Hole = at.kind {
            self.consume(1);
            return Some(OptIdent { source: at_src, value: None.into() })
        }
        if let TokenKind::Ident(ident) = at.kind {
            self.consume(1);
            return Some(OptIdent { source: at_src, value: ident.some() })
        }
        return None;
    }

    fn parse_ident_or_path(&mut self, start: Ident) -> Option<IdentOrPath<'out>> {
        if self.consume_if_eq(TokenKind::ColonColon) {
            let mut parts = Vec::with_cap_in(self.alloc, 4);
            parts.push(start);

            loop { // don't use `self.arena` in here.
                let (at, at_src) = self.next();
                let TokenKind::Ident(part) = at.kind else { return None };
                parts.push(Ident { source: at_src, value: part });

                if !self.consume_if_eq(TokenKind::ColonColon) {
                    break;
                }
            }
            parts.trim_exact();

            return Some(IdentOrPath::Path(Path { parts: parts.leak() }));
        }
        else {
            return Some(IdentOrPath::Ident(start));
        }
    }


    // returns: (exprs, last_had_sep, had_error)
    #[inline]
    fn sep_by_ex<T, F: FnMut(&mut Self) -> Option<T>>
        (&mut self, sep: TokenKind, end: TokenKind, mut f: F)
        -> (&'out mut [T], bool, bool)
    {
        let temp = ArenaPool::tls_get_rec();
        let mut buffer = Vec::new_in(&*temp);

        let mut last_had_sep = true;
        let mut last_end = TokenId::ZERO;
        let mut had_error = false;
        loop {
            if self.consume_if_eq(end) {
                break;
            }

            if !last_had_sep {
                debug_assert!(last_end != TokenId::ZERO);
                self.error_expect(last_end, sep.repr());
            }

            if let Some(x) = f(self) {
                last_end = self.current_token_id();
                buffer.push(x);
            }
            else {
                had_error = true;
                break;
            }

            last_had_sep = self.consume_if_eq(sep);
        }

        let result = buffer.move_into(self.alloc).leak();
        (result, last_had_sep, had_error)
    }

    #[inline]
    fn sep_by<T, F: FnMut(&mut Self) -> Option<T>>
        (&mut self, sep: TokenKind, end: TokenKind, f: F)
        -> Option<&'out mut [T]>
    {
        let (result, _, had_error) = self.sep_by_ex(sep, end, f);
        if had_error {
            return None;
        }
        return Some(result);
    }

    #[inline(always)]
    fn current_token_id(&self) -> TokenId {
        TokenId::new_unck(self.token_cursor as u32)
    }

    #[inline(always)]
    fn token_range_from(&self, begin: TokenId) -> TokenRange {
        TokenRange::new_unck(begin, self.current_token_id())
    }


    #[inline(always)]
    fn peek(&self) -> (Token, TokenId) {
        (self.parse.tokens.inner()[self.token_cursor], self.current_token_id())
    }

    #[inline(always)]
    fn next(&mut self) -> (Token, TokenId) {
        let src = self.current_token_id();
        let at = self.parse.tokens.inner()[self.token_cursor];
        if at.kind != TokenKind::EndOfFile {
            self.token_cursor += 1;
        }
        return (at, src);
    }

    #[inline(always)]
    fn consume(&mut self, n: usize) {
        debug_assert!(self.token_cursor + n <= self.parse.tokens.len());
        self.token_cursor += n;
    }

    #[inline(always)]
    fn consume_if_eq(&mut self, kind: TokenKind) -> bool {
        if let Some(at) = self.parse.tokens.inner().get(self.token_cursor) {
            if at.kind == kind {
                self.token_cursor += 1;
                true
            }
            else { false }
        }
        else { false }
    }

    #[must_use]
    #[inline(always)]
    fn expect(&mut self, kind: TokenKind) -> Option<()> {
        let (at, at_src) = self.next();
        if at.kind == kind {
            return Some(());
        }
        self.error_expect(at_src, kind.repr());
        return None;
    }


    fn error_expect(&mut self, source: TokenId, what: &'out str) {
        self.parse.diagnostics.push(
            Diagnostic {
                source: DiagnosticSource::TokenRange(TokenRange::from_key(source)),
                kind: DiagnosticKind::ParseError(ParseError::Expected(what)),
            });
    }

    fn error_expect_expr(&mut self, source: ExprId, what: &'out str) {
        self.parse.diagnostics.push(
            Diagnostic {
                source: DiagnosticSource::Expr(source),
                kind: DiagnosticKind::ParseError(ParseError::Expected(what)),
            });
    }

    fn error_unexpected(&mut self, token: Token, source: TokenId) {
        if token.kind == TokenKind::Error { return }

        self.parse.diagnostics.push(
            Diagnostic {
                source: DiagnosticSource::TokenRange(TokenRange::from_key(source)),
                kind: DiagnosticKind::ParseError(ParseError::Unexpected(token.kind.repr())),
            });
    }


    #[inline]
    fn new_expr_uninit(&mut self, parent: AstParent) -> (ExprId, AstParent) {
        let id = self.parse.exprs.push(Expr {
            parent,
            source: TokenRange::ZERO,
            kind: ExprKind::Error,
        });
        (id, Some(AstId::Expr(id)))
    }

    #[inline]
    fn expr_init_from(&mut self, id: ExprId, from: TokenId, kind: ExprKind<'out>) {
        let source = self.token_range_from(from);

        let this = &mut self.parse.exprs[id];
        debug_assert_eq!(this.source, TokenRange::ZERO);
        debug_assert!(matches!(this.kind, ExprKind::Error));

        this.source = source;
        this.kind = kind;
    }
}



#[derive(Clone, Copy, Debug)]
pub struct ParseExprFlags {
    pub tuple: bool,
    pub type_hint: bool,
    pub ty: bool,
    pub no_cmp: bool,
}

impl ParseExprFlags {
    #[inline(always)]
    pub fn with_tuple(self) -> Self { Self { tuple: true, ..self } }

    #[inline(always)]
    pub fn with_type_hint(self) -> Self { Self { type_hint: true, ..self } }

    #[inline(always)]
    pub fn with_ty(self) -> Self { Self { ty: true, ..self } }

    #[inline(always)]
    pub fn with_no_cmp(self) -> Self { Self { no_cmp: true, ..self } }
}

impl Default for ParseExprFlags {
    #[inline(always)]
    fn default() -> Self {
        Self {
            tuple: false,
            type_hint: false,
            ty: false,
            no_cmp: false,
        }
    }
}



pub const PREC_PREFIX:  u32 =  900;
pub const PREC_POSTFIX: u32 = 1000;


#[derive(Clone, Copy, Debug, PartialEq)]
pub struct PrefixOp(pub expr::Op1Kind);

impl PrefixOp {
    #[inline]
    pub fn from_token(token: Token) -> Option<Self> {
        use expr::Op1Kind::*;
        Some(PrefixOp(match token.kind {
            TokenKind::KwNot => LogicNot,
            TokenKind::Not   => Not,
            TokenKind::Minus => Negate,

            _ => return None,
        }))
    }
}


#[derive(Clone, Copy, Debug, PartialEq)]
pub enum InfixOp {
    Assign,
    Op2Assign(expr::Op2Kind),
    Op2(expr::Op2Kind),
}

impl InfixOp {
    #[inline(always)]
    pub fn from_token(token: Token) -> Option<Self> {
        use InfixOp::*;
        use expr::Op2Kind::*;
        Some(match token.kind {
            TokenKind::Eq               => Assign,
            TokenKind::AddAssign        => Op2Assign(Add),
            TokenKind::SubAssign        => Op2Assign(Sub),
            TokenKind::MulAssign        => Op2Assign(Mul),
            TokenKind::DivAssign        => Op2Assign(Div),
            TokenKind::FloorDivAssign   => Op2Assign(FloorDiv),
            TokenKind::RemAssign        => Op2Assign(Rem),
            TokenKind::Add              => Op2(Add),
            TokenKind::Minus            => Op2(Sub),
            TokenKind::Star             => Op2(Mul),
            TokenKind::Div              => Op2(Div),
            TokenKind::FloorDiv         => Op2(FloorDiv),
            TokenKind::Rem              => Op2(Rem),
            TokenKind::EqEq             => Op2(CmpEq),
            TokenKind::NotEq            => Op2(CmpNe),
            TokenKind::Le               => Op2(CmpLe),
            TokenKind::Lt               => Op2(CmpLt),
            TokenKind::Ge               => Op2(CmpGe),
            TokenKind::Gt               => Op2(CmpGt),

            _ => return None,
        })
    }

    #[inline(always)]
    pub fn lprec(self) -> u32 {
        use InfixOp::*;
        use expr::Op2Kind::*;
        match self {
            Assign          => 100,
            Op2Assign(_)    => 100,
            Op2(op) => match op {
                Or          => 200,
                And         => 300,
                CmpEq       => 400,
                CmpNe       => 400,
                CmpLe       => 400,
                CmpLt       => 400,
                CmpGe       => 400,
                CmpGt       => 400,
                Add         => 600,
                Sub         => 600,
                Mul         => 800,
                Div         => 800,
                FloorDiv    => 800,
                Rem         => 800,
            }
        }
    }

    #[inline(always)]
    pub fn rprec(self) -> u32 {
        use InfixOp::*;
        use expr::Op2Kind::*;
        match self {
            Assign          => 100,
            Op2Assign(_)    => 100,
            Op2(op) => match op {
                Or          => 201,
                And         => 301,
                CmpEq       => 401,
                CmpNe       => 401,
                CmpLe       => 401,
                CmpLt       => 401,
                CmpGe       => 401,
                CmpGt       => 401,
                Add         => 601,
                Sub         => 601,
                Mul         => 801,
                Div         => 801,
                FloorDiv    => 801,
                Rem         => 801,
            }
        }
    }
}

pub const PREC_ARROW: u32 = 50;
pub const PREC_EQ:    u32 = 60;

