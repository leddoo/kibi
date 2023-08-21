use sti::alloc::{Alloc, GlobalAlloc};
use sti::arena::Arena;
use sti::vec::Vec;
use sti::reader::Reader;

use crate::error::*;
use crate::ast::*;


pub struct Tokenizer<'a> {
    #[allow(dead_code)]
    pub arena:  &'a Arena,
    pub source_offset: u32,
    pub reader: Reader<'a, u8>,
}

impl<'a> Tokenizer<'a> {
    pub fn tokenize(input: &'a [u8], source_offset: u32, arena: &'a Arena) -> Vec<Token<'a>> {
        Self::tokenize_in(input, source_offset, arena, GlobalAlloc)
    }

    pub fn tokenize_in<A: Alloc>(input: &'a [u8], source_offset: u32, arena: &'a Arena, alloc: A) -> Vec<Token<'a>, A> {
        Self::new(input, source_offset, arena).run_in(alloc)
    }


    pub fn new(input: &'a [u8], source_offset: u32, arena: &'a Arena) -> Self {
        Self { arena, source_offset, reader: Reader::new(input) }
    }

    pub fn run(&mut self) -> Vec<Token<'a>> {
        self.run_in(GlobalAlloc)
    }

    pub fn run_in<A: Alloc>(&mut self, alloc: A) -> Vec<Token<'a>, A> {
        let mut tokens = Vec::new_in(alloc);
        while let Some(tok) = self.next() {
            tokens.push(tok);
        }
        return tokens;
    }


    pub fn next(&mut self) -> Option<Token<'a>> {
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
        let at = self.reader.next()?;

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

                TokenKind::String(value)
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

                    "def" => TokenKind::KwDef,

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

                    _ => TokenKind::Ident(value),
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

                TokenKind::Number(value)
            }
            // error.
            else {
                TokenKind::Error
            }
        };

        let end_offset = self.reader.offset();
        let source = SourceRange {
            begin: self.source_offset + begin_offset as u32,
            end:   self.source_offset + end_offset as u32,
        };

        Some(Token { source, kind })
    }


    fn skip_ws(&mut self) {
        self.reader.consume_while(|at|
            at.is_ascii_whitespace());
    }
}



#[derive(Clone, Copy)]
pub struct ParseExprFlags {
    pub tuple: bool,
    pub type_hint: bool,
    pub ty: bool,
}

impl ParseExprFlags {
    #[inline(always)]
    pub fn with_tuple(self) -> Self { Self { tuple: true, ..self } }

    #[inline(always)]
    pub fn with_type_hint(self) -> Self { Self { type_hint: true, ..self } }

    #[inline(always)]
    pub fn with_ty(self) -> Self { Self { ty: true, ..self } }
}

impl Default for ParseExprFlags {
    #[inline(always)]
    fn default() -> Self {
        Self {
            tuple: false,
            type_hint: false,
            ty: false,
        }
    }
}


pub struct Parser<'me, 'err, 'a> {
    pub arena:  &'a Arena,
    pub errors: &'me ErrorCtx<'err>,
    pub tokens: Reader<'me, Token<'a>>,
}

impl<'me, 'err, 'a> Parser<'me, 'err, 'a> {
    pub fn new(tokens: &'me [Token<'a>], errors: &'me ErrorCtx<'err>, arena: &'a Arena) -> Self {
        Self { arena, errors, tokens: Reader::new(tokens) }
    }

    pub fn parse_item(&mut self) -> Option<Item<'a>> {
        let at = self.tokens.next_ref()?;

        let kind = match at.kind {
            TokenKind::KwDef => {
                let name = self.parse_ident()?;
                let name = self.parse_ident_or_path(name)?;

                let mut levels = &mut [][..];
                if self.tokens.consume_if(|at| at.kind == TokenKind::Dot) {
                    self.expect(TokenKind::LCurly)?;
                    levels = self.sep_by(TokenKind::Comma, TokenKind::RCurly, |this| {
                        this.parse_ident()
                    })?;
                }

                let mut params = &mut [][..];
                if self.tokens.consume_if(|at| at.kind == TokenKind::LParen) {
                    params = self.sep_by(TokenKind::Comma, TokenKind::RParen, |this| {
                        this.parse_binder()
                    })?;
                }

                let mut ty = None;
                if self.tokens.consume_if(|at| at.kind == TokenKind::Colon) {
                    ty = Some(self.parse_expr()?);
                }

                self.expect(TokenKind::ColonEq)?;

                let value = self.parse_expr()?;

                ItemKind::Def(item::Def { name, levels, params, ty, value })
            }

            TokenKind::Ident("reduce") => {
                let expr = self.arena.alloc_new(self.parse_expr()?);
                ItemKind::Reduce(expr)
            }

            _ => {
                self.error_unexpected(at);
                return None;
            }
        };

        Some(Item { kind })
    }

    pub fn parse_stmt(&mut self) -> Option<Stmt<'a>> {
        unimplemented!()
    }

    pub fn parse_expr(&mut self) -> Option<Expr<'a>> {
        self.parse_expr_exw(ParseExprFlags::default(), 0)
    }

    pub fn parse_expr_ex(&mut self, prec: u32) -> Option<Expr<'a>> {
        self.parse_expr_exw(ParseExprFlags::default(), prec)
    }

    pub fn parse_expr_exw(&mut self, flags: ParseExprFlags, prec: u32) -> Option<Expr<'a>> {
        let mut result = self.parse_leading_expr(flags, prec)?;

        while let Some(at) = self.tokens.peek_ref() {
            let source_begin = result.source;

            // infix operators.
            if let Some(op) = InfixOp::from_token(at) {
                if op.lprec() >= prec {
                    self.tokens.consume(1);

                    let lhs = self.arena.alloc_new(result);
                    let rhs = self.arena.alloc_new(
                        self.parse_expr_ex(op.rprec())?);

                    let source = source_begin.join(rhs.source);

                    let kind = match op {
                        InfixOp::Assign =>
                            ExprKind::Assign(expr::Assign { lhs, rhs }),

                        InfixOp::Op2Assign(op) =>
                            ExprKind::Op2Assign(expr::Op2 { op, lhs, rhs }),

                        InfixOp::Op2(op) =>
                            ExprKind::Op2(expr::Op2 { op, lhs, rhs }),
                    };

                    result = Expr { source, kind };

                    continue;
                }
            }

            // postfix operators.
            if PREC_POSTFIX < prec {
                break;
            }

            if at.kind == TokenKind::Dot {
                self.tokens.consume(1);

                let at = self.tokens.next_ref()?;
                let kind = match at.kind {
                    // field.
                    TokenKind::Ident(name) => {
                        ExprKind::Field(expr::Field {
                            name,
                            base: self.arena.alloc_new(result),
                        })
                    }

                    // levels
                    TokenKind::LCurly => {
                        let symbol = match result.kind {
                            ExprKind::Ident(name) => IdentOrPath::Ident(name),
                            ExprKind::Path(path)  => IdentOrPath::Path(path),
                            _ => {
                                self.error_expect(result.source, "ident | path");
                                return None;
                            }
                        };

                        let levels = self.sep_by(TokenKind::Comma, TokenKind::RCurly, |this| {
                            this.parse_level()
                        })?;

                        ExprKind::Levels(expr::Levels { symbol, levels })
                    }

                    _ => {
                        self.error_expect(result.source, "ident | '{'");
                        return None;
                    }
                };

                let source = source_begin.join(self.prev_token_source());
                result = Expr { source, kind };

                continue;
            }

            if at.kind == TokenKind::LParen {
                self.tokens.consume(1);

                let args = self.sep_by(TokenKind::Comma, TokenKind::RParen, |this| {
                    // @temp: named args.
                    this.parse_expr()
                    .map(|value| expr::CallArg::Positional(value))
                })?;

                let source = source_begin.join(self.prev_token_source());
                let kind = ExprKind::Call(expr::Call {
                    func: self.arena.alloc_new(result),
                    args,
                });
                result = Expr { source, kind };
            }

            break;
        }

        return Some(result);
    }

    fn parse_leading_expr(&mut self, flags: ParseExprFlags, prec: u32) -> Option<Expr<'a>> {
        let at = self.tokens.next_ref()?;

        let source_begin = at.source;

        let kind = 'kind: {
            'next: { break 'kind match at.kind {
                TokenKind::Hole => {
                    ExprKind::Hole
                }

                TokenKind::Ident(ident) => {
                    match self.parse_ident_or_path(ident)? {
                        IdentOrPath::Ident(ident) => ExprKind::Ident(ident),
                        IdentOrPath::Path(path) => ExprKind::Path(path),
                    }
                }

                TokenKind::Dot => {
                    let ident = self.parse_ident()?;
                    ExprKind::DotIdent(ident)
                }


                TokenKind::KwSort => {
                    self.expect(TokenKind::LParen)?;
                    let level = self.arena.alloc_new(self.parse_level()?);
                    self.expect(TokenKind::RParen)?;
                    ExprKind::Sort(level)
                }

                TokenKind::KwProp => {
                    ExprKind::Sort(self.arena.alloc_new(
                        Level { source: at.source, kind: LevelKind::Nat(0) }))
                }

                TokenKind::KwType => {
                    ExprKind::Sort(self.arena.alloc_new(
                        Level { source: at.source, kind: LevelKind::Nat(1) }))
                }

                TokenKind::KwPi => {
                    let binders = self.parse_binders()?;

                    self.expect(TokenKind::Arrow)?;

                    let ret = self.arena.alloc_new(self.parse_expr()?);
                    ExprKind::Forall(expr::Forall { binders, ret })
                }

                TokenKind::KwLam => {
                    let binders = self.parse_binders()?;

                    self.expect(TokenKind::FatArrow)?;

                    let value = self.arena.alloc_new(self.parse_expr()?);
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
                    let inner = self.arena.alloc_new(
                        self.parse_expr_exw(
                            ParseExprFlags::default()
                                .with_tuple()
                                .with_type_hint(),
                            0)?);

                    self.expect(TokenKind::RParen)?;

                    ExprKind::Parens(inner)
                }

                // list & list type.
                TokenKind::LBracket => {
                    let (children, last_had_sep, had_error) =
                        self.sep_by_ex(TokenKind::Comma, TokenKind::RBracket, |this| {
                            this.parse_expr()
                        });

                    if had_error {
                        return None;
                    }

                    // list type.
                    if !last_had_sep && children.len() == 1 && flags.ty {
                        ExprKind::ListType(&mut children[0])
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

                let expr = self.arena.alloc_new(
                    self.parse_expr_ex(PREC_PREFIX)?);

                break 'kind ExprKind::Op1(expr::Op1 { op, expr });
            }


            self.error_unexpected(at);
            return None;
        };

        let source = source_begin.join(self.prev_token_source());
        return Some(Expr { source, kind });
    }


    fn parse_level(&mut self) -> Option<Level<'a>> {
        let at = self.tokens.next_ref()?;

        let source_begin = at.source;

        let mut kind = match at.kind {
            TokenKind::Hole => {
                LevelKind::Hole
            }

            TokenKind::Ident(v) => {
                if v == "max" || v == "imax" {
                    self.expect(TokenKind::LParen)?;
                    let lhs = self.arena.alloc_new(self.parse_level()?);
                    self.expect(TokenKind::Comma)?;
                    let rhs = self.arena.alloc_new(self.parse_level()?);
                    self.expect(TokenKind::RParen)?;

                    if v == "max" {
                        LevelKind::Max((lhs, rhs))
                    }
                    else if v == "imax" {
                        LevelKind::IMax((lhs, rhs))
                    }
                    else { unreachable!() }
                }
                else {
                    LevelKind::Ident(v)
                }
            }

            TokenKind::Number(v) => {
                let v = u32::from_str_radix(v, 10).ok()?;
                LevelKind::Nat(v)
            }

            _ => {
                self.error_unexpected(at);
                return None;
            }
        };

        let source = source_begin.join(self.prev_token_source());

        if self.tokens.consume_if(|at| at.kind == TokenKind::Add) {
            let at = self.tokens.next_ref()?;
            let TokenKind::Number(v) = at.kind else {
                self.error_expect(at.source, "number");
                return None;
            };

            let l = self.arena.alloc_new(Level { source, kind });
            let v = u32::from_str_radix(v, 10).ok()?;
            kind = LevelKind::Add((l, v));
        }

        let source = source_begin.join(self.prev_token_source());

        return Some(Level { source, kind });
    }

    fn parse_binders(&mut self) -> Option<BinderList<'a>> {
        self.expect(TokenKind::LParen)?;

        self.sep_by(TokenKind::Comma, TokenKind::RParen, |this| {
            this.parse_binder()
        })
    }

    fn parse_binder(&mut self) -> Option<Binder<'a>> {
        let name = self.parse_ident_or_hole()?;

        let mut ty = None;
        if self.tokens.consume_if(|at| at.kind == TokenKind::Colon) {
            ty = Some(self.arena.alloc_new(self.parse_expr()?));
        }

        let default = None;
        return Some(Binder { name, ty, default });
    }

    #[inline(always)]
    fn parse_ident(&mut self) -> Option<&'a str> {
        let at = self.tokens.next_ref()?;
        if let TokenKind::Ident(ident) = at.kind {
            return Some(ident);
        }
        self.error_expect(at.source, "ident");
        return None;
    }

    #[inline(always)]
    fn parse_ident_or_hole(&mut self) -> Option<Option<&'a str>> {
        let at = self.tokens.next_ref()?;
        if let TokenKind::Ident(ident) = at.kind {
            return Some(Some(ident));
        }
        if let TokenKind::Hole = at.kind {
            return Some(None);
        }
        self.error_expect(at.source, "ident | '_'");
        return None;
    }

    fn parse_ident_or_path(&mut self, start: &'a str) -> Option<IdentOrPath<'a>> {
        if self.tokens.consume_if(|at| at.kind == TokenKind::ColonColon) {
            let mut parts = Vec::with_cap_in(4, self.arena);
            parts.push(start);

            loop { // don't use `self.arena` in here.
                let at = self.tokens.next_ref()?;
                let TokenKind::Ident(part) = at.kind else { return None };
                parts.push(part);

                if !self.tokens.consume_if(|at| at.kind == TokenKind::ColonColon) {
                    break;
                }
            }
            parts.trim_exact();

            return Some(IdentOrPath::Path(Path { local: true, parts: parts.leak() }));
        }
        else {
            return Some(IdentOrPath::Ident(start));
        }
    }


    // returns: (exprs, last_had_sep, had_error)
    #[inline]
    fn sep_by_ex<T, F: FnMut(&mut Self) -> Option<T>>
        (&mut self, sep: TokenKind<'static>, end: TokenKind<'static>, mut f: F)
        -> (&'a mut [T], bool, bool)
    {
        // @temp: sti temp arena.
        let mut buffer = Vec::new();

        let mut last_had_sep = true;
        let mut last_end = 0;
        let mut had_error = false;
        loop {
            if self.tokens.consume_if(|at| at.kind == end) {
                break;
            }

            if !last_had_sep {
                debug_assert!(last_end != 0);
                self.error_expect(SourceRange::collapsed(last_end), sep.repr());
            }

            if let Some(x) = f(self) {
                last_end = self.prev_token_source().end;
                buffer.push(x);
            }
            else {
                had_error = true;
                break;
            }

            last_had_sep = self.tokens.consume_if(|at| at.kind == sep);
        }

        let result = buffer.move_into(self.arena).leak();
        (result, last_had_sep, had_error)
    }

    #[inline]
    fn sep_by<T, F: FnMut(&mut Self) -> Option<T>>
        (&mut self, sep: TokenKind<'static>, end: TokenKind<'static>, f: F)
        -> Option<&'a mut [T]>
    {
        let (result, _, had_error) = self.sep_by_ex(sep, end, f);
        if had_error {
            return None;
        }
        return Some(result);
    }

    #[track_caller]
    #[inline(always)]
    fn prev_token_source(&self) -> SourceRange {
        self.tokens.consumed_slice().last().unwrap().source
    }


    #[must_use]
    #[inline(always)]
    fn expect(&mut self, kind: TokenKind) -> Option<()> {
        let at = self.tokens.next_ref()?;
        if at.kind == kind {
            return Some(());
        }
        self.error_expect(at.source, kind.repr());
        return None;
    }


    fn error_expect(&mut self, source: SourceRange, what: &'err str) {
        self.errors.with(|errors| {
            errors.report(Error {
                source,
                kind: ErrorKind::Parse(ParseError::Expected(what)),
            });
        });
    }

    fn error_unexpected(&mut self, token: &Token<'a>) {
        self.errors.with(|errors| {
            errors.report(Error {
                source: token.source,
                kind: ErrorKind::Parse(ParseError::Unexpected(token.kind.repr())),
            });
        });
    }
}



pub const PREC_PREFIX:  u32 =  900;
pub const PREC_POSTFIX: u32 = 1000;


#[derive(Clone, Copy, Debug, PartialEq)]
pub struct PrefixOp(pub expr::Op1Kind);

impl PrefixOp {
    pub fn from_token(token: &Token) -> Option<Self> {
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
    pub fn from_token(token: &Token) -> Option<Self> {
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

