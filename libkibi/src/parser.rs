use sti::alloc::{Alloc, GlobalAlloc};
use sti::growing_arena::GrowingArena;
use sti::vec::Vec;
use sti::reader::Reader;

use crate::ast::*;


pub struct Tokenizer<'a> {
    #[allow(dead_code)]
    arena:  &'a GrowingArena,
    reader: Reader<'a, u8>,
}

impl<'a> Tokenizer<'a> {
    pub fn new(arena: &'a GrowingArena, input: &'a [u8]) -> Self {
        Self { arena, reader: Reader::new(input) }
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

        let start_offset = self.reader.offset();
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
                    if self.reader.consume_if_eq(&b'=') {
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
                    else { TokenKind::Sub }
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
                let (value, _) = self.reader.consume_while_slice_from(start_offset, |at|
                    at.is_ascii_alphanumeric() || *at == b'_');

                let value = unsafe { core::str::from_utf8_unchecked(value) };

                // keywords.
                match value {
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
                if self.reader.consume_if_eq(&b'.') {
                    // after decimal.
                    self.reader.consume_while(|at| at.is_ascii_digit());
                }

                let value = &self.reader.consumed_slice()[start_offset..];
                let value = unsafe { core::str::from_utf8_unchecked(value) };

                TokenKind::Number(value)
            }
            // error.
            else {
                TokenKind::Error
            }
        };

        Some(Token {
            kind,
        })
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


pub struct Parser<'t, 'a> {
    arena:  &'a GrowingArena,
    tokens: Reader<'t, Token<'a>>,
}

impl<'t, 'a> Parser<'t, 'a> {
    pub fn new(arena: &'a GrowingArena, tokens: &'t [Token<'a>]) -> Self {
        Self { arena, tokens: Reader::new(tokens) }
    }

    pub fn parse_item(&mut self) -> Option<Item<'a>> {
        unimplemented!()
    }

    pub fn parse_stmt(&mut self) -> Option<Stmt<'a>> {
        unimplemented!()
    }

    pub fn parse_expr(&mut self) -> Option<Expr<'a>> {
        self.parse_expr_ex(ParseExprFlags::default(), 0)
    }

    pub fn parse_expr_ex(&mut self, flags: ParseExprFlags, prec: u32) -> Option<Expr<'a>> {
        let mut result = self.parse_leading_expr(flags, prec)?;

        loop {
            result = result;
            break;
        }

        return Some(result);
    }

    fn parse_leading_expr(&mut self, flags: ParseExprFlags, prec: u32) -> Option<Expr<'a>> {
        let at = self.tokens.next_ref()?;

        let kind = 'kind: {
            // lookahead 1 cases.
            'next: { break 'kind match at.kind {
                TokenKind::Ident(ident) => ExprKind::Ident(ident),

                TokenKind::Dot => {
                    if let Some(at) = self.tokens.peek_ref() {
                        if let TokenKind::Ident(ident) = at.kind {
                            break 'kind ExprKind::DotIdent(ident);
                        }
                    }

                    ExprKind::Error
                }


                TokenKind::Bool(value) => ExprKind::Bool(value),

                TokenKind::Number(value) => {
                    // @temp: analyze compatible types.
                    // maybe convert to value.
                    ExprKind::Number(value)
                }

                TokenKind::String(value) => {
                    // @temp: remove escapes.
                    ExprKind::String(value)
                }


                // subexpr.
                TokenKind::LParen => {
                    let inner = self.arena.alloc_new(
                        self.parse_expr_ex(
                            ParseExprFlags::default()
                                .with_tuple()
                                .with_type_hint(),
                            0)?);

                    if !self.tokens.consume_if(|at| at.kind == TokenKind::RParen) {
                        println!("todo: missing `)`");
                    }

                    ExprKind::Parens(inner)
                }

                // list & list type.
                TokenKind::LBracket => {
                    let (children, last_had_sep, had_error) =
                        self.sep_by(TokenKind::Comma, TokenKind::RBracket, |this| {
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

                // map & map type.
                TokenKind::LCurly => {
                    unimplemented!()
                }

                /*
                Match(expr::Match<'a>),
                If(expr::If<'a>),
                */

                _ => break 'next
            }}

            unimplemented!()
        };

        return Some(Expr { kind });
    }


    // returns: (exprs, last_had_sep, had_error)
    #[inline]
    fn sep_by<F: FnMut(&mut Parser<'t, 'a>) -> Option<Expr<'a>>>
        (&mut self, sep: TokenKind<'static>, end: TokenKind<'static>, mut f: F)
        -> (ExprList<'a>, bool, bool)
    {
        // @temp: sti temp arena.
        let mut buffer = Vec::new();

        let mut last_had_sep = true;
        let mut had_error = false;
        loop {
            if self.tokens.consume_if(|at| at.kind == end) {
                break;
            }

            if !last_had_sep {
                println!("todo: missing sep error");
            }

            if let Some(expr) = f(self) {
                buffer.push(expr);
            }
            else {
                had_error = true;
                break;
            }

            last_had_sep = self.tokens.consume_if(|at| at.kind == sep);
        }

        // @temp: sti Vec::move_into
        //let exprs = Vec::leak(buffer.move_into(self.arena));
        let exprs = {
            let mut result = Vec::with_cap_in(buffer.len(), self.arena);
            // @temp: sti Vec::into_iter.
            while let Some(expr) = buffer.pop() {
                result.push(expr);
            }
            result.reverse();
            Vec::leak(result)
        };
        (exprs, last_had_sep, had_error)
    }
}

