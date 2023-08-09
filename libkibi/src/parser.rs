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

            if self.reader.rest().starts_with(b"--") {
                self.reader.consume(2);
                self.reader.consume_while(|at| at != '\n' as u8);
                continue;
            }

            break;
        }

        let initial = self.reader.rest();

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
                    if self.reader.next_if(|at| at as char == '=').is_some() {
                        TokenKind::ColonEq
                    }
                    else { TokenKind::Colon }
                }

                '+' => {
                    if self.reader.next_if(|at| at as char == '=').is_some() {
                        TokenKind::AddAssign
                    }
                    else { TokenKind::Add }
                }

                '-' => {
                    if self.reader.next_if(|at| at as char == '=').is_some() {
                        TokenKind::SubAssign
                    }
                    else if self.reader.next_if(|at| at as char == '>').is_some() {
                        TokenKind::Arrow
                    }
                    else { TokenKind::Sub }
                }

                '*' => {
                    if self.reader.next_if(|at| at as char == '=').is_some() {
                        TokenKind::MulAssign
                    }
                    else { TokenKind::Star }
                }

                '/' => {
                    if self.reader.next_if(|at| at as char == '=').is_some() {
                        TokenKind::DivAssign
                    }
                    else if self.reader.next_if(|at| at as char == '/').is_some() {
                        if self.reader.next_if(|at| at as char == '=').is_some() {
                            TokenKind::FloorDivAssign
                        }
                        else { TokenKind::FloorDiv }
                    }
                    else { TokenKind::Div }
                }

                '%' => {
                    if self.reader.next_if(|at| at as char == '=').is_some() {
                        TokenKind::RemAssign
                    }
                    else { TokenKind::Rem }
                }

                '=' => {
                    if self.reader.next_if(|at| at as char == '=').is_some() {
                        TokenKind::EqEq
                    }
                    else if self.reader.next_if(|at| at as char == '>').is_some() {
                        TokenKind::FatArrow
                    }
                    else { TokenKind::Eq }
                }

                '!' => {
                    if self.reader.next_if(|at| at as char == '=').is_some() {
                        TokenKind::NotEq
                    }
                    else { TokenKind::Not }
                }

                '<' => {
                    if self.reader.next_if(|at| at as char == '=').is_some() {
                        TokenKind::Le
                    }
                    else { TokenKind::Lt }
                }

                '>' => {
                    if self.reader.next_if(|at| at as char == '=').is_some() {
                        TokenKind::Ge
                    }
                    else { TokenKind::Gt }
                }

                _ => break 'next
            }}

            // strings.
            if at == '"' as u8 {
                let mut is_escaped = false;
                self.reader.consume_while(|at| {
                    let done = !is_escaped && at == '"' as u8;
                    is_escaped = at == '\\' as u8 && !is_escaped;
                    return !done;
                });
                self.reader.consume(1);

                let len = self.reader.rest().as_ptr() as usize
                    - initial.as_ptr() as usize;

                let value = &initial[1 .. len-1];
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
            else if at.is_ascii_alphabetic() || at == '_' as u8 {
                self.reader.consume_while(|at|
                    at.is_ascii_alphanumeric() || at == '_' as u8);

                let len = self.reader.rest().as_ptr() as usize
                    - initial.as_ptr() as usize;

                let value = &initial[..len];
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

                if self.reader.next_if(|at| at == '.' as u8).is_some() {
                    // after decimal.
                    self.reader.consume_while(|at| at.is_ascii_digit());
                }

                let len = self.reader.rest().as_ptr() as usize
                    - initial.as_ptr() as usize;

                let value = &initial[..len];
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
        let at = self.tokens.next()?;

        let kind = 'kind: {
            // lookahead 1 cases.
            'next: { break 'kind match at.kind {
                TokenKind::Ident(ident) => ExprKind::Ident(ident),

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

                    self.tokens.next_if(|at|
                        matches!(at.kind, TokenKind::RParen))?;

                    ExprKind::Parens(inner)
                }

                TokenKind::KwDo => {
                    unimplemented!()
                }

                // list & list type.
                TokenKind::LBracket => {
                    unimplemented!()
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
}

