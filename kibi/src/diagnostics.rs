use sti::vec::Vec;

use crate::ast::{ParseId, ParseRange, TokenId, TokenRange, ItemId, LevelId, ExprId};
use crate::pp::DocRef;


pub struct Diagnostics<'a> {
    diagnostics: Vec<Diagnostic<'a>>,
}


#[derive(Clone, Copy, Debug)]
pub struct Diagnostic<'a> {
    pub parse: ParseId,
    pub source: DiagnosticSource,
    pub kind: DiagnosticKind<'a>,
}

#[derive(Clone, Copy, Debug)]
pub enum DiagnosticSource {
    ParseRange(ParseRange),
    Token(TokenId),
    TokenRange(TokenRange),
    Item(ItemId),
    Level(LevelId),
    Expr(ExprId),
}

#[derive(Clone, Copy, Debug)]
pub enum DiagnosticKind<'a> {
    ParseError(ParseError<'a>),
    ElabError(ElabError<'a>),
}


#[derive(Clone, Copy, Debug)]
pub enum ParseError<'a> {
    Expected(&'a str),
    Unexpected(&'a str),
}


#[derive(Clone, Copy, Debug)]
pub enum ElabError<'a> {
    SymbolShadowedByLocal (&'a str),
    UnresolvedName { base: &'a str, name: &'a str },
    UnresolvedLevel (&'a str),
    LevelMismatch { expected: u32, found: u32 },
    TypeMismatch { expected: DocRef<'a>, found: DocRef<'a> },
    TypeExpected { found: DocRef<'a> },
    TooManyArgs,
}


impl<'a> Diagnostics<'a> {
    #[inline(always)]
    pub fn new() -> Self {
        Self { diagnostics: Vec::new() }
    }

    #[inline(always)]
    pub fn push(&mut self, diagnostic: Diagnostic<'a>) {
        self.diagnostics.push(diagnostic);
    }
}


impl Into<DiagnosticSource> for ParseRange { #[inline(always)] fn into(self) -> DiagnosticSource { DiagnosticSource::ParseRange(self) } }
impl Into<DiagnosticSource> for TokenId    { #[inline(always)] fn into(self) -> DiagnosticSource { DiagnosticSource::Token(self)      } }
impl Into<DiagnosticSource> for TokenRange { #[inline(always)] fn into(self) -> DiagnosticSource { DiagnosticSource::TokenRange(self) } }
impl Into<DiagnosticSource> for ItemId     { #[inline(always)] fn into(self) -> DiagnosticSource { DiagnosticSource::Item(self)       } }
impl Into<DiagnosticSource> for LevelId    { #[inline(always)] fn into(self) -> DiagnosticSource { DiagnosticSource::Level(self)      } }
impl Into<DiagnosticSource> for ExprId     { #[inline(always)] fn into(self) -> DiagnosticSource { DiagnosticSource::Expr(self)       } }

