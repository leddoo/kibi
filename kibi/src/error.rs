use core::cell::RefCell;
use sti::arena::*;
use sti::vec::Vec;

use crate::ast::{ParseId, ParseRange, TokenId, TokenRange, ItemId, LevelId, ExprId};
use crate::pp::DocRef;


pub struct ErrorCtx<'err> {
    inner: RefCell<ErrorCtxMut<'err>>,
}

pub struct ErrorCtxMut<'err> {
    pub alloc: &'err Arena,
    errors: Vec<Error<'err>>,
}


#[derive(Clone, Copy, Debug)]
pub struct Error<'a> {
    pub parse: ParseId,
    pub source: ErrorSource,
    pub kind: ErrorKind<'a>,
}

#[derive(Clone, Copy, Debug)]
pub enum ErrorSource {
    ParseRange(ParseRange),
    Token(TokenId),
    TokenRange(TokenRange),
    Item(ItemId),
    Level(LevelId),
    Expr(ExprId),
}

#[derive(Clone, Copy, Debug)]
pub enum ErrorKind<'a> {
    Parse(ParseError<'a>),
    Elab(ElabError<'a>),
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


impl<'err> ErrorCtx<'err> {
    #[inline(always)]
    pub fn new(alloc: &'err Arena) -> Self {
        Self { inner: RefCell::new(ErrorCtxMut {
            alloc,
            errors: Vec::new(),
        })}
    }

    #[inline(always)]
    pub fn with<F: FnOnce(&mut ErrorCtxMut<'err>)>(&self, f: F) {
        f(&mut self.inner.borrow_mut());
    }
}

impl<'err> ErrorCtxMut<'err> {
    #[inline(always)]
    pub fn report(&mut self, error: Error<'err>) {
        self.errors.push(error);
    }

    #[inline(always)]
    pub fn empty(&self) -> bool {
        self.errors.is_empty()
    }

    #[inline(always)]
    pub fn iter<F: FnMut(&Error<'err>)>(&self, mut f: F) {
        for e in &self.errors {
            f(e);
        }
    }
}


impl Into<ErrorSource> for ParseRange { #[inline(always)] fn into(self) -> ErrorSource { ErrorSource::ParseRange(self) } }
impl Into<ErrorSource> for TokenId    { #[inline(always)] fn into(self) -> ErrorSource { ErrorSource::Token(self)      } }
impl Into<ErrorSource> for TokenRange { #[inline(always)] fn into(self) -> ErrorSource { ErrorSource::TokenRange(self) } }
impl Into<ErrorSource> for ItemId     { #[inline(always)] fn into(self) -> ErrorSource { ErrorSource::Item(self)       } }
impl Into<ErrorSource> for LevelId    { #[inline(always)] fn into(self) -> ErrorSource { ErrorSource::Level(self)      } }
impl Into<ErrorSource> for ExprId     { #[inline(always)] fn into(self) -> ErrorSource { ErrorSource::Expr(self)       } }

