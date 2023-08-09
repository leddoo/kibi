use sti::reader::Reader;

use crate::ast::*;


pub struct Toker<'a> {
    _reader: Reader<'a, u8>,
}

impl<'a> Toker<'a> {
}


pub enum ParseError {
}

pub type ParseResult<T> = Result<T, ParseError>;

pub fn parse_item<'a>(_tokens: &mut Reader<Token<'a>>) -> ParseResult<Item<'a>> {
    unimplemented!()
}


