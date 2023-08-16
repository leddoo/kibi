use crate::source_map::SourceRange;


#[derive(Clone, Copy, Debug)]
pub struct Error<'a> {
    pub source: SourceRange,
    pub kind: ErrorKind<'a>,
}

#[derive(Clone, Copy, Debug)]
pub enum ErrorKind<'a> {
    Parse(ParseError<'a>),

    Foo(&'a ()),
}


#[derive(Clone, Copy, Debug)]
pub enum ParseError<'a> {
    Expected(&'a str),
    Unexpected(&'a str),
}

