#[derive(Debug)]
pub enum Ast<'i> {
    Number (f64),
    String (&'i str),
    Atom (&'i str),
    List (Vec<Ast<'i>>),
    Array (Vec<Ast<'i>>),
    Table (Vec<(Ast<'i>, Ast<'i>)>),
}

#[derive(Debug)]
pub enum ParseError {
    Eoi,
    Error,
}

pub type ParseResult<T> = Result<T, ParseError>;

pub struct Parser<'i> {
    input: &'i str,
    cursor: usize,
}

impl<'i> Parser<'i> {
    pub fn new(input: &str) -> Parser {
        Parser {
            input,
            cursor: 0,
        }
    }

    #[inline]
    fn peek(&self) -> ParseResult<char> {
        if self.cursor < self.input.len() {
            let c = self.input.as_bytes()[self.cursor];
            return unsafe { Ok(char::from_u32_unchecked(c as u32)) };
        }
        Err(ParseError::Eoi)
    }

    fn skip_whitespace(&mut self) {
        while let Ok(at) = self.peek() {
            if !at.is_ascii_whitespace() {
                break;
            }
            self.cursor += 1;
        }
    }

    fn consume(&mut self, expected: char) -> ParseResult<()> {
        let at = self.peek()?;
        self.cursor += 1;
        if at != expected {
            return Err(ParseError::Error);
        }
        Ok(())
    }

    pub fn parse(&mut self) -> ParseResult<Ast<'i>> {
        let at = self.peek()?;

        if at.is_ascii_digit() {
            let begin = self.cursor;
            self.cursor += 1;

            while let Ok(at) = self.peek() {
                if !(at.is_ascii_digit() || at == '.') {
                    break;
                }
                self.cursor += 1;
            }

            let end = self.cursor;
            let value = &self.input[begin..end];
            let value = value.parse::<f64>().map_err(|_| ParseError::Error)?;
            return Ok(Ast::Number(value));
        }

        if at == '"' {
            self.cursor += 1;
            let begin = self.cursor;

            while let Ok(at) = self.peek() {
                if at == '"' {
                    let end = self.cursor;
                    self.cursor += 1;

                    let value = &self.input[begin..end];
                    return Ok(Ast::String(value));
                }

                self.cursor += 1;
            }
            return Err(ParseError::Eoi);
        }

        #[inline]
        fn is_operator(at: char) -> bool {
            match at {
                '+' | '-' | '*' | '/' | '=' | '<' | '>' => true,
                _ => false,
            }
        }

        if at.is_ascii_alphabetic() || at == '_' || is_operator(at) {
            let begin = self.cursor;
            self.cursor += 1;

            while let Ok(at) = self.peek() {
                if !(at.is_ascii_alphanumeric() || at == '_' || is_operator(at)) {
                    break;
                }
                self.cursor += 1;
            }

            let end = self.cursor;
            let value = &self.input[begin..end];
            return Ok(Ast::Atom(value));
        }

        if at == '(' {
            self.cursor += 1;
            self.skip_whitespace();

            let mut values = vec![];
            while let Ok(at) = self.peek() {
                if at == ')' {
                    self.cursor += 1;
                    return Ok(Ast::List(values));
                }

                values.push(self.parse()?);
                self.skip_whitespace();
            }
            return Err(ParseError::Eoi);
        }

        if at == '[' {
            self.cursor += 1;
            self.skip_whitespace();

            let mut values = vec![];
            while let Ok(at) = self.peek() {
                if at == ']' {
                    self.cursor += 1;
                    return Ok(Ast::Array(values));
                }

                values.push(self.parse()?);
                self.skip_whitespace();
            }
            return Err(ParseError::Eoi);
        }

        if at == '{' {
            self.cursor += 1;
            self.skip_whitespace();

            let mut values = vec![];
            while let Ok(at) = self.peek() {
                if at == '}' {
                    self.cursor += 1;
                    return Ok(Ast::Table(values));
                }

                self.consume('(')?;
                self.skip_whitespace();
                let key = self.parse()?;
                self.skip_whitespace();
                let value = self.parse()?;
                self.skip_whitespace();
                self.consume(')')?;
                self.skip_whitespace();

                values.push((key, value));
            }
            return Err(ParseError::Eoi);
        }

        Err(ParseError::Error)
    }
}

pub fn parse_single(input: &str) -> ParseResult<Ast> {
    let mut p = Parser::new(input);
    let result = p.parse()?;
    p.skip_whitespace();
    if p.cursor != p.input.len() {
        return Err(ParseError::Error);
    }
    return Ok(result);
}

pub fn parse_many(input: &str) -> ParseResult<Vec<Ast>> {
    let mut p = Parser::new(input);
    let mut result = vec![];
    while p.cursor < p.input.len() {
        p.skip_whitespace();
        result.push(p.parse()?);
        p.skip_whitespace();
    }
    Ok(result)
}

