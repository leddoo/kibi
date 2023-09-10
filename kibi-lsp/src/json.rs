use kibi::sti;
use sti::arena::Arena;
use sti::string::String;
use sti::utf8;
use sti::vec::Vec;
use sti::reader::Reader;


#[derive(Clone, Copy, Debug, PartialEq)]
pub enum JsonValue<'a> {
    Null,
    Bool(bool),
    Number(f64),
    String(&'a str),
    Array(&'a [JsonValue<'a>]),
    Object(&'a [(&'a str, JsonValue<'a>)]),
}


#[derive(Clone, Copy, Debug)]
pub enum JsonError {
    UnexpectedEof,
    Expected(usize, &'static str),
    InvalidUtf8(usize),
    InvalidEscape(usize),
    MalformedNumber(usize),
}


pub fn parse<'a>(alloc: &'a Arena, input: &'a [u8]) -> Result<JsonValue<'a>, JsonError> {
    let mut parser = Parser { alloc, reader: Reader::new(input) };
    let result = parser.parse()?;
    parser.skip_ws();
    if parser.reader.remaining() != 0 {
        return Err(JsonError::Expected(parser.reader.consumed(), "eof"));
    }
    return Ok(result);
}

struct Parser<'a> {
    alloc: &'a Arena,
    reader: Reader<'a, u8>,
}

impl<'a> Parser<'a> {
    fn parse(&mut self) -> Result<JsonValue<'a>, JsonError> {
        self.skip_ws();

        let start_pos = self.reader.offset();
        let at = self.reader.next().ok_or(JsonError::UnexpectedEof)?;
        match at {
            b'n' => {
                let ull = self.reader.next_n(3).ok_or(JsonError::UnexpectedEof)?;
                if ull != b"ull" {
                    return Err(JsonError::Expected(start_pos, "null"));
                }
                Ok(JsonValue::Null)
            }

            b'f' => {
                let alse = self.reader.next_n(4).ok_or(JsonError::UnexpectedEof)?;
                if alse != b"alse" {
                    return Err(JsonError::Expected(start_pos, "false"));
                }
                Ok(JsonValue::Bool(false))
            }

            b't' => {
                let rue = self.reader.next_n(3).ok_or(JsonError::UnexpectedEof)?;
                if rue != b"rue" {
                    return Err(JsonError::Expected(start_pos, "true"));
                }
                Ok(JsonValue::Bool(true))
            }

            b'-' | b'0'..=b'9' => {
                let number = self.reader.consume_while_slice_from(start_pos,
                    |at| at.is_ascii_digit() || *at == b'.' || *at == b'e' || *at == b'E').0;

                let number = unsafe { core::str::from_utf8_unchecked(number) };

                let number = number.parse::<f64>().ok()
                    .ok_or(JsonError::MalformedNumber(start_pos))?;

                Ok(JsonValue::Number(number))
            }

            b'"' => {
                Ok(JsonValue::String(self.parse_string()?))
            }

            b'[' => {
                let mut result = Vec::new_in(self.alloc);

                self.skip_ws();

                let mut had_sep = true;
                while !self.reader.consume_if_eq(&b']') {
                    if !had_sep {
                        return Err(JsonError::Expected(self.reader.consumed(), "']'"));
                    }

                    result.push(self.parse()?);
                    self.skip_ws();

                    had_sep = self.reader.consume_if_eq(&b',');
                    self.skip_ws();
                }

                Ok(JsonValue::Array(result.clone_in(self.alloc).leak()))
            }

            b'{' => {
                let mut result = Vec::new_in(self.alloc);

                self.skip_ws();

                let mut had_sep = true;
                while !self.reader.consume_if_eq(&b'}') {
                    if !had_sep {
                        return Err(JsonError::Expected(self.reader.consumed(), "'}'"));
                    }

                    if !self.reader.consume_if_eq(&b'"') {
                        return Err(JsonError::Expected(self.reader.consumed(), "'\"'"));
                    }
                    let key = self.parse_string()?;
                    self.skip_ws();

                    if !self.reader.consume_if_eq(&b':') {
                        return Err(JsonError::Expected(self.reader.consumed(), "':'"));
                    }

                    let value = self.parse()?;

                    result.push((key, value));
                    self.skip_ws();

                    had_sep = self.reader.consume_if_eq(&b',');
                    self.skip_ws();
                }

                Ok(JsonValue::Object(result.clone_in(self.alloc).leak()))
            }

            _ => Err(JsonError::Expected(start_pos, "value")),
        }
    }

    fn parse_string(&mut self) -> Result<&'a str, JsonError> {
        let mut buffer = String::new_in(self.alloc);
        loop {
            match utf8::validate_string_inline(self.reader.as_slice()) {
                Ok((str, stopper)) => {
                    if !stopper { return Err(JsonError::UnexpectedEof) }

                    self.reader.consume(str.len());

                    let escape_pos = self.reader.consumed();

                    let stopper = self.reader.next().unwrap();
                    if stopper == b'"' && buffer.cap() == 0 {
                        return Ok(str);
                    }

                    buffer.push(str);

                    if stopper == b'"' {
                        return Ok(buffer.leak());
                    }
                    else {
                        debug_assert_eq!(stopper, b'\\');

                        // process escape.
                        match self.reader.next().unwrap() {
                            b'"'  => buffer.push_char('"'),
                            b'\\' => buffer.push_char('\\'),
                            b'/'  => buffer.push_char('/'),
                            b'b'  => buffer.push_char('\x08'),
                            b'f'  => buffer.push_char('\x0C'),
                            b'n'  => buffer.push_char('\n'),
                            b'r'  => buffer.push_char('\r'),
                            b't'  => buffer.push_char('\r'),

                            b'u' => {
                                unimplemented!()
                            }

                            _ => return Err(JsonError::InvalidEscape(escape_pos)),
                        }
                    }
                }

                Err(_) => {
                    return Err(JsonError::InvalidUtf8(self.reader.consumed()));
                }
            }
        }
    }

    #[inline]
    fn skip_ws(&mut self) {
        self.reader.consume_while(|at| at.is_ascii_whitespace());
    }
}


impl<'a> core::fmt::Display for JsonValue<'a> {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        fn rec(value: &JsonValue, f: &mut core::fmt::Formatter, indent: usize) -> core::fmt::Result {
            match value {
                JsonValue::Null =>
                    write!(f, "null"),

                JsonValue::Bool(v) =>
                    if *v { write!(f, "true")  }
                    else  { write!(f, "false") },

                JsonValue::Number(v) =>
                    write!(f, "{}", v),

                JsonValue::String(v) =>
                    write!(f, "\"{}\"", v),

                JsonValue::Array(values) => {
                    if values.len() == 0 {
                        return write!(f, "{{}}");
                    }

                    write!(f, "[")?;
                    for (i, value) in values.iter().enumerate() {
                        if i != 0 { write!(f, ",")?; }

                        if f.alternate() {
                            write!(f, "\n")?;
                            for _ in 0..indent+1 { write!(f, "    ")?; }
                        }
                        else if i != 0 {
                            write!(f, " ")?;
                        }

                        rec(value, f, indent+1)?;
                    }
                    if f.alternate() {
                        write!(f, "\n")?;
                        for _ in 0..indent { write!(f, "    ")?; }
                    }
                    write!(f, "]")
                }

                JsonValue::Object(entries) => {
                    if entries.len() == 0 {
                        return write!(f, "{{}}");
                    }

                    write!(f, "{{")?;
                    for (i, (key, value)) in entries.iter().enumerate() {
                        if i != 0 { write!(f, ",")?; }

                        if f.alternate() {
                            write!(f, "\n")?;
                            for _ in 0..indent+1 { write!(f, "    ")?; }
                        }
                        else if i != 0 {
                            write!(f, " ")?;
                        }

                        write!(f, "\"{}\": ", key)?;
                        rec(value, f, indent+1)?;
                    }
                    if f.alternate() {
                        write!(f, "\n")?;
                        for _ in 0..indent { write!(f, "    ")?; }
                    }
                    write!(f, "}}")
                }
            }
        }
        rec(self, f, 0)
    }
}

