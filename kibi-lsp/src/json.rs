use kibi::sti;
use sti::traits::CopyIt;
use sti::arena::Arena;
use sti::string::String;
use sti::utf8;
use sti::vec::Vec;
use sti::reader::Reader;


#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Value<'a> {
    Null,
    Bool(bool),
    Number(f64),
    String(&'a str),
    Array(&'a [Value<'a>]),
    Object(&'a [(&'a str, Value<'a>)]),
    Encoded(&'a str),
}

impl<'a> Value<'a> {
    #[inline(always)] pub fn is_null(self)   -> bool { if let Value::Null      = self { true } else { false } }
    #[inline(always)] pub fn is_bool(self)   -> bool { if let Value::Bool(_)   = self { true } else { false } }
    #[inline(always)] pub fn is_number(self) -> bool { if let Value::Number(_) = self { true } else { false } }
    #[inline(always)] pub fn is_string(self) -> bool { if let Value::String(_) = self { true } else { false } }
    #[inline(always)] pub fn is_array(self)  -> bool { if let Value::Array(_)  = self { true } else { false } }
    #[inline(always)] pub fn is_object(self) -> bool { if let Value::Object(_) = self { true } else { false } }

    #[inline(always)] pub fn try_null(self)   -> Option<()>                         { if let Value::Null       = self { Some(()) } else { None } }
    #[inline(always)] pub fn try_bool(self)   -> Option<bool>                       { if let Value::Bool(it)   = self { Some(it) } else { None } }
    #[inline(always)] pub fn try_number(self) -> Option<f64>                        { if let Value::Number(it) = self { Some(it) } else { None } }
    #[inline(always)] pub fn try_string(self) -> Option<&'a str>                    { if let Value::String(it) = self { Some(it) } else { None } }
    #[inline(always)] pub fn try_array(self)  -> Option<&'a [Value<'a>]>            { if let Value::Array(it)  = self { Some(it) } else { None } }
    #[inline(always)] pub fn try_object(self) -> Option<&'a [(&'a str, Value<'a>)]> { if let Value::Object(it) = self { Some(it) } else { None } }

    #[track_caller] #[inline(always)] pub fn as_null(self)   -> ()                         { if let Value::Null       = self { () } else { unreachable!() } }
    #[track_caller] #[inline(always)] pub fn as_bool(self)   -> bool                       { if let Value::Bool(it)   = self { it } else { unreachable!() } }
    #[track_caller] #[inline(always)] pub fn as_number(self) -> f64                        { if let Value::Number(it) = self { it } else { unreachable!() } }
    #[track_caller] #[inline(always)] pub fn as_string(self) -> &'a str                    { if let Value::String(it) = self { it } else { unreachable!() } }
    #[track_caller] #[inline(always)] pub fn as_array(self)  -> &'a [Value<'a>]            { if let Value::Array(it)  = self { it } else { unreachable!() } }
    #[track_caller] #[inline(always)] pub fn as_object(self) -> &'a [(&'a str, Value<'a>)] { if let Value::Object(it) = self { it } else { unreachable!() } }

    #[inline(always)]
    pub fn get(self, key: &str) -> Option<Value<'a>> {
        if let Value::Object(entries) = self {
            let mut result = None;
            for (k, v) in entries.copy_it() {
                if k == key {
                    if result.is_some() {
                        return None;
                    }
                    result = Some(v);
                }
            }
            return result;
        }
        else { None }
    }
}

impl<'a> core::ops::Index<&str> for Value<'a> {
    type Output = Value<'a>;

    #[track_caller]
    #[inline(always)]
    fn index(&self, key: &str) -> &Self::Output {
        let entries = self.as_object();
        let mut result = None;
        for (k, v) in entries {
            if *k == key {
                if result.is_some() {
                    unreachable!();
                }
                result = Some(v);
            }
        }
        return result.unwrap();
    }
}


#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Error {
    UnexpectedEof,
    Expected(usize, &'static str),
    InvalidUtf8(usize),
    InvalidEscape(usize),
    MalformedNumber(usize),
}


pub fn parse<'a>(alloc: &'a Arena, input: &'a [u8]) -> Result<Value<'a>, Error> {
    let mut parser = Parser { alloc, reader: Reader::new(input) };
    let result = parser.parse()?;
    parser.skip_ws();
    if parser.reader.remaining() != 0 {
        return Err(Error::Expected(parser.reader.consumed(), "eof"));
    }
    return Ok(result);
}

struct Parser<'a> {
    alloc: &'a Arena,
    reader: Reader<'a, u8>,
}

impl<'a> Parser<'a> {
    fn parse(&mut self) -> Result<Value<'a>, Error> {
        self.skip_ws();

        let start_pos = self.reader.offset();
        let at = self.reader.next().ok_or(Error::UnexpectedEof)?;
        match at {
            b'n' => {
                let ull = self.reader.next_n(3).ok_or(Error::UnexpectedEof)?;
                if ull != b"ull" {
                    return Err(Error::Expected(start_pos, "null"));
                }
                Ok(Value::Null)
            }

            b'f' => {
                let alse = self.reader.next_n(4).ok_or(Error::UnexpectedEof)?;
                if alse != b"alse" {
                    return Err(Error::Expected(start_pos, "false"));
                }
                Ok(Value::Bool(false))
            }

            b't' => {
                let rue = self.reader.next_n(3).ok_or(Error::UnexpectedEof)?;
                if rue != b"rue" {
                    return Err(Error::Expected(start_pos, "true"));
                }
                Ok(Value::Bool(true))
            }

            b'-' | b'0'..=b'9' => {
                let number = self.reader.consume_while_slice_from(start_pos,
                    |at| at.is_ascii_digit() || *at == b'.' || *at == b'e' || *at == b'E').0;

                let number = unsafe { core::str::from_utf8_unchecked(number) };

                let number = number.parse::<f64>().ok()
                    .ok_or(Error::MalformedNumber(start_pos))?;

                Ok(Value::Number(number))
            }

            b'"' => {
                Ok(Value::String(self.parse_string()?))
            }

            b'[' => {
                let mut result = Vec::new_in(self.alloc);

                self.skip_ws();

                let mut had_sep = true;
                while !self.reader.consume_if_eq(&b']') {
                    if !had_sep {
                        return Err(Error::Expected(self.reader.consumed(), "']'"));
                    }

                    result.push(self.parse()?);
                    self.skip_ws();

                    had_sep = self.reader.consume_if_eq(&b',');
                    self.skip_ws();
                }

                Ok(Value::Array(result.clone_in(self.alloc).leak()))
            }

            b'{' => {
                let mut result = Vec::new_in(self.alloc);

                self.skip_ws();

                let mut had_sep = true;
                while !self.reader.consume_if_eq(&b'}') {
                    if !had_sep {
                        return Err(Error::Expected(self.reader.consumed(), "'}'"));
                    }

                    if !self.reader.consume_if_eq(&b'"') {
                        return Err(Error::Expected(self.reader.consumed(), "'\"'"));
                    }
                    let key = self.parse_string()?;
                    self.skip_ws();

                    if !self.reader.consume_if_eq(&b':') {
                        return Err(Error::Expected(self.reader.consumed(), "':'"));
                    }

                    let value = self.parse()?;

                    result.push((key, value));
                    self.skip_ws();

                    had_sep = self.reader.consume_if_eq(&b',');
                    self.skip_ws();
                }

                Ok(Value::Object(result.clone_in(self.alloc).leak()))
            }

            _ => Err(Error::Expected(start_pos, "value")),
        }
    }

    fn parse_string(&mut self) -> Result<&'a str, Error> {
        let mut buffer = String::new_in(self.alloc);
        loop {
            match utf8::validate_string_inline(self.reader.as_slice()) {
                Ok((str, stopper)) => {
                    if !stopper { return Err(Error::UnexpectedEof) }

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
                            b't'  => buffer.push_char('\t'),

                            b'u' => {
                                unimplemented!()
                            }

                            _ => return Err(Error::InvalidEscape(escape_pos)),
                        }
                    }
                }

                Err(_) => {
                    return Err(Error::InvalidUtf8(self.reader.consumed()));
                }
            }
        }
    }

    #[inline]
    fn skip_ws(&mut self) {
        self.reader.consume_while(|at| at.is_ascii_whitespace());
    }
}


impl Into<Value<'static>> for () {
    #[inline(always)]
    fn into(self) -> Value<'static> { Value::Null }
}

impl Into<Value<'static>> for bool {
    #[inline(always)]
    fn into(self) -> Value<'static> { Value::Bool(self) }
}

impl Into<Value<'static>> for f64 {
    #[inline(always)]
    fn into(self) -> Value<'static> { Value::Number(self) }
}

impl<'a> Into<Value<'a>> for &'a str {
    #[inline(always)]
    fn into(self) -> Value<'a> { Value::String(self) }
}

impl<'a> Into<Value<'a>> for &'a [Value<'a>] {
    #[inline(always)]
    fn into(self) -> Value<'a> { Value::Array(self) }
}

impl<'a> Into<Value<'a>> for &'a [(&'a str, Value<'a>)] {
    #[inline(always)]
    fn into(self) -> Value<'a> { Value::Object(self) }
}

impl<'a> core::fmt::Display for Value<'a> {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        fn rec(value: &Value, f: &mut core::fmt::Formatter, indent: usize) -> core::fmt::Result {
            match value {
                Value::Null =>
                    write!(f, "null"),

                Value::Bool(v) =>
                    if *v { write!(f, "true")  }
                    else  { write!(f, "false") },

                Value::Number(v) =>
                    write!(f, "{}", v),

                Value::String(v) =>
                    write!(f, "{:?}", v),

                Value::Array(values) => {
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

                Value::Object(entries) => {
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

                Value::Encoded(v) => {
                    write!(f, "{}", v)
                }
            }
        }
        rec(self, f, 0)
    }
}

