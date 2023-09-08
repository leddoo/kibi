use kibi::sti;
use sti::arena::Arena;
use sti::arena_pool::ArenaPool;
use sti::vec::Vec;
use sti::reader::Reader;


#[derive(Clone, Copy, Debug)]
pub enum JsonValue<'a> {
    Null,
    Bool(bool),
    Number(f64),
    String(&'a str),
    Array(&'a [JsonValue<'a>]),
    Object(&'a [(&'a str, JsonValue<'a>)]),
}

impl<'a> JsonValue<'a> {
    pub fn parse(alloc: &'a Arena, input: &[u8]) -> Result<JsonValue<'a>, JsonError> {
        Parser { alloc, reader: Reader::new(input) }.parse()
    }
}

#[derive(Clone, Copy, Debug)]
pub enum JsonError {
    UnexpectedEof,
    ExpectedNull(usize),
    ExpectedFalse(usize),
    ExpectedTrue(usize),
    MalformedNumber(usize),
}

struct Parser<'i, 'a> {
    alloc: &'a Arena,
    reader: Reader<'i, u8>,
}

impl<'i, 'a> Parser<'i, 'a> {
    fn parse(&mut self) -> Result<JsonValue<'a>, JsonError> {
        self.skip_ws();

        let start_pos = self.reader.offset();
        let at = self.reader.next().ok_or(JsonError::UnexpectedEof)?;
        match at {
            b'n' => {
                let ull = self.reader.next_n(3).ok_or(JsonError::UnexpectedEof)?;
                if ull != b"ull" {
                    return Err(JsonError::ExpectedNull(start_pos));
                }
                Ok(JsonValue::Null)
            }

            b'f' => {
                let alse = self.reader.next_n(4).ok_or(JsonError::UnexpectedEof)?;
                if alse != b"alse" {
                    return Err(JsonError::ExpectedFalse(start_pos));
                }
                Ok(JsonValue::Bool(false))
            }

            b't' => {
                let rue = self.reader.next_n(3).ok_or(JsonError::UnexpectedEof)?;
                if rue != b"rue" {
                    return Err(JsonError::ExpectedTrue(start_pos));
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
                let _temp = unsafe { ArenaPool::tls_get_scoped(&[]) };
                unimplemented!()
            }

            b'[' => {
                unimplemented!()
            }

            b'{' => {
                unimplemented!()
            }

            _ => unimplemented!()
        }
    }

    #[inline]
    fn skip_ws(&mut self) {
        self.reader.consume_while(|at| at.is_ascii_whitespace());
    }
}

