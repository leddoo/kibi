#[derive(Clone, Copy, Debug, PartialEq)]
pub struct SourcePos {
    pub line:   u32,
    pub column: u32,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct SourceRange {
    pub begin: SourcePos,
    pub end:   SourcePos,
}

impl SourceRange {
    #[inline(always)]
    pub fn is_collapsed(&self) -> bool {
        self.begin == self.end
    }
}


#[derive(Clone, Copy, Debug)]
pub struct Token<'a> {
    pub range: SourceRange,
    pub data: TokenData<'a>,
}

impl<'a> Token<'a> {
    #[inline(always)]
    pub fn new(begin: SourcePos, end: SourcePos, data: TokenData<'a>) -> Self {
        Self { range: SourceRange { begin, end }, data }
    }
}


#[derive(Clone, Copy, Debug)]
pub enum TokenData<'a> {
    Name   (&'a str),
    Number (&'a str),
    LParen,
    RParen,
    LBracket,
    RBracket,
    LCurly,
    RCurly,
    Dot,
    Comma,
    Colon,
    SemiColon,
    KwEnd,
    KwLet, KwVar,
    KwDo,
    KwIf,
    KwElif,
    KwElse,
    KwWhile,
    KwFor,
    OpPlus,
    OpPlusEq,
    OpMinus,
    OpMinusEq,
    OpStar,
    OpStarEq,
    OpSlash,
    OpSlashEq,
    OpSlashSlash,
    OpSlashSlashEq,
    OpEq,
    OpEqEq,
    OpNeq,
    OpLeq,
    OpLt,
    OpGeq,
    OpGt,
    OpNot,
}

impl<'a> TokenData<'a> {
    pub fn semi_colon_after(&self) -> bool {
        use TokenData::*;
        match self {
            Name (_) | Number (_) |
            RParen | RBracket | RCurly |
            KwEnd
            => true,

            LParen | LBracket | LCurly |
            Dot | Comma | Colon | SemiColon |
            KwLet | KwVar |
            KwDo |
            KwIf | KwElif | KwElse |
            KwWhile | KwFor |
            OpPlus | OpPlusEq |
            OpMinus | OpMinusEq |
            OpStar | OpStarEq |
            OpSlash | OpSlashEq |
            OpSlashSlash | OpSlashSlashEq |
            OpEq | OpEqEq | OpNeq |
            OpLeq | OpLt | OpGeq | OpGt |
            OpNot
            => false,
        }
    }

    pub fn semi_colon_before(&self) -> bool {
        use TokenData::*;
        match self {
            Name (_) |
            Number (_) |
            LParen |
            LBracket |
            LCurly |
            KwLet | KwVar |
            KwDo |
            KwIf |
            KwWhile |
            KwFor |
            OpNot
            => true,

            RParen |
            RBracket |
            RCurly |
            Dot | Comma | Colon | SemiColon |
            KwEnd |
            KwElif | KwElse |
            OpPlus | OpPlusEq |
            OpMinus | OpMinusEq |
            OpStar | OpStarEq |
            OpSlash | OpSlashEq |
            OpSlashSlash | OpSlashSlashEq |
            OpEq | OpEqEq | OpNeq |
            OpLeq | OpLt | OpGeq | OpGt
            => false,
        }
    }
}


pub struct Tokenizer<'i> {
    input: &'i [u8],
    current: usize,

    line: u32,
    line_begin: usize,

    current_token: Option<Token<'i>>,
    next_token:    Option<Token<'i>>,
}

impl<'i> Tokenizer<'i> {
    pub fn new(input: &'i [u8]) -> Self {
        let mut r = Tokenizer {
            input, current: 0,
            line: 1, line_begin: 0,
            current_token: None, next_token: None,
        };
        r.next();
        r
    }

    #[inline(always)]
    pub fn current(&mut self) -> Option<&Token> {
        self.current_token.as_ref()
    }

    #[inline(always)]
    pub fn try_consume(&mut self) -> Option<Token> {
        if let Some(at) = self.current_token {
            self.next();
            return Some(at)
        }
        None
    }

    #[inline(always)]
    pub fn consume(&mut self) -> Token {
        self.try_consume().unwrap()
    }

    fn next(&mut self) {
        if let Some(current) = self.current_token {
            if let Some(next) = self.next_token {
                let has_line_break = current.range.end.line < next.range.begin.line;

                // insert semi-colon.
                if has_line_break
                && current.data.semi_colon_after()
                && next.data.semi_colon_before() {
                    // @auto-semi-colon-collapsed-range
                    let pos = current.range.end;
                    self.current_token = Some(Token::new(pos, pos, TokenData::SemiColon));
                }
                else {
                    self.current_token = self.next_token;
                    self.next_token    = self.next_token();
                }
            }
            else {
                assert_eq!(self.current, self.input.len());
                self.current_token = None;
            }
        }
        else {
            self.current_token = self.next_token();
            self.next_token    = self.next_token();
        }
    }

    #[inline(always)]
    fn pos(&self) -> SourcePos {
        SourcePos { line: self.line, column: (1 + self.current - self.line_begin) as u32 }
    }

    #[inline(always)]
    fn peek_ch(&self, offset: usize) -> Option<u8> {
        self.input.get(self.current + offset).cloned()
    }

    #[inline(always)]
    fn peek_ch_zero(&self, offset: usize) -> u8 {
        self.peek_ch(offset).unwrap_or(0)
    }

    #[inline(always)]
    fn consume_ch(&mut self, count: usize) {
        self.current += count;
    }

    #[inline(always)]
    fn consume_ch_while<P: Fn(char) -> bool>(&mut self, p: P) {
        while let Some(at) = self.peek_ch(0) {
            if p(at as char) {
                self.current += 1;
            }
            else { break }
        }
    }

    #[inline(always)]
    fn mk_token(&self, begin: SourcePos, data: TokenData<'i>) -> Token<'i> {
        Token::new(begin, self.pos(), data)
    }

    fn skip_whitespace(&mut self) {
        while let Some(at) = self.peek_ch(0) {
            if at == '\n' as u8 {
                self.consume_ch(1);
                self.line += 1;
                self.line_begin = self.current;
            }
            else if at.is_ascii_whitespace() {
                self.consume_ch(1);
            }
            else { break }
        }
    }

    fn next_token(&mut self) -> Option<Token<'i>> {
        self.skip_whitespace();

        let at = self.peek_ch(0)?;

        let begin_offset = self.current;
        let begin_pos = self.pos();

        macro_rules! single_ch {
            ($td: expr) => {{
                self.consume_ch(1);
                return Some(self.mk_token(begin_pos, $td));
            }};
        }

        macro_rules! single_or_double {
            ($td: expr, $cont: expr, $td_cont: expr) => {{
                self.consume_ch(1);

                if self.peek_ch_zero(0) == $cont as u8 {
                    self.consume_ch(1);
                    return Some(self.mk_token(begin_pos, $td_cont));
                }
                else {
                    return Some(self.mk_token(begin_pos, $td));
                }
            }};
        }

        match at as char {
            '(' => single_ch!(TokenData::LParen),
            ')' => single_ch!(TokenData::RParen),
            '[' => single_ch!(TokenData::LBracket),
            ']' => single_ch!(TokenData::LBracket),
            '{' => single_ch!(TokenData::LCurly),
            '}' => single_ch!(TokenData::LCurly),

            '.' => single_ch!(TokenData::Dot),
            ',' => single_ch!(TokenData::Comma),
            ':' => single_ch!(TokenData::Colon),
            ';' => single_ch!(TokenData::SemiColon),

            '+' => single_or_double!(TokenData::OpPlus,  '=', TokenData::OpPlusEq),
            '-' => single_or_double!(TokenData::OpMinus, '=', TokenData::OpMinusEq),
            '*' => single_or_double!(TokenData::OpStar,  '=', TokenData::OpStarEq),

            '/' => {
                self.consume_ch(1);

                if self.peek_ch_zero(0) == '=' as u8 {
                    self.consume_ch(1);
                    return Some(self.mk_token(begin_pos, TokenData::OpSlashEq));
                }
                else if self.peek_ch_zero(0) == '/' as u8 {
                    self.consume_ch(1);
                    if self.peek_ch_zero(0) == '=' as u8 {
                        self.consume_ch(1);
                        return Some(self.mk_token(begin_pos, TokenData::OpSlashSlashEq));
                    }
                    else {
                        return Some(self.mk_token(begin_pos, TokenData::OpSlashSlash));
                    }
                }
                else {
                    return Some(self.mk_token(begin_pos, TokenData::OpSlash));
                }
            }

            '=' => single_or_double!(TokenData::OpEq,  '=', TokenData::OpEqEq),
            '!' => single_or_double!(TokenData::OpNot, '=', TokenData::OpNeq),
            '<' => single_or_double!(TokenData::OpLt,  '=', TokenData::OpLeq),
            '>' => single_or_double!(TokenData::OpGt,  '=', TokenData::OpGeq),

            _ => (),
        }

        // name
        if at.is_ascii_alphabetic() || at == '_' as u8 {
            self.consume_ch(1);
            self.consume_ch_while(|c|
                c.is_ascii_alphanumeric() || c == '_');

            let value = &self.input[begin_offset..self.current];
            let value = unsafe { core::str::from_utf8_unchecked(value) };

            let data = match value {
                "end"   => TokenData::KwEnd,
                "let"   => TokenData::KwLet,
                "var"   => TokenData::KwVar,
                "do"    => TokenData::KwDo,
                "if"    => TokenData::KwIf,
                "elif"  => TokenData::KwElif,
                "else"  => TokenData::KwElse,
                "while" => TokenData::KwWhile,
                "for"   => TokenData::KwFor,

                _ => TokenData::Name(value),
            };
            return Some(self.mk_token(begin_pos, data));
        }

        // number
        if at.is_ascii_digit() {
            self.consume_ch(1);
            self.consume_ch_while(|c| c.is_ascii_digit());

            let value = &self.input[begin_offset..self.current];
            let value = unsafe { core::str::from_utf8_unchecked(value) };
            return Some(self.mk_token(begin_pos, TokenData::Number(value)));
        }

        unimplemented!();
    }
}


