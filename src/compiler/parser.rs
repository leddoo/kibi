use derive_more::Deref;
use super::*;


#[derive(Clone, Copy, Debug, Deref)]
pub struct Token<'a> {
    #[deref]
    pub data:   TokenData<'a>,
    pub source: SourceRange,
}

impl<'a> Token<'a> {
    #[inline(always)]
    pub fn new(begin: SourcePos, end: SourcePos, data: TokenData<'a>) -> Self {
        Self { source: SourceRange { begin, end }, data }
    }
}



#[derive(Clone, Copy, Debug, PartialEq)]
pub enum TokenData<'a> {
    Ident  (&'a str),
    Number (&'a str),
    Bool   (bool),
    Nil,
    QuotedString (&'a str),
    LParen,
    RParen,
    LBracket,
    RBracket,
    LCurly,
    RCurly,
    Dot,
    Comma,
    Colon,
    Semicolon,
    KwLet, KwVar,
    KwDo,
    KwIf,
    KwElif,
    KwElse,
    KwWhile,
    KwFor,
    KwIn,
    KwBreak,
    KwContinue,
    KwReturn,
    KwEnd,
    KwFn,
    KwAnd,
    KwOr,
    KwNot,
    KwEnv,
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
    FatArrow,
    ColonEq,
    OpEq,
    OpEqEq,
    OpNe,
    OpLe,
    OpLt,
    OpGe,
    OpGt,
    OpNot,
    OpQ,
    OpQDot,
    OpQQ,
    OpQQEq,
}

impl<'a> TokenData<'a> {
    pub fn semicolon_after(&self) -> bool {
        use TokenData::*;
        match self {
            // anything that can mark the end
            // of an expression.
            Ident (_) | Number (_) | Bool(_) | Nil | QuotedString(_) |
            RParen | RBracket | RCurly |
            KwBreak | KwContinue | KwReturn |
            KwEnv |
            KwEnd
            => true,

            LParen | LBracket | LCurly |
            Dot | Comma | Colon | Semicolon |
            KwLet | KwVar |
            KwDo |
            KwIf | KwElif | KwElse |
            KwWhile | KwFor | KwIn |
            KwFn |
            KwAnd | KwOr |
            OpPlus | OpPlusEq |
            OpMinus | OpMinusEq |
            OpStar | OpStarEq |
            OpSlash | OpSlashEq |
            OpSlashSlash | OpSlashSlashEq |
            FatArrow | ColonEq |
            OpEq | OpEqEq | OpNe | OpLe | OpLt | OpGe | OpGt |
            OpQ | OpQDot | OpQQ | OpQQEq |
            OpNot | KwNot
            => false,
        }
    }

    pub fn semicolon_before(&self) -> bool {
        use TokenData::*;
        match self {
            Ident (_) | Number (_) | Bool(_) | Nil | QuotedString(_) |
            LParen | LBracket | LCurly |
            KwLet | KwVar |
            KwDo | KwIf | KwElif | KwElse | KwWhile | KwFor |
            KwBreak | KwContinue | KwReturn |
            KwEnd |
            KwFn |
            KwEnv |
            OpNot | KwNot
            => true,

            // unless the next token indicates
            // that the expression may continue.
            RParen |
            RBracket |
            RCurly |
            Dot | Comma | Colon | Semicolon |
            KwIn |
            KwAnd | KwOr |
            OpPlus | OpPlusEq |
            OpMinus | OpMinusEq |
            OpStar | OpStarEq |
            OpSlash | OpSlashEq |
            OpSlashSlash | OpSlashSlashEq |
            FatArrow | ColonEq |
            OpEq | OpEqEq | OpNe | OpLe | OpLt | OpGe | OpGt |
            OpQ | OpQDot | OpQQ | OpQQEq
            => false,
        }
    }

    #[inline(always)]
    pub fn is_ident(&self) -> bool {
        if let TokenData::Ident(_) = self { true } else { false }
    }


    #[inline(always)]
    pub fn is_block_end(&self) -> bool {
        use TokenData::*;
        match self {
            KwEnd | KwElse | KwElif => true,
            _ => false,
        }
    }

    #[inline]
    pub fn is_expr_start(&self) -> bool {
        use TokenData::*;
        match self {
            Ident (_) | Number (_) | Bool (_) | Nil | QuotedString (_) |
            LParen | LBracket | LCurly |
            KwLet | KwVar |
            KwDo | KwIf | KwWhile | KwFor |
            KwBreak | KwContinue | KwReturn |
            KwFn |
            KwNot | OpNot |
            KwEnv |
            OpPlus | OpMinus | OpStar
            => true,

            RParen | RBracket | RCurly |
            Dot | Comma | Colon | Semicolon |
            KwEnd |
            KwElif | KwElse |
            KwIn |
            KwAnd | KwOr |
            OpPlusEq | OpMinusEq | OpStarEq |
            OpSlash | OpSlashEq | OpSlashSlash | OpSlashSlashEq |
            FatArrow | ColonEq |
            OpEq | OpEqEq | OpNe | OpLe | OpLt | OpGe | OpGt |
            OpQ | OpQDot | OpQQ | OpQQEq
            => false
        }
    }
}


#[derive(Clone, Copy, Debug)]
pub struct ParseError {
    pub source: SourceRange,
    pub data: ParseErrorData,
}

impl ParseError {
    #[inline(always)]
    pub fn eof() -> ParseError {
        ParseError { source: SourceRange::null(), data: ParseErrorData::UnexpectedEof }
    }

    #[inline(always)]
    pub fn at_pos(pos: SourcePos, data: ParseErrorData) -> ParseError {
        ParseError { source: pos.to_range(), data }
    }

    #[inline(always)]
    pub fn at(token: &Token, data: ParseErrorData) -> ParseError {
        ParseError { source: token.source, data }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum ParseErrorData {
    Expected(TokenData<'static>),
    ExpectedExpression,
    UnexpectedEof,
    UnexpectedChar,
    TrailingInput,
    TempWonkyString,
}

pub type ParseResult<T> = Result<T, ParseError>;



pub struct Tokenizer<'i> {
    input: &'i [u8],
    cursor: usize,

    line: u32,
    line_begin: usize,

    tokens: Vec<Token<'i>>,
}

impl<'i> Tokenizer<'i> {
    pub fn new(input: &'i [u8]) -> Self {
        Tokenizer {
            input, cursor: 0,
            line: 1, line_begin: 0,
            tokens: vec![],
        }
    }

    #[inline(always)]
    fn pos(&self) -> SourcePos {
        SourcePos { line: self.line, column: (1 + self.cursor - self.line_begin) as u32 }
    }

    #[inline(always)]
    fn peek_ch(&self, offset: usize) -> Option<u8> {
        self.input.get(self.cursor + offset).cloned()
    }

    #[inline(always)]
    fn peek_ch_zero(&self, offset: usize) -> u8 {
        self.peek_ch(offset).unwrap_or(0)
    }

    #[inline(always)]
    fn consume_ch(&mut self, count: usize) {
        self.cursor += count;
    }

    #[inline(always)]
    fn consume_ch_while<P: Fn(char) -> bool>(&mut self, p: P) {
        while let Some(at) = self.peek_ch(0) {
            if p(at as char) {
                self.cursor += 1;
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
                self.line_begin = self.cursor;
            }
            else if at.is_ascii_whitespace() {
                self.consume_ch(1);
            }
            // block comments.
            else if self.at_block_comment_start() {
                self.consume_ch(4);

                let mut depth = 1;
                while depth > 0 {
                    if self.at_block_comment_start() {
                        self.consume_ch(4);
                        depth += 1;
                    }
                    else if self.at_block_comment_stop() {
                        self.consume_ch(4);
                        depth -= 1;
                    }
                    else if self.peek_ch(0) == Some('\n' as u8) {
                        self.consume_ch(1);
                        self.line += 1;
                        self.line_begin = self.cursor;
                    }
                    else {
                        self.consume_ch(1);
                    }
                }
            }
            // single line comments.
            else if at == '-' as u8 && self.peek_ch(1) == Some('-' as u8) {
                self.consume_ch_while(|c| c != '\n');
            }
            else { break }
        }
    }

    #[inline]
    fn at_block_comment_start(&self) -> bool {
        if self.cursor + 4 <= self.input.len() {
               self.input[self.cursor + 0] == '-' as u8
            && self.input[self.cursor + 1] == '-' as u8
            && self.input[self.cursor + 2] == '[' as u8
            && self.input[self.cursor + 3] == '[' as u8
        }
        else { false }
    }

    #[inline]
    fn at_block_comment_stop(&self) -> bool {
        if self.cursor + 4 <= self.input.len() {
               self.input[self.cursor + 0] == '-' as u8
            && self.input[self.cursor + 1] == '-' as u8
            && self.input[self.cursor + 2] == ']' as u8
            && self.input[self.cursor + 3] == ']' as u8
        }
        else { false }
    }

    pub fn run(&mut self, insert_semicolons: bool) -> ParseResult<()> {
        while let Some(tok) = self.next_token()? {
            if insert_semicolons {
                if let Some(prev) = self.tokens.last() {
                    if prev.source.end.line < tok.source.begin.line
                    && prev.semicolon_after()
                    && tok.semicolon_before() {
                        self.tokens.push(Token {
                            data: TokenData::Semicolon,
                            source: prev.source.end.to_range(),
                        });
                    }
                }
            }

            self.tokens.push(tok);
        }
        Ok(())
    }

    fn next_token(&mut self) -> ParseResult<Option<Token<'i>>> {
        self.skip_whitespace();

        let Some(at) = self.peek_ch(0) else {
            return Ok(None);
        };

        let begin_offset = self.cursor;
        let begin_pos = self.pos();

        macro_rules! tok_1 {
            ($td: expr) => {{
                self.consume_ch(1);
                return Ok(Some(self.mk_token(begin_pos, $td)));
            }};
        }

        macro_rules! tok_2 {
            ($td: expr, $cont: expr, $td_cont: expr) => {{
                self.consume_ch(1);

                if self.peek_ch_zero(0) == $cont as u8 {
                    self.consume_ch(1);
                    return Ok(Some(self.mk_token(begin_pos, $td_cont)));
                }
                else {
                    return Ok(Some(self.mk_token(begin_pos, $td)));
                }
            }};
        }

        match at as char {
            '(' => tok_1!(TokenData::LParen),
            ')' => tok_1!(TokenData::RParen),
            '[' => tok_1!(TokenData::LBracket),
            ']' => tok_1!(TokenData::RBracket),
            '{' => tok_1!(TokenData::LCurly),
            '}' => tok_1!(TokenData::RCurly),

            '.' => tok_1!(TokenData::Dot),
            ',' => tok_1!(TokenData::Comma),
            ':' => tok_2!(TokenData::Colon, '=', TokenData::ColonEq),
            ';' => tok_1!(TokenData::Semicolon),
            '?' => {
                self.consume_ch(1);

                if self.peek_ch_zero(0) == '?' as u8 {
                    self.consume_ch(1);

                    if self.peek_ch_zero(0) == '=' as u8 {
                        self.consume_ch(1);
                        return Ok(Some(self.mk_token(begin_pos, TokenData::OpQQEq)));
                    }
                    else {
                        return Ok(Some(self.mk_token(begin_pos, TokenData::OpQQ)));
                    }
                }
                else if self.peek_ch_zero(0) == '.' as u8 {
                    self.consume_ch(1);
                    return Ok(Some(self.mk_token(begin_pos, TokenData::OpQDot)));
                }
                else {
                    return Ok(Some(self.mk_token(begin_pos, TokenData::OpQ)));
                }
            }

            '+' => tok_2!(TokenData::OpPlus,  '=', TokenData::OpPlusEq),
            '-' => tok_2!(TokenData::OpMinus, '=', TokenData::OpMinusEq),
            '*' => tok_2!(TokenData::OpStar,  '=', TokenData::OpStarEq),

            '/' => {
                self.consume_ch(1);

                if self.peek_ch_zero(0) == '=' as u8 {
                    self.consume_ch(1);
                    return Ok(Some(self.mk_token(begin_pos, TokenData::OpSlashEq)));
                }
                else if self.peek_ch_zero(0) == '/' as u8 {
                    self.consume_ch(1);

                    if self.peek_ch_zero(0) == '=' as u8 {
                        self.consume_ch(1);
                        return Ok(Some(self.mk_token(begin_pos, TokenData::OpSlashSlashEq)));
                    }
                    else {
                        return Ok(Some(self.mk_token(begin_pos, TokenData::OpSlashSlash)));
                    }
                }
                else {
                    return Ok(Some(self.mk_token(begin_pos, TokenData::OpSlash)));
                }
            }

            '=' => {
                self.consume_ch(1);

                if self.peek_ch_zero(0) == '>' as u8 {
                    self.consume_ch(1);
                    return Ok(Some(self.mk_token(begin_pos, TokenData::FatArrow)));
                }
                else if self.peek_ch_zero(0) == '=' as u8 {
                    self.consume_ch(1);
                    return Ok(Some(self.mk_token(begin_pos, TokenData::OpEqEq)));
                }
                else {
                    return Ok(Some(self.mk_token(begin_pos, TokenData::OpEq)));
                }
            }

            '!' => tok_2!(TokenData::OpNot, '=', TokenData::OpNe),
            '<' => tok_2!(TokenData::OpLt,  '=', TokenData::OpLe),
            '>' => tok_2!(TokenData::OpGt,  '=', TokenData::OpGe),

            '"' => {
                self.consume_ch(1);

                loop {
                    let Some(at) = self.peek_ch(0) else {
                        return Err(ParseError::eof());
                    };

                    self.consume_ch(1);

                    if at == '"' as u8 {
                        let value = &self.input[begin_offset+1 .. self.cursor-1];

                        let Ok(value) = core::str::from_utf8(value) else {
                            return Err(ParseError::at_pos(begin_pos, ParseErrorData::TempWonkyString));
                        };

                        return Ok(Some(self.mk_token(begin_pos, TokenData::QuotedString(value))));
                    }

                    if at == '\\' as u8 {
                        unimplemented!();
                    }

                    if at == '\n' as u8 {
                        self.line += 1;
                        self.line_begin = self.cursor;
                    }
                }
            }

            _ => (),
        }

        // name
        if at.is_ascii_alphabetic() || at == '_' as u8 {
            self.consume_ch(1);
            self.consume_ch_while(|c|
                c.is_ascii_alphanumeric() || c == '_');

            let value = &self.input[begin_offset..self.cursor];
            let value = unsafe { core::str::from_utf8_unchecked(value) };

            let data = match value {
                "end"       => TokenData::KwEnd,
                "let"       => TokenData::KwLet,
                "var"       => TokenData::KwVar,
                "do"        => TokenData::KwDo,
                "if"        => TokenData::KwIf,
                "elif"      => TokenData::KwElif,
                "else"      => TokenData::KwElse,
                "while"     => TokenData::KwWhile,
                "for"       => TokenData::KwFor,
                "in"        => TokenData::KwIn,
                "break"     => TokenData::KwBreak,
                "continue"  => TokenData::KwContinue,
                "return"    => TokenData::KwReturn,
                "fn"        => TokenData::KwFn,
                "and"       => TokenData::KwAnd,
                "or"        => TokenData::KwOr,
                "not"       => TokenData::KwNot,
                "false"     => TokenData::Bool(false),
                "true"      => TokenData::Bool(true),
                "nil"       => TokenData::Nil,
                "ENV"       => TokenData::KwEnv,

                _ => TokenData::Ident(value),
            };
            return Ok(Some(self.mk_token(begin_pos, data)));
        }

        // number
        if at.is_ascii_digit() {
            self.consume_ch(1);
            self.consume_ch_while(|c| c.is_ascii_digit());

            let value = &self.input[begin_offset..self.cursor];
            let value = unsafe { core::str::from_utf8_unchecked(value) };
            return Ok(Some(self.mk_token(begin_pos, TokenData::Number(value))));
        }

        self.consume_ch(1);
        Err(ParseError { source: begin_pos.to_range(), data: ParseErrorData::UnexpectedChar })
    }

    pub fn tokenize(input: &'i [u8], insert_semicolons: bool) -> ParseResult<Vec<Token<'i>>> {
        let mut toker = Self::new(input);
        toker.run(insert_semicolons)?;
        Ok(toker.tokens)
    }
}



#[derive(Clone, Debug, Deref)]
pub struct Ast<'a> {
    pub source: SourceRange,
    #[deref]
    pub data:   AstData<'a>,
}

#[derive(Clone, Debug)]
pub enum AstData<'a> {
    Nil,
    Bool        (bool),
    Number      (&'a str),
    QuotedString(&'a str),
    Ident       (&'a str),
    Tuple       (Box<ast::Tuple<'a>>),
    List        (Box<ast::List<'a>>),
    Table       (Box<ast::Table<'a>>),
    Do          (Box<ast::Block<'a>>),
    SubExpr     (Box<Ast<'a>>),
    Local       (Box<ast::Local<'a>>),
    Op1         (Box<ast::Op1<'a>>),
    Op2         (Box<ast::Op2<'a>>),
    Field       (Box<ast::Field<'a>>),
    OptChain    (Box<ast::Field<'a>>),
    Index       (Box<ast::Index<'a>>),
    Call        (Box<ast::Call<'a>>),
    If          (Box<ast::If<'a>>),
    While       (Box<ast::While<'a>>),
    Break       (ast::Break<'a>),
    Continue,
    Return      (ast::Return<'a>),
    Fn          (Box<ast::Fn<'a>>),
    Env,
}

impl<'a> AstData<'a> {
    #[inline(always)]
    pub fn is_local(&self) -> bool {
        if let AstData::Local(_) = self { true } else { false }
    }
}

pub mod ast {
    use super::*;

    #[derive(Clone, Debug)]
    pub struct Tuple<'a> {
        pub values: Vec<Ast<'a>>,
    }

    #[derive(Clone, Debug)]
    pub struct List<'a> {
        pub values: Vec<Ast<'a>>,
    }

    #[derive(Clone, Debug)]
    pub struct Table<'a> {
        pub values: Vec<(Ident<'a>, Ast<'a>)>,
    }


    #[derive(Clone, Debug)]
    pub struct Block<'a> {
        pub stmts: Vec<Ast<'a>>,
    }


    #[derive(Clone, Debug)]
    pub struct Local<'a> {
        pub name:  &'a str,
        pub value: Option<Ast<'a>>,
        pub kind:  LocalKind,
    }

    #[derive(Clone, Debug)]
    pub enum LocalKind {
        Let,
        Var,
    }


    #[derive(Clone, Debug)]
    pub struct Op1<'a> {
        pub kind:  Op1Kind,
        pub child: Ast<'a>,
    }

    #[derive(Clone, Copy, Debug, PartialEq)]
    pub struct Op1Kind (pub super::Op1);


    #[derive(Clone, Debug)]
    pub struct Op2<'a> {
        pub kind:     Op2Kind,
        pub children: [Ast<'a>; 2],
    }

    #[derive(Clone, Copy, Debug, PartialEq)]
    pub enum Op2Kind {
        Op2       (super::Op2),
        Op2Assign (super::Op2),
        Assign,
        Define,
    }

    impl Op2Kind {
        #[inline]
        pub fn lprec(self) -> u32 {
            use Op2Kind::*;
            use super::Op2::*;
            match self {
                Assign             => 100,
                Define             => 100,
                Op2Assign(_)       => 100,
                Op2(op) => match op {
                    OrElse      => 150,
                    Or          => 200,
                    And         => 300,
                    CmpEq       => 400,
                    CmpNe       => 400,
                    CmpLe       => 400,
                    CmpLt       => 400,
                    CmpGe       => 400,
                    CmpGt       => 400,
                    Add         => 600,
                    Sub         => 600,
                    Mul         => 800,
                    Div         => 800,
                    IntDiv      => 800,
                }
            }
        }

        #[inline]
        pub fn rprec(self) -> u32 {
            use Op2Kind::*;
            use super::Op2::*;
            match self {
                Assign                 => 100,
                Define                 => 100,
                Op2Assign(_)           => 100,
                Op2(op) => match op {
                    OrElse          => 151,
                    Or              => 201,
                    And             => 301,
                    CmpEq           => 401,
                    CmpNe           => 401,
                    CmpLe           => 401,
                    CmpLt           => 401,
                    CmpGe           => 401,
                    CmpGt           => 401,
                    Add             => 601,
                    Sub             => 601,
                    Mul             => 801,
                    Div             => 801,
                    IntDiv          => 801,
                }
            }
        }
    }

    pub const PREC_PREFIX:  u32 =  900;
    pub const PREC_POSTFIX: u32 = 1000;


    #[derive(Clone, Debug)]
    pub struct Field<'a> {
        pub base: Ast<'a>,
        pub name: &'a str,
    }

    #[derive(Clone, Debug)]
    pub struct Index<'a> {
        pub base:  Ast<'a>,
        pub index: Ast<'a>,
    }

    #[derive(Clone, Debug)]
    pub struct Call<'a> {
        pub func: Ast<'a>,
        pub args: Vec<Ast<'a>>,
    }


    #[derive(Clone, Debug)]
    pub struct IfBlock<'a> {
        pub stmts: Vec<Ast<'a>>,
        pub is_do: bool,
    }

    #[derive(Clone, Debug)]
    pub struct If<'a> {
        pub condition: Ast<'a>,
        pub on_true:   IfBlock<'a>,
        pub on_false:  Option<IfBlock<'a>>,
    }

    #[derive(Clone, Debug)]
    pub struct While<'a> {
        pub condition: Ast<'a>,
        pub body:      Vec<Ast<'a>>,
    }


    #[derive(Clone, Debug)]
    pub struct Break<'a> {
        pub value: Option<Box<Ast<'a>>>,
    }

    #[derive(Clone, Debug)]
    pub struct Return<'a> {
        pub value: Option<Box<Ast<'a>>>,
    }


    #[derive(Clone, Debug)]
    pub struct Fn<'a> {
        pub name:   Option<&'a str>,
        pub params: Vec<FnParam<'a>>,
        pub body:   Vec<Ast<'a>>,
    }

    #[derive(Clone, Debug)]
    pub struct FnParam<'a> {
        pub name: &'a str,
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Ident<'i> {
    source: SourceRange,
    value:  &'i str,
}

impl<'i> Ident<'i> {
    #[inline(always)]
    fn to_ast(self) -> Ast<'i> {
        Ast { source: self.source, data: AstData::Ident(self.value) }
    }
}


pub struct Parser<'p, 'i> {
    tokens: &'p [Token<'i>],
    cursor: usize,
}

impl<'p, 'i> Parser<'p, 'i> {
    pub fn new(tokens: &'p [Token<'i>]) -> Self {
        Self { tokens, cursor: 0 }
    }

    fn peek(&self, offset: usize) -> Option<&Token<'i>> {
        self.tokens.get(self.cursor + offset)
    }

    fn peek_or_eof(&self, offset: usize) -> ParseResult<&Token<'i>> {
        self.tokens.get(self.cursor + offset).ok_or(ParseError::eof())
    }

    fn peek_if(&self, offset: usize, kind: TokenData<'static>) -> bool {
        if let Some(at) = self.peek(offset) {
            return at.data == kind;
        }
        false
    }

    fn next(&mut self) -> ParseResult<&Token<'i>> {
        let result = self.tokens.get(self.cursor).ok_or(ParseError::eof());
        self.cursor += 1;
        result
    }

    fn next_if(&mut self, kind: TokenData<'static>) -> bool {
        if let Some(at) = self.peek(0) {
            if at.data == kind {
                self.cursor += 1;
                return true;
            }
        }
        false
    }

    fn next_if_ident(&mut self) -> Option<&'i str> {
        if let Some(Token { data: TokenData::Ident(name), source: _ }) = self.tokens.get(self.cursor) {
            self.cursor += 1;
            return Some(name);
        }
        None
    }

    fn expect_ident(&mut self) -> ParseResult<Ident<'i>> {
        let tok = self.next()?;
        if let TokenData::Ident(value) = tok.data {
            return Ok(Ident { source: tok.source, value });
        }
        Err(ParseError::at(&tok, ParseErrorData::Expected(TokenData::Ident(""))))
    }

    fn expect(&mut self, kind: TokenData<'static>) -> ParseResult<SourceRange> {
        let tok = self.next()?;
        if tok.data == kind {
            return Ok(tok.source);
        }
        Err(ParseError::at(&tok, ParseErrorData::Expected(kind)))
    }

    fn peek_op1(&mut self) -> Option<ast::Op1Kind> {
        use TokenData::*;
        use super::Op1::*;
        Some(match self.peek(0)?.data {
            KwNot   => ast::Op1Kind(BoolNot),
            OpNot   => ast::Op1Kind(BitNot),
            OpMinus => ast::Op1Kind(Neg),
            OpPlus  => ast::Op1Kind(Plus),
            _ => return None,
        })
    }

    fn peek_op2(&mut self) -> Option<ast::Op2Kind> {
        use TokenData::*;
        use super::Op2::*;
        Some(match self.peek(0)?.data {
            KwAnd           => ast::Op2Kind::Op2(And),
            KwOr            => ast::Op2Kind::Op2(Or),
            OpPlus          => ast::Op2Kind::Op2(Add),
            OpPlusEq        => ast::Op2Kind::Op2Assign(Add),
            OpMinus         => ast::Op2Kind::Op2(Sub),
            OpMinusEq       => ast::Op2Kind::Op2Assign(Sub),
            OpStar          => ast::Op2Kind::Op2(Mul),
            OpStarEq        => ast::Op2Kind::Op2Assign(Mul),
            OpSlash         => ast::Op2Kind::Op2(Div),
            OpSlashEq       => ast::Op2Kind::Op2Assign(Div),
            OpSlashSlash    => ast::Op2Kind::Op2(IntDiv),
            OpSlashSlashEq  => ast::Op2Kind::Op2Assign(IntDiv),
            ColonEq         => ast::Op2Kind::Define,
            OpEq            => ast::Op2Kind::Assign,
            OpEqEq          => ast::Op2Kind::Op2(CmpEq),
            OpNe            => ast::Op2Kind::Op2(CmpNe),
            OpLe            => ast::Op2Kind::Op2(CmpLe),
            OpLt            => ast::Op2Kind::Op2(CmpLt),
            OpGe            => ast::Op2Kind::Op2(CmpGe),
            OpGt            => ast::Op2Kind::Op2(CmpGt),
            OpQQ            => ast::Op2Kind::Op2(OrElse),
            OpQQEq          => ast::Op2Kind::Op2Assign(OrElse),
            _ => return None
        })
    }


    // bool: terminated (needs no semi-colon).
    fn parse_leading_expr(&mut self, prec: u32) -> ParseResult<Ast<'i>> {
        let current = *self.next()?;

        // ident.
        if let TokenData::Ident(ident) = current.data {
            let source = current.source;
            return Ok(Ast { source, data: AstData::Ident(ident) });
        }

        // number.
        if let TokenData::Number(value) = current.data {
            let source = current.source;
            return Ok(Ast { source, data: AstData::Number(value) });
        }

        // bool.
        if let TokenData::Bool(value) = current.data {
            let source = current.source;
            return Ok(Ast { source, data: AstData::Bool(value) });
        }

        // nil.
        if let TokenData::Nil = current.data {
            let source = current.source;
            return Ok(Ast { source, data: AstData::Nil });
        }

        // string.
        if let TokenData::QuotedString(value) = current.data {
            let source = current.source;
            return Ok(Ast { source, data: AstData::QuotedString(value) });
        }

        let begin = current.source.begin;

        // tuples & sub-expr.
        if let TokenData::LParen = current.data {
            let (values, had_comma) = self.parse_comma_exprs(TokenData::RParen)?;
            let data =
                if values.len() == 1 && !had_comma {
                    AstData::SubExpr(Box::new(values.into_iter().next().unwrap()))
                }
                else {
                    AstData::Tuple(Box::new(ast::Tuple { values }))
                };

            let end = self.expect(TokenData::RParen)?.end;
            return Ok(Ast { source: SourceRange { begin, end }, data });
        }

        // if
        if let TokenData::KwIf = current.data {
            return self.parse_if_as_ast(begin);
        }

        // while
        if let TokenData::KwWhile = current.data {
            let condition = self.parse_expr(0)?;
            self.expect(TokenData::Colon)?;

            let body = self.parse_block()?.stmts;

            let data = AstData::While(Box::new(ast::While { condition, body }));
            let end = self.expect(TokenData::KwEnd)?.end;
            return Ok(Ast { source: SourceRange { begin, end }, data });
        }

        // do
        if let TokenData::KwDo = current.data {
            self.expect(TokenData::Colon)?;

            let block = self.parse_block()?;
            let data = AstData::Do(Box::new(block));

            let end = self.expect(TokenData::KwEnd)?.end;
            return Ok(Ast { source: SourceRange { begin, end }, data });
        }

        // break
        if let TokenData::KwBreak = current.data {
            let mut source = current.source;

            let mut value = None;
            if let Some(at) = self.peek(0) {
                if at.is_expr_start() {
                    let v = self.parse_expr(0)?;
                    source.end = v.source.end;
                    value = Some(Box::new(v));
                }
            }

            return Ok(Ast { source, data: AstData::Break(ast::Break { value }) });
        }

        // continue
        if let TokenData::KwContinue = current.data {
            let source = current.source;
            return Ok(Ast { source, data: AstData::Continue });
        }

        // return
        if let TokenData::KwReturn = current.data {
            let mut end = current.source.end;

            let mut value = None;
            if let Some(at) = self.peek(0) {
                if at.is_expr_start()  {
                    let v = self.parse_expr(0)?;
                    end = v.source.end;
                    value = Some(Box::new(v));
                }
            }

            let data = AstData::Return(ast::Return { value });
            return Ok(Ast { source: SourceRange { begin, end }, data });
        }

        // functions
        if let TokenData::KwFn = current.data {
            let at   = self.peek_or_eof(0)?;
            let next = self.peek_or_eof(1)?;

            // fn name? ( params ) ':'? block end
            if at.is_ident() && next.data == TokenData::LParen
            || at.data == TokenData::LParen {
                let name =
                    if let TokenData::Ident(name) = at.data {
                        self.next().unwrap();
                        Some(name)
                    } else { None };
                self.expect(TokenData::LParen).unwrap();

                let params = self.parse_fn_params()?.0;
                self.expect(TokenData::RParen)?;
                self.expect(TokenData::Colon)?;

                let body = self.parse_block()?.stmts;
                let end = self.expect(TokenData::KwEnd)?.end;

                let data = AstData::Fn(Box::new(
                    ast::Fn { name, params, body }));
                return Ok(Ast { source: SourceRange { begin, end }, data });
            }
            // fn params => expr
            else {
                let params = self.parse_fn_params()?.0;
                self.expect(TokenData::FatArrow)?;

                let body = self.parse_expr(0)?;
                let end = body.source.end;

                let data = AstData::Fn(Box::new(
                    ast::Fn { name: None, params, body: vec![body] }));
                return Ok(Ast { source: SourceRange { begin, end }, data });
            }
        }

        // list.
        if let TokenData::LBracket = current.data {
            let values = self.parse_comma_exprs(TokenData::RBracket)?.0;
            let end = self.expect(TokenData::RBracket)?.end;

            let data = AstData::List(Box::new(ast::List { values }));
            return Ok(Ast { source: SourceRange { begin, end }, data });
        }

        // table.
        if let TokenData::LCurly = current.data {
            let values = self.parse_kv_exprs(TokenData::RCurly)?.0;
            let end = self.expect(TokenData::RCurly)?.end;

            let data = AstData::Table(Box::new(ast::Table { values }));
            return Ok(Ast { source: SourceRange { begin, end }, data });
        }

        // prefix operators.
        if let Some(op1) = self.peek_op1() {
            if ast::PREC_PREFIX < prec {
                unimplemented!()
            }

            let value = self.parse_expr(ast::PREC_PREFIX)?;

            let end = value.source.end;
            let data = AstData::Op1(Box::new(ast::Op1 { kind: op1, child: value }));
            return Ok(Ast { source: SourceRange { begin, end }, data });
        }


        // env.
        if current.data == TokenData::KwEnv {
            return Ok(Ast {
                source: current.source,
                data:   AstData::Env,
            });
        }


        Err(ParseError::at(&current, ParseErrorData::ExpectedExpression))
    }

    pub fn parse_expr(&mut self, prec: u32) -> ParseResult<Ast<'i>> {
        let mut result = self.parse_leading_expr(prec)?;

        loop {
            // binary operator.
            if let Some(op2) = self.peek_op2() {
                if op2.lprec() >= prec {
                    self.next().unwrap();

                    let other = self.parse_expr(op2.rprec())?;
                    let begin = result.source.begin;
                    let end   = other.source.end;
                    result = Ast {
                        source: SourceRange { begin, end },
                        data: AstData::Op2(Box::new(ast::Op2 {
                            kind: op2,
                            children: [result, other]
                        })),
                    };
                    continue;
                }
            }

            // "postfix" operators.
            if ast::PREC_POSTFIX < prec {
                break;
            }

            let Some(current) = self.peek(0) else { break };

            // call.
            if current.data == TokenData::LParen {
                self.next().unwrap();

                let args = self.parse_comma_exprs(TokenData::RParen)?.0;

                let begin = result.source.begin;
                let end   = self.expect(TokenData::RParen)?.end;
                result = Ast {
                    source: SourceRange { begin, end },
                    data: AstData::Call(Box::new(ast::Call {
                        func: result,
                        args,
                    })),
                };
                continue;
            }

            // field.
            if current.data == TokenData::Dot {
                self.next().unwrap();

                let name = self.expect_ident()?;

                let begin = result.source.begin;
                let end   = name.source.end;
                result = Ast {
                    source: SourceRange { begin, end },
                    data: AstData::Field(Box::new(ast::Field {
                        base: result,
                        name: name.value,
                    })),
                };
                continue;
            }

            // opt-chain.
            if current.data == TokenData::OpQDot {
                self.next().unwrap();

                let name = self.expect_ident()?;

                let begin = result.source.begin;
                let end   = name.source.end;
                result = Ast {
                    source: SourceRange { begin, end },
                    data: AstData::OptChain(Box::new(ast::Field {
                        base: result,
                        name: name.value,
                    })),
                };
                continue;
            }

            // index.
            if current.data == TokenData::LBracket {
                self.next().unwrap();

                let index = self.parse_expr(0)?;

                let begin = result.source.begin;
                let end   = self.expect(TokenData::RBracket)?.end;
                result = Ast {
                    source: SourceRange { begin, end },
                    data: AstData::Index(Box::new(ast::Index {
                        base: result,
                        index,
                    })),
                };
                continue;
            }

            break;
        }

        return Ok(result);
    }

    // bool: ends with comma.
    pub fn parse_comma_exprs(&mut self, until: TokenData<'static>) -> ParseResult<(Vec<Ast<'i>>, bool)> {
        let mut result = vec![];

        let mut had_comma = true;
        while had_comma && !self.peek_if(0, until) {
            result.push(self.parse_expr(0)?);

            if !self.next_if(TokenData::Comma) {
                had_comma = false;
            }
        }

        Ok((result, had_comma))
    }

    // bool: ends with comma.
    pub fn parse_kv_exprs(&mut self, until: TokenData<'static>) -> ParseResult<(Vec<(Ident<'i>, Ast<'i>)>, bool)> {
        let mut result = vec![];

        let mut had_comma = true;
        while had_comma && !self.peek_if(0, until) {
            let key = self.expect_ident()?;

            if self.next_if(TokenData::Colon) {
                let value = self.parse_expr(0)?;
                result.push((key, value));
            }
            else {
                result.push((key, key.to_ast()));
            }

            if !self.next_if(TokenData::Comma) {
                had_comma = false;
            }
        }

        Ok((result, had_comma))
    }

    pub fn parse_block(&mut self) -> ParseResult<ast::Block<'i>> {
        let Some(begin) = self.peek(0) else {
            return Ok(ast::Block { stmts: vec![] });
        };

        let begin = begin.source.begin;
        let mut end = begin;

        let mut stmts = vec![];

        let mut terminated = true;
        loop {
            let Some(at) = self.peek(0).copied() else { break };
            if at.is_block_end() { break }

            if !terminated {
                return Err(ParseError::at_pos(end, ParseErrorData::Expected(TokenData::Semicolon)));
            }

            // empty stmt.
            if at.data == TokenData::Semicolon {
                self.next().unwrap();
                let source = at.source;
                end = source.end;
            }
            // local ::= (let | var) ident (= expr)? (;)?
            else if at.data == TokenData::KwLet
            ||      at.data == TokenData::KwVar {
                let kind = match at.data {
                    TokenData::KwLet => ast::LocalKind::Let,
                    TokenData::KwVar => ast::LocalKind::Var,
                    _ => unreachable!()
                };
                self.next().unwrap();

                let name = self.expect_ident()?;

                let mut end = name.source.end;

                let mut value = None;
                if self.next_if(TokenData::OpEq) {
                    let v = self.parse_expr(0)?;
                    end = v.source.end;
                    value = Some(v);
                }

                stmts.push(Ast {
                    source: SourceRange { begin, end },
                    data: AstData::Local(Box::new(ast::Local {
                        name: name.value, value, kind,
                    })),
                });
            }
            // expr stmt
            else {
                let expr = self.parse_expr(0)?;
                terminated = self.next_if(TokenData::Semicolon);

                end = expr.source.end;
                stmts.push(expr);
            }
        }

        // @todo-dbg-info
        let _ = end;

        Ok(ast::Block { stmts })
    }

    // consumes `do` & colon.
    pub fn parse_if_block(&mut self) -> ParseResult<ast::IfBlock<'i>> {
        let is_do = self.next_if(TokenData::KwDo);
        self.expect(TokenData::Colon)?;

        let block = self.parse_block()?;
        Ok(ast::IfBlock { stmts: block.stmts, is_do })
    }

    pub fn parse_if(&mut self) -> ParseResult<(SourcePos, ast::If<'i>)> {
        let condition = self.parse_expr(0)?;

        let on_true = self.parse_if_block()?;

        let (end, on_false) = {
            let at = self.next()?;

            if at.data == TokenData::KwElif {
                let begin = at.source.begin;
                let body = self.parse_if_as_ast(begin)?;
                (body.source.end, Some(ast::IfBlock { stmts: vec![body], is_do: false }))
            }
            else if at.data == TokenData::KwElse {
                let body = self.parse_if_block()?;
                let end = self.expect(TokenData::KwEnd)?.end;
                (end, Some(body))
            }
            else if at.data == TokenData::KwEnd {
                let end = at.source.end;
                (end, None)
            }
            else {
                return Err(ParseError::at(&at, ParseErrorData::Expected(TokenData::KwEnd)));
            }
        };

        Ok((end, ast::If { condition, on_true, on_false }))
    }

    pub fn parse_if_as_ast(&mut self, begin: SourcePos) -> ParseResult<Ast<'i>> {
        let (end, data) = self.parse_if()?;
        let data = AstData::If(Box::new(data));
        Ok(Ast { source: SourceRange { begin, end }, data })
    }

    // bool: ends with comma.
    pub fn parse_fn_params(&mut self) -> ParseResult<(Vec<ast::FnParam<'i>>, bool)> {
        let mut result = vec![];

        let mut had_comma = true;
        while had_comma {
            let Some(name) = self.next_if_ident() else { break };
            result.push(ast::FnParam { name });

            if !self.next_if(TokenData::Comma) {
                had_comma = false;
            }
        }

        Ok((result, had_comma))
    }


    pub fn parse_single(input: &'i [u8]) -> ParseResult<Ast<'i>> {
        let tokens = Tokenizer::tokenize(input, true)?;
        let mut p = Parser::new(&tokens);

        let result = p.parse_expr(0)?;

        if let Some(tok) = p.peek(0) {
            return Err(ParseError::at_pos(tok.source.begin, ParseErrorData::TrailingInput));
        }
        Ok(result)
    }

    pub fn parse_chunk(input: &'i [u8]) -> ParseResult<ast::Block<'i>> {
        let tokens = Tokenizer::tokenize(input, true)?;
        let mut p = Parser::new(&tokens);
        p.parse_block()
    }
}

