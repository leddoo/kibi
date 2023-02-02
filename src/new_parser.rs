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
    pub source: SourceRange,
    pub data: TokenData<'a>,
}

impl<'a> Token<'a> {
    #[inline(always)]
    pub fn new(begin: SourcePos, end: SourcePos, data: TokenData<'a>) -> Self {
        Self { source: SourceRange { begin, end }, data }
    }
}

impl<'a> Default for Token<'a> {
    fn default() -> Self {
        let zero = SourcePos { line: 0, column: 0 };
        let source = SourceRange { begin: zero, end: zero };
        Token { source, data: TokenData::Error }
    }
}

impl<'a> core::ops::Deref for Token<'a> {
    type Target = TokenData<'a>;
    #[inline(always)] fn deref(&self) -> &Self::Target { &self.data }
}



#[derive(Clone, Copy, Debug, PartialEq)]
pub enum TokenData<'a> {
    Eof,
    Error,
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
    SemiColon,
    KwEnd,
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
    KwFn,
    KwAnd,
    KwOr,
    KwNot,
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
    FatArrow,
    OpEqEq,
    OpNe,
    OpLe,
    OpLt,
    OpGe,
    OpGt,
    OpNot,
    OpQ,
    QDot,
    OpQQ,
    OpQQEq,
}

impl<'a> TokenData<'a> {
    pub fn semi_colon_after(&self) -> bool {
        use TokenData::*;
        match self {
            // anything that can mark the end
            // of an expression.
            Ident (_) | Number (_) | Bool(_) | Nil | QuotedString(_) |
            RParen | RBracket | RCurly |
            KwBreak | KwContinue | KwReturn |
            KwEnd
            => true,

            LParen | LBracket | LCurly |
            Dot | Comma | Colon | SemiColon |
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
            OpEq | FatArrow |
            OpEqEq | OpNe | OpLe | OpLt | OpGe | OpGt |
            OpQ | QDot | OpQQ | OpQQEq |
            OpNot | KwNot |
            Eof | Error
            => false,
        }
    }

    pub fn semi_colon_before(&self) -> bool {
        use TokenData::*;
        match self {
            Ident (_) | Number (_) | Bool(_) | Nil | QuotedString(_) |
            LParen | LBracket | LCurly |
            KwLet | KwVar |
            KwDo | KwIf | KwWhile | KwFor |
            KwBreak | KwContinue | KwReturn |
            KwFn |
            OpNot | KwNot |
            Eof
            => true,

            // unless the next token indicates
            // that the expression may continue.
            RParen |
            RBracket |
            RCurly |
            Dot | Comma | Colon | SemiColon |
            KwEnd |
            KwElif | KwElse |
            KwIn |
            KwAnd | KwOr |
            OpPlus | OpPlusEq |
            OpMinus | OpMinusEq |
            OpStar | OpStarEq |
            OpSlash | OpSlashEq |
            OpSlashSlash | OpSlashSlashEq |
            OpEq | FatArrow |
            OpEqEq | OpNe | OpLe | OpLt | OpGe | OpGt |
            OpQ | QDot | OpQQ | OpQQEq |
            Error
            => false,
        }
    }

    #[inline(always)]
    pub fn is_eof(&self) -> bool {
        if let TokenData::Eof = self { true } else { false }
    }

    #[inline(always)]
    pub fn is_error(&self) -> bool {
        if let TokenData::Error = self { true } else { false }
    }

    #[inline(always)]
    pub fn is_ident(&self) -> bool {
        if let TokenData::Ident(_) = self { true } else { false }
    }


    #[inline(always)]
    pub fn is_block_end(&self) -> bool {
        use TokenData::*;
        match self {
            KwEnd | KwElse | KwElif | Eof => true,
            _ => false,
        }
    }

    #[inline(always)]
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
            OpPlus | OpMinus | OpStar
            => true,

            Eof | Error |
            RParen | RBracket | RCurly |
            Dot | Comma | Colon | SemiColon |
            KwEnd |
            KwElif | KwElse |
            KwIn |
            KwAnd | KwOr |
            OpPlusEq | OpMinusEq | OpStarEq |
            OpSlash | OpSlashEq | OpSlashSlash | OpSlashSlashEq |
            OpEq | FatArrow |
            OpEqEq | OpNe | OpLe | OpLt | OpGe | OpGt |
            OpQ | QDot | OpQQ | OpQQEq
            => false
        }
    }
}


pub struct Tokenizer<'i> {
    input: &'i [u8],
    cursor: usize,

    line: u32,
    line_begin: usize,

    current_token: Token<'i>,
    next_token:    Token<'i>,
}

impl<'i> Tokenizer<'i> {
    pub fn new(input: &'i [u8]) -> Self {
        let mut toker = Tokenizer {
            input, cursor: 0,
            line: 1, line_begin: 0,
            current_token: Default::default(),
            next_token:    Default::default(),
        };
        toker.current_token = toker._next_token();
        toker.next_token    = toker._next_token();
        toker
    }

    #[inline(always)]
    pub fn peek(&self) -> &Token<'i> {
        &self.current_token
    }

    #[inline(always)]
    pub fn peek_next(&self) -> &Token<'i> {
        &self.next_token
    }

    #[inline(always)]
    pub fn next(&mut self) -> Token<'i> {
        let result = self.current_token;
        self._advance();
        result
    }

    #[inline(always)]
    pub fn next_if(&mut self, kind: TokenData) -> bool {
        if self.current_token.data == kind {
            self.next();
            return true
        }
        false
    }

    fn _advance(&mut self) {
        if self.current_token.is_eof() { return }

        let current = &self.current_token;
        let next    = &self.next_token;

        // insert semi-colon.
        if current.source.end.line < next.source.begin.line
        && current.semi_colon_after()
        && next.semi_colon_before() {
            // @auto-semi-colon-collapsed-range
            let pos = current.source.end;
            self.current_token = Token::new(pos, pos, TokenData::SemiColon);
        }
        else {
            self.current_token = self.next_token;
            self.next_token    = self._next_token();
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
            else if at == '-' as u8 && self.peek_ch(1) == Some('-' as u8) {
                self.consume_ch_while(|c| c != '\n');
            }
            else { break }
        }
    }

    fn _next_token(&mut self) -> Token<'i> {
        self.skip_whitespace();

        let Some(at) = self.peek_ch(0) else {
            return self.mk_token(self.pos(), TokenData::Eof);
        };

        let begin_offset = self.cursor;
        let begin_pos = self.pos();

        macro_rules! tok_1 {
            ($td: expr) => {{
                self.consume_ch(1);
                return self.mk_token(begin_pos, $td);
            }};
        }

        macro_rules! tok_2 {
            ($td: expr, $cont: expr, $td_cont: expr) => {{
                self.consume_ch(1);

                if self.peek_ch_zero(0) == $cont as u8 {
                    self.consume_ch(1);
                    return self.mk_token(begin_pos, $td_cont);
                }
                else {
                    return self.mk_token(begin_pos, $td);
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
            ':' => tok_1!(TokenData::Colon),
            ';' => tok_1!(TokenData::SemiColon),
            '?' => {
                self.consume_ch(1);

                if self.peek_ch_zero(0) == '?' as u8 {
                    self.consume_ch(1);

                    if self.peek_ch_zero(0) == '=' as u8 {
                        self.consume_ch(1);
                        return self.mk_token(begin_pos, TokenData::OpQQEq);
                    }
                    else {
                        return self.mk_token(begin_pos, TokenData::OpQQ);
                    }
                }
                else if self.peek_ch_zero(0) == '.' as u8 {
                    self.consume_ch(1);
                    return self.mk_token(begin_pos, TokenData::QDot);
                }
                else {
                    return self.mk_token(begin_pos, TokenData::OpQ);
                }
            }

            '+' => tok_2!(TokenData::OpPlus,  '=', TokenData::OpPlusEq),
            '-' => tok_2!(TokenData::OpMinus, '=', TokenData::OpMinusEq),
            '*' => tok_2!(TokenData::OpStar,  '=', TokenData::OpStarEq),

            '/' => {
                self.consume_ch(1);

                if self.peek_ch_zero(0) == '=' as u8 {
                    self.consume_ch(1);
                    return self.mk_token(begin_pos, TokenData::OpSlashEq);
                }
                else if self.peek_ch_zero(0) == '/' as u8 {
                    self.consume_ch(1);

                    if self.peek_ch_zero(0) == '=' as u8 {
                        self.consume_ch(1);
                        return self.mk_token(begin_pos, TokenData::OpSlashSlashEq);
                    }
                    else {
                        return self.mk_token(begin_pos, TokenData::OpSlashSlash);
                    }
                }
                else {
                    return self.mk_token(begin_pos, TokenData::OpSlash);
                }
            }

            '=' => {
                self.consume_ch(1);

                if self.peek_ch_zero(0) == '>' as u8 {
                    self.consume_ch(1);
                    return self.mk_token(begin_pos, TokenData::FatArrow);
                }
                else if self.peek_ch_zero(0) == '=' as u8 {
                    self.consume_ch(1);
                    return self.mk_token(begin_pos, TokenData::OpEqEq);
                }
                else {
                    return self.mk_token(begin_pos, TokenData::OpEq);
                }
            }

            '!' => tok_2!(TokenData::OpNot, '=', TokenData::OpNe),
            '<' => tok_2!(TokenData::OpLt,  '=', TokenData::OpLe),
            '>' => tok_2!(TokenData::OpGt,  '=', TokenData::OpGe),

            '"' => {
                self.consume_ch(1);

                loop {
                    let Some(at) = self.peek_ch(0) else {
                        unimplemented!()
                    };

                    self.consume_ch(1);

                    if at == '"' as u8 {
                        let value = &self.input[begin_offset+1 .. self.cursor-1];

                        let Ok(value) = core::str::from_utf8(value) else {
                            unimplemented!()
                        };

                        return self.mk_token(begin_pos, TokenData::QuotedString(value));
                    }

                    if at == '\\' as u8 {
                        unimplemented!();
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

                _ => TokenData::Ident(value),
            };
            return self.mk_token(begin_pos, data);
        }

        // number
        if at.is_ascii_digit() {
            self.consume_ch(1);
            self.consume_ch_while(|c| c.is_ascii_digit());

            let value = &self.input[begin_offset..self.cursor];
            let value = unsafe { core::str::from_utf8_unchecked(value) };
            return self.mk_token(begin_pos, TokenData::Number(value));
        }

        unimplemented!();
    }
}



#[derive(Clone, Debug)]
pub struct Ast<'a> {
    pub source: SourceRange,
    pub data:   AstData<'a>,
}

#[derive(Clone, Debug)]
pub enum AstData<'a> {
    Empty,
    Nil,
    Bool        (bool),
    Number      (&'a str),
    QuotedString(&'a str),
    Ident       (&'a str),
    Tuple       (Box<ast::Tuple<'a>>),
    List        (Box<ast::List<'a>>),
    Table       (Box<ast::Table<'a>>),
    Block       (Box<ast::Block<'a>>),
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
    Break,
    Continue,
    Return      (ast::Return<'a>),
    Fn          (Box<ast::Fn<'a>>),
}

pub mod ast {
    use super::*;

    #[derive(Clone, Debug)]
    pub struct Block<'a> {
        pub children: Vec<Ast<'a>>,
        pub last_is_expr: bool,
    }

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
    pub enum Op1Kind {
        Not,
        BitNot,
        Neg,
        Plus,
    }

    #[derive(Clone, Debug)]
    pub struct Op2<'a> {
        pub kind:     Op2Kind,
        pub children: [Ast<'a>; 2],
    }

    #[derive(Clone, Copy, Debug, PartialEq)]
    pub enum Op2Kind {
        And,
        Or,
        Assign,
        Add,
        AddAssign,
        Sub,
        SubAssign,
        Mul,
        MulAssign,
        Div,
        DivAssign,
        IntDiv,
        IntDivAssign,
        CmpEq,
        CmpNe,
        CmpLe,
        CmpLt,
        CmpGe,
        CmpGt,
        OrElse,
        OrElseAssign,
    }

    impl Op2Kind {
        #[inline(always)]
        pub fn lprec(self) -> u32 {
            use Op2Kind::*;
            match self {
                Assign          => 100,
                AddAssign       => 100,
                SubAssign       => 100,
                MulAssign       => 100,
                DivAssign       => 100,
                IntDivAssign    => 100,
                OrElseAssign    => 100,
                OrElse          => 150,
                Or              => 200,
                And             => 300,
                CmpEq           => 400,
                CmpNe           => 400,
                CmpLe           => 400,
                CmpLt           => 400,
                CmpGe           => 400,
                CmpGt           => 400,
                Add             => 600,
                Sub             => 600,
                Mul             => 800,
                Div             => 800,
                IntDiv          => 800,
            }
        }

        #[inline(always)]
        pub fn rprec(self) -> u32 {
            use Op2Kind::*;
            match self {
                Assign          => 100,
                AddAssign       => 100,
                SubAssign       => 100,
                MulAssign       => 100,
                DivAssign       => 100,
                IntDivAssign    => 100,
                OrElseAssign    => 100,
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
    pub struct If<'a> {
        pub condition: Ast<'a>,
        pub on_true:   Ast<'a>,
        pub on_false:  Option<Ast<'a>>,
    }

    #[derive(Clone, Debug)]
    pub struct While<'a> {
        pub condition: Ast<'a>,
        pub body:      Block<'a>,
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
        pub body:   Ast<'a>,
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


#[derive(Clone, Copy, Debug)]
pub enum ParseError {
    Error,
}

pub type ParseResult<T> = Result<T, ParseError>;


pub struct Parser<'i> {
    toker: Tokenizer<'i>,
}

impl<'i> Parser<'i> {
    pub fn new(input: &'i [u8]) -> Self {
        Self {
            toker: Tokenizer::new(input)
        }
    }

    pub fn expect_ident(&mut self) -> ParseResult<Ident<'i>> {
        let tok = self.toker.next();
        if let TokenData::Ident(value) = tok.data {
            return Ok(Ident { source: tok.source, value });
        }
        Err(ParseError::Error)
    }

    pub fn expect(&mut self, kind: TokenData) -> ParseResult<SourceRange> {
        let tok = self.toker.next();
        if tok.data == kind {
            return Ok(tok.source);
        }
        Err(ParseError::Error)
    }

    pub fn peek_op1(&mut self) -> Option<ast::Op1Kind> {
        use TokenData::*;
        use ast::Op1Kind::*;
        Some(match self.toker.peek().data {
            KwNot   => Not,
            OpNot   => BitNot,
            OpMinus => Neg,
            OpPlus  => Plus,
            _ => return None,
        })
    }

    pub fn peek_op2(&mut self) -> Option<ast::Op2Kind> {
        use TokenData::*;
        use ast::Op2Kind::*;
        Some(match self.toker.peek().data {
            KwAnd           => And,
            KwOr            => Or,
            OpPlus          => Add,
            OpPlusEq        => AddAssign,
            OpMinus         => Sub,
            OpMinusEq       => SubAssign,
            OpStar          => Mul,
            OpStarEq        => MulAssign,
            OpSlash         => Div,
            OpSlashEq       => DivAssign,
            OpSlashSlash    => IntDiv,
            OpSlashSlashEq  => IntDivAssign,
            OpEq            => Assign,
            OpEqEq          => CmpEq,
            OpNe            => CmpNe,
            OpLe            => CmpLe,
            OpLt            => CmpLt,
            OpGe            => CmpGe,
            OpGt            => CmpGt,
            OpQQ            => OrElse,
            OpQQEq          => OrElseAssign,
            _ => return None
        })
    }


    pub fn parse_leading_expr(&mut self, prec: u32) -> ParseResult<(Ast<'i>, bool)> {
        let current = self.toker.peek();

        // ident.
        if let TokenData::Ident(ident) = current.data {
            let source = self.toker.next().source;
            return Ok((Ast { source, data: AstData::Ident(ident) }, false));
        }

        // number.
        if let TokenData::Number(value) = current.data {
            let source = self.toker.next().source;
            return Ok((Ast { source, data: AstData::Number(value) }, false));
        }

        // bool.
        if let TokenData::Bool(value) = current.data {
            let source = self.toker.next().source;
            return Ok((Ast { source, data: AstData::Bool(value) }, false));
        }

        // nil.
        if let TokenData::Nil = current.data {
            let source = self.toker.next().source;
            return Ok((Ast { source, data: AstData::Nil }, false));
        }

        // string.
        if let TokenData::QuotedString(value) = current.data {
            let source = self.toker.next().source;
            return Ok((Ast { source, data: AstData::QuotedString(value) }, false));
        }

        let begin = current.source.begin;

        // tuples & sub-expr.
        if let TokenData::LParen = current.data {
            self.toker.next();

            let (values, had_comma) = self.parse_comma_exprs(TokenData::RParen)?;
            let data =
                if values.len() == 1 && !had_comma {
                    AstData::SubExpr(Box::new(values.into_iter().next().unwrap()))
                }
                else {
                    AstData::Tuple(Box::new(ast::Tuple { values }))
                };

            let end = self.expect(TokenData::RParen)?.end;
            return Ok((Ast { source: SourceRange { begin, end }, data }, false));
        }

        // if
        if let TokenData::KwIf = current.data {
            self.toker.next();
            return Ok((self.parse_if_as_ast(begin)?, true));
        }

        // while
        if let TokenData::KwWhile = current.data {
            self.toker.next();

            let condition = self.parse_expr(0)?.0;
            self.expect(TokenData::Colon)?;

            let body = self.parse_block()?.1;

            let data = AstData::While(Box::new(ast::While { condition, body }));
            let end = self.expect(TokenData::KwEnd)?.end;
            return Ok((Ast { source: SourceRange { begin, end }, data }, false));
        }

        // do
        if let TokenData::KwDo = current.data {
            self.toker.next();

            let block = self.parse_block()?.1;
            let data = AstData::Block(Box::new(block));

            let end = self.expect(TokenData::KwEnd)?.end;
            return Ok((Ast { source: SourceRange { begin, end }, data }, true));
        }

        // break
        if let TokenData::KwBreak = current.data {
            let source = self.toker.next().source;
            return Ok((Ast { source, data: AstData::Break }, false));
        }

        // continue
        if let TokenData::KwContinue = current.data {
            let source = self.toker.next().source;
            return Ok((Ast { source, data: AstData::Continue }, false));
        }

        // return
        if let TokenData::KwReturn = current.data {
            let mut end = self.toker.next().source.end;

            let mut value = None;
            if self.toker.peek().is_expr_start() {
                let v = self.parse_expr(0)?.0;
                end = v.source.end;
                value = Some(Box::new(v));
            }

            let data = AstData::Return(ast::Return { value });
            return Ok((Ast { source: SourceRange { begin, end }, data }, false));
        }

        // functions
        if let TokenData::KwFn = current.data {
            self.toker.next();

            // fn name ( params ) ':'? block end
            if let (TokenData::Ident(name), TokenData::LParen)
                = (self.toker.peek().data, self.toker.peek_next().data)
            {
                self.toker.next();
                self.toker.next();

                let params = self.parse_fn_params()?.0;
                self.expect(TokenData::RParen)?;
                self.toker.next_if(TokenData::Colon);

                let body = self.parse_block_as_ast()?;
                let end = self.expect(TokenData::KwEnd)?.end;

                let data = AstData::Fn(Box::new(
                    ast::Fn { name: Some(name), params, body }));
                return Ok((Ast { source: SourceRange { begin, end }, data }, false));
            }
            // fn params => expr
            else {
                let params = self.parse_fn_params()?.0;
                self.expect(TokenData::FatArrow)?;

                let body = self.parse_expr(0)?.0;
                let end = body.source.end;

                let data = AstData::Fn(Box::new(
                    ast::Fn { name: None, params, body }));
                return Ok((Ast { source: SourceRange { begin, end }, data }, false));
            }
        }

        // list.
        if let TokenData::LBracket = current.data {
            self.toker.next();

            let values = self.parse_comma_exprs(TokenData::RBracket)?.0;
            let end = self.expect(TokenData::RBracket)?.end;

            let data = AstData::List(Box::new(ast::List { values }));
            return Ok((Ast { source: SourceRange { begin, end }, data }, false));
        }

        // table.
        if let TokenData::LCurly = current.data {
            self.toker.next();

            let values = self.parse_kv_exprs(TokenData::RCurly)?.0;
            let end = self.expect(TokenData::RCurly)?.end;

            let data = AstData::Table(Box::new(ast::Table { values }));
            return Ok((Ast { source: SourceRange { begin, end }, data }, false));
        }

        // prefix operators.
        if let Some(op1) = self.peek_op1() {
            if ast::PREC_PREFIX < prec {
                unimplemented!()
            }
            self.toker.next();

            let value = self.parse_expr(ast::PREC_PREFIX)?.0;

            let end = value.source.end;
            let data = AstData::Op1(Box::new(ast::Op1 { kind: op1, child: value }));
            return Ok((Ast { source: SourceRange { begin, end }, data }, false));
        }

        unimplemented!()
    }

    pub fn parse_expr(&mut self, prec: u32) -> ParseResult<(Ast<'i>, bool)> {
        let mut result = self.parse_leading_expr(prec)?.0;

        loop {
            // binary operator.
            if let Some(op2) = self.peek_op2() {
                if op2.lprec() >= prec {
                    self.toker.next();

                    let other = self.parse_expr(op2.rprec())?.0;
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

            let current = self.toker.peek();

            // call.
            if current.data == TokenData::LParen {
                self.toker.next();

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
                self.toker.next();

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
            if current.data == TokenData::QDot {
                self.toker.next();

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
                self.toker.next();

                let index = self.parse_expr(0)?.0;

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

        // @todo-complete: h2 terminated?
        return Ok((result, false));
    }

    pub fn parse_comma_exprs(&mut self, until: TokenData) -> ParseResult<(Vec<Ast<'i>>, bool)> {
        let mut result = vec![];

        let mut had_comma = true;
        while had_comma && self.toker.peek().data != until {
            result.push(self.parse_expr(0)?.0);

            if self.toker.peek().data == TokenData::Comma {
                self.toker.next();
            }
            else {
                had_comma = false;
            }
        }

        Ok((result, had_comma))
    }

    pub fn parse_kv_exprs(&mut self, until: TokenData) -> ParseResult<(Vec<(Ident<'i>, Ast<'i>)>, bool)> {
        let mut result = vec![];

        let mut had_comma = true;
        while had_comma && self.toker.peek().data != until {
            let key = self.expect_ident()?;

            if self.toker.next_if(TokenData::Colon) {
                let value = self.parse_expr(0)?.0;
                result.push((key, value));
            }
            else {
                result.push((key, key.to_ast()));
            }

            if self.toker.peek().data == TokenData::Comma {
                self.toker.next();
            }
            else {
                had_comma = false;
            }
        }

        Ok((result, had_comma))
    }

    pub fn parse_stmt(&mut self) -> ParseResult<(Ast<'i>, bool)> {
        // local | empty_stmt | expr_stmt

        let current = self.toker.peek();
        let begin = current.source.begin;

        // local ::= (let | var) ident (= expr)? ;
        if current.data == TokenData::KwLet
        || current.data == TokenData::KwVar {
            let kind = match current.data {
                TokenData::KwLet => ast::LocalKind::Let,
                TokenData::KwVar => ast::LocalKind::Var,
                _ => unreachable!()
            };
            self.toker.next();

            let name = self.expect_ident()?.value;

            let mut value = None;
            if self.toker.peek().data == TokenData::OpEq {
                self.toker.next();

                value = Some(self.parse_expr(0)?.0);
            }

            let end = self.expect(TokenData::SemiColon)?.end;

            return Ok((Ast {
                source: SourceRange { begin, end },
                data: AstData::Local(Box::new(ast::Local {
                    name, value, kind,
                })),
            }, true));
        }

        // empty
        if current.data == TokenData::SemiColon {
            let source = self.toker.next().source;
            return Ok((Ast { source, data: AstData::Empty }, true));
        }

        // expr_stmt
        let (expr, mut terminated) = self.parse_expr(0)?;
        if self.toker.peek().data == TokenData::SemiColon {
            self.toker.next();
            terminated = true;
        }
        Ok((expr, terminated))
    }

    pub fn parse_block(&mut self) -> ParseResult<(SourceRange, ast::Block<'i>)> {
        let mut result = vec![];

        let begin = self.toker.peek().source.begin;
        let mut end = begin;

        let mut last_is_expr = false;
        while !self.toker.peek().is_block_end() {
            let (stmt, terminated) = self.parse_stmt()?;
            if !terminated {
                if last_is_expr {
                    unimplemented!()
                }
                last_is_expr = true;
            }
            end = stmt.source.end;
            result.push(stmt);
        }

        let range = SourceRange { begin, end };
        Ok((range, ast::Block { children: result, last_is_expr }))
    }

    pub fn parse_block_as_ast(&mut self) -> ParseResult<Ast<'i>> {
        let (source, block) = self.parse_block()?;
        if block.last_is_expr && block.children.len() == 1 {
            Ok(block.children.into_iter().next().unwrap())
        }
        else {
            Ok(Ast { source, data: AstData::Block(Box::new(block)) })
        }
    }

    pub fn parse_if(&mut self) -> ParseResult<(SourcePos, ast::If<'i>)> {
        let condition = self.parse_expr(0)?.0;
        self.expect(TokenData::Colon)?;

        let on_true = self.parse_block_as_ast()?;

        let (end, on_false) = {
            let at = self.toker.peek();
            if at.data == TokenData::KwElif {
                let begin = self.toker.next().source.begin;
                let body = self.parse_if_as_ast(begin)?;
                (body.source.end, Some(body))
            }
            else if at.data == TokenData::KwElse {
                self.toker.next();
                self.toker.next_if(TokenData::Colon);

                let body = self.parse_block_as_ast()?;
                let end = self.expect(TokenData::KwEnd)?.end;
                (end, Some(body))
            }
            else if at.data == TokenData::KwEnd {
                let end = self.toker.next().source.end;
                (end, None)
            }
            else {
                unimplemented!()
            }
        };

        Ok((end, ast::If { condition, on_true, on_false }))
    }

    pub fn parse_if_as_ast(&mut self, begin: SourcePos) -> ParseResult<Ast<'i>> {
        let (end, data) = self.parse_if()?;
        let data = AstData::If(Box::new(data));
        Ok(Ast { source: SourceRange { begin, end }, data })
    }

    pub fn parse_fn_params(&mut self) -> ParseResult<(Vec<ast::FnParam<'i>>, bool)> {
        let mut result = vec![];

        let mut had_comma = true;
        while let TokenData::Ident(name) = self.toker.peek().data {
            if !had_comma { break }
            self.toker.next();

            result.push(ast::FnParam { name });

            if self.toker.peek().data == TokenData::Comma {
                self.toker.next();
            }
            else {
                had_comma = false;
            }
        }

        Ok((result, had_comma))
    }
}


