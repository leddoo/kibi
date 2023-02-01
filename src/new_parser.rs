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
    OpEqEq,
    OpNe,
    OpLe,
    OpLt,
    OpGe,
    OpGt,
    OpNot,
}

impl<'a> TokenData<'a> {
    pub fn semi_colon_after(&self) -> bool {
        use TokenData::*;
        match self {
            // anything that can mark the end
            // of an expression.
            Ident (_) | Number (_) | QuotedString(_) |
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
            OpEq | OpEqEq | OpNe |
            OpLe | OpLt | OpGe | OpGt |
            OpNot | KwNot |
            Eof | Error
            => false,
        }
    }

    pub fn semi_colon_before(&self) -> bool {
        use TokenData::*;
        match self {
            Ident (_) | Number (_) | QuotedString(_) |
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
            OpEq | OpEqEq | OpNe |
            OpLe | OpLt | OpGe | OpGt |
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
    pub fn is_semi_colon(&self) -> bool {
        if let TokenData::SemiColon = self { true } else { false }
    }


    #[inline(always)]
    pub fn is_block_end(&self) -> bool {
        use TokenData::*;
        match self {
            KwEnd | KwElse | KwElif | Eof => true,
            _ => false,
        }
    }
}


pub struct Tokenizer<'i> {
    input: &'i [u8],
    current: usize,

    line: u32,
    line_begin: usize,

    current_token: Token<'i>,
    next_token:    Token<'i>,
}

impl<'i> Tokenizer<'i> {
    pub fn new(input: &'i [u8]) -> Self {
        let mut toker = Tokenizer {
            input, current: 0,
            line: 1, line_begin: 0,
            current_token: Default::default(),
            next_token:    Default::default(),
        };
        toker.current_token = toker._next_token();
        toker.next_token    = toker._next_token();
        toker
    }

    #[inline(always)]
    pub fn current(&self) -> &Token<'i> {
        &self.current_token
    }

    #[inline(always)]
    pub fn consume(&mut self) -> Token<'i> {
        let result = self.current_token;
        self.next();
        result
    }

    #[inline(always)]
    pub fn try_consume(&mut self) -> Option<Token<'i>> {
        if self.current_token.is_eof() {
            return None;
        }
        Some(self.consume())
    }

    fn next(&mut self) {
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

    fn _next_token(&mut self) -> Token<'i> {
        self.skip_whitespace();

        let Some(at) = self.peek_ch(0) else {
            return self.mk_token(self.pos(), TokenData::Eof);
        };

        let begin_offset = self.current;
        let begin_pos = self.pos();

        macro_rules! single_ch {
            ($td: expr) => {{
                self.consume_ch(1);
                return self.mk_token(begin_pos, $td);
            }};
        }

        macro_rules! single_or_double {
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

            '=' => single_or_double!(TokenData::OpEq,  '=', TokenData::OpEqEq),
            '!' => single_or_double!(TokenData::OpNot, '=', TokenData::OpNe),
            '<' => single_or_double!(TokenData::OpLt,  '=', TokenData::OpLe),
            '>' => single_or_double!(TokenData::OpGt,  '=', TokenData::OpGe),

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

                _ => TokenData::Ident(value),
            };
            return self.mk_token(begin_pos, data);
        }

        // number
        if at.is_ascii_digit() {
            self.consume_ch(1);
            self.consume_ch_while(|c| c.is_ascii_digit());

            let value = &self.input[begin_offset..self.current];
            let value = unsafe { core::str::from_utf8_unchecked(value) };
            return self.mk_token(begin_pos, TokenData::Number(value));
        }

        unimplemented!();
    }
}



#[derive(Debug)]
pub struct Ast<'a> {
    pub source: SourceRange,
    pub data: AstData<'a>,
}

#[derive(Debug)]
pub enum AstData<'a> {
    Empty,
    Number      (&'a str),
    Ident       (&'a str),
    Block       (Box<ast::Block<'a>>),
    Tuple       (Box<ast::Tuple<'a>>),
    Local       (Box<ast::Local<'a>>),
    Op1         (Box<ast::Op1<'a>>),
    Op2         (Box<ast::Op2<'a>>),
    Field       (Box<ast::Field<'a>>),
    Index       (Box<ast::Index<'a>>),
    Call        (Box<ast::Call<'a>>),
    If          (Box<ast::If<'a>>),
    While       (Box<ast::While<'a>>),
    Break       (ast::Break<'a>),
    Continue,
    Return      (ast::Return<'a>),
    Fn          (Box<ast::Fn<'a>>),
}

pub mod ast {
    use super::*;

    #[derive(Debug)]
    pub struct Block<'a> {
        pub children: Vec<Ast<'a>>,
        pub last_is_expr: bool,
    }

    #[derive(Debug)]
    pub struct Tuple<'a> {
        pub children: Vec<Ast<'a>>,
    }


    #[derive(Debug)]
    pub struct Local<'a> {
        pub name:  &'a str,
        pub value: Option<Ast<'a>>,
        pub kind:  LocalKind,
    }

    #[derive(Debug)]
    pub enum LocalKind {
        Let,
        Var,
    }


    #[derive(Debug)]
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

    #[derive(Debug)]
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
                Assign          => 101,
                AddAssign       => 101,
                SubAssign       => 101,
                MulAssign       => 101,
                DivAssign       => 101,
                IntDivAssign    => 101,
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
    }

    pub const PREC_POSTFIX: u32 = 1000;


    #[derive(Debug)]
    pub struct Field<'a> {
        pub base: Ast<'a>,
        pub name: &'a str,
    }

    #[derive(Debug)]
    pub struct Index<'a> {
        pub base:  Ast<'a>,
        pub index: Ast<'a>,
    }

    #[derive(Debug)]
    pub struct Call<'a> {
        pub func: Ast<'a>,
        pub args: Vec<Ast<'a>>,
    }


    #[derive(Debug)]
    pub struct If<'a> {
        pub condition: Ast<'a>,
        pub on_true:   Ast<'a>,
        pub on_false:  Option<Ast<'a>>,
    }

    #[derive(Debug)]
    pub struct While<'a> {
        pub condition: Ast<'a>,
        pub body:      Block<'a>,
    }


    #[derive(Debug)]
    pub struct Break<'a> {
        pub value: Option<Box<Ast<'a>>>,
    }

    #[derive(Debug)]
    pub struct Return<'a> {
        pub value: Option<Box<Ast<'a>>>,
    }


    #[derive(Debug)]
    pub struct Fn<'a> {
        pub params: Vec<FnParam<'a>>,
        pub body:   Block<'a>,
    }

    #[derive(Debug)]
    pub struct FnParam<'a> {
        pub name: &'a str,
    }
}


#[derive(Debug)]
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

    pub fn expect_ident(&mut self) -> ParseResult<(SourceRange, &'i str)> {
        let tok = self.toker.consume();
        if let TokenData::Ident(ident) = tok.data {
            return Ok((tok.source, ident));
        }
        Err(ParseError::Error)
    }

    pub fn expect(&mut self, kind: TokenData) -> ParseResult<SourceRange> {
        let tok = self.toker.consume();
        if tok.data == kind {
            return Ok(tok.source);
        }
        Err(ParseError::Error)
    }

    pub fn peek_op2(&mut self) -> Option<ast::Op2Kind> {
        use TokenData::*;
        use ast::Op2Kind::*;
        Some(match self.toker.current().data {
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
            _ => return None
        })
    }


    pub fn parse_leading_expr(&mut self, _prec: u32) -> ParseResult<(Ast<'i>, bool)> {
        let current = self.toker.current();

        if let TokenData::Ident(ident) = current.data {
            let source = current.source;
            self.toker.consume();

            return Ok((Ast { source, data: AstData::Ident(ident) }, false));
        }

        if let TokenData::Number(value) = current.data {
            let source = current.source;
            self.toker.consume();

            return Ok((Ast { source, data: AstData::Number(value) }, false));
        }

        if let TokenData::LParen = current.data {
            self.toker.consume();

            let result = self.parse_expr(0)?.0;

            self.expect(TokenData::RParen)?;
            return Ok((result, false));
        }

        unimplemented!()
    }

    pub fn parse_expr(&mut self, prec: u32) -> ParseResult<(Ast<'i>, bool)> {
        let mut result = self.parse_leading_expr(prec)?.0;

        loop {
            // binary operator.
            if let Some(op2) = self.peek_op2() {
                if op2.lprec() >= prec {
                    self.toker.consume();

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

            let current = self.toker.current();

            // call.
            if current.data == TokenData::LParen {
                self.toker.consume();
                let args = self.parse_comma_exprs(TokenData::RParen)?.0;

                let begin = result.source.begin;
                let end = self.expect(TokenData::RParen)?.end;

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
                unimplemented!()
            }

            // index.
            if current.data == TokenData::LBracket {
                unimplemented!()
            }

            break;
        }

        // @todo-complete: h2 terminated?
        return Ok((result, false));
    }

    // bool: last expr had comma.
    pub fn parse_comma_exprs(&mut self, until: TokenData) -> ParseResult<(Vec<Ast<'i>>, bool)> {
        let mut result = vec![];

        let mut had_comma = true;
        while had_comma && self.toker.current().data != until {
            result.push(self.parse_expr(0)?.0);
            
            if self.toker.current().data == TokenData::Comma {
                self.toker.consume();
            }
            else {
                had_comma = false;
            }
        }

        Ok((result, had_comma))
    }

    pub fn parse_stmt(&mut self) -> ParseResult<(Ast<'i>, bool)> {
        // local | expr_stmt

        let current = self.toker.current();
        let begin = current.source.begin;

        // local ::= (let | var) ident (= expr)? ;
        if current.data == TokenData::KwLet
        || current.data == TokenData::KwVar {
            let kind = match current.data {
                TokenData::KwLet => ast::LocalKind::Let,
                TokenData::KwVar => ast::LocalKind::Var,
                _ => unreachable!()
            };
            self.toker.consume();

            let name = self.expect_ident()?.1;

            let mut value = None;
            if self.toker.current().data == TokenData::OpEq {
                self.toker.consume();

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

        // expr_stmt
        let (expr, mut terminated) = self.parse_expr(0)?;
        if self.toker.current().is_semi_colon() {
            self.toker.consume();
            terminated = true;
        }
        Ok((expr, terminated))
    }

    pub fn parse_block(&mut self) -> ParseResult<(SourceRange, ast::Block<'i>)> {
        let mut result = vec![];

        let begin = self.toker.current().source.begin;
        let mut end = begin;

        let mut last_is_expr = false;
        while !self.toker.current().is_block_end() {
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
}


