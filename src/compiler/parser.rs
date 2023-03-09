use derive_more::Deref;
use super::ast::*;


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
    Label (&'a str),
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
    FatArrow,
    ColonEq,
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
    OpAdd,
    OpAddAssign,
    OpMinus,
    OpMinusAssign,
    OpMul,
    OpMulAssign,
    OpDiv,
    OpDivAssign,
    OpFloorDiv,
    OpFloorDivAssign,
    OpRem,
    OpRemAssign,
    OpAssign,
    OpEq,
    OpNe,
    OpLe,
    OpLt,
    OpGe,
    OpGt,
    OpOptChain,
    OpOrElse,
    OpOrElseAssign,
}

impl<'a> TokenData<'a> {
    pub fn semicolon_after(&self) -> bool {
        use TokenData::*;
        match self {
            // anything that can mark the end
            // of an expression.
            Ident (_) | Number (_) | Bool(_) | Nil | QuotedString(_) |
            Label(_) |
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
            OpAdd | OpAddAssign |
            OpMinus | OpMinusAssign |
            OpMul | OpMulAssign |
            OpDiv | OpDivAssign |
            OpFloorDiv | OpFloorDivAssign |
            OpRem | OpRemAssign |
            FatArrow | ColonEq |
            OpAssign | OpEq | OpNe | OpLe | OpLt | OpGe | OpGt |
            OpOptChain | OpOrElse | OpOrElseAssign |
            KwNot
            => false,
        }
    }

    pub fn semicolon_before(&self) -> bool {
        use TokenData::*;
        match self {
            Ident (_) | Number (_) | Bool(_) | Nil | QuotedString(_) |
            Label(_) |
            LParen | LBracket | LCurly |
            KwLet | KwVar |
            KwDo | KwIf | KwElif | KwElse | KwWhile | KwFor |
            KwBreak | KwContinue | KwReturn |
            KwEnd |
            KwFn |
            KwEnv |
            KwNot
            => true,

            // unless the next token indicates
            // that the expression may continue.
            RParen |
            RBracket |
            RCurly |
            Dot | Comma | Colon | Semicolon |
            KwIn |
            KwAnd | KwOr |
            OpAdd | OpAddAssign |
            OpMinus | OpMinusAssign |
            OpMul | OpMulAssign |
            OpDiv | OpDivAssign |
            OpFloorDiv | OpFloorDivAssign |
            OpRem | OpRemAssign |
            FatArrow | ColonEq |
            OpAssign | OpEq | OpNe | OpLe | OpLt | OpGe | OpGt |
            OpOptChain | OpOrElse | OpOrElseAssign
            => false,
        }
    }

    #[inline(always)]
    pub fn is_ident(&self) -> bool {
        if let TokenData::Ident(_) = self { true } else { false }
    }

    #[inline(always)]
    pub fn is_label(&self) -> bool {
        if let TokenData::Label(_) = self { true } else { false }
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
            Label(_) |
            LParen | LBracket | LCurly |
            KwLet | KwVar |
            KwDo | KwIf | KwWhile | KwFor |
            KwBreak | KwContinue | KwReturn |
            KwFn |
            KwNot |
            KwEnv |
            OpMinus | OpMul
            => true,

            RParen | RBracket | RCurly |
            Dot | Comma | Colon | Semicolon |
            KwEnd |
            KwElif | KwElse |
            KwIn |
            KwAnd | KwOr |
            OpAdd | OpAddAssign | OpMinusAssign | OpMulAssign |
            OpDiv | OpDivAssign | OpFloorDiv | OpFloorDivAssign |
            OpRem | OpRemAssign |
            FatArrow | ColonEq |
            OpAssign | OpEq | OpNe | OpLe | OpLt | OpGe | OpGt |
            OpOptChain | OpOrElse | OpOrElseAssign
            => false
        }
    }


    pub fn try_op1(&self) -> Option<expr::Op1Kind> {
        use TokenData::*;
        use super::Op1::*;
        Some(match self {
            KwNot    => expr::Op1Kind(Not),
            OpMinus  => expr::Op1Kind(Negate),
            _ => return None,
        })
    }

    pub fn try_op2(&self) -> Option<expr::Op2Kind> {
        use TokenData::*;
        use super::Op2::*;
        Some(match self {
            OpAdd               => expr::Op2Kind::Op2(Add),
            OpAddAssign         => expr::Op2Kind::Op2Assign(Add),
            OpMinus             => expr::Op2Kind::Op2(Sub),
            OpMinusAssign       => expr::Op2Kind::Op2Assign(Sub),
            OpMul               => expr::Op2Kind::Op2(Mul),
            OpMulAssign         => expr::Op2Kind::Op2Assign(Mul),
            OpDiv               => expr::Op2Kind::Op2(Div),
            OpDivAssign         => expr::Op2Kind::Op2Assign(Div),
            OpFloorDiv          => expr::Op2Kind::Op2(FloorDiv),
            OpFloorDivAssign    => expr::Op2Kind::Op2Assign(FloorDiv),
            OpRem               => expr::Op2Kind::Op2(Rem),
            OpRemAssign         => expr::Op2Kind::Op2Assign(Rem),
            KwAnd               => expr::Op2Kind::Op2(And),
            KwOr                => expr::Op2Kind::Op2(Or),
            OpOrElse            => expr::Op2Kind::Op2(OrElse),
            OpOrElseAssign      => expr::Op2Kind::Op2Assign(OrElse),
            ColonEq             => expr::Op2Kind::Define,
            OpAssign            => expr::Op2Kind::Assign,
            OpEq                => expr::Op2Kind::Op2(CmpEq),
            OpNe                => expr::Op2Kind::Op2(CmpNe),
            OpLe                => expr::Op2Kind::Op2(CmpLe),
            OpLt                => expr::Op2Kind::Op2(CmpLt),
            OpGe                => expr::Op2Kind::Op2(CmpGe),
            OpGt                => expr::Op2Kind::Op2(CmpGt),
            _ => return None
        })
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
                //self.consume_ch(1);

                if self.peek_ch_zero(0) == '?' as u8 {
                    self.consume_ch(2);

                    if self.peek_ch_zero(0) == '=' as u8 {
                        self.consume_ch(1);
                        return Ok(Some(self.mk_token(begin_pos, TokenData::OpOrElseAssign)));
                    }
                    else {
                        return Ok(Some(self.mk_token(begin_pos, TokenData::OpOrElse)));
                    }
                }
                else if self.peek_ch_zero(0) == '.' as u8 {
                    self.consume_ch(2);
                    return Ok(Some(self.mk_token(begin_pos, TokenData::OpOptChain)));
                }
                else {
                    //return Ok(Some(self.mk_token(begin_pos, TokenData::OpTry)));
                }
            }

            '+' => tok_2!(TokenData::OpAdd,  '=', TokenData::OpAddAssign),
            '-' => tok_2!(TokenData::OpMinus, '=', TokenData::OpMinusAssign),
            '*' => tok_2!(TokenData::OpMul,  '=', TokenData::OpMulAssign),

            '/' => {
                self.consume_ch(1);

                if self.peek_ch_zero(0) == '=' as u8 {
                    self.consume_ch(1);
                    return Ok(Some(self.mk_token(begin_pos, TokenData::OpDivAssign)));
                }
                else if self.peek_ch_zero(0) == '/' as u8 {
                    self.consume_ch(1);

                    if self.peek_ch_zero(0) == '=' as u8 {
                        self.consume_ch(1);
                        return Ok(Some(self.mk_token(begin_pos, TokenData::OpFloorDivAssign)));
                    }
                    else {
                        return Ok(Some(self.mk_token(begin_pos, TokenData::OpFloorDiv)));
                    }
                }
                else {
                    return Ok(Some(self.mk_token(begin_pos, TokenData::OpDiv)));
                }
            }

            '%' => tok_2!(TokenData::OpRem,  '=', TokenData::OpRemAssign),

            '=' => {
                self.consume_ch(1);

                if self.peek_ch_zero(0) == '>' as u8 {
                    self.consume_ch(1);
                    return Ok(Some(self.mk_token(begin_pos, TokenData::FatArrow)));
                }
                else if self.peek_ch_zero(0) == '=' as u8 {
                    self.consume_ch(1);
                    return Ok(Some(self.mk_token(begin_pos, TokenData::OpEq)));
                }
                else {
                    return Ok(Some(self.mk_token(begin_pos, TokenData::OpAssign)));
                }
            }

            '!' => {
                if self.peek_ch_zero(1) == '=' as u8 {
                    self.consume_ch(2);
                    return Ok(Some(self.mk_token(begin_pos, TokenData::OpNe)));
                }
            }

            '<' => tok_2!(TokenData::OpLt, '=', TokenData::OpLe),
            '>' => tok_2!(TokenData::OpGt, '=', TokenData::OpGe),

            '\'' => {
                self.consume_ch(1);

                let start = self.cursor;

                loop {
                    if self.peek_ch(0).filter(|c| c.is_ascii_alphabetic()).is_none() {
                        if self.cursor == start {
                            return Err(ParseError::eof());
                        }
                        else { break }
                    };
                    self.consume_ch(1)
                }

                let value = &self.input[start..self.cursor];
                let value = unsafe { core::str::from_utf8_unchecked(value) };
                return Ok(Some(self.mk_token(begin_pos, TokenData::Label(value))));
            }

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


#[derive(Clone, Copy, Debug)]
pub struct Ident<'i> {
    source: SourceRange,
    value:  &'i str,
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

    fn next_if_label(&mut self, current_source: SourceRange) -> (SourceRange, Option<&'i str>) {
        if let Some(Token { data: TokenData::Label(name), source }) = self.tokens.get(self.cursor) {
            self.cursor += 1;
            let source = SourceRange { begin: current_source.begin, end: source.end };
            return (source, Some(name));
        }
        (current_source, None)
    }

    fn next_if_expr(&mut self, current_source: SourceRange, prec: u32) -> ParseResult<(SourceRange, Option<Box<Expr<'i>>>)> {
        if self.peek(0).filter(|at| at.is_expr_start()).is_some() {
            let expr = self.parse_expr(prec)?;
            let source = SourceRange { begin: current_source.begin, end: expr.source.end };
            return Ok((source, Some(Box::new(expr))));
        }
        Ok((current_source, None))
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


    // bool: terminated (needs no semi-colon).
    fn parse_leading_expr(&mut self, prec: u32) -> ParseResult<Expr<'i>> {
        let current = *self.next()?;

        // ident.
        if let TokenData::Ident(name) = current.data {
            let source = current.source;
            return Ok(Expr::new(source, ExprData::Ident(expr::Ident { name, info: None })));
        }

        // number.
        if let TokenData::Number(value) = current.data {
            let source = current.source;
            return Ok(Expr::new(source, ExprData::Number(value)));
        }

        // bool.
        if let TokenData::Bool(value) = current.data {
            let source = current.source;
            return Ok(Expr::new(source, ExprData::Bool(value)));
        }

        // nil.
        if let TokenData::Nil = current.data {
            let source = current.source;
            return Ok(Expr::new(source, ExprData::Nil));
        }

        // string.
        if let TokenData::QuotedString(value) = current.data {
            let source = current.source;
            return Ok(Expr::new(source, ExprData::QuotedString(value)));
        }

        let begin = current.source.begin;

        // tuples & sub-expr.
        if let TokenData::LParen = current.data {
            let (values, had_comma) = self.parse_comma_exprs(TokenData::RParen)?;
            let data =
                if values.len() == 1 && !had_comma {
                    ExprData::SubExpr(Box::new(values.into_iter().next().unwrap()))
                }
                else {
                    ExprData::Tuple(Box::new(expr::Tuple { values }))
                };

            let end = self.expect(TokenData::RParen)?.end;
            return Ok(Expr::new(SourceRange { begin, end }, data));
        }

        // if
        if let TokenData::KwIf = current.data {
            return self.parse_if_as_expr(begin);
        }

        // while
        if current.data == TokenData::KwWhile
        || current.data.is_label() && self.peek_if(0, TokenData::KwWhile) {
            let label = if let TokenData::Label(label) = current.data {
                self.next().unwrap();
                Some(label)
            }
            else { None };

            let condition = self.parse_expr(0)?;
            let body_begin = self.expect(TokenData::Colon)?.end;

            let body = self.parse_block(body_begin)?.1.stmts;

            let data = ExprData::While(Box::new(expr::While { label, condition, body }));
            let end = self.expect(TokenData::KwEnd)?.end;
            return Ok(Expr::new(SourceRange { begin, end }, data));
        }

        // do
        if current.data == TokenData::KwDo
        || current.data.is_label() && self.peek_if(0, TokenData::KwDo) {
            let label = if let TokenData::Label(label) = current.data {
                self.next().unwrap();
                Some(label)
            }
            else { None };

            let body_begin = self.expect(TokenData::Colon)?.end;

            let block = self.parse_block(body_begin)?.1;
            let data = ExprData::Do(Box::new(expr::Do { label, stmts: block.stmts }));

            let end = self.expect(TokenData::KwEnd)?.end;
            return Ok(Expr::new(SourceRange { begin, end }, data));
        }

        // break
        if let TokenData::KwBreak = current.data {
            let source = current.source;
            let (source, label) = self.next_if_label(source);
            let (source, value) = self.next_if_expr(source, 0)?;
            return Ok(Expr::new(source, ExprData::Break(Box::new(
                expr::Break { label, value, info: None }))));
        }

        // continue
        if let TokenData::KwContinue = current.data {
            let source = current.source;
            let (source, label) = self.next_if_label(source);
            return Ok(Expr::new(source, ExprData::Continue(Box::new(
                expr::Continue { label, info: None }))));
        }

        // return
        if let TokenData::KwReturn = current.data {
            let source = current.source;
            let (source, value) = self.next_if_expr(source, 0)?;
            let data = ExprData::Return(expr::Return { value });
            return Ok(Expr::new(source, data));
        }

        // list.
        if let TokenData::LBracket = current.data {
            let values = self.parse_comma_exprs(TokenData::RBracket)?.0;
            let end = self.expect(TokenData::RBracket)?.end;

            let data = ExprData::List(Box::new(expr::List { values }));
            return Ok(Expr::new(SourceRange { begin, end }, data));
        }

        /*
        // map.
        if let TokenData::LCurly = current.data {
            let values = self.parse_kv_exprs(TokenData::RCurly)?.0;
            let end = self.expect(TokenData::RCurly)?.end;

            let data = ExprData::Map(Box::new(data::Map { values }));
            return Ok(Expr { source: SourceRange { begin, end }, data });
        }
        */

        // prefix operators.
        if let Some(op1) = current.try_op1() {
            if expr::PREC_PREFIX < prec {
                unimplemented!()
            }

            let value = self.parse_expr(expr::PREC_PREFIX)?;

            let end = value.source.end;
            let data = ExprData::Op1(Box::new(expr::Op1 { kind: op1, child: value }));
            return Ok(Expr::new(SourceRange { begin, end }, data));
        }


        // env.
        if current.data == TokenData::KwEnv {
            return Ok(Expr::new(current.source, ExprData::Env));
        }


        Err(ParseError::at(&current, ParseErrorData::ExpectedExpression))
    }

    pub fn parse_expr(&mut self, prec: u32) -> ParseResult<Expr<'i>> {
        let mut result = self.parse_leading_expr(prec)?;

        loop {
            let Some(current) = self.peek(0) else { break };

            // binary operator.
            if let Some(op2) = current.try_op2() {
                if op2.lprec() >= prec {
                    self.next().unwrap();

                    let other = self.parse_expr(op2.rprec())?;
                    let begin = result.source.begin;
                    let end   = other.source.end;
                    result = Expr::new(
                        SourceRange { begin, end },
                        ExprData::Op2(Box::new(expr::Op2 {
                            kind: op2,
                            children: [result, other]
                        })));
                    continue;
                }
            }

            // "postfix" operators.
            if expr::PREC_POSTFIX < prec {
                break;
            }

            // call.
            if current.data == TokenData::LParen {
                self.next().unwrap();

                let args = self.parse_comma_exprs(TokenData::RParen)?.0;

                let begin = result.source.begin;
                let end   = self.expect(TokenData::RParen)?.end;
                result = Expr::new(
                    SourceRange { begin, end },
                    ExprData::Call(Box::new(expr::Call {
                        func: result,
                        args,
                    })));
                continue;
            }

            // field.
            if current.data == TokenData::Dot {
                self.next().unwrap();

                let name = self.expect_ident()?;

                let begin = result.source.begin;
                let end   = name.source.end;
                result = Expr::new(
                    SourceRange { begin, end },
                    ExprData::Field(Box::new(expr::Field {
                        base: result,
                        name: name.value,
                    })));
                continue;
            }

            /*
            // opt-chain.
            if current.data == TokenData::OpOptChain {
                self.next().unwrap();

                let name = self.expect_ident()?;

                let begin = result.source.begin;
                let end   = name.source.end;
                result = Expr::new(
                    SourceRange { begin, end },
                    ExprData::OptChain(Box::new(data::Field {
                        base: result,
                        name: name.value,
                    })));
                continue;
            }
            */

            // index.
            if current.data == TokenData::LBracket {
                self.next().unwrap();

                let index = self.parse_expr(0)?;

                let begin = result.source.begin;
                let end   = self.expect(TokenData::RBracket)?.end;
                result = Expr::new(
                    SourceRange { begin, end },
                    ExprData::Index(Box::new(expr::Index {
                        base: result,
                        index,
                    })));
                continue;
            }

            break;
        }

        return Ok(result);
    }

    // bool: ends with comma.
    pub fn parse_comma_exprs(&mut self, until: TokenData<'static>) -> ParseResult<(Vec<Expr<'i>>, bool)> {
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

    /*
    // bool: ends with comma.
    pub fn parse_kv_exprs(&mut self, until: TokenData<'static>) -> ParseResult<(Vec<(Ident<'i>, Expr<'i>)>, bool)> {
        let mut result = vec![];

        let mut had_comma = true;
        while had_comma && !self.peek_if(0, until) {
            let key = self.expect_ident()?;

            if self.next_if(TokenData::Colon) {
                let value = self.parse_expr(0)?;
                result.push((key, value));
            }
            else {
                result.push((key, key.to_Expr()));
            }

            if !self.next_if(TokenData::Comma) {
                had_comma = false;
            }
        }

        Ok((result, had_comma))
    }
    */

    pub fn parse_block(&mut self, begin: SourcePos) -> ParseResult<(SourceRange, expr::Block<'i>)> {
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
            // mod
            //else if at.data == TokenData::KwMod {
            //}
            // func
            else if at.data == TokenData::KwFn {
                self.next().unwrap();
                let (source, func) = self.parse_func(at.source.begin)?;
                stmts.push(Stmt::new(source, StmtData::Item(Item::new(source, ItemData::Func(func)))));
            }
            // local ::= (let | var) ident (= expr)? (;)?
            else if at.data == TokenData::KwLet
            ||      at.data == TokenData::KwVar {
                let kind = match at.data {
                    TokenData::KwLet => expr::LocalKind::Let,
                    TokenData::KwVar => expr::LocalKind::Var,
                    _ => unreachable!()
                };
                self.next().unwrap();

                let name = self.expect_ident()?;

                let mut end = name.source.end;

                let mut value = None;
                if self.next_if(TokenData::OpAssign) {
                    let v = self.parse_expr(0)?;
                    end = v.source.end;
                    value = Some(v);
                }

                stmts.push(Stmt::new(
                    SourceRange { begin, end },
                    StmtData::Local(expr::Local {
                        name: name.value, value, kind, info: None
                    }),
                ));
            }
            // expr stmt
            else {
                let expr = self.parse_expr(0)?;
                terminated = self.next_if(TokenData::Semicolon);

                end = expr.source.end;
                stmts.push(expr.to_stmt());
            }
        }

        Ok((SourceRange { begin, end }, expr::Block { stmts }))
    }

    // consumes `do` & colon.
    pub fn parse_if_block(&mut self) -> ParseResult<expr::IfBlock<'i>> {
        let is_do = self.next_if(TokenData::KwDo);
        let block_begin = self.expect(TokenData::Colon)?.end;

        let block = self.parse_block(block_begin)?.1;
        Ok(expr::IfBlock { stmts: block.stmts, is_do })
    }

    pub fn parse_if(&mut self) -> ParseResult<(SourcePos, expr::If<'i>)> {
        let condition = self.parse_expr(0)?;

        let on_true = self.parse_if_block()?;

        let (end, on_false) = {
            let at = self.next()?;

            if at.data == TokenData::KwElif {
                let begin = at.source.begin;
                let body = self.parse_if_as_expr(begin)?.to_stmt();
                (body.source.end, Some(expr::IfBlock { stmts: vec![body], is_do: false }))
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

        Ok((end, expr::If { condition, on_true, on_false }))
    }

    pub fn parse_if_as_expr(&mut self, begin: SourcePos) -> ParseResult<Expr<'i>> {
        let (end, data) = self.parse_if()?;
        let data = ExprData::If(Box::new(data));
        Ok(Expr::new(SourceRange { begin, end }, data))
    }

    // bool: ends with comma.
    pub fn parse_func_params(&mut self) -> ParseResult<(Vec<item::FuncParam<'i>>, bool)> {
        let mut result = vec![];

        let mut had_comma = true;
        while had_comma {
            let Some(name) = self.next_if_ident() else { break };
            result.push(item::FuncParam { name });

            if !self.next_if(TokenData::Comma) {
                had_comma = false;
            }
        }

        Ok((result, had_comma))
    }

    pub fn parse_func(&mut self, begin: SourcePos) -> ParseResult<(SourceRange, item::Func<'i>)> {
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

            let params = self.parse_func_params()?.0;
            self.expect(TokenData::RParen)?;
            let body_begin = self.expect(TokenData::Colon)?.end;

            let body = self.parse_block(body_begin)?.1.stmts;
            let end = self.expect(TokenData::KwEnd)?.end;

            return Ok((SourceRange { begin, end }, item::Func { name, params, body }));
        }
        // fn params => expr
        else {
            let params = self.parse_func_params()?.0;
            self.expect(TokenData::FatArrow)?;

            let name = None;
            let body = self.parse_expr(0)?;
            let end = body.source.end;
            let body = vec![body.to_stmt()];

            return Ok((SourceRange { begin, end }, item::Func { name, params, body }));
        }
    }


    pub fn parse_module(&mut self, begin: SourcePos) -> ParseResult<item::Module<'i>> {
        let (source, block) = self.parse_block(begin)?;
        return Ok(item::Module { source, block });
    }
}


pub fn parse_single<'i>(input: &'i [u8]) -> ParseResult<Expr<'i>> {
    let tokens = Tokenizer::tokenize(input, true)?;
    let mut p = Parser::new(&tokens);

    let result = p.parse_expr(0)?;

    if let Some(tok) = p.peek(0) {
        return Err(ParseError::at_pos(tok.source.begin, ParseErrorData::TrailingInput));
    }
    Ok(result)
}

pub fn parse_module<'i>(input: &'i [u8]) -> ParseResult<item::Module<'i>> {
    let tokens = Tokenizer::tokenize(input, true)?;
    let mut p = Parser::new(&tokens);
    p.parse_module(SourcePos { line: 0, column: 0 })
}

