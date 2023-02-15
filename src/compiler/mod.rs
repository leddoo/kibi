pub mod parser;
pub mod bbir;
pub mod analysis;
pub mod compiler;
pub mod opt;
pub mod codegen;

pub use parser::*;
pub use bbir::*;
pub use analysis::*;
pub use compiler::*;



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



#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Op1 {
    BoolNot,
    BitNot,
    Neg,
    Plus,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Op2 {
    And,
    Or,
    Add,
    Sub,
    Mul,
    Div,
    IntDiv,
    CmpEq,
    CmpNe,
    CmpLe,
    CmpLt,
    CmpGe,
    CmpGt,
    OrElse,
}



impl SourcePos {
    pub fn to_range(self) -> SourceRange {
        SourceRange { begin: self, end: self }
    }
}


impl SourceRange {
    #[inline(always)]
    pub fn is_collapsed(&self) -> bool {
        self.begin == self.end
    }

    #[inline(always)]
    pub const fn null() -> SourceRange {
        let zero = SourcePos { line: 0, column: 0 };
        SourceRange { begin: zero, end: zero }
    }
}


impl Op1 {
    #[inline]
    pub fn str(self) -> &'static str {
        use self::Op1::*;
        match self {
            BoolNot => { "not" }
            BitNot  => { "bit_not" }
            Neg     => { "neg" }
            Plus    => { "plus" }
        }
    }
}


impl Op2 {
    #[inline]
    pub fn str(self) -> &'static str {
        use Op2::*;
        match self {
            And    => { "and" }
            Or     => { "or" }
            Add    => { "add" }
            Sub    => { "sub" }
            Mul    => { "mul" }
            Div    => { "div" }
            IntDiv => { "int_div" }
            CmpEq  => { "cmp_eq" }
            CmpNe  => { "cmp_ne" }
            CmpLe  => { "cmp_le" }
            CmpLt  => { "cmp_lt" }
            CmpGe  => { "cmp_ge" }
            CmpGt  => { "cmp_gt" }
            OrElse => { "or_else" }
        }
    }
}

