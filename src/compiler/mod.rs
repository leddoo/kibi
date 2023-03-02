pub mod parser;
pub mod bbir;
pub mod analysis;
pub mod compiler;
pub mod opt;
pub mod transform;
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
    Not,
    Negate, // the real negate.
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Op2 {
    Add,
    Sub,
    Mul,
    Div,
    FloorDiv,
    Rem,
    And,
    Or,
    OrElse,
    CmpEq,
    CmpNe,
    CmpLe,
    CmpLt,
    CmpGe,
    CmpGt,
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
            Not    => { "not" }
            Negate => { "negate" }
        }
    }
}


impl Op2 {
    #[inline]
    pub fn str(self) -> &'static str {
        use Op2::*;
        match self {
            Add         => { "add" }
            Sub         => { "sub" }
            Mul         => { "mul" }
            Div         => { "div" }
            FloorDiv    => { "floor_div" }
            Rem         => { "rem" }
            And         => { "and" }
            Or          => { "or" }
            OrElse      => { "or_else" }
            CmpEq       => { "cmp_eq" }
            CmpNe       => { "cmp_ne" }
            CmpLe       => { "cmp_le" }
            CmpLt       => { "cmp_lt" }
            CmpGe       => { "cmp_ge" }
            CmpGt       => { "cmp_gt" }
        }
    }

    #[inline]
    pub fn is_cancelling(self) -> bool {
        use Op2::*;
        match self {
            And | Or | OrElse => true,

            Add | Sub | Mul | Div | FloorDiv | Rem |
            CmpEq | CmpNe | CmpLe | CmpLt | CmpGe | CmpGt => false,
        }
    }
}

