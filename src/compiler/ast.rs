use derive_more::Deref;
use crate::macros::define_id;
use crate::infer::LocalId;



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


impl core::fmt::Display for SourcePos {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}:{}", self.line, self.column)
    }
}
impl core::fmt::Display for SourceRange {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}-{}", self.begin, self.end)
    }
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
    #[inline(always)]
    pub const fn to_range(self) -> SourceRange {
        SourceRange { begin: self, end: self }
    }

    #[inline(always)]
    pub const fn null() -> SourcePos {
        SourcePos { line: 0, column: 0 }
    }
}




impl SourceRange {
    #[inline(always)]
    pub fn is_collapsed(&self) -> bool {
        self.begin == self.end
    }

    #[inline(always)]
    pub const fn null() -> SourceRange {
        SourcePos::null().to_range()
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


define_id!(NodeId, OptNodeId);

// @todo-cleanup: put these into the macro?
impl NodeId {
    pub const ZERO: NodeId = NodeId(0);

    pub fn inc(&mut self) -> NodeId {
        assert!(self.0 < u32::MAX - 1);
        self.0 += 1;
        *self
    }
}



define_id!(ItemId, OptItemId);

impl ItemId {
    pub const ZERO: ItemId = ItemId(0);

    pub fn inc(&mut self) -> ItemId {
        assert!(self.0 < u32::MAX - 1);
        self.0 += 1;
        *self
    }
}


#[derive(Clone, Debug, Deref)]
pub struct Item<'a> {
    #[deref]
    pub data:   ItemData<'a>,
    pub source: SourceRange,
    pub id:     ItemId,     // computed by `Infer::assign_ids_*`.
    pub num_nodes: u32,     // computed by `Infer::assign_ids_*`.
}

#[derive(Clone, Debug)]
pub enum ItemData<'a> {
    Module          (item::Module<'a>),
    Func            (item::Func<'a>),
}

impl<'a> Item<'a> {
    #[inline(always)]
    pub fn new(source: SourceRange, data: ItemData<'a>) -> Self {
        Item { source, data, id: ItemId::ZERO, num_nodes: 0 }
    }
}



#[derive(Clone, Debug, Deref)]
pub struct Stmt<'a> {
    #[deref]
    pub data:   StmtData<'a>,
    pub source: SourceRange,
    pub id:     NodeId,     // computed by `Infer::assign_ids_*`.
}

#[derive(Clone, Debug)]
pub enum StmtData<'a> {
    Item            (Item<'a>),
    Local           (expr::Local<'a>),
    Expr            (Expr<'a>),
    Empty,
}

impl<'a> Stmt<'a> {
    #[inline(always)]
    pub fn new(source: SourceRange, data: StmtData<'a>) -> Self {
        Stmt { source, data, id: NodeId::ZERO }
    }
}



#[derive(Clone, Debug, Deref)]
pub struct Expr<'a> {
    #[deref]
    pub data:   ExprData<'a>,
    pub source: SourceRange,
    pub id:     NodeId,     // computed by `Infer::assign_ids_*`.
    pub ty:     Option<super::infer::Type>,
}

#[derive(Clone, Debug)]
pub enum ExprData<'a> {
    Nil,
    Bool            (bool),
    Number          (&'a str),
    QuotedString    (&'a str),
    Ident           (expr::Ident<'a>),
    Tuple           (Box<expr::Tuple<'a>>),
    List            (Box<expr::List<'a>>),
    Do              (Box<expr::Do<'a>>),
    SubExpr         (Box<Expr<'a>>),
    Op1             (Box<expr::Op1<'a>>),
    Op2             (Box<expr::Op2<'a>>),
    Field           (Box<expr::Field<'a>>),
    Index           (Box<expr::Index<'a>>),
    Call            (Box<expr::Call<'a>>),
    If              (Box<expr::If<'a>>),
    While           (Box<expr::While<'a>>),
    Break           (Box<expr::Break<'a>>),
    Continue        (Box<expr::Continue<'a>>),
    Return          (expr::Return<'a>),
    Env,
}

impl<'a> Expr<'a> {
    #[inline(always)]
    pub fn new(source: SourceRange, data: ExprData<'a>) -> Self {
        Expr { source, data, id: NodeId::ZERO, ty: None }
    }

    #[inline(always)]
    pub fn to_stmt(self) -> Stmt<'a> {
        Stmt::new(self.source, StmtData::Expr(self))
    }
}



pub mod item {
    use super::*;

    #[derive(Clone, Debug)]
    pub struct Func<'a> {
        pub name:   Option<&'a str>,
        pub params: Vec<FuncParam<'a>>,
        pub body:   Vec<Stmt<'a>>,
    }

    #[derive(Clone, Copy, Debug)]
    pub struct FuncParam<'a> {
        pub name: &'a str,
    }


    #[derive(Clone, Debug)]
    pub struct Module<'a> {
        pub source:    SourceRange,
        pub block:     expr::Block<'a>,
    }
}


pub mod expr {
    use super::*;

    #[derive(Clone, Copy, Debug)]
    pub struct Ident<'a> {
        pub name: &'a str,
        pub info: Option<IdentInfo>,
    }

    #[derive(Clone, Copy, Debug)]
    pub enum IdentTarget {
        Dynamic,
        Local { node: NodeId, local: LocalId },
        Item (ItemId),
    }

    #[derive(Clone, Copy, Debug)]
    pub struct IdentInfo {
        pub target: IdentTarget,
    }


    #[derive(Clone, Debug)]
    pub struct Local<'a> {
        pub name:  &'a str,
        pub value: Option<Expr<'a>>,
        pub kind:  LocalKind,
        pub info:  Option<LocalInfo>,
    }

    #[derive(Clone, Debug)]
    pub enum LocalKind {
        Let,
        Var,
    }

    #[derive(Clone, Copy, Debug)]
    pub struct LocalInfo {
        pub id: crate::infer::LocalId,
    }



    #[derive(Clone, Debug)]
    pub struct Tuple<'a> {
        pub values: Vec<Expr<'a>>,
    }

    #[derive(Clone, Debug)]
    pub struct List<'a> {
        pub values: Vec<Expr<'a>>,
    }

    #[derive(Clone, Debug)]
    pub struct Map<'a> {
        pub values: Vec<(Expr<'a>, Expr<'a>)>,
    }




    #[derive(Clone, Debug)]
    pub struct Op1<'a> {
        pub kind:  Op1Kind,
        pub child: Expr<'a>,
    }

    #[derive(Clone, Copy, Debug, PartialEq)]
    pub struct Op1Kind (pub super::Op1);


    #[derive(Clone, Debug)]
    pub struct Op2<'a> {
        pub kind:     Op2Kind,
        pub children: [Expr<'a>; 2],
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
                    FloorDiv    => 800,
                    Rem         => 800,
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
                    FloorDiv        => 801,
                    Rem             => 801,
                }
            }
        }
    }

    pub const PREC_PREFIX:  u32 =  900;
    pub const PREC_POSTFIX: u32 = 1000;


    #[derive(Clone, Debug)]
    pub struct Field<'a> {
        pub base: Expr<'a>,
        pub name: &'a str,
    }

    #[derive(Clone, Debug)]
    pub struct Index<'a> {
        pub base:  Expr<'a>,
        pub index: Expr<'a>,
    }

    #[derive(Clone, Debug)]
    pub struct Call<'a> {
        pub func: Expr<'a>,
        pub args: Vec<Expr<'a>>,
    }



    #[derive(Clone, Debug)]
    pub struct Block<'a> {
        pub stmts: Vec<Stmt<'a>>,
    }

    #[derive(Clone, Debug)]
    pub struct Do<'a> {
        pub label: Option<&'a str>,
        pub stmts: Vec<Stmt<'a>>,
    }


    #[derive(Clone, Debug)]
    pub struct IfBlock<'a> {
        pub stmts: Vec<Stmt<'a>>,
        pub is_do: bool,
    }

    #[derive(Clone, Debug)]
    pub struct If<'a> {
        pub condition: Expr<'a>,
        pub on_true:   IfBlock<'a>,
        pub on_false:  Option<IfBlock<'a>>,
    }

    #[derive(Clone, Debug)]
    pub struct While<'a> {
        pub label:     Option<&'a str>,
        pub condition: Expr<'a>,
        pub body:      Vec<Stmt<'a>>,
    }


    #[derive(Clone, Debug)]
    pub struct Break<'a> {
        pub label: Option<&'a str>,
        pub value: Option<Box<Expr<'a>>>,
        pub info:  Option<Option<BreakInfo>>,
    }

    #[derive(Clone, Debug)]
    pub struct Continue<'a> {
        pub label: Option<&'a str>,
        pub info:  Option<Option<BreakInfo>>,
    }

    #[derive(Clone, Copy, Debug)]
    pub struct BreakInfo {
        pub node:        NodeId,
        pub scope_index: u32,
    }


    #[derive(Clone, Debug)]
    pub struct Return<'a> {
        pub value: Option<Box<Expr<'a>>>,
    }
}

