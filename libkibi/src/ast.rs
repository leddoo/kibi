use crate::string_table::{Atom, OptAtom};


//
// common
//

pub use crate::source_map::SourceRange;

#[derive(Clone, Copy, Debug)]
pub struct Path<'a> {
    pub local: bool,
    pub parts: &'a [Atom],
}

#[derive(Clone, Copy, Debug)]
pub enum IdentOrPath<'a> {
    Ident(Atom),
    Path(Path<'a>),
}


#[derive(Debug)]
pub enum Binder<'a> {
    Ident(OptAtom),
    Typed(TypedBinder<'a>),
}

pub type BinderList<'a> = &'a mut [Binder<'a>];

#[derive(Debug)]
pub struct TypedBinder<'a> {
    pub implicit: bool,
    pub names:   &'a[OptAtom],
    pub ty:      ExprRef<'a>,
    pub default: Option<ExprRef<'a>>,
}




//
// tokens
//

#[derive(Debug)]
pub struct Token<'a> {
    pub source: SourceRange,
    pub kind: TokenKind<'a>,
}

#[derive(Debug, PartialEq)]
pub enum TokenKind<'a> {
    Error,

    Hole,
    Ident(Atom),

    Bool(bool),
    Number(&'a str),
    String(&'a str),
    //FString(&'a str),

    //Code(&'a str),

    KwSort, KwProp, KwType,
    KwLam, KwPi,

    KwInductive,
    KwStruct,
    KwEnum,
    KwDef,

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

    LParen,   RParen,
    LBracket, RBracket,
    LCurly,   RCurly,

    Dot,
    Comma,
    Semicolon,
    Colon,
    ColonColon,
    ColonEq,

    Arrow,
    FatArrow,

    Add,
    AddAssign,
    Minus,
    SubAssign,
    Star,
    MulAssign,
    Div,
    DivAssign,
    FloorDiv,
    FloorDivAssign,
    Rem,
    RemAssign,

    Eq,
    EqEq,
    Not,
    NotEq,
    Le,
    Lt,
    Ge,
    Gt,
}


impl<'a> TokenKind<'a> {
    pub fn repr(&self) -> &'static str {
        match self {
            TokenKind::Error => unreachable!(),
            TokenKind::Hole => "hole",
            TokenKind::Ident(_) => "ident",
            TokenKind::Bool(_) => "bool",
            TokenKind::Number(_) => "number",
            TokenKind::String(_) => "string",
            TokenKind::KwSort => "'Sort'",
            TokenKind::KwProp => "'Prop'",
            TokenKind::KwType => "'Type'",
            TokenKind::KwLam => "'λ' | 'lam'",
            TokenKind::KwPi => "'Π' | 'Pi'",
            TokenKind::KwInductive => "'inductive'",
            TokenKind::KwStruct => "'struct'",
            TokenKind::KwEnum => "'enum'",
            TokenKind::KwDef => "'def'",
            TokenKind::KwLet => "'let'",
            TokenKind::KwVar => "'var'",
            TokenKind::KwDo => "'do'",
            TokenKind::KwIf => "'if'",
            TokenKind::KwElif => "'elif'",
            TokenKind::KwElse => "'else'",
            TokenKind::KwWhile => "'while'",
            TokenKind::KwFor => "'for'",
            TokenKind::KwIn => "'in'",
            TokenKind::KwBreak => "'break'",
            TokenKind::KwContinue => "'continue'",
            TokenKind::KwReturn => "'return'",
            TokenKind::KwFn => "'fn'",
            TokenKind::KwAnd => "'and'",
            TokenKind::KwOr => "'or'",
            TokenKind::KwNot => "'not'",
            TokenKind::LParen => "'('",
            TokenKind::RParen => "')'",
            TokenKind::LBracket => "'['",
            TokenKind::RBracket => "']'",
            TokenKind::LCurly => "'{'",
            TokenKind::RCurly => "'}'",
            TokenKind::Dot => "'.'",
            TokenKind::Comma => "','",
            TokenKind::Semicolon => "';'",
            TokenKind::Colon => "':'",
            TokenKind::ColonColon => "'::'",
            TokenKind::ColonEq => "':='",
            TokenKind::Arrow => "'->'",
            TokenKind::FatArrow => "'=>'",
            TokenKind::Add => "'+'",
            TokenKind::AddAssign => "'+='",
            TokenKind::Minus => "'-'",
            TokenKind::SubAssign => "'-='",
            TokenKind::Star => "'*'",
            TokenKind::MulAssign => "'*='",
            TokenKind::Div => "'/'",
            TokenKind::DivAssign => "'/='",
            TokenKind::FloorDiv => "'//'",
            TokenKind::FloorDivAssign => "'//='",
            TokenKind::Rem => "'%'",
            TokenKind::RemAssign => "'%='",
            TokenKind::Eq => "'='",
            TokenKind::EqEq => "'=='",
            TokenKind::Not => "''!",
            TokenKind::NotEq => "'!='",
            TokenKind::Le => "'<='",
            TokenKind::Lt => "'<'",
            TokenKind::Ge => "'>='",
            TokenKind::Gt => "'>'",
        }
    }
}



//
// items
//

#[derive(Debug)]
pub struct Item<'a> {
    pub kind: ItemKind<'a>,
}

#[derive(Debug)]
pub enum ItemKind<'a> {
    Axiom(item::Axiom<'a>),
    Def(item::Def<'a>),
    Reduce(ExprRef<'a>),
    Inductive(adt::Inductive<'a>),
}


pub mod item {
    use super::*;


    #[derive(Debug)]
    pub struct Axiom<'a> {
        pub name:   IdentOrPath<'a>,
        pub levels: &'a [Atom],
        pub params: BinderList<'a>,
        pub ty:     Expr<'a>,
    }

    #[derive(Debug)]
    pub struct Def<'a> {
        pub name:   IdentOrPath<'a>,
        pub levels: &'a [Atom],
        pub params: BinderList<'a>,
        pub ty:     Option<Expr<'a>>,
        pub value:  Expr<'a>,
    }
}



//
// stmts
//

pub type StmtRef<'a> = &'a mut Stmt<'a>;

pub type StmtList<'a> = &'a mut [StmtRef<'a>];

#[derive(Debug)]
pub struct Stmt<'a> {
    pub kind: StmtKind<'a>,
}

#[derive(Debug)]
pub enum StmtKind<'a> {
    Let(stmt::Let<'a>),
    Expr(Expr<'a>),
}


pub mod stmt {
    use super::*;


    #[derive(Debug)]
    pub struct Let<'a> {
        pub is_var: bool,
        pub ident:  &'a str,
        pub ty:     Option<ExprRef<'a>>,
        pub value:  Option<ExprRef<'a>>,
    }
}



//
// exprs
//

pub type ExprRef<'a> = &'a mut Expr<'a>;

pub type ExprList<'a> = &'a mut [Expr<'a>];

#[derive(Debug)]
pub struct Expr<'a> {
    pub source: SourceRange,
    pub kind: ExprKind<'a>,
}

#[derive(Debug)]
pub enum ExprKind<'a> {
    Error,

    Hole,
    Ident(Atom),
    DotIdent(Atom),
    Path(Path<'a>),

    Levels(expr::Levels<'a>),
    Sort(LevelRef<'a>),
    Forall(expr::Forall<'a>),
    Lambda(expr::Lambda<'a>),

    Bool(bool),
    Number(&'a str),
    String(&'a str),

    Parens(ExprRef<'a>),
    Block(expr::Block<'a>),

    Op1(expr::Op1<'a>),
    Op2(expr::Op2<'a>),
    Op2Assign(expr::Op2<'a>),

    Assign(expr::Assign<'a>),

    Field(expr::Field<'a>),
    Index(expr::Index<'a>),
    Call(expr::Call<'a>),

    List(ExprList<'a>),
    ListType(ExprRef<'a>),
    Map(expr::Map<'a>),
    MapType(expr::MapType<'a>),

    Match(expr::Match<'a>),
    If(expr::If<'a>),
    Loop(expr::Loop<'a>),

    TypeHint(expr::TypeHint<'a>),
}


pub mod expr {
    use super::*;


    #[derive(Debug)]
    pub struct Levels<'a> {
        pub symbol: IdentOrPath<'a>,
        pub levels: LevelList<'a>,
    }


    #[derive(Debug)]
    pub struct Forall<'a> {
        pub binders: BinderList<'a>,
        pub ret:     ExprRef<'a>,
    }

    #[derive(Debug)]
    pub struct Lambda<'a> {
        pub binders: BinderList<'a>,
        pub value:   ExprRef<'a>,
    }


    #[derive(Debug)]
    pub struct Block<'a> {
        pub is_do: bool,
        pub stmts: StmtList<'a>,
    }


    #[derive(Clone, Copy, Debug, PartialEq)]
    pub enum Op1Kind {
        LogicNot,
        Not,
        Negate, // the real negate.
    }

    #[derive(Debug)]
    pub struct Op1<'a> {
        pub op:   Op1Kind,
        pub expr: ExprRef<'a>,
    }


    #[derive(Clone, Copy, Debug, PartialEq)]
    pub enum Op2Kind {
        Add,
        Sub,
        Mul,
        Div,
        FloorDiv,
        Rem,
        And,
        Or,
        CmpEq,
        CmpNe,
        CmpLe,
        CmpLt,
        CmpGe,
        CmpGt,
    }

    #[derive(Debug)]
    pub struct Op2<'a> {
        pub op:  Op2Kind,
        pub lhs: ExprRef<'a>,
        pub rhs: ExprRef<'a>,
    }


    #[derive(Debug)]
    pub struct Field<'a> {
        pub base: ExprRef<'a>,
        pub name: Atom,
    }

    #[derive(Debug)]
    pub struct Index<'a> {
        pub base:  ExprRef<'a>,
        pub index: ExprRef<'a>,
    }

    #[derive(Debug)]
    pub struct Call<'a> {
        //pub self_post_eval: bool,
        pub func: ExprRef<'a>,
        pub args: CallArgList<'a>,
    }

    pub type CallArgList<'a> = &'a mut [CallArg<'a>];

    #[derive(Debug)]
    pub enum CallArg<'a> {
        Positional(Expr<'a>),
        Named(NamedArg<'a>),
    }

    #[derive(Debug)]
    pub struct NamedArg<'a> {
        pub name:  &'a str,
        pub value: Expr<'a>,
    }


    #[derive(Debug)]
    pub struct Assign<'a> {
        pub lhs: ExprRef<'a>,
        pub rhs: ExprRef<'a>,
    }


    #[derive(Debug)]
    pub struct Map<'a> {
        pub entries: MapEntryList<'a>,
    }

    pub type MapEntryList<'a> = &'a mut [MapEntry<'a>];

    #[derive(Debug)]
    pub struct MapEntry<'a> {
        pub key:   &'a str,
        pub value: ExprRef<'a>,
    }

    #[derive(Debug)]
    pub struct MapType<'a> {
        pub key:   ExprRef<'a>,
        pub value: ExprRef<'a>,
    }


    #[derive(Debug)]
    pub struct Match<'a> {
        pub expr: ExprRef<'a>,
        pub cases: MatchCaseList<'a>,
    }

    pub type MatchCaseList<'a> = &'a mut [MatchCase<'a>];

    #[derive(Debug)]
    pub struct MatchCase<'a> {
        //pub ctor:    GenericIdent<'a>,
        pub binding: Option<&'a str>,
        pub expr:    ExprRef<'a>,
    }


    #[derive(Debug)]
    pub struct If<'a> {
        pub cond:  ExprRef<'a>,
        pub then:  Block<'a>,
        pub els:   Option<ExprRef<'a>>,
    }

    pub type IfCaseList<'a> = &'a mut [IfCase<'a>];

    #[derive(Debug)]
    pub struct IfCase<'a> {
        pub cond: ExprRef<'a>,
        pub then: Block<'a>,
    }


    #[derive(Debug)]
    pub struct Loop<'a> {
        pub cond: Option<ExprRef<'a>>,
        pub body: Block<'a>,
    }


    #[derive(Debug)]
    pub struct TypeHint<'a> {
        pub expr: ExprRef<'a>,
        pub ty:   ExprRef<'a>,
    }
}



//
// levels
//

pub type LevelRef<'a> = &'a mut Level<'a>;

pub type LevelList<'a> = &'a mut [Level<'a>];

#[derive(Debug)]
pub struct Level<'a> {
    pub source: SourceRange,
    pub kind: LevelKind<'a>,
}

#[derive(Debug)]
pub enum LevelKind<'a> {
    Hole,
    Ident(Atom),

    Nat(u32),
    Add((LevelRef<'a>, u32)),
    Max((LevelRef<'a>, LevelRef<'a>)),
    IMax((LevelRef<'a>, LevelRef<'a>)),
}



//
// user types
//

pub mod adt {
    use super::*;

    #[derive(Debug)]
    pub struct Inductive<'a> {
        pub name:   IdentOrPath<'a>,
        pub levels: &'a [Atom],
        pub params: BinderList<'a>,
        pub ty:     Option<Expr<'a>>,
        pub ctors:  CtorList<'a>,
    }


    #[derive(Debug)]
    pub struct Ctor<'a> {
        pub name: Atom,
        pub args: BinderList<'a>,
        pub ty:   Option<Expr<'a>>,
    }

    pub type CtorList<'a> = &'a [Ctor<'a>];
}

