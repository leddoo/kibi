use crate::string_table::{Atom, OptAtom, StringTable};


//
// common
//

sti::define_key!(pub, u32, SourceId);

sti::define_key!(pub, u32, ParseId);
sti::define_key!(pub, u32, ParseStringId);
sti::define_key!(pub, u32, ParseNumberId);

sti::define_key!(pub, u32, TokenId, rng: TokenRange);
sti::define_key!(pub, u32, ItemId, opt: OptItemId);
sti::define_key!(pub, u32, StmtId);
sti::define_key!(pub, u32, LevelId);
sti::define_key!(pub, u32, ExprId, opt: OptExprId);
sti::define_key!(pub, u32, TacticId);


#[derive(Clone, Copy, Debug)]
pub enum AstId {
    Item(ItemId),
    Stmt(StmtId),
    Level(LevelId),
    Expr(ExprId),
    Tactic(TacticId),
}

pub type AstParent = Option<AstId>;

impl Into<AstId> for ItemId   { #[inline(always)] fn into(self) -> AstId { AstId::Item(self) } }
impl Into<AstId> for StmtId   { #[inline(always)] fn into(self) -> AstId { AstId::Stmt(self) } }
impl Into<AstId> for LevelId  { #[inline(always)] fn into(self) -> AstId { AstId::Level(self) } }
impl Into<AstId> for ExprId   { #[inline(always)] fn into(self) -> AstId { AstId::Expr(self) } }
impl Into<AstId> for TacticId { #[inline(always)] fn into(self) -> AstId { AstId::Tactic(self) } }


#[derive(Clone, Copy, Debug)]
pub struct Ident {
    pub source: TokenId,
    pub value: Atom,
}

#[derive(Clone, Copy, Debug)]
pub struct OptIdent {
    pub source: TokenId,
    pub value: OptAtom,
}

#[derive(Clone, Copy, Debug)]
pub struct Path<'a> {
    pub parts: &'a [Ident],
}

#[derive(Clone, Copy, Debug)]
pub enum IdentOrPath<'a> {
    Ident(Ident),
    Path(Path<'a>),
}


#[derive(Clone, Copy, Debug)]
pub enum Binder<'a> {
    Ident(OptIdent),
    Typed(TypedBinder<'a>),
}

pub type BinderList<'a> = &'a [Binder<'a>];

#[derive(Clone, Copy, Debug)]
pub struct TypedBinder<'a> {
    pub implicit: bool,
    pub names:   &'a [OptIdent],
    pub ty:      ExprId,
    pub default: OptExprId,
}


/// zero based.
#[derive(Clone, Copy, Debug)]
pub struct UserSourcePos {
    pub line: u32,
    pub col:  u32,
}

#[derive(Clone, Copy, Debug)]
pub struct UserSourceRange {
    pub begin: UserSourcePos,
    pub end:   UserSourcePos,
}


#[derive(Clone, Copy, Debug)]
pub struct SourceRange {
    pub begin: u32,
    pub end:   u32,
}

#[derive(Clone, Copy, Debug)]
pub struct ParseRange {
    pub begin: u32,
    pub end:   u32,
}

impl ParseRange {
    pub const UNKNOWN: ParseRange = ParseRange { begin: 0, end: 0 };
}



//
// tokens
//

#[derive(Clone, Copy, Debug)]
pub struct Token {
    pub source: ParseRange,
    pub kind: TokenKind,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum TokenKind {
    Error,
    EndOfFile,

    Hole,
    Ident(Atom),
    Label(Atom),

    Bool(bool),
    Number(ParseNumberId),
    String(ParseStringId),

    KwSort, KwProp, KwType,
    KwLam, KwPi,

    KwInductive,
    KwStruct,
    KwEnum,
    KwDef,

    KwTrait,
    KwImpl,

    KwLet, KwVar,
    KwIn,

    KwBy,

    KwDo,
    KwIf,
    KwThen,
    KwWhile,
    KwLoop,
    KwElse,
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
    LeftArrow,
    FatArrow,

    Ampersand,

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


impl TokenKind {
    pub fn is_expr_start(&self) -> bool {
        match self {
            TokenKind::Hole |
            TokenKind::Ident(_) |
            TokenKind::Bool(_) |
            TokenKind::Number(_) |
            TokenKind::String(_) |
            TokenKind::KwSort |
            TokenKind::KwProp |
            TokenKind::KwType |
            TokenKind::KwLam |
            TokenKind::KwPi |
            TokenKind::KwLet |
            TokenKind::KwBy |
            TokenKind::KwDo |
            TokenKind::KwIf |
            TokenKind::KwWhile |
            TokenKind::KwLoop |
            TokenKind::KwBreak |
            TokenKind::KwContinue |
            TokenKind::KwReturn |
            TokenKind::KwFn |
            TokenKind::KwNot |
            TokenKind::LParen |
            TokenKind::LBracket |
            TokenKind::LCurly |
            TokenKind::Dot |
            TokenKind::Ampersand |
            TokenKind::Minus |
            TokenKind::Star |
            TokenKind::Not => true,

            TokenKind::Error |
            TokenKind::EndOfFile |
            TokenKind::Label(_) |
            TokenKind::KwInductive |
            TokenKind::KwStruct |
            TokenKind::KwEnum |
            TokenKind::KwDef |
            TokenKind::KwTrait |
            TokenKind::KwImpl |
            TokenKind::KwVar |
            TokenKind::KwIn |
            TokenKind::KwThen |
            TokenKind::KwElse |
            TokenKind::KwAnd |
            TokenKind::KwOr |
            TokenKind::RParen |
            TokenKind::RBracket |
            TokenKind::RCurly |
            TokenKind::Comma |
            TokenKind::Semicolon |
            TokenKind::Colon |
            TokenKind::ColonColon |
            TokenKind::ColonEq |
            TokenKind::Arrow |
            TokenKind::LeftArrow |
            TokenKind::FatArrow |
            TokenKind::Add |
            TokenKind::AddAssign |
            TokenKind::SubAssign |
            TokenKind::MulAssign |
            TokenKind::Div |
            TokenKind::DivAssign |
            TokenKind::FloorDiv |
            TokenKind::FloorDivAssign |
            TokenKind::Rem |
            TokenKind::RemAssign |
            TokenKind::Eq |
            TokenKind::EqEq |
            TokenKind::NotEq |
            TokenKind::Le |
            TokenKind::Lt |
            TokenKind::Ge |
            TokenKind::Gt => false,
        }
    }

    pub fn repr(&self) -> &'static str {
        match self {
            TokenKind::Error => unreachable!(),
            TokenKind::EndOfFile => "eof",
            TokenKind::Hole => "hole",
            TokenKind::Ident(_) => "ident",
            TokenKind::Label(_) => "label",
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
            TokenKind::KwTrait => "'trait'",
            TokenKind::KwImpl => "'impl'",
            TokenKind::KwLet => "'let'",
            TokenKind::KwVar => "'var'",
            TokenKind::KwIn => "'in'",
            TokenKind::KwBy => "'by'",
            TokenKind::KwDo => "'do'",
            TokenKind::KwIf => "'if'",
            TokenKind::KwThen => "'then'",
            TokenKind::KwWhile => "'while'",
            TokenKind::KwLoop => "'loop'",
            TokenKind::KwElse => "'else'",
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
            TokenKind::LeftArrow => "'<-'",
            TokenKind::FatArrow => "'=>'",
            TokenKind::Ampersand => "'&'",
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
    pub parent: AstParent,
    pub source: TokenRange,

    pub kind: ItemKind<'a>,
}

#[derive(Debug)]
pub enum ItemKind<'a> {
    Error,
    Axiom(item::Axiom<'a>),
    Def(item::Def<'a>),
    Reduce(ExprId),
    Inductive(adt::Inductive<'a>),
    Trait(item::Trait<'a>),
    Impl(item::Impl<'a>),
}


pub mod item {
    use super::*;


    #[derive(Debug)]
    pub struct Axiom<'a> {
        pub name:   IdentOrPath<'a>,
        pub levels: &'a [Ident],
        pub params: BinderList<'a>,
        pub ty:     ExprId,
    }

    #[derive(Debug)]
    pub struct Def<'a> {
        pub name:   IdentOrPath<'a>,
        pub levels: &'a [Ident],
        pub params: BinderList<'a>,
        pub ty:     OptExprId,
        pub value:  ExprId,
    }

    #[derive(Debug)]
    pub enum Trait<'a> {
        Inductive(adt::Inductive<'a>),
    }

    #[derive(Debug)]
    pub struct Impl<'a> {
        pub levels: &'a [Ident],
        pub params: BinderList<'a>,
        pub ty:     ExprId,
        pub value:  ExprId,
    }
}



//
// stmts
//

pub type StmtList<'a> = &'a [StmtId];

#[derive(Clone, Copy, Debug)]
pub struct Stmt {
    pub parent: AstParent,
    pub source: TokenRange,

    pub kind: StmtKind,
}

#[derive(Clone, Copy, Debug)]
pub enum StmtKind {
    Error,
    Let(stmt::Let),
    Assign(ExprId, ExprId),
    Expr(ExprId),
}


pub mod stmt {
    use super::*;

    #[derive(Clone, Copy, Debug)]
    pub struct Let {
        pub is_var: bool,
        pub name:   OptIdent,
        pub ty:     OptExprId,
        pub val:    OptExprId,
    }
}



//
// exprs
//

pub type ExprList<'a> = &'a [ExprId];

#[derive(Clone, Copy, Debug)]
pub struct Expr<'a> {
    pub parent: AstParent,
    pub source: TokenRange,
    pub flags: ExprFlags,

    pub kind: ExprKind<'a>,
}

#[derive(Clone, Copy, Debug)]
pub enum ExprKind<'a> {
    Error,

    Hole,
    Ident(Ident),
    DotIdent(Ident),
    Path(Path<'a>),

    Levels(expr::Levels<'a>),
    Sort(LevelId),
    Forall(expr::Binder<'a>),
    Lambda(expr::Binder<'a>),
    Let(expr::Let),

    By(TacticList<'a>),

    Bool(bool),
    Number(ParseNumberId),
    String(ParseStringId),

    Parens(ExprId),

    Ref(expr::Ref),
    Deref(ExprId),

    // @cleanup: how to handle operators & prop types?
    Eq(ExprId, ExprId),
    Op1(expr::Op1),
    Op2(expr::Op2),

    Field(expr::Field),
    Index(expr::Index),
    Call(expr::Call<'a>),

    Do(expr::Block<'a>),
    If(expr::If),
    While(expr::While),
    Loop(expr::Loop<'a>),
    Break(expr::Break),
    Continue(OptAtom),
    ContinueElse(OptAtom),
    Return(OptExprId),

    TypeHint(expr::TypeHint),
}

#[derive(Clone, Copy, Debug)]
pub struct ExprFlags {
    pub has_assign: bool,
    pub has_if: bool,
    pub has_loop: bool,
    pub has_jump: bool,
}


pub mod expr {
    use super::*;


    #[derive(Clone, Copy, Debug)]
    pub struct Levels<'a> {
        pub symbol: IdentOrPath<'a>,
        pub levels: LevelList<'a>,
    }


    #[derive(Clone, Copy, Debug)]
    pub struct Binder<'a> {
        pub binders: BinderList<'a>,
        pub value:   ExprId,
    }

    #[derive(Clone, Copy, Debug)]
    pub struct Let {
        pub name: OptIdent,
        pub ty:   OptExprId,
        pub val:  ExprId,
        pub body: ExprId,
    }


    #[derive(Clone, Copy, Debug, PartialEq)]
    pub enum RefKind {
        Mut,
        Shared,
        Const,
    }

    #[derive(Clone, Copy, Debug)]
    pub struct Ref {
        pub kind: RefKind,
        pub expr: ExprId,
    }


    #[derive(Clone, Copy, Debug, PartialEq)]
    pub enum Op1Kind {
        LogicNot,
        Not,
        Negate, // the real negate.
    }

    #[derive(Clone, Copy, Debug)]
    pub struct Op1 {
        pub op:   Op1Kind,
        pub expr: ExprId,
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

    #[derive(Clone, Copy, Debug)]
    pub struct Op2 {
        pub op:  Op2Kind,
        pub lhs: ExprId,
        pub rhs: ExprId,
    }


    #[derive(Clone, Copy, Debug)]
    pub struct Field {
        pub base: ExprId,
        pub name: Ident,
    }

    #[derive(Clone, Copy, Debug)]
    pub struct Index {
        pub base:  ExprId,
        pub index: ExprId,
    }

    #[derive(Clone, Copy, Debug)]
    pub struct Call<'a> {
        //pub self_post_eval: bool,
        pub func: ExprId,
        pub args: ExprList<'a>,
    }


    #[derive(Clone, Copy, Debug)]
    pub struct Map<'a> {
        pub entries: MapEntryList<'a>,
    }

    pub type MapEntryList<'a> = &'a [MapEntry<'a>];

    #[derive(Clone, Copy, Debug)]
    pub struct MapEntry<'a> {
        pub key:   &'a str,
        pub value: ExprId,
    }

    #[derive(Clone, Copy, Debug)]
    pub struct MapType {
        pub key:   ExprId,
        pub value: ExprId,
    }


    #[derive(Clone, Copy, Debug)]
    pub struct Block<'a> {
        pub is_do: bool,
        pub label: OptAtom,
        pub stmts: &'a [StmtId],
    }

    #[derive(Clone, Copy, Debug)]
    pub struct If {
        pub is_do: bool,
        pub label: OptAtom,
        pub cond:  ExprId,
        pub then:  ExprId,
        pub els:   OptExprId,
    }

    #[derive(Clone, Copy, Debug)]
    pub struct While {
        pub is_do: bool,
        pub label: OptAtom,
        pub cond: ExprId,
        pub body: ExprId,
        pub els:  OptExprId,
    }

    #[derive(Clone, Copy, Debug)]
    pub struct Loop<'a> {
        pub is_do: bool,
        pub label: OptAtom,
        pub stmts: &'a [StmtId],
    }

    #[derive(Clone, Copy, Debug)]
    pub struct Break {
        pub label: OptAtom,
        pub value: OptExprId,
    }


    #[derive(Clone, Copy, Debug)]
    pub struct TypeHint {
        pub expr: ExprId,
        pub ty:   ExprId,
    }
}


impl ExprFlags {
    #[inline]
    pub const fn new() -> ExprFlags {
        ExprFlags {
            has_assign: false,
            has_if: false,
            has_loop: false,
            has_jump: false,
        }
    }
}

impl core::ops::BitOr for ExprFlags {
    type Output = Self;

    #[inline(always)]
    fn bitor(self, rhs: Self) -> Self::Output {
        ExprFlags {
            has_assign: self.has_assign | rhs.has_assign,
            has_if:     self.has_if     | rhs.has_if,
            has_loop:   self.has_loop   | rhs.has_loop,
            has_jump:   self.has_jump   | rhs.has_jump,
        }
    }
}

impl core::ops::BitOrAssign for ExprFlags {
    #[inline(always)]
    fn bitor_assign(&mut self, rhs: Self) { *self = *self | rhs }
}



//
// levels
//

pub type LevelList<'a> = &'a [LevelId];

#[derive(Clone, Copy, Debug)]
pub struct Level {
    pub parent: AstParent,
    pub source: TokenRange,
    pub kind: LevelKind,
}

#[derive(Clone, Copy, Debug)]
pub enum LevelKind {
    Error,

    Hole,
    Ident(Ident),

    Nat(u32),
    Add((LevelId, u32)),
    Max((LevelId, LevelId)),
    IMax((LevelId, LevelId)),
}



//
// user types
//

pub mod adt {
    use super::*;

    #[derive(Debug)]
    pub struct Inductive<'a> {
        pub name:   Ident,
        pub levels: &'a [Ident],
        pub params: BinderList<'a>,
        pub ty:     OptExprId,
        pub ctors:  CtorList<'a>,
    }


    #[derive(Clone, Copy, Debug)]
    pub struct Ctor<'a> {
        pub name: Ident,
        pub args: BinderList<'a>,
        pub ty:   OptExprId,
    }

    pub type CtorList<'a> = &'a [Ctor<'a>];
}



//
// tactics
//

pub type TacticList<'a> = &'a [TacticId];

#[derive(Clone, Copy, Debug)]
pub struct Tactic<'a> {
    pub parent: AstParent,
    pub source: TokenRange,

    pub kind: TacticKind<'a>,
}

#[derive(Clone, Copy, Debug)]
pub enum TacticKind<'a> {
    Error,

    Goal,

    Sorry,
    Assumption,
    Refl,
    Rewrite(tactic::Rewrite),

    By(TacticList<'a>),
}


pub mod tactic {
    use super::*;


    #[derive(Clone, Copy, Debug)]
    pub struct Rewrite {
        pub symm: bool,
        pub with: ExprId,
    }
}



//
// stuff
//

impl<'a> IdentOrPath<'a> {
    #[inline(always)]
    pub fn display<'s>(self, strings: &'s StringTable<'s>) -> IdentOrPathDisplay<'a, 's> {
        IdentOrPathDisplay { this: self, strings }
    }
}

pub struct IdentOrPathDisplay<'a, 's> {
    this: IdentOrPath<'a>,
    strings: &'s StringTable<'s>,
}

impl<'a, 's> core::fmt::Display for IdentOrPathDisplay<'a, 's> {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        match self.this {
            IdentOrPath::Ident(ident) =>
                sti::write!(f, "{}", &self.strings[ident.value]),

            IdentOrPath::Path(parts) => {
                let mut first = true;
                for part in parts.parts.iter().copied() {
                    if !first { sti::write!(f, "::"); }
                    first = false;
                    sti::write!(f, "{}", &self.strings[part.value]);
                }
            }
        }
        Ok(())
    }
}

