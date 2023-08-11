use super::level::*;
use super::local_ctx::LocalId;


pub type TermRef<'a> = &'a Term<'a>;

#[derive(Clone, Debug)]
pub struct Term<'a> {
    pub kind: TermKind<'a>
}

#[derive(Clone, Debug)]
pub enum TermKind<'a> {
    Sort(LevelRef<'a>),

    BVar(BVar),
    Local(LocalId),
    Global(term::Global<'a>),

    Forall(term::Binder<'a>),
    Lambda(term::Binder<'a>),
    Apply(term::Apply<'a>),
}


#[derive(Clone, Copy, Debug)]
pub struct BVar(pub u32);

#[derive(Clone, Copy, Debug)]
pub struct GlobalId(pub u32);


pub mod term {
    use super::*;

    #[derive(Clone, Debug)]
    pub struct Global<'a> {
        pub id: GlobalId,
        pub levels: LevelList<'a>,
    }

    #[derive(Clone, Debug)]
    pub struct Binder<'a> {
        pub name: u32,
        pub param: TermRef<'a>,
        pub value: TermRef<'a>,
    }

    #[derive(Clone, Debug)]
    pub struct Apply<'a> {
        pub fun: TermRef<'a>,
        pub arg: TermRef<'a>,
    }
}

