
pub type LevelRef<'a> = &'a Level<'a>;

pub type LevelList<'a> = &'a [Level<'a>];


#[derive(Clone, Debug)]
pub struct Level<'a> {
    pub kind: LevelKind<'a>,
}

#[derive(Clone, Debug)]
pub enum LevelKind<'a> {
    Zero,
    Succ(LevelRef<'a>),
    Max(level::Pair<'a>),
    IMax(level::Pair<'a>),
}


pub mod level {
    use super::*;


    #[derive(Clone, Debug)]
    pub struct Pair<'a> {
        pub lhs: LevelRef<'a>,
        pub rhs: LevelRef<'a>,
    }
}

