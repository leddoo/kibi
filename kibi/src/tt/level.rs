use sti::arena::Arena;


pub use crate::string_table::Atom;
pub use crate::elab::LevelVarId;


pub type Level<'a> = impel::Level<'a>;

pub type LevelList<'a> = &'a [Level<'a>];


#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum LevelKind {
    Zero,
    Succ,
    Max,
    IMax,
    Param,
    IVar,
}

#[derive(Clone, Copy, Debug)]
pub enum LevelData<'a> {
    Zero,
    Succ(Level<'a>),
    Max(Pair<'a>),
    IMax(Pair<'a>),
    Param(Param),
    IVar(LevelVarId),

    // sync: `Level::syntax_eq`
}


#[derive(Clone, Copy, Debug)]
pub struct Pair<'a> {
    pub lhs: Level<'a>,
    pub rhs: Level<'a>,
}

#[derive(Clone, Copy, Debug)]
pub struct Param {
    pub name: Atom,
    pub index: u32,
}


impl<'a> Level<'a> {
    #[inline(always)]
    pub fn is_zero(self) -> bool { self.kind() == LevelKind::Zero }

    #[inline(always)]
    pub fn is_succ(self) -> bool { self.kind() == LevelKind::Succ }

    #[inline(always)]
    pub fn is_max(self) -> bool { self.kind() == LevelKind::Max }

    #[inline(always)]
    pub fn is_imax(self) -> bool { self.kind() == LevelKind::IMax }

    #[inline(always)]
    pub fn is_param(self) -> bool { self.kind() == LevelKind::Param }

    #[inline(always)]
    pub fn is_ivar(self) -> bool { self.kind() == LevelKind::IVar }


    pub fn non_zero(&self) -> bool {
        match self.data() {
            LevelData::Zero     => false,
            LevelData::Succ(_)  => true,
            LevelData::Max(p)   => p.lhs.non_zero() || p.rhs.non_zero(),
            LevelData::IMax(p)  => p.rhs.non_zero(),
            LevelData::Param(_) => false,
            LevelData::IVar(_)  => false,
        }
    }

    pub fn has_ivars(&self) -> bool {
        self.find(|at| { Some(at.is_ivar()) }).is_some()
    }


    pub fn to_offset(self) -> (Level<'a>, u32) {
        let mut at = self;
        let mut offset = 0;
        while let Some(pred) = at.try_succ() {
            offset += 1;
            at = pred;
        }
        return (at, offset);
    }

    #[inline(always)]
    pub fn to_nat(&self) -> Option<u32> {
        let (l, offset) = self.to_offset();
        l.is_zero().then_some(offset)
    }


    #[inline(always)]
    pub fn succ(self, alloc: &'a Arena) -> Level<'a> {
        alloc.mkl_succ(self)
    }

    #[inline(always)]
    pub fn offset(self, n: u32, alloc: &'a Arena) -> Level<'a> {
        let mut result = self;
        for _ in 0..n {
            result = result.succ(alloc)
        }
        return result;
    }

    #[inline(always)]
    pub fn max(self, other: Level<'a>, alloc: &'a Arena) -> Level<'a> {
        // @temp: proper impl.
        alloc.mkl_max(self, other)
    }

    #[inline(always)]
    pub fn imax(self, other: Level<'a>, alloc: &'a Arena) -> Level<'a> {
        let (a, b) = (self, other);

        // imax(a 0) = 0
        if b.is_zero() { return b; /*aka zero*/ }

        // imax(0 b) = b
        if a.is_zero() { return b; }

        // imax(a (succ b)) = max(a (succ b))
        // note: this handles the numeric cases.
        if b.non_zero() { return alloc.mkl_max(a, b); }

        // imax(a a) = a
        if a.syntax_eq(b) { return a; }

        alloc.mkl_imax(a, b)
    }


    #[inline(always)]
    pub fn syntax_eq(self, other: Level) -> bool {
        if self.ptr_eq(other) {
            return true;
        }

        use LevelData::*;
        match (self.data(), other.data()) {
            (Zero, Zero) => true,

            (Succ(a), Succ(b)) => a.syntax_eq(b),

            (Max(a),  Max(b)) |
            (IMax(a), IMax(b)) =>
                a.lhs.syntax_eq(b.lhs) && a.rhs.syntax_eq(b.rhs),

            (Param(a), Param(b)) => a.index == b.index,

            (IVar(v1), IVar(v2)) => v1 == v2,

            _ => false
        }
    }

    #[inline(always)]
    pub fn list_syntax_eq(a: &[Level], b: &[Level]) -> bool {
        if a.len() != b.len() {
            return false;
        }
        for i in 0..a.len() {
            if !a[i].syntax_eq(b[i]) {
                return false;
            }
        }
        true
    }


    pub fn find<F>(&'a self, f: F) -> Option<Level<'a>>
    where F: Fn(Level<'a>) -> Option<bool> {
        self.find_ex(&f)
    }

    pub fn find_ex<F>(self, f: &F) -> Option<Level<'a>>
    where F: Fn(Level<'a>) -> Option<bool> {
        if let Some(true) = f(self) {
            return Some(self);
        }

        match self.data() {
            LevelData::Zero => None,

            LevelData::Succ(l) => l.find_ex(f),

            LevelData::Max(p) |
            LevelData::IMax(p) => {
                p.lhs.find_ex(f).or_else(||
                p.rhs.find_ex(f))
            }

            LevelData::Param(_) |
            LevelData::IVar(_) => None,
        }
    }


    pub fn replace<F>(self, alloc: &'a Arena, f: F) -> Level<'a>
    where F: Fn(Level<'a>, &'a Arena) -> Option<Level<'a>> {
        self.replace_ex(alloc, &f)
    }

    pub fn replace_ex<F>(self, alloc: &'a Arena, f: &F) -> Level<'a>
    where F: Fn(Level<'a>, &'a Arena) -> Option<Level<'a>> {
        if let Some(new) = f(self, alloc) {
            return new;
        }

        match self.data() {
            LevelData::Zero => self,

            LevelData::Succ(of) => {
                let new_of = of.replace_ex(alloc, f);
                if new_of.ptr_eq(of) {
                    return self;
                }
                new_of.succ(alloc)
            }

            LevelData::Max(p) |
            LevelData::IMax(p) => {
                let new_lhs = p.lhs.replace_ex(alloc, f);
                let new_rhs = p.rhs.replace_ex(alloc, f);
                if new_lhs.ptr_eq(p.lhs) && new_rhs.ptr_eq(p.rhs) {
                    return self;
                }
                if self.is_max() { new_lhs.max(new_rhs, alloc)  }
                else             { new_lhs.imax(new_rhs, alloc) }
            }

            LevelData::Param(_) => self,

            LevelData::IVar(_) => self,
        }
    }

    pub fn instantiate_params(self, subst: LevelList<'a>, alloc: &'a Arena) -> Option<Level<'a>> {
        // @speed: has_param.
        let result = self.replace(alloc, |at, _| {
            let p = at.try_param()?;
            return Some(subst[p.index as usize]);
        });
        (!result.ptr_eq(self)).then_some(result)
    }
}


pub trait LevelAlloc {
    fn mkl_zero<'a>(&'a self) -> Level<'a>;
    fn mkl_succ<'a>(&'a self, of: Level<'a>) -> Level<'a>;
    fn mkl_max<'a>(&'a self, lhs: Level<'a>, rhs: Level<'a>) -> Level<'a>;
    fn mkl_imax<'a>(&'a self, lhs: Level<'a>, rhs: Level<'a>) -> Level<'a>;
    fn mkl_param<'a>(&'a self, name: Atom, index: u32) -> Level<'a>;
    fn mkl_ivar<'a>(&'a self, id: LevelVarId) -> Level<'a>;
    fn mkl_nat<'a>(&'a self, n: u32) -> Level<'a>;
}



mod impel {
    use super::*;

    #[derive(Clone, Copy, Debug)]
    pub struct Level<'a>(&'a LevelData<'a>);

    impl<'a> Level<'a> {
        pub const L0: Level<'static> = Level(&LevelData::Zero);
        pub const L1: Level<'static> = Level(&LevelData::Succ(Level::L0));
        pub const L2: Level<'static> = Level(&LevelData::Succ(Level::L1));
        pub const L3: Level<'static> = Level(&LevelData::Succ(Level::L2));


        #[inline(always)]
        pub fn kind(self) -> LevelKind {
            match self.0 {
                LevelData::Zero     => LevelKind::Zero,
                LevelData::Succ(_)  => LevelKind::Succ,
                LevelData::Max(_)   => LevelKind::Max,
                LevelData::IMax(_)  => LevelKind::IMax,
                LevelData::Param(_) => LevelKind::Param,
                LevelData::IVar(_)  => LevelKind::IVar,
            }
        }

        #[inline(always)]
        pub fn data(self) -> LevelData<'a> { *self.0 }

        #[inline(always)]
        pub fn try_succ(self) -> Option<Level<'a>> {
            if let LevelData::Succ(x) = *self.0 { Some(x) } else { None }
        }

        #[inline(always)]
        pub fn try_max(self) -> Option<Pair<'a>> {
            if let LevelData::Max(x) = *self.0 { Some(x) } else { None }
        }

        #[inline(always)]
        pub fn try_imax(self) -> Option<Pair<'a>> {
            if let LevelData::IMax(x) = *self.0 { Some(x) } else { None }
        }

        #[inline(always)]
        pub fn try_param(self) -> Option<Param> {
            if let LevelData::Param(x) = *self.0 { Some(x) } else { None }
        }

        #[inline(always)]
        pub fn try_ivar(self) -> Option<LevelVarId> {
            if let LevelData::IVar(x) = *self.0 { Some(x) } else { None }
        }


        #[inline(always)]
        pub fn ptr_eq(self, other: Level) -> bool {
            core::ptr::eq(self.0, other.0)
        }
    }


    impl LevelAlloc for Arena {
        #[inline(always)]
        fn mkl_zero<'a>(&'a self) -> Level<'a> {
            Level::L0
        }

        #[inline(always)]
        fn mkl_succ<'a>(&'a self, of: Level<'a>) -> Level<'a> {
            Level(self.alloc_new(LevelData::Succ(of)))
        }

        #[inline(always)]
        fn mkl_max<'a>(&'a self, lhs: Level<'a>, rhs: Level<'a>) -> Level<'a> {
            Level(self.alloc_new(LevelData::Max(Pair { lhs, rhs })))
        }

        #[inline(always)]
        fn mkl_imax<'a>(&'a self, lhs: Level<'a>, rhs: Level<'a>) -> Level<'a> {
            Level(self.alloc_new(LevelData::IMax(Pair { lhs, rhs })))
        }

        #[inline(always)]
        fn mkl_param<'a>(&'a self, name: Atom, index: u32) -> Level<'a> {
            Level(self.alloc_new(LevelData::Param(Param { name, index })))
        }

        #[inline(always)]
        fn mkl_ivar<'a>(&'a self, id: LevelVarId) -> Level<'a> {
            Level(self.alloc_new(LevelData::IVar(id)))
        }

        fn mkl_nat<'a>(&'a self, n: u32) -> Level<'a> {
            match n {
                0 => Level::L0,
                1 => Level::L1,
                2 => Level::L2,
                3 => Level::L3,
                _ => {
                    let mut result = Level::L3;
                    for _ in 3..n {
                        result = self.mkl_succ(result);
                    }
                    result
                }
            }
        }
    }
}

