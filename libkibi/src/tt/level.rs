use sti::arena::Arena;


pub use crate::string_table::Atom;
pub use crate::elab::LevelVarId;


pub type LevelRef<'a> = &'a Level<'a>;

pub type LevelList<'a> = &'a [LevelRef<'a>];


#[derive(Clone, Debug)]
pub struct Level<'a> {
    pub data: LevelData<'a>,
}

#[derive(Clone, Copy, Debug)]
pub enum LevelData<'a> {
    Zero,
    Succ(LevelRef<'a>),
    Max(Pair<'a>),
    IMax(Pair<'a>),
    Param(Param),
    IVar(LevelVarId),

    // sync: `Level::syntax_eq`
}


#[derive(Clone, Copy, Debug)]
pub struct Pair<'a> {
    pub lhs: LevelRef<'a>,
    pub rhs: LevelRef<'a>,
}

#[derive(Clone, Copy, Debug)]
pub struct Param {
    pub name: Atom,
    pub index: u32,
}


impl<'a> Level<'a> {
    pub const L0: LevelRef<'static> = &Level::mk_zero();
    pub const L1: LevelRef<'static> = &Level::mk_succ(Level::L0);
    pub const L2: LevelRef<'static> = &Level::mk_succ(Level::L1);
    pub const L3: LevelRef<'static> = &Level::mk_succ(Level::L2);

    #[inline(always)]
    pub const fn mk_zero() -> Self {
        Self { data: LevelData::Zero }
    }

    #[inline(always)]
    pub const fn mk_succ(of: LevelRef<'a>) -> Self {
        Self { data: LevelData::Succ(of) }
    }

    #[inline(always)]
    pub const fn mk_max(lhs: LevelRef<'a>, rhs: LevelRef<'a>) -> Self {
        Self { data: LevelData::Max(Pair { lhs, rhs }) }
    }

    #[inline(always)]
    pub const fn mk_imax(lhs: LevelRef<'a>, rhs: LevelRef<'a>) -> Self {
        Self { data: LevelData::IMax(Pair { lhs, rhs }) }
    }

    #[inline(always)]
    pub const fn mk_param(name: Atom, index: u32) -> Self {
        Self { data: LevelData::Param(Param { name, index }) }
    }

    #[inline(always)]
    pub const fn mk_ivar(id: LevelVarId) -> Self {
        Self { data: LevelData::IVar(id) }
    }


    #[inline(always)]
    pub fn ptr_eq(&self, other: &Level) -> bool {
        core::ptr::eq(self, other)
    }

    #[inline(always)]
    pub fn syntax_eq(&self, other: &Level) -> bool {
        if self.ptr_eq(other) {
            return true;
        }

        use LevelData::*;
        match (self.data, other.data) {
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
    pub fn list_syntax_eq(a: &[LevelRef], b: &[LevelRef]) -> bool {
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


    pub fn has_ivars(&self) -> bool {
        self.find(|at| { Some(at.is_ivar()) }).is_some()
    }


    #[inline(always)]
    pub const fn is_zero(&self) -> bool { matches!(self.data, LevelData::Zero) }

    #[inline(always)]
    pub const fn is_succ(&self) -> bool { matches!(self.data, LevelData::Succ(_)) }

    #[inline(always)]
    pub const fn is_max(&self) -> bool { matches!(self.data, LevelData::Max(_)) }

    #[inline(always)]
    pub const fn is_imax(&self) -> bool { matches!(self.data, LevelData::IMax(_)) }

    #[inline(always)]
    pub const fn is_param(&self) -> bool { matches!(self.data, LevelData::Param(_)) }

    #[inline(always)]
    pub const fn is_ivar(&self) -> bool { matches!(self.data, LevelData::IVar(_)) }

    pub fn non_zero(&self) -> bool {
        match self.data {
            LevelData::Zero     => false,
            LevelData::Succ(_)  => true,
            LevelData::Max(p)   => p.lhs.non_zero() || p.rhs.non_zero(),
            LevelData::IMax(p)  => p.rhs.non_zero(),
            LevelData::Param(_) => false,
            LevelData::IVar(_)   => false,
        }
    }


    pub fn to_offset(&'a self) -> (LevelRef<'a>, u32) {
        let mut at = self;
        let mut offset = 0;
        while let LevelData::Succ(l) = at.data {
            offset += 1;
            at = l;
        }
        return (at, offset);
    }

    #[inline(always)]
    pub fn to_nat(&self) -> Option<u32> {
        let (l, offset) = self.to_offset();
        l.is_zero().then_some(offset)
    }



    #[inline(always)]
    pub fn succ(&'a self, alloc: &'a Arena) -> LevelRef<'a> {
        alloc.mkl_succ(self)
    }

    #[inline(always)]
    pub fn offset(&'a self, n: u32, alloc: &'a Arena) -> LevelRef<'a> {
        let mut result = self;
        for _ in 0..n {
            result = result.succ(alloc)
        }
        return result;
    }

    #[inline(always)]
    pub fn max(&'a self, other: LevelRef<'a>, alloc: &'a Arena) -> LevelRef<'a> {
        // @temp: proper impl.
        alloc.mkl_max(self, other)
    }

    #[inline(always)]
    pub fn imax(&'a self, other: LevelRef<'a>, alloc: &'a Arena) -> LevelRef<'a> {
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



    pub fn find<F: Fn(LevelRef<'a>) -> Option<bool>>
        (&'a self, f: F) -> Option<LevelRef<'a>>
    {
        self.find_ex(&f)
    }

    pub fn find_ex<F: Fn(LevelRef<'a>) -> Option<bool>>
        (&'a self, f: &F) -> Option<LevelRef<'a>>
    {
        if let Some(true) = f(self) {
            return Some(self);
        }

        match self.data {
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


    pub fn replace<F: Fn(LevelRef<'a>, &'a Arena) -> Option<LevelRef<'a>>>
        (&'a self, alloc: &'a Arena, f: F) -> LevelRef<'a>
    {
        self.replace_ex(alloc, &f)
    }

    pub fn replace_ex<F: Fn(LevelRef<'a>, &'a Arena) -> Option<LevelRef<'a>>>
        (&'a self, alloc: &'a Arena, f: &F) -> LevelRef<'a>
    {
        if let Some(new) = f(self, alloc) {
            return new;
        }

        match self.data {
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

    pub fn instantiate_params(&'a self, subst: LevelList<'a>, alloc: &'a Arena) -> Option<LevelRef<'a>> {
        // @speed: has_param.
        let result = self.replace(alloc, |at, _| {
            if let LevelData::Param(p) = at.data {
                return Some(&subst[p.index as usize]);
            }
            None
        });
        (!result.ptr_eq(self)).then_some(result)
    }
}




pub trait LevelAlloc {
    fn mkl_zero<'a>(&'a self) -> LevelRef<'a>;
    fn mkl_succ<'a>(&'a self, of: LevelRef<'a>) -> LevelRef<'a>;
    fn mkl_max<'a>(&'a self, lhs: LevelRef<'a>, rhs: LevelRef<'a>) -> LevelRef<'a>;
    fn mkl_imax<'a>(&'a self, lhs: LevelRef<'a>, rhs: LevelRef<'a>) -> LevelRef<'a>;
    fn mkl_param<'a>(&'a self, name: Atom, index: u32) -> LevelRef<'a>;
    fn mkl_ivar<'a>(&'a self, id: LevelVarId) -> LevelRef<'a>;
    fn mkl_nat<'a>(&'a self, n: u32) -> LevelRef<'a>;
}



mod impel {
    use super::*;

    impl LevelAlloc for Arena {
        #[inline(always)]
        fn mkl_zero<'a>(&'a self) -> LevelRef<'a> {
            Level::L0
        }

        #[inline(always)]
        fn mkl_succ<'a>(&'a self, of: LevelRef<'a>) -> LevelRef<'a> {
            self.alloc_new(Level::mk_succ(of))
        }

        #[inline(always)]
        fn mkl_max<'a>(&'a self, lhs: LevelRef<'a>, rhs: LevelRef<'a>) -> LevelRef<'a> {
            self.alloc_new(Level::mk_max(lhs, rhs))
        }

        #[inline(always)]
        fn mkl_imax<'a>(&'a self, lhs: LevelRef<'a>, rhs: LevelRef<'a>) -> LevelRef<'a> {
            self.alloc_new(Level::mk_imax(lhs, rhs))
        }

        #[inline(always)]
        fn mkl_param<'a>(&'a self, name: Atom, index: u32) -> LevelRef<'a> {
            self.alloc_new(Level::mk_param(name, index))
        }

        #[inline(always)]
        fn mkl_ivar<'a>(&'a self, id: LevelVarId) -> LevelRef<'a> {
            self.alloc_new(Level::mk_ivar(id))
        }

        fn mkl_nat<'a>(&'a self, n: u32) -> LevelRef<'a> {
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

