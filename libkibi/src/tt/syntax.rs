use sti::arena::Arena;
use sti::vec::Vec;

use crate::string_table::{Atom, atoms};

pub use crate::elab::{LevelVarId, TermVarId};
pub use crate::env::SymbolId;

pub use super::local_ctx::ScopeId;


pub type LevelRef<'a> = &'a Level<'a>;

pub type LevelList<'a> = &'a [LevelRef<'a>];


#[derive(Clone, Debug)]
pub struct Level<'a> {
    pub kind: LevelKind<'a>,
}

#[derive(Clone, Copy, Debug)]
pub enum LevelKind<'a> {
    Zero,
    Succ(LevelRef<'a>),
    Max(level::Pair<'a>),
    IMax(level::Pair<'a>),
    Param(level::Param),
    IVar(LevelVarId),

    // sync: `Level::syntax_eq`
}


pub mod level {
    use super::*;


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
}



pub type TermRef<'a> = &'a Term<'a>;

#[derive(Clone, Debug)]
pub struct Term<'a> {
    pub kind: TermKind<'a>
}

#[derive(Clone, Copy, Debug)]
pub enum TermKind<'a> {
    Sort(LevelRef<'a>),

    Bound(BVar),
    Local(ScopeId),
    Global(term::Global<'a>),
    IVar(TermVarId),

    Forall(term::Binder<'a>),
    Lambda(term::Binder<'a>),
    Apply(term::Apply<'a>),

    Nat,
    NatZero,
    NatSucc,
    NatRec(LevelRef<'a>),

    Eq(LevelRef<'a>),
    EqRefl(LevelRef<'a>),
    EqRec(LevelRef<'a>, LevelRef<'a>),

    // sync:
    // - `Term::syntax_eq`.
    // - @pp_needs_parens.
}


#[derive(Clone, Copy, Debug, PartialEq)]
pub struct BVar(pub u32);


pub mod term {
    use super::*;

    #[derive(Clone, Copy, Debug)]
    pub struct Global<'a> {
        pub id: SymbolId,
        pub levels: LevelList<'a>,
    }

    #[derive(Clone, Copy, Debug)]
    pub struct Binder<'a> {
        pub name: Atom,
        pub ty:  TermRef<'a>,
        pub val: TermRef<'a>,
    }

    #[derive(Clone, Copy, Debug)]
    pub struct Apply<'a> {
        pub fun: TermRef<'a>,
        pub arg: TermRef<'a>,
    }
}


pub trait TTArena {
    fn mkl_zero<'a>(&'a self) -> LevelRef<'a>;
    fn mkl_succ<'a>(&'a self, of: LevelRef<'a>) -> LevelRef<'a>;
    fn mkl_max<'a>(&'a self, lhs: LevelRef<'a>, rhs: LevelRef<'a>) -> LevelRef<'a>;
    fn mkl_imax<'a>(&'a self, lhs: LevelRef<'a>, rhs: LevelRef<'a>) -> LevelRef<'a>;
    fn mkl_param<'a>(&'a self, name: Atom, index: u32) -> LevelRef<'a>;
    fn mkl_ivar<'a>(&'a self, id: LevelVarId) -> LevelRef<'a>;
    fn mkl_nat<'a>(&'a self, n: u32) -> LevelRef<'a>;

    fn mkt_sort<'a>(&'a self, level: LevelRef<'a>) -> TermRef<'a>;
    fn mkt_bound<'a>(&'a self, bvar: BVar) -> TermRef<'a>;
    fn mkt_local<'a>(&'a self, id: ScopeId) -> TermRef<'a>;
    fn mkt_global<'a>(&'a self, id: SymbolId, levels: LevelList<'a>) -> TermRef<'a>;
    fn mkt_ivar<'a>(&'a self, id: TermVarId) -> TermRef<'a>;
    fn mkt_forall_b<'a>(&'a self, binder: term::Binder<'a>) -> TermRef<'a>;
    fn mkt_forall<'a>(&'a self, name: Atom, ty: TermRef<'a>, ret: TermRef<'a>) -> TermRef<'a>;
    fn mkt_lambda_b<'a>(&'a self, binder: term::Binder<'a>) -> TermRef<'a>;
    fn mkt_lambda<'a>(&'a self, name: Atom, ty: TermRef<'a>, val: TermRef<'a>) -> TermRef<'a>;
    fn mkt_apply_a<'a>(&'a self, apply: term::Apply<'a>) -> TermRef<'a>;
    fn mkt_apply<'a>(&'a self, fun: TermRef<'a>, arg: TermRef<'a>) -> TermRef<'a>;
    fn mkt_apps<'a>(&'a self, fun: TermRef<'a>, args: &[TermRef<'a>]) -> TermRef<'a>;

    fn mkt_nat<'a>(&'a self) -> TermRef<'a>;
    fn mkt_nat_zero<'a>(&'a self) -> TermRef<'a>;
    fn mkt_nat_succ<'a>(&'a self) -> TermRef<'a>;
    fn mkt_nat_rec<'a>(&'a self, r: LevelRef<'a>) -> TermRef<'a>;
    fn mkt_nat_rec_ty<'a>(&'a self, r: LevelRef<'a>) -> TermRef<'a>;
    fn mkt_nat_val<'a>(&'a self, n: u32) -> TermRef<'a>;


    fn mkt_eq<'a>(&'a self, l: LevelRef<'a>) -> TermRef<'a>;
    fn mkt_eq_refl<'a>(&'a self, l: LevelRef<'a>) -> TermRef<'a>;
    fn mkt_eq_rec<'a>(&'a self, l: LevelRef<'a>, r: LevelRef<'a>) -> TermRef<'a>;
    fn mkt_eq_ty<'a>(&'a self, l: LevelRef<'a>) -> TermRef<'a>;
    fn mkt_eq_refl_ty<'a>(&'a self, l: LevelRef<'a>) -> TermRef<'a>;
    fn mkt_eq_rec_ty<'a>(&'a self, l: LevelRef<'a>, r: LevelRef<'a>) -> TermRef<'a>;
}

impl TTArena for Arena {
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


    #[inline(always)]
    fn mkt_sort<'a>(&'a self, level: LevelRef<'a>) -> TermRef<'a> {
        self.alloc_new(Term::mk_sort(level))
    }

    #[inline(always)]
    fn mkt_bound<'a>(&'a self, bvar: BVar) -> TermRef<'a> {
        self.alloc_new(Term::mk_bound(bvar))
    }

    #[inline(always)]
    fn mkt_local<'a>(&'a self, id: ScopeId) -> TermRef<'a> {
        self.alloc_new(Term::mk_local(id))
    }

    #[inline(always)]
    fn mkt_global<'a>(&'a self, id: SymbolId, levels: LevelList<'a>) -> TermRef<'a> {
        self.alloc_new(Term::mk_global(id, levels))
    }

    #[inline(always)]
    fn mkt_ivar<'a>(&'a self, id: TermVarId) -> TermRef<'a> {
        self.alloc_new(Term::mk_ivar(id))
    }

    #[inline(always)]
    fn mkt_forall_b<'a>(&'a self, binder: term::Binder<'a>) -> TermRef<'a> {
        self.alloc_new(Term::mk_forall_b(binder))
    }

    #[inline(always)]
    fn mkt_forall<'a>(&'a self, name: Atom, ty: TermRef<'a>, ret: TermRef<'a>) -> TermRef<'a> {
        self.alloc_new(Term::mk_forall(name, ty, ret))
    }

    #[inline(always)]
    fn mkt_lambda_b<'a>(&'a self, binder: term::Binder<'a>) -> TermRef<'a> {
        self.alloc_new(Term::mk_lambda_b(binder))
    }

    #[inline(always)]
    fn mkt_lambda<'a>(&'a self, name: Atom, ty: TermRef<'a>, val: TermRef<'a>) -> TermRef<'a> {
        self.alloc_new(Term::mk_lambda(name, ty, val))
    }

    #[inline(always)]
    fn mkt_apply_a<'a>(&'a self, apply: term::Apply<'a>) -> TermRef<'a> {
        self.alloc_new(Term::mk_apply_a(apply))
    }

    #[inline(always)]
    fn mkt_apply<'a>(&'a self, fun: TermRef<'a>, arg: TermRef<'a>) -> TermRef<'a> {
        self.alloc_new(Term::mk_apply(fun, arg))
    }

    #[inline(always)]
    fn mkt_apps<'a>(&'a self, fun: TermRef<'a>, args: &[TermRef<'a>]) -> TermRef<'a> {
        let mut result = fun;
        for arg in args {
            result = self.mkt_apply(result, arg);
        }
        return result;
    }

    #[inline(always)]
    fn mkt_nat<'a>(&'a self) -> TermRef<'a> {
        self.alloc_new(Term::mk_nat())
    }

    #[inline(always)]
    fn mkt_nat_zero<'a>(&'a self) -> TermRef<'a> {
        self.alloc_new(Term::mk_nat_zero())
    }

    #[inline(always)]
    fn mkt_nat_succ<'a>(&'a self) -> TermRef<'a> {
        self.alloc_new(Term::mk_nat_succ())
    }

    #[inline(always)]
    fn mkt_nat_rec<'a>(&'a self, r: LevelRef<'a>) -> TermRef<'a> {
        self.alloc_new(Term::mk_nat_rec(r))
    }

    fn mkt_nat_rec_ty<'a>(&'a self, r: LevelRef<'a>) -> TermRef<'a> {
        self.mkt_forall(atoms::M,
            // M: Nat -> Sort(r)
            self.mkt_forall(atoms::Nat,
                Term::NAT,
                self.mkt_sort(r)),
        self.mkt_forall(atoms::m_zero,
            // m_zero: M(0)
            self.mkt_apply(
                self.mkt_bound(BVar(0)),
                Term::NAT_ZERO),
        self.mkt_forall(atoms::m_succ,
            // m_succ: Π(n, ih) => M(n.succ())
            self.mkt_forall(atoms::n,
                // n: Nat
                Term::NAT,
            self.mkt_forall(atoms::ih,
                // ih: M(n)
                self.mkt_apply(
                    self.mkt_bound(BVar(2)),
                    self.mkt_bound(BVar(0))),
                // -> M(n.succ())
                self.mkt_apply(
                    self.mkt_bound(BVar(3)),
                    self.mkt_apply(
                        Term::NAT_SUCC,
                        self.mkt_bound(BVar(1)))))),
        self.mkt_forall(atoms::mp,
            // mp: Nat
            Term::NAT,
            // -> M(mp)
            self.mkt_apply(
                self.mkt_bound(BVar(3)),
                self.mkt_bound(BVar(0)))))))
    }

    fn mkt_nat_val<'a>(&'a self, n: u32) -> TermRef<'a> {
        let mut result = Term::NAT_ZERO;
        for _ in 0..n {
            result = self.mkt_apply(Term::NAT_SUCC, result);
        }
        return result;
    }


    #[inline(always)]
    fn mkt_eq<'a>(&'a self, l: LevelRef<'a>) -> TermRef<'a> {
        self.alloc_new(Term::mk_eq(l))
    }

    #[inline(always)]
    fn mkt_eq_refl<'a>(&'a self, l: LevelRef<'a>) -> TermRef<'a> {
        self.alloc_new(Term::mk_eq_refl(l))
    }

    #[inline(always)]
    fn mkt_eq_rec<'a>(&'a self, l: LevelRef<'a>, r: LevelRef<'a>) -> TermRef<'a> {
        self.alloc_new(Term::mk_eq_rec(l, r))
    }

    fn mkt_eq_ty<'a>(&'a self, l: LevelRef<'a>) -> TermRef<'a> {
        self.mkt_forall(atoms::T,
            // T: Sort(l)
            self.mkt_sort(l),
        self.mkt_forall(atoms::a,
            // a: T
            self.mkt_bound(BVar(0)),
        self.mkt_forall(atoms::b,
            // b: T
            self.mkt_bound(BVar(1)),
            // -> Prop
            self.mkt_sort(self.mkl_zero()))))
    }

    fn mkt_eq_refl_ty<'a>(&'a self, l: LevelRef<'a>) -> TermRef<'a> {
        self.mkt_forall(atoms::T,
            // T: Sort(l)
            self.mkt_sort(l),
        self.mkt_forall(atoms::a,
            // a: T
            self.mkt_bound(BVar(0)),
            // -> Eq(T, a, a)
            self.mkt_apps(self.mkt_eq(l), &[
                self.mkt_bound(BVar(1)),
                self.mkt_bound(BVar(0)),
                self.mkt_bound(BVar(0)),
            ])))
    }

    fn mkt_eq_rec_ty<'a>(&'a self, l: LevelRef<'a>, r: LevelRef<'a>) -> TermRef<'a> {
        self.mkt_forall(atoms::T,
            // T: Sort(l)
            self.mkt_sort(l),
        self.mkt_forall(atoms::a,
            // a: T
            self.mkt_bound(BVar(0)),
        self.mkt_forall(atoms::M,
            // M: Π(b: T) -> Sort(r)
            self.mkt_forall(atoms::b,
                self.mkt_bound(BVar(1)),
                self.mkt_sort(r)),
        self.mkt_forall(atoms::m_refl,
            // m_refl: M(a)
            self.mkt_apply(
                self.mkt_bound(BVar(0)),
                self.mkt_bound(BVar(1))),
        self.mkt_forall(atoms::b,
            // b: T
            self.mkt_bound(BVar(3)),
        self.mkt_forall(atoms::mp,
            // mp: Eq(T, a, b)
            self.mkt_apps(self.mkt_eq(l), &[
                self.mkt_bound(BVar(4)),
                self.mkt_bound(BVar(3)),
                self.mkt_bound(BVar(0)),
            ]),
            // -> M(b)
            self.mkt_apply(
                self.mkt_bound(BVar(3)),
                self.mkt_bound(BVar(1)))))))))
    }
}


impl<'a> Level<'a> {
    pub const L0: LevelRef<'static> = &Level::mk_zero();
    pub const L1: LevelRef<'static> = &Level::mk_succ(Level::L0);
    pub const L2: LevelRef<'static> = &Level::mk_succ(Level::L1);
    pub const L3: LevelRef<'static> = &Level::mk_succ(Level::L2);

    #[inline(always)]
    pub const fn mk_zero() -> Self {
        Self { kind: LevelKind::Zero }
    }

    #[inline(always)]
    pub const fn mk_succ(of: LevelRef<'a>) -> Self {
        Self { kind: LevelKind::Succ(of) }
    }

    #[inline(always)]
    pub const fn mk_max(lhs: LevelRef<'a>, rhs: LevelRef<'a>) -> Self {
        Self { kind: LevelKind::Max(level::Pair { lhs, rhs }) }
    }

    #[inline(always)]
    pub const fn mk_imax(lhs: LevelRef<'a>, rhs: LevelRef<'a>) -> Self {
        Self { kind: LevelKind::IMax(level::Pair { lhs, rhs }) }
    }

    #[inline(always)]
    pub const fn mk_param(name: Atom, index: u32) -> Self {
        Self { kind: LevelKind::Param(level::Param { name, index }) }
    }

    #[inline(always)]
    pub const fn mk_ivar(id: LevelVarId) -> Self {
        Self { kind: LevelKind::IVar(id) }
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

        use LevelKind::*;
        match (self.kind, other.kind) {
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
    pub const fn is_zero(&self) -> bool { matches!(self.kind, LevelKind::Zero) }

    #[inline(always)]
    pub const fn is_succ(&self) -> bool { matches!(self.kind, LevelKind::Succ(_)) }

    #[inline(always)]
    pub const fn is_max(&self) -> bool { matches!(self.kind, LevelKind::Max(_)) }

    #[inline(always)]
    pub const fn is_imax(&self) -> bool { matches!(self.kind, LevelKind::IMax(_)) }

    #[inline(always)]
    pub const fn is_param(&self) -> bool { matches!(self.kind, LevelKind::Param(_)) }

    #[inline(always)]
    pub const fn is_ivar(&self) -> bool { matches!(self.kind, LevelKind::IVar(_)) }

    pub fn non_zero(&self) -> bool {
        match self.kind {
            LevelKind::Zero     => false,
            LevelKind::Succ(_)  => true,
            LevelKind::Max(p)   => p.lhs.non_zero() || p.rhs.non_zero(),
            LevelKind::IMax(p)  => p.rhs.non_zero(),
            LevelKind::Param(_) => false,
            LevelKind::IVar(_)   => false,
        }
    }


    pub fn to_offset(&'a self) -> (LevelRef<'a>, u32) {
        let mut at = self;
        let mut offset = 0;
        while let LevelKind::Succ(l) = at.kind {
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

        match self.kind {
            LevelKind::Zero => None,

            LevelKind::Succ(l) => l.find_ex(f),

            LevelKind::Max(p) |
            LevelKind::IMax(p) => {
                p.lhs.find_ex(f).or_else(||
                p.rhs.find_ex(f))
            }

            LevelKind::Param(_) |
            LevelKind::IVar(_) => None,
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

        match self.kind {
            LevelKind::Zero => self,

            LevelKind::Succ(of) => {
                let new_of = of.replace_ex(alloc, f);
                if new_of.ptr_eq(of) {
                    return self;
                }
                new_of.succ(alloc)
            }

            LevelKind::Max(p) |
            LevelKind::IMax(p) => {
                let new_lhs = p.lhs.replace_ex(alloc, f);
                let new_rhs = p.rhs.replace_ex(alloc, f);
                if new_lhs.ptr_eq(p.lhs) && new_rhs.ptr_eq(p.rhs) {
                    return self;
                }
                if self.is_max() { new_lhs.max(new_rhs, alloc)  }
                else             { new_lhs.imax(new_rhs, alloc) }
            }

            LevelKind::Param(_) => self,

            LevelKind::IVar(_) => self,
        }
    }

    pub fn instantiate_params(&'a self, subst: LevelList<'a>, alloc: &'a Arena) -> Option<LevelRef<'a>> {
        // @speed: has_param.
        let result = self.replace(alloc, |at, _| {
            if let LevelKind::Param(p) = at.kind {
                return Some(&subst[p.index as usize]);
            }
            None
        });
        (!result.ptr_eq(self)).then_some(result)
    }
}


impl<'a> term::Binder<'a> {
    pub fn update(&self, t: TermRef<'a>, alloc: &'a Arena, new_ty: TermRef<'a>, new_val: TermRef<'a>) -> TermRef<'a> {
        debug_assert!(t.is_forall() || t.is_lambda());

        if !new_ty.ptr_eq(self.ty) || !new_val.ptr_eq(self.val) {
            let b = Self { name: self.name, ty: new_ty, val: new_val };

            if t.is_forall() { alloc.mkt_forall_b(b) }
            else             { alloc.mkt_lambda_b(b) }
        }
        else { t }
    }
}

impl<'a> term::Apply<'a> {
    pub fn update(&self, t: TermRef<'a>, alloc: &'a Arena, new_fun: TermRef<'a>, new_arg: TermRef<'a>) -> TermRef<'a> {
        debug_assert!(t.is_apply());

        if !new_fun.ptr_eq(self.fun) || !new_arg.ptr_eq(self.arg) {
            alloc.mkt_apply_a(Self { fun: new_fun, arg: new_arg })
        }
        else { t }
    }
}


impl<'a> Term<'a> {
    pub const SORT_0: TermRef<'static> = &Term::mk_sort(Level::L0);
    pub const SORT_1: TermRef<'static> = &Term::mk_sort(Level::L1);

    pub const NAT: TermRef<'static> = &Term::mk_nat();
    pub const NAT_ZERO: TermRef<'static> = &Term::mk_nat_zero();
    pub const NAT_SUCC: TermRef<'static> = &Term::mk_nat_succ();
    pub const NAT_SUCC_TY: TermRef<'static> = &Term::mk_forall(Atom::NULL, Self::NAT, Self::NAT);

    #[inline(always)]
    pub const fn mk_sort(level: LevelRef<'a>) -> Self {
        Self { kind: TermKind::Sort(level) }
    }

    #[inline(always)]
    pub const fn mk_bound(bvar: BVar) -> Self {
        Self { kind: TermKind::Bound(bvar) }
    }

    #[inline(always)]
    pub const fn mk_local(id: ScopeId) -> Self {
        Self { kind: TermKind::Local(id) }
    }

    #[inline(always)]
    pub const fn mk_global(id: SymbolId, levels: LevelList<'a>) -> Self {
        Self { kind: TermKind::Global(term::Global { id, levels }) }
    }

    #[inline(always)]
    pub const fn mk_ivar(id: TermVarId) -> Self {
        Self { kind: TermKind::IVar(id) }
    }

    #[inline(always)]
    pub const fn mk_forall_b(binder: term::Binder<'a>) -> Self {
        Self { kind: TermKind::Forall(binder) }
    }

    #[inline(always)]
    pub const fn mk_forall(name: Atom, ty: TermRef<'a>, ret: TermRef<'a>) -> Self {
        Self::mk_forall_b(term::Binder { name, ty, val: ret })
    }

    #[inline(always)]
    pub const fn mk_lambda_b(binder: term::Binder<'a>) -> Self {
        Self { kind: TermKind::Lambda(binder) }
    }

    #[inline(always)]
    pub const fn mk_lambda(name: Atom, ty: TermRef<'a>, val: TermRef<'a>) -> Self {
        Self::mk_lambda_b(term::Binder { name, ty, val })
    }

    #[inline(always)]
    pub const fn mk_apply_a(apply: term::Apply<'a>) -> Self {
        Self { kind: TermKind::Apply(apply) }
    }

    #[inline(always)]
    pub const fn mk_apply(fun: TermRef<'a>, arg: TermRef<'a>) -> Self {
        Self::mk_apply_a(term::Apply { fun, arg })
    }

    #[inline(always)]
    pub const fn mk_nat() -> Self {
        Self { kind: TermKind::Nat }
    }

    #[inline(always)]
    pub const fn mk_nat_zero() -> Self {
        Self { kind: TermKind::NatZero }
    }

    #[inline(always)]
    pub const fn mk_nat_succ() -> Self {
        Self { kind: TermKind::NatSucc }
    }

    #[inline(always)]
    pub const fn mk_nat_rec(r: LevelRef<'a>) -> Self {
        Self { kind: TermKind::NatRec(r) }
    }

    #[inline(always)]
    pub const fn mk_eq(l: LevelRef<'a>) -> Self {
        Self { kind: TermKind::Eq(l) }
    }

    #[inline(always)]
    pub const fn mk_eq_refl(l: LevelRef<'a>) -> Self {
        Self { kind: TermKind::EqRefl(l) }
    }

    #[inline(always)]
    pub const fn mk_eq_rec(l: LevelRef<'a>, r: LevelRef<'a>) -> Self {
        Self { kind: TermKind::EqRec(l, r) }
    }


    #[inline(always)]
    pub fn is_sort(&self) -> bool { matches!(self.kind, TermKind::Sort(_)) }

    #[inline(always)]
    pub fn is_bvar(&self) -> bool { matches!(self.kind, TermKind::Bound(_)) }

    #[inline(always)]
    pub fn is_local(&self) -> bool { matches!(self.kind, TermKind::Local(_)) }

    #[inline(always)]
    pub fn is_global(&self) -> bool { matches!(self.kind, TermKind::Global(_)) }

    #[inline(always)]
    pub fn is_forall(&self) -> bool { matches!(self.kind, TermKind::Forall(_)) }

    #[inline(always)]
    pub fn is_lambda(&self) -> bool { matches!(self.kind, TermKind::Lambda(_)) }

    #[inline(always)]
    pub fn is_apply(&self) -> bool { matches!(self.kind, TermKind::Apply(_)) }


    #[inline(always)]
    pub fn ptr_eq(&self, other: &Term) -> bool {
        core::ptr::eq(self, other)
    }

    #[inline(always)]
    pub fn syntax_eq(&self, other: &Term) -> bool {
        if self.ptr_eq(other) {
            return true;
        }

        use TermKind::*;
        match (self.kind, other.kind) {
            (Sort(l1), Sort(l2)) => l1.syntax_eq(l2),

            (Bound(b1), Bound(b2)) => b1 == b2,

            (Local(l1), Local(l2)) => l1 == l2,

            (Global(g1), Global(g2)) =>
                g1.id == g2.id && Level::list_syntax_eq(g1.levels, g2.levels),

            (IVar(v1), IVar(v2)) => v1 == v2,

            (Forall(b1), Forall(b2)) |
            (Lambda(b1), Lambda(b2)) =>
               b1.ty.syntax_eq(b2.ty) && b1.val.syntax_eq(b2.val),

            (Apply(a1), Apply(a2)) =>
                a1.fun.syntax_eq(a2.fun) && a1.arg.syntax_eq(a2.arg),

            (Nat, Nat) => true,
            (NatZero, NatZero) => true,
            (NatSucc, NatSucc) => true,
            (NatRec(l1), NatRec(l2)) => l1.syntax_eq(l2),

            (Eq(l1), Eq(l2)) => l1.syntax_eq(l2),
            (EqRefl(l1), EqRefl(l2)) => l1.syntax_eq(l2),
            (EqRec(l1, r1), EqRec(l2, r2)) => l1.syntax_eq(l2) && r1.syntax_eq(r2),

            _ => false
        }
    }


    pub fn closed(&self) -> bool {
        self.find(|at, offset| {
            if let TermKind::Bound(BVar(i)) = at.kind {
                return Some(i >= offset);
            }
            None
        }).is_none()
    }

    pub fn has_locals(&self) -> bool {
        self.find(|at, _| {
            Some(at.is_local())
        }).is_some()
    }

    pub fn has_ivars(&self) -> bool {
        self.find(|at, _| {
            Some(match at.kind {
                TermKind::Sort(l) => l.has_ivars(),

                TermKind::Global(g) => {
                    let mut has_ivars = false;
                    for l in g.levels.iter() {
                        has_ivars |= l.has_ivars();
                    }
                    has_ivars
                }

                TermKind::IVar(_) => true,

                TermKind::NatRec(l) |
                TermKind::Eq(l) |
                TermKind::EqRefl(l) => l.has_ivars(),

                TermKind::EqRec(l, r) =>
                    l.has_ivars() || r.has_ivars(),

                _ => return None,
            })
        }).is_some()
    }


    pub fn find<F: Fn(TermRef<'a>, u32) -> Option<bool>>
        (&'a self, f: F) -> Option<TermRef<'a>>
    {
        self.find_ex(0, &f)
    }

    pub fn find_ex<F: Fn(TermRef<'a>, u32) -> Option<bool>>
        (&'a self, offset: u32, f: &F) -> Option<TermRef<'a>>
    {
        if let Some(true) = f(self, offset) {
            return Some(self);
        }

        match self.kind {
            TermKind::Sort(_) |
            TermKind::Bound(_) |
            TermKind::Local(_) |
            TermKind::Global(_) |
            TermKind::IVar(_) => None,

            TermKind::Forall(b) |
            TermKind::Lambda(b) => {
                b.ty.find_ex(offset, f).or_else(||
                b.val.find_ex(offset + 1, f))
            }

            TermKind::Apply(a) => {
                a.fun.find_ex(offset, f).or_else(||
                a.arg.find_ex(offset, f))
            }

            TermKind::Nat |
            TermKind::NatZero |
            TermKind::NatSucc |
            TermKind::NatRec(_) |
            TermKind::Eq(_) |
            TermKind::EqRefl(_) |
            TermKind::EqRec(_, _) => None,
        }
    }


    pub fn replace<F: FnMut(TermRef<'a>, u32, &'a Arena) -> Option<TermRef<'a>>>
        (&'a self, alloc: &'a Arena, mut f: F) -> TermRef<'a>
    {
        self.replace_ex(0, alloc, &mut f)
    }

    pub fn replace_ex<F: FnMut(TermRef<'a>, u32, &'a Arena) -> Option<TermRef<'a>>>
        (&'a self, offset: u32, alloc: &'a Arena, f: &mut F) -> TermRef<'a>
    {
        if let Some(new) = f(self, offset, alloc) {
            return new;
        }

        match self.kind {
            TermKind::Sort(_) |
            TermKind::Bound(_) |
            TermKind::Local(_) |
            TermKind::Global(_) |
            TermKind::IVar(_) => self,

            TermKind::Forall(b) |
            TermKind::Lambda(b) => {
                b.update(self, alloc,
                    b.ty.replace_ex(offset, alloc, f),
                    b.val.replace_ex(offset + 1, alloc, f))
            }

            TermKind::Apply(a) => {
                a.update(self, alloc,
                    a.fun.replace_ex(offset, alloc, f),
                    a.arg.replace_ex(offset, alloc, f))
            }

            TermKind::Nat |
            TermKind::NatZero |
            TermKind::NatSucc |
            TermKind::NatRec(_) |
            TermKind::Eq(_) |
            TermKind::EqRefl(_) |
            TermKind::EqRec(_, _) => self
        }
    }


    pub fn abstracc(&'a self, id: ScopeId, alloc: &'a Arena) -> TermRef<'a> {
        // @speed: has_local. or even max_local?
        self.replace(alloc, |at, offset, alloc| {
            if let TermKind::Local(l) = at.kind {
                if l == id {
                    return Some(alloc.mkt_bound(BVar(offset)));
                }
            }
            None
        })
    }

    pub fn instantiate(&'a self, subst: TermRef<'a>, alloc: &'a Arena) -> TermRef<'a> {
        // @speed: max_bvar.
        self.replace(alloc, |at, offset, _| {
            if let TermKind::Bound(b) = at.kind {
                if b.0 == offset {
                    return Some(subst);
                }
            }
            None
        })
    }

    pub fn replace_levels_flat<F: Fn(LevelRef<'a>, &'a Arena) -> Option<LevelRef<'a>>>
        (&self, alloc: &'a Arena, f: F) -> Option<TermRef<'a>>
    {
        match self.kind {
            TermKind::Sort(l) => {
                if let Some(l) = f(l, alloc) {
                    return Some(alloc.mkt_sort(l));
                }
            }

            TermKind::Global(g) => {
                let mut new_levels = Vec::new_in(alloc);

                for (i, l) in g.levels.iter().enumerate() {
                    if let Some(l) = f(l, alloc) {
                        if new_levels.len() == 0 {
                            new_levels.reserve_exact(g.levels.len());
                            for k in 0..i {
                                new_levels.push(g.levels[k]);
                            }
                        }

                        new_levels.push(l);
                    }
                    else if new_levels.len() != 0 {
                        new_levels.push(l)
                    }
                }

                if new_levels.len() != 0 {
                    debug_assert_eq!(new_levels.len(), g.levels.len());
                    let levels = new_levels.leak();
                    return Some(alloc.mkt_global(g.id, levels));
                }
            }

            TermKind::NatRec(r) => {
                if let Some(r) = f(r, alloc) {
                    return Some(alloc.mkt_nat_rec(r));
                }
            }

            TermKind::Eq(l) => {
                if let Some(l) = f(l, alloc) {
                    return Some(alloc.mkt_eq(l));
                }
            }

            TermKind::EqRefl(l) => {
                if let Some(l) = f(l, alloc) {
                    return Some(alloc.mkt_eq_refl(l));
                }
            }

            TermKind::EqRec(l, r) => {
                let new_l = f(l, alloc);
                let new_r = f(r, alloc);
                if new_l.is_some() || new_r.is_some() {
                    let l = new_l.unwrap_or(l);
                    let r = new_r.unwrap_or(r);
                    return Some(alloc.mkt_eq_rec(l, r));
                }
            }

            _ => ()
        }
        return None;
    }

    pub fn instantiate_level_params(&'a self, subst: LevelList<'a>, alloc: &'a Arena) -> TermRef<'a> {
        if subst.len() == 0 {
            return self;
        }

        // @speed: has_level_param.
        self.replace(alloc, |at, _, alloc| {
            at.replace_levels_flat(alloc, |l, alloc|
                l.instantiate_params(subst, alloc))
        })
    }


    #[inline]
    pub fn app_fun(&'a self) -> (TermRef<'a>, usize) {
        let mut f = self;
        let mut num_args = 0;
        while let TermKind::Apply(app) = f.kind {
            f = app.fun;
            num_args += 1;
        }
        return (f, num_args);
    }

    // @speed: arena.
    pub fn app_args_rev(&'a self) -> (TermRef<'a>, Vec<TermRef<'a>>) {
        let mut f = self;
        let mut args = Vec::new();
        while let TermKind::Apply(app) = f.kind {
            f = app.fun;
            args.push(app.arg);
        }
        return (f, args);
    }

    // @speed: arena.
    pub fn app_args(&'a self) -> (TermRef<'a>, Vec<TermRef<'a>>) {
        let (f, mut args) = self.app_args_rev();
        args.reverse();
        return (f, args);
    }


    // @speed: arena.
    pub fn try_ivar_app(&self) -> Option<(TermVarId, Vec<ScopeId>)> {
        let mut args = Vec::new();
        let var = rec(self, 0, &mut args)?;
        return Some((var, args));

        fn rec(at: TermRef, num_args: usize, result: &mut Vec<ScopeId>) -> Option<TermVarId> {
            if let TermKind::Apply(app) = at.kind {
                let TermKind::Local(local) = app.arg.kind else { return None };

                let var = rec(app.fun, num_args + 1, result)?;
                result.push(local);
                Some(var)
            }
            else if let TermKind::IVar(var) = at.kind {
                result.reserve_exact(num_args);
                Some(var)
            }
            else { None }
        }
    }



    // doesn't check for `ptr_eq` of old `app_fun`.
    pub fn replace_app_fun(&self, new_fun: TermRef<'a>, alloc: &'a Arena) -> TermRef<'a> {
        if let TermKind::Apply(app) = self.kind {
            let fun = app.fun.replace_app_fun(new_fun, alloc);
            return alloc.mkt_apply(fun, app.arg);
        }
        return new_fun;
    }
}

