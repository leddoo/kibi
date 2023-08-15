use sti::growing_arena::GrowingArena;


pub mod syntax;
pub mod local_ctx;
pub mod ty_ctx;

pub use syntax::*;
pub use local_ctx::{LocalId, LocalCtx};
pub use ty_ctx::*;




#[derive(Clone, Copy)]
pub struct Alloc<'a> {
    pub arena: &'a GrowingArena,
}

impl<'a> Alloc<'a> {
    #[inline(always)]
    pub fn new(arena: &'a GrowingArena) -> Self {
        Self { arena }
    }


    #[inline(always)]
    pub fn mkl_zero(&self) -> LevelRef<'a> {
        Level::L0
    }

    #[inline(always)]
    pub fn mkl_succ(&self, of: LevelRef<'a>) -> LevelRef<'a> {
        self.arena.alloc_new(Level::mk_succ(of))
    }

    #[inline(always)]
    pub fn mkl_nat(&self, n: u32) -> LevelRef<'a> {
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
    pub fn mkl_max(&self, lhs: LevelRef<'a>, rhs: LevelRef<'a>) -> LevelRef<'a> {
        self.arena.alloc_new(Level::mk_max(lhs, rhs))
    }

    #[inline(always)]
    pub fn mkl_imax(&self, lhs: LevelRef<'a>, rhs: LevelRef<'a>) -> LevelRef<'a> {
        self.arena.alloc_new(Level::mk_imax(lhs, rhs))
    }


    #[inline(always)]
    pub fn mkt_sort(&self, level: LevelRef<'a>) -> TermRef<'a> {
        self.arena.alloc_new(Term::mk_sort(level))
    }

    #[inline(always)]
    pub fn mkt_bvar(&self, bvar: BVar) -> TermRef<'a> {
        self.arena.alloc_new(Term::mk_bvar(bvar))
    }

    #[inline(always)]
    pub fn mkt_local(&self, id: LocalId) -> TermRef<'a> {
        self.arena.alloc_new(Term::mk_local(id))
    }

    #[inline(always)]
    pub fn mkt_global(&self, id: GlobalId, levels: LevelList<'a>) -> TermRef<'a> {
        self.arena.alloc_new(Term::mk_global(id, levels))
    }

    #[inline(always)]
    pub fn mkt_forall_b(&self, binder: term::Binder<'a>) -> TermRef<'a> {
        self.arena.alloc_new(Term::mk_forall_b(binder))
    }

    #[inline(always)]
    pub fn mkt_forall(&self, name: u32, ty: TermRef<'a>, ret: TermRef<'a>) -> TermRef<'a> {
        self.arena.alloc_new(Term::mk_forall(name, ty, ret))
    }

    #[inline(always)]
    pub fn mkt_lambda_b(&self, binder: term::Binder<'a>) -> TermRef<'a> {
        self.arena.alloc_new(Term::mk_lambda_b(binder))
    }

    #[inline(always)]
    pub fn mkt_lambda(&self, name: u32, ty: TermRef<'a>, val: TermRef<'a>) -> TermRef<'a> {
        self.arena.alloc_new(Term::mk_lambda(name, ty, val))
    }

    #[inline(always)]
    pub fn mkt_apply_a(&self, apply: term::Apply<'a>) -> TermRef<'a> {
        self.arena.alloc_new(Term::mk_apply_a(apply))
    }

    #[inline(always)]
    pub fn mkt_apply(&self, fun: TermRef<'a>, arg: TermRef<'a>) -> TermRef<'a> {
        self.arena.alloc_new(Term::mk_apply(fun, arg))
    }

    #[inline(always)]
    pub fn mkt_apps(&self, fun: TermRef<'a>, args: &[TermRef<'a>]) -> TermRef<'a> {
        let mut result = fun;
        for arg in args {
            result = self.mkt_apply(result, arg);
        }
        return result;
    }

    #[inline(always)]
    pub fn mkt_nat(&self) -> TermRef<'a> {
        self.arena.alloc_new(Term::mk_nat())
    }

    #[inline(always)]
    pub fn mkt_nat_zero(&self) -> TermRef<'a> {
        self.arena.alloc_new(Term::mk_nat_zero())
    }

    #[inline(always)]
    pub fn mkt_nat_succ(&self) -> TermRef<'a> {
        self.arena.alloc_new(Term::mk_nat_succ())
    }

    #[inline(always)]
    pub fn mkt_nat_rec(&self, r: LevelRef<'a>) -> TermRef<'a> {
        self.arena.alloc_new(Term::mk_nat_rec(r))
    }

    pub fn mkt_nat_rec_ty(&self, r: LevelRef<'a>) -> TermRef<'a> {
        self.mkt_forall(0,
            // M: Nat -> Sort(r)
            self.mkt_forall(0,
                Term::NAT,
                self.mkt_sort(r)),
        self.mkt_forall(0,
            // M(0)
            self.mkt_apply(
                self.mkt_bvar(BVar(0)),
                Term::NAT_ZERO),
        self.mkt_forall(0,
            // Π(n, ih) => M(n.succ())
            self.mkt_forall(0,
                // n: Nat
                Term::NAT,
            self.mkt_forall(0,
                // ih: M(n)
                self.mkt_apply(
                    self.mkt_bvar(BVar(2)),
                    self.mkt_bvar(BVar(0))),
                // -> M(n.succ())
                self.mkt_apply(
                    self.mkt_bvar(BVar(3)),
                    self.mkt_apply(
                        Term::NAT_SUCC,
                        self.mkt_bvar(BVar(1)))))),
        self.mkt_forall(0,
            // n: Nat
            Term::NAT,
            // -> M(n)
            self.mkt_apply(
                self.mkt_bvar(BVar(3)),
                self.mkt_bvar(BVar(0)))))))
    }

    pub fn mkt_nat_val(&self, n: u32) -> TermRef<'a> {
        let mut result = Term::NAT_ZERO;
        for _ in 0..n {
            result = self.mkt_apply(Term::NAT_SUCC, result);
        }
        return result;
    }


    #[inline(always)]
    pub fn mkt_eq(&self, l: LevelRef<'a>) -> TermRef<'a> {
        self.arena.alloc_new(Term::mk_eq(l))
    }

    #[inline(always)]
    pub fn mkt_eq_refl(&self, l: LevelRef<'a>) -> TermRef<'a> {
        self.arena.alloc_new(Term::mk_eq_refl(l))
    }

    #[inline(always)]
    pub fn mkt_eq_rec(&self, l: LevelRef<'a>, r: LevelRef<'a>) -> TermRef<'a> {
        self.arena.alloc_new(Term::mk_eq_rec(l, r))
    }
}

