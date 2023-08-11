use sti::growing_arena::GrowingArena;
use sti::vec::Vec;

use super::local_ctx::LocalId;


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

    // @temp
    Nat,
    NatZero,
    NatSucc,
    NatRec(LevelRef<'a>),

    Eq,
    EqRefl,
    EqRec(LevelRef<'a>),
}


#[derive(Clone, Copy, Debug)]
pub struct BVar(pub u32);

#[derive(Clone, Copy, Debug)]
pub struct GlobalId(pub u32);


pub mod term {
    use super::*;

    #[derive(Clone, Copy, Debug)]
    pub struct Global<'a> {
        pub id: GlobalId,
        pub levels: LevelList<'a>,
    }

    #[derive(Clone, Copy, Debug)]
    pub struct Binder<'a> {
        pub name: u32,
        pub ty:  TermRef<'a>,
        pub val: TermRef<'a>,
    }

    #[derive(Clone, Copy, Debug)]
    pub struct Apply<'a> {
        pub fun: TermRef<'a>,
        pub arg: TermRef<'a>,
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
}


impl<'a> term::Binder<'a> {
    pub fn update(&self, new_ty: TermRef<'a>, new_val: TermRef<'a>) -> Option<Self> {
        if new_ty.ptr_eq(self.ty) && new_val.ptr_eq(self.val) {
            return None;
        }
        Some(Self { name: self.name, ty: new_ty, val: new_val })
    }
}

impl<'a> term::Apply<'a> {
    pub fn update(&self, new_fun: TermRef<'a>, new_arg: TermRef<'a>) -> Option<Self> {
        if new_fun.ptr_eq(self.fun) && new_arg.ptr_eq(self.arg) {
            return None;
        }
        Some(Self { fun: new_fun, arg: new_arg })
    }
}


impl<'a> Term<'a> {
    #[inline(always)]
    pub const fn mk_sort(level: LevelRef<'a>) -> Self {
        Self { kind: TermKind::Sort(level) }
    }

    #[inline(always)]
    pub const fn mk_bvar(bvar: BVar) -> Self {
        Self { kind: TermKind::BVar(bvar) }
    }

    #[inline(always)]
    pub const fn mk_local(id: LocalId) -> Self {
        Self { kind: TermKind::Local(id) }
    }

    #[inline(always)]
    pub const fn mk_global(id: GlobalId, levels: LevelList<'a>) -> Self {
        Self { kind: TermKind::Global(term::Global { id, levels }) }
    }

    #[inline(always)]
    pub const fn mk_forall_b(binder: term::Binder<'a>) -> Self {
        Self { kind: TermKind::Forall(binder) }
    }

    #[inline(always)]
    pub const fn mk_forall(name: u32, ty: TermRef<'a>, ret: TermRef<'a>) -> Self {
        Self::mk_forall_b(term::Binder { name, ty, val: ret })
    }

    #[inline(always)]
    pub const fn mk_lambda_b(binder: term::Binder<'a>) -> Self {
        Self { kind: TermKind::Lambda(binder) }
    }

    #[inline(always)]
    pub const fn mk_lambda(name: u32, ty: TermRef<'a>, val: TermRef<'a>) -> Self {
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
    pub fn mk_apps(fun: TermRef<'a>, args: &[TermRef<'a>], alloc: &'a GrowingArena) -> TermRef<'a> {
        let mut result = fun;
        for arg in args {
            result = alloc.alloc_new(Term::mk_apply(result, arg));
        }
        return result;
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
    pub const fn mk_nat_rec(l: LevelRef<'a>) -> Self {
        Self { kind: TermKind::NatRec(l) }
    }

    #[inline(always)]
    pub const fn mk_eq() -> Self {
        Self { kind: TermKind::Eq }
    }

    #[inline(always)]
    pub const fn mk_eq_zero() -> Self {
        Self { kind: TermKind::EqRefl }
    }

    #[inline(always)]
    pub const fn mk_eq_rec(l: LevelRef<'a>) -> Self {
        Self { kind: TermKind::EqRec(l) }
    }


    #[inline(always)]
    pub fn is_sort(&self) -> bool { matches!(self.kind, TermKind::Sort(_)) }

    #[inline(always)]
    pub fn is_bvar(&self) -> bool { matches!(self.kind, TermKind::BVar(_)) }

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


    pub fn closed(&self) -> bool {
        unimplemented!()
    }


    pub fn replace<F: Fn(TermRef<'a>, u32, &'a GrowingArena) -> Option<TermRef<'a>>>
        (&'a self, alloc: &'a GrowingArena, f: F) -> TermRef<'a>
    {
        self.replace_ex(0, alloc, &f)
    }

    pub fn replace_ex<F: Fn(TermRef<'a>, u32, &'a GrowingArena) -> Option<TermRef<'a>>>
        (&'a self, offset: u32, alloc: &'a GrowingArena, f: &F) -> TermRef<'a>
    {
        if let Some(new) = f(self, offset, alloc) {
            return new;
        }

        match self.kind {
            TermKind::Sort(_) |
            TermKind::BVar(_) |
            TermKind::Local(_) |
            TermKind::Global(_) => self,

            TermKind::Forall(b) |
            TermKind::Lambda(b) => {
                let new_b = b.update(
                    b.ty.replace_ex(offset, alloc, f),
                    b.val.replace_ex(offset + 1, alloc, f));

                if let Some(b) = new_b {
                    alloc.alloc_new(
                        if self.is_forall() { Term::mk_forall_b(b) }
                        else                { Term::mk_lambda_b(b) })
                }
                else { self }
            }

            TermKind::Apply(a) => {
                let new_a = a.update(
                    a.fun.replace_ex(offset, alloc, f),
                    a.arg.replace_ex(offset, alloc, f));

                if let Some(a) = new_a {
                    alloc.alloc_new(Term::mk_apply_a(a))
                }
                else { self }
            }

            TermKind::Nat |
            TermKind::NatZero |
            TermKind::NatSucc |
            TermKind::NatRec(_) |
            TermKind::Eq |
            TermKind::EqRefl |
            TermKind::EqRec(_) => self
        }
    }


    pub fn abstracc(&'a self, id: LocalId, alloc: &'a GrowingArena) -> TermRef<'a> {
        // @speed: has_local. or even max_local?
        self.replace(alloc, |at, offset, alloc| {
            if let TermKind::Local(l) = at.kind {
                if l == id {
                    return Some(alloc.alloc_new(
                        Term::mk_bvar(BVar(offset))));
                }
            }
            None
        })
    }

    pub fn instantiate(&'a self, subst: TermRef<'a>, alloc: &'a GrowingArena) -> TermRef<'a> {
        // @speed: max_bvar.
        self.replace(alloc, |at, offset, _| {
            if let TermKind::BVar(b) = at.kind {
                if b.0 == offset {
                    return Some(subst);
                }
            }
            None
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


    // doesn't check for `ptr_eq` of old `app_fun`.
    pub fn replace_app_fun(&self, new_fun: TermRef<'a>, alloc: &'a GrowingArena) -> TermRef<'a> {
        if let TermKind::Apply(app) = self.kind {
            let fun = app.fun.replace_app_fun(new_fun, alloc);
            return alloc.alloc_new(Term::mk_apply(fun, app.arg));
        }
        return new_fun;
    }
}

