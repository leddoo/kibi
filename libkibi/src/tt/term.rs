use sti::arena::Arena;
use sti::vec::Vec;


pub use crate::string_table::{Atom, atoms};
pub use crate::env::SymbolId;
pub use crate::elab::TermVarId;

pub use super::local_ctx::ScopeId;
use super::level::*;


pub type Term<'a> = impel::Term<'a>;


#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum TermKind {
    Sort,

    Bound,
    Local,
    Global,
    IVar,

    Forall,
    Lambda,
    Apply,

    Nat,
    NatZero,
    NatSucc,
    NatRec,

    Eq,
    EqRefl,
    EqRec,
}

#[derive(Clone, Copy, Debug)]
pub enum TermData<'a> {
    Sort(Level<'a>),

    Bound(BVar),
    Local(ScopeId),
    Global(Global<'a>),
    IVar(TermVarId),

    Forall(Binder<'a>),
    Lambda(Binder<'a>),
    Apply(Apply<'a>),

    Nat,
    NatZero,
    NatSucc,
    NatRec(Level<'a>),

    Eq(Level<'a>),
    EqRefl(Level<'a>),
    EqRec(Level<'a>, Level<'a>),

    // sync:
    // - `Term::syntax_eq`.
    // - @pp_needs_parens.
}


#[derive(Clone, Copy, Debug, PartialEq)]
pub struct BVar {
    pub offset: u32,
}


#[derive(Clone, Copy, Debug)]
pub struct Global<'a> {
    pub id: SymbolId,
    pub levels: LevelList<'a>,
}

#[derive(Clone, Copy, Debug)]
pub enum BinderKind {
    Explicit,
    Implicit,
}

#[derive(Clone, Copy, Debug)]
pub struct Binder<'a> {
    pub kind: BinderKind,
    pub name: Atom,
    pub ty:  Term<'a>,
    pub val: Term<'a>,
}

#[derive(Clone, Copy, Debug)]
pub struct Apply<'a> {
    pub fun: Term<'a>,
    pub arg: Term<'a>,
}


impl<'a> Binder<'a> {
    pub fn update(&self, t: Term<'a>, alloc: &'a Arena, new_ty: Term<'a>, new_val: Term<'a>) -> Term<'a> {
        debug_assert!(t.is_forall() || t.is_lambda());

        if !new_ty.ptr_eq(self.ty) || !new_val.ptr_eq(self.val) {
            let b = Self {
                kind: self.kind, name: self.name,
                ty: new_ty, val: new_val,
            };

            if t.is_forall() { alloc.mkt_forall_b(b) }
            else             { alloc.mkt_lambda_b(b) }
        }
        else { t }
    }
}

impl<'a> Apply<'a> {
    pub fn update(&self, t: Term<'a>, alloc: &'a Arena, new_fun: Term<'a>, new_arg: Term<'a>) -> Term<'a> {
        debug_assert!(t.is_apply());

        if !new_fun.ptr_eq(self.fun) || !new_arg.ptr_eq(self.arg) {
            alloc.mkt_apply_a(Self { fun: new_fun, arg: new_arg })
        }
        else { t }
    }
}


impl<'a> Term<'a> {
    #[inline(always)]
    pub fn is_sort(self) -> bool { self.kind() == TermKind::Sort }

    #[inline(always)]
    pub fn is_bvar(self) -> bool { self.kind() == TermKind::Bound }

    #[inline(always)]
    pub fn is_local(self) -> bool { self.kind() == TermKind::Local }

    #[inline(always)]
    pub fn is_global(self) -> bool { self.kind() == TermKind::Global }

    #[inline(always)]
    pub fn is_ivar(self) -> bool { self.kind() == TermKind::IVar }

    #[inline(always)]
    pub fn is_forall(self) -> bool { self.kind() == TermKind::Forall }

    #[inline(always)]
    pub fn is_lambda(self) -> bool { self.kind() == TermKind::Lambda }

    #[inline(always)]
    pub fn is_apply(self) -> bool { self.kind() == TermKind::Apply }


    #[inline(always)]
    pub fn syntax_eq(self, other: Term) -> bool {
        if self.ptr_eq(other) {
            return true;
        }

        use TermData::*;
        match (self.data(), other.data()) {
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


    pub fn closed(self) -> bool {
        //self.find(|at, offset| Some(at.try_bvar()?.offset >= offset)).is_none()
        self.max_succ_bvar() == 0
    }

    pub fn has_locals(self) -> bool {
        //self.find(|at, _| { Some(at.is_local()) }).is_some()
        self.max_succ_local() != 0
    }

    pub fn has_ivars(self) -> bool {
        self.find(|at, _| {
            Some(match at.data() {
                TermData::Sort(l) => l.has_ivars(),

                TermData::Global(g) => {
                    let mut has_ivars = false;
                    for l in g.levels.iter() {
                        has_ivars |= l.has_ivars();
                    }
                    has_ivars
                }

                TermData::IVar(_) => true,

                TermData::NatRec(l) |
                TermData::Eq(l) |
                TermData::EqRefl(l) => l.has_ivars(),

                TermData::EqRec(l, r) =>
                    l.has_ivars() || r.has_ivars(),

                _ => return None,
            })
        }).is_some()
    }


    pub fn find<F>(self, f: F) -> Option<Term<'a>>
    where F: Fn(Term<'a>, u32) -> Option<bool> {
        self.find_ex(0, &f)
    }

    pub fn find_ex<F>(self, offset: u32, f: &F) -> Option<Term<'a>>
    where F: Fn(Term<'a>, u32) -> Option<bool> {
        if let Some(true) = f(self, offset) {
            return Some(self);
        }

        match self.data() {
            TermData::Sort(_) |
            TermData::Bound(_) |
            TermData::Local(_) |
            TermData::Global(_) |
            TermData::IVar(_) => None,

            TermData::Forall(b) |
            TermData::Lambda(b) => {
                b.ty.find_ex(offset, f).or_else(||
                b.val.find_ex(offset + 1, f))
            }

            TermData::Apply(a) => {
                a.fun.find_ex(offset, f).or_else(||
                a.arg.find_ex(offset, f))
            }

            TermData::Nat |
            TermData::NatZero |
            TermData::NatSucc |
            TermData::NatRec(_) |
            TermData::Eq(_) |
            TermData::EqRefl(_) |
            TermData::EqRec(_, _) => None,
        }
    }


    pub fn replace<F>(self, alloc: &'a Arena, mut f: F) -> Term<'a>
    where F: FnMut(Term<'a>, u32, &'a Arena) -> Option<Term<'a>> {
        self.replace_ex(0, alloc, &mut f)
    }

    pub fn replace_ex<F>(self, offset: u32, alloc: &'a Arena, f: &mut F) -> Term<'a>
    where F: FnMut(Term<'a>, u32, &'a Arena) -> Option<Term<'a>> {
        if let Some(new) = f(self, offset, alloc) {
            return new;
        }

        match self.data() {
            TermData::Sort(_) |
            TermData::Bound(_) |
            TermData::Local(_) |
            TermData::Global(_) |
            TermData::IVar(_) => self,

            TermData::Forall(b) |
            TermData::Lambda(b) => {
                b.update(self, alloc,
                    b.ty.replace_ex(offset, alloc, f),
                    b.val.replace_ex(offset + 1, alloc, f))
            }

            TermData::Apply(a) => {
                a.update(self, alloc,
                    a.fun.replace_ex(offset, alloc, f),
                    a.arg.replace_ex(offset, alloc, f))
            }

            TermData::Nat |
            TermData::NatZero |
            TermData::NatSucc |
            TermData::NatRec(_) |
            TermData::Eq(_) |
            TermData::EqRefl(_) |
            TermData::EqRec(_, _) => self
        }
    }


    pub fn abstracc(self, id: ScopeId, alloc: &'a Arena) -> Term<'a> {
        self.replace(alloc, |at, offset, alloc| {
            if at.max_succ_local() < id.inner().saturating_add(1) {
                return Some(at);
            }

            let local = at.try_local()?;
            (local == id).then(|| alloc.mkt_bound(BVar { offset }))
        })
    }

    pub fn instantiate(self, subst: Term<'a>, alloc: &'a Arena) -> Term<'a> {
        self.replace(alloc, |at, offset, _| {
            if at.max_succ_bvar() < offset.saturating_add(1) {
                return Some(at);
            }

            let bvar = at.try_bvar()?;
            (bvar.offset == offset).then_some(subst)
        })
    }

    pub fn replace_levels_flat<F: Fn(Level<'a>, &'a Arena) -> Option<Level<'a>>>
        (self, alloc: &'a Arena, f: F) -> Option<Term<'a>>
    {
        match self.data() {
            TermData::Sort(l) => {
                if let Some(l) = f(l, alloc) {
                    return Some(alloc.mkt_sort(l));
                }
            }

            TermData::Global(g) => {
                let mut new_levels = Vec::new_in(alloc);

                for (i, l) in g.levels.iter().copied().enumerate() {
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

            TermData::NatRec(r) => {
                if let Some(r) = f(r, alloc) {
                    return Some(alloc.mkt_nat_rec(r));
                }
            }

            TermData::Eq(l) => {
                if let Some(l) = f(l, alloc) {
                    return Some(alloc.mkt_eq(l));
                }
            }

            TermData::EqRefl(l) => {
                if let Some(l) = f(l, alloc) {
                    return Some(alloc.mkt_eq_refl(l));
                }
            }

            TermData::EqRec(l, r) => {
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

    pub fn instantiate_level_params(self, subst: LevelList<'a>, alloc: &'a Arena) -> Term<'a> {
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
    pub fn app_fun(self) -> (Term<'a>, usize) {
        let mut f = self;
        let mut num_args = 0;
        while let Some(app) = f.try_apply() {
            f = app.fun;
            num_args += 1;
        }
        return (f, num_args);
    }

    // @speed: arena.
    pub fn app_args_rev(self) -> (Term<'a>, Vec<Term<'a>>) {
        let mut f = self;
        let mut args = Vec::new();
        while let Some(app) = f.try_apply() {
            f = app.fun;
            args.push(app.arg);
        }
        return (f, args);
    }

    // @speed: arena.
    pub fn app_args(self) -> (Term<'a>, Vec<Term<'a>>) {
        let (f, mut args) = self.app_args_rev();
        args.reverse();
        return (f, args);
    }


    // @speed: arena.
    pub fn try_ivar_app(self) -> Option<(TermVarId, Vec<ScopeId>)> {
        let mut args = Vec::new();
        let var = rec(self, 0, &mut args)?;
        return Some((var, args));

        fn rec(at: Term, num_args: usize, result: &mut Vec<ScopeId>) -> Option<TermVarId> {
            if let Some(app) = at.try_apply() {
                let local = app.arg.try_local()?;

                let var = rec(app.fun, num_args + 1, result)?;
                result.push(local);
                Some(var)
            }
            else if let Some(var) = at.try_ivar() {
                result.reserve_exact(num_args);
                Some(var)
            }
            else { None }
        }
    }



    // doesn't check for `ptr_eq` of old `app_fun`.
    pub fn replace_app_fun(self, new_fun: Term<'a>, alloc: &'a Arena) -> Term<'a> {
        if let Some(app) = self.try_apply() {
            let fun = app.fun.replace_app_fun(new_fun, alloc);
            return alloc.mkt_apply(fun, app.arg);
        }
        return new_fun;
    }
}



pub trait TermAlloc {
    fn mkt_sort<'a>(&'a self, level: Level<'a>) -> Term<'a>;
    fn mkt_bound<'a>(&'a self, bvar: BVar) -> Term<'a>;
    fn mkt_local<'a>(&'a self, id: ScopeId) -> Term<'a>;
    fn mkt_global<'a>(&'a self, id: SymbolId, levels: LevelList<'a>) -> Term<'a>;
    fn mkt_ivar<'a>(&'a self, id: TermVarId) -> Term<'a>;
    fn mkt_forall_b<'a>(&'a self, binder: Binder<'a>) -> Term<'a>;
    fn mkt_forall<'a>(&'a self, kind: BinderKind, name: Atom, ty: Term<'a>, ret: Term<'a>) -> Term<'a>;
    fn mkt_lambda_b<'a>(&'a self, binder: Binder<'a>) -> Term<'a>;
    fn mkt_lambda<'a>(&'a self, kind: BinderKind, name: Atom, ty: Term<'a>, val: Term<'a>) -> Term<'a>;
    fn mkt_apply_a<'a>(&'a self, apply: Apply<'a>) -> Term<'a>;
    fn mkt_apply<'a>(&'a self, fun: Term<'a>, arg: Term<'a>) -> Term<'a>;
    fn mkt_apps<'a>(&'a self, fun: Term<'a>, args: &[Term<'a>]) -> Term<'a>;

    fn mkt_nat<'a>(&'a self) -> Term<'a>;
    fn mkt_nat_zero<'a>(&'a self) -> Term<'a>;
    fn mkt_nat_succ<'a>(&'a self) -> Term<'a>;
    fn mkt_nat_rec<'a>(&'a self, r: Level<'a>) -> Term<'a>;
    fn mkt_nat_rec_ty<'a>(&'a self, r: Level<'a>) -> Term<'a>;
    fn mkt_nat_val<'a>(&'a self, n: u32) -> Term<'a>;


    fn mkt_eq<'a>(&'a self, l: Level<'a>) -> Term<'a>;
    fn mkt_eq_refl<'a>(&'a self, l: Level<'a>) -> Term<'a>;
    fn mkt_eq_rec<'a>(&'a self, l: Level<'a>, r: Level<'a>) -> Term<'a>;
    fn mkt_eq_ty<'a>(&'a self, l: Level<'a>) -> Term<'a>;
    fn mkt_eq_refl_ty<'a>(&'a self, l: Level<'a>) -> Term<'a>;
    fn mkt_eq_rec_ty<'a>(&'a self, l: Level<'a>, r: Level<'a>) -> Term<'a>;
}


mod impel {
    use super::*;

    #[derive(Clone, Copy, Debug)]
    pub struct Term<'a>(&'a Data<'a>);

    #[derive(Debug)]
    struct Data<'a> {
        data: TermData<'a>,
        max_succ_bvar:  u32,
        max_succ_local: u32,
    }


    impl<'a> Term<'a> {
        pub const SORT_0: Term<'static> = Term(&Data { data: TermData::Sort(Level::L0), max_succ_bvar: 0, max_succ_local: 0 });
        pub const SORT_1: Term<'static> = Term(&Data { data: TermData::Sort(Level::L1), max_succ_bvar: 0, max_succ_local: 0 });

        pub const NAT: Term<'static> = Term(&Data { data: TermData::Nat, max_succ_bvar: 0, max_succ_local: 0 });
        pub const NAT_ZERO: Term<'static> = Term(&Data { data: TermData::NatZero, max_succ_bvar: 0, max_succ_local: 0 });
        pub const NAT_SUCC: Term<'static> = Term(&Data { data: TermData::NatSucc, max_succ_bvar: 0, max_succ_local: 0 });
        pub const NAT_SUCC_TY: Term<'static> = Term(&Data { data: TermData::Forall(Binder{ kind: BinderKind::Explicit, name: Atom::NULL, ty: Self::NAT, val: Self::NAT }), max_succ_bvar: 0, max_succ_local: 0 });


        #[inline(always)]
        pub fn kind(self) -> TermKind {
            match self.0.data {
                TermData::Sort(_)       => TermKind::Sort,
                TermData::Bound(_)      => TermKind::Bound,
                TermData::Local(_)      => TermKind::Local,
                TermData::Global(_)     => TermKind::Global,
                TermData::IVar(_)       => TermKind::IVar,
                TermData::Forall(_)     => TermKind::Forall,
                TermData::Lambda(_)     => TermKind::Lambda,
                TermData::Apply(_)      => TermKind::Apply,
                TermData::Nat           => TermKind::Nat,
                TermData::NatZero       => TermKind::NatZero,
                TermData::NatSucc       => TermKind::NatSucc,
                TermData::NatRec(_)     => TermKind::NatRec,
                TermData::Eq(_)         => TermKind::Eq,
                TermData::EqRefl(_)     => TermKind::EqRefl,
                TermData::EqRec(_, _)   => TermKind::EqRec,
            }
        }

        #[inline(always)]
        pub fn max_succ_bvar(self) -> u32 { self.0.max_succ_bvar }

        #[inline(always)]
        pub fn max_succ_local(self) -> u32 { self.0.max_succ_local }

        #[inline(always)]
        pub fn data(self) -> TermData<'a> {
            self.0.data
        }

        #[inline(always)]
        pub fn try_sort(self) -> Option<Level<'a>> {
            if let TermData::Sort(x) = self.0.data { Some(x) } else { None }
        }

        #[inline(always)]
        pub fn try_bvar(self) -> Option<BVar> {
            if let TermData::Bound(x) = self.0.data { Some(x) } else { None }
        }

        #[inline(always)]
        pub fn try_local(self) -> Option<ScopeId> {
            if let TermData::Local(x) = self.0.data { Some(x) } else { None }
        }

        #[inline(always)]
        pub fn try_global(self) -> Option<Global<'a>> {
            if let TermData::Global(x) = self.0.data { Some(x) } else { None }
        }

        #[inline(always)]
        pub fn try_ivar(self) -> Option<TermVarId> {
            if let TermData::IVar(x) = self.0.data { Some(x) } else { None }
        }

        #[inline(always)]
        pub fn try_forall(self) -> Option<Binder<'a>> {
            if let TermData::Forall(x) = self.0.data { Some(x) } else { None }
        }

        #[inline(always)]
        pub fn try_lambda(self) -> Option<Binder<'a>> {
            if let TermData::Lambda(x) = self.0.data { Some(x) } else { None }
        }

        #[inline(always)]
        pub fn try_apply(self) -> Option<Apply<'a>> {
            if let TermData::Apply(x) = self.0.data { Some(x) } else { None }
        }

        #[inline(always)]
        pub fn try_nat_rec(self) -> Option<Level<'a>> {
            if let TermData::NatRec(x) = self.0.data { Some(x) } else { None }
        }

        #[inline(always)]
        pub fn try_eq(self) -> Option<Level<'a>> {
            if let TermData::Eq(x) = self.0.data { Some(x) } else { None }
        }

        #[inline(always)]
        pub fn try_eq_refl(self) -> Option<Level<'a>> {
            if let TermData::EqRefl(x) = self.0.data { Some(x) } else { None }
        }

        #[inline(always)]
        pub fn try_eq_rec(self) -> Option<(Level<'a>, Level<'a>)> {
            if let TermData::EqRec(x1, x2) = self.0.data { Some((x1, x2)) } else { None }
        }


        #[inline(always)]
        pub fn ptr_eq(self, other: Term) -> bool {
            core::ptr::eq(self.0, other.0)
        }
    }


    impl TermAlloc for Arena {
        #[inline(always)]
        fn mkt_sort<'a>(&'a self, level: Level<'a>) -> Term<'a> {
            Term(self.alloc_new(Data {
                data: TermData::Sort(level),
                max_succ_bvar: 0,
                max_succ_local: 0,
            }))
        }

        #[inline(always)]
        fn mkt_bound<'a>(&'a self, bvar: BVar) -> Term<'a> {
            Term(self.alloc_new(Data {
                data: TermData::Bound(bvar),
                max_succ_bvar: bvar.offset.saturating_add(1),
                max_succ_local: 0,
            }))
        }

        #[inline(always)]
        fn mkt_local<'a>(&'a self, id: ScopeId) -> Term<'a> {
            Term(self.alloc_new(Data {
                data: TermData::Local(id),
                max_succ_bvar: 0,
                max_succ_local: id.inner().saturating_add(1),
            }))
        }

        #[inline(always)]
        fn mkt_global<'a>(&'a self, id: SymbolId, levels: LevelList<'a>) -> Term<'a> {
            Term(self.alloc_new(Data {
                data: TermData::Global(Global { id, levels }),
                max_succ_bvar: 0,
                max_succ_local: 0,
            }))
        }

        #[inline(always)]
        fn mkt_ivar<'a>(&'a self, id: TermVarId) -> Term<'a> {
            Term(self.alloc_new(Data {
                data: TermData::IVar(id),
                max_succ_bvar: 0,
                max_succ_local: 0,
            }))
        }

        #[inline(always)]
        fn mkt_forall_b<'a>(&'a self, binder: Binder<'a>) -> Term<'a> {
            Term(self.alloc_new(Data {
                data: TermData::Forall(binder),
                max_succ_bvar:
                    binder.ty.0.max_succ_bvar.max(
                    binder.val.0.max_succ_bvar.saturating_sub(1)),
                max_succ_local:
                    binder.ty.0.max_succ_local.max(
                    binder.val.0.max_succ_local),
            }))
        }

        #[inline(always)]
        fn mkt_forall<'a>(&'a self, kind: BinderKind, name: Atom, ty: Term<'a>, ret: Term<'a>) -> Term<'a> {
            Term(self.alloc_new(Data {
                data: TermData::Forall(Binder { kind, name, ty, val: ret }),
                max_succ_bvar:
                    ty.0.max_succ_bvar.max(
                    ret.0.max_succ_bvar.saturating_sub(1)),
                max_succ_local:
                    ty.0.max_succ_local.max(
                    ret.0.max_succ_local),
            }))
        }

        #[inline(always)]
        fn mkt_lambda_b<'a>(&'a self, binder: Binder<'a>) -> Term<'a> {
            Term(self.alloc_new(Data {
                data: TermData::Lambda(binder),
                max_succ_bvar:
                    binder.ty.0.max_succ_bvar.max(
                    binder.val.0.max_succ_bvar.saturating_sub(1)),
                max_succ_local:
                    binder.ty.0.max_succ_local.max(
                    binder.val.0.max_succ_local),
            }))
        }

        #[inline(always)]
        fn mkt_lambda<'a>(&'a self, kind: BinderKind, name: Atom, ty: Term<'a>, val: Term<'a>) -> Term<'a> {
            Term(self.alloc_new(Data {
                data: TermData::Lambda(Binder { kind, name, ty, val }),
                max_succ_bvar:
                    ty.0.max_succ_bvar.max(
                    val.0.max_succ_bvar.saturating_sub(1)),
                max_succ_local:
                    ty.0.max_succ_local.max(
                    val.0.max_succ_local),
            }))
        }

        #[inline(always)]
        fn mkt_apply_a<'a>(&'a self, apply: Apply<'a>) -> Term<'a> {
            Term(self.alloc_new(Data {
                data: TermData::Apply(apply),
                max_succ_bvar:
                    apply.fun.0.max_succ_bvar.max(
                    apply.arg.0.max_succ_bvar),
                max_succ_local:
                    apply.fun.0.max_succ_local.max(
                    apply.arg.0.max_succ_local),
            }))
        }

        #[inline(always)]
        fn mkt_apply<'a>(&'a self, fun: Term<'a>, arg: Term<'a>) -> Term<'a> {
            Term(self.alloc_new(Data {
                data: TermData::Apply(Apply { fun, arg }),
                max_succ_bvar:
                    fun.0.max_succ_bvar.max(
                    arg.0.max_succ_bvar),
                max_succ_local:
                    fun.0.max_succ_local.max(
                    arg.0.max_succ_local),
            }))
        }

        #[inline(always)]
        fn mkt_apps<'a>(&'a self, fun: Term<'a>, args: &[Term<'a>]) -> Term<'a> {
            let mut result = fun;
            for arg in args.iter().copied() {
                result = self.mkt_apply(result, arg);
            }
            return result;
        }

        #[inline(always)]
        fn mkt_nat<'a>(&'a self) -> Term<'a> {
            Term(self.alloc_new(Data {
                data: TermData::Nat,
                max_succ_bvar: 0,
                max_succ_local: 0,
            }))
        }

        #[inline(always)]
        fn mkt_nat_zero<'a>(&'a self) -> Term<'a> {
            Term(self.alloc_new(Data {
                data: TermData::NatZero,
                max_succ_bvar: 0,
                max_succ_local: 0,
            }))
        }

        #[inline(always)]
        fn mkt_nat_succ<'a>(&'a self) -> Term<'a> {
            Term(self.alloc_new(Data {
                data: TermData::NatSucc,
                max_succ_bvar: 0,
                max_succ_local: 0,
            }))
        }

        #[inline(always)]
        fn mkt_nat_rec<'a>(&'a self, r: Level<'a>) -> Term<'a> {
            Term(self.alloc_new(Data {
                data: TermData::NatRec(r),
                max_succ_bvar: 0,
                max_succ_local: 0,
            }))
        }

        fn mkt_nat_rec_ty<'a>(&'a self, r: Level<'a>) -> Term<'a> {
            self.mkt_forall(BinderKind::Implicit, atoms::M,
                // M: Nat -> Sort(r)
                self.mkt_forall(BinderKind::Explicit, atoms::Nat,
                    Term::NAT,
                    self.mkt_sort(r)),
            self.mkt_forall(BinderKind::Explicit, atoms::m_zero,
                // m_zero: M(0)
                self.mkt_apply(
                    self.mkt_bound(BVar { offset: 0 }),
                    Term::NAT_ZERO),
            self.mkt_forall(BinderKind::Explicit, atoms::m_succ,
                // m_succ: Π(n, ih) => M(n.succ())
                self.mkt_forall(BinderKind::Explicit, atoms::n,
                    // n: Nat
                    Term::NAT,
                self.mkt_forall(BinderKind::Explicit, atoms::ih,
                    // ih: M(n)
                    self.mkt_apply(
                        self.mkt_bound(BVar { offset: 2 }),
                        self.mkt_bound(BVar { offset: 0 })),
                    // -> M(n.succ())
                    self.mkt_apply(
                        self.mkt_bound(BVar { offset: 3 }),
                        self.mkt_apply(
                            Term::NAT_SUCC,
                            self.mkt_bound(BVar { offset: 1 }))))),
            self.mkt_forall(BinderKind::Explicit, atoms::mp,
                // mp: Nat
                Term::NAT,
                // -> M(mp)
                self.mkt_apply(
                    self.mkt_bound(BVar { offset: 3 }),
                    self.mkt_bound(BVar { offset: 0 }))))))
        }

        fn mkt_nat_val<'a>(&'a self, n: u32) -> Term<'a> {
            let mut result = Term::NAT_ZERO;
            for _ in 0..n {
                result = self.mkt_apply(Term::NAT_SUCC, result);
            }
            return result;
        }


        #[inline(always)]
        fn mkt_eq<'a>(&'a self, l: Level<'a>) -> Term<'a> {
            Term(self.alloc_new(Data {
                data: TermData::Eq(l),
                max_succ_bvar: 0,
                max_succ_local: 0,
            }))
        }

        #[inline(always)]
        fn mkt_eq_refl<'a>(&'a self, l: Level<'a>) -> Term<'a> {
            Term(self.alloc_new(Data {
                data: TermData::EqRefl(l),
                max_succ_bvar: 0,
                max_succ_local: 0,
            }))
        }

        #[inline(always)]
        fn mkt_eq_rec<'a>(&'a self, l: Level<'a>, r: Level<'a>) -> Term<'a> {
            Term(self.alloc_new(Data {
                data: TermData::EqRec(l, r),
                max_succ_bvar: 0,
                max_succ_local: 0,
            }))
        }

        fn mkt_eq_ty<'a>(&'a self, l: Level<'a>) -> Term<'a> {
            self.mkt_forall(BinderKind::Implicit, atoms::T,
                // T: Sort(l)
                self.mkt_sort(l),
            self.mkt_forall(BinderKind::Explicit, atoms::a,
                // a: T
                self.mkt_bound(BVar { offset: 0 }),
            self.mkt_forall(BinderKind::Explicit, atoms::b,
                // b: T
                self.mkt_bound(BVar { offset: 1 }),
                // -> Prop
                self.mkt_sort(self.mkl_zero()))))
        }

        fn mkt_eq_refl_ty<'a>(&'a self, l: Level<'a>) -> Term<'a> {
            self.mkt_forall(BinderKind::Implicit, atoms::T,
                // T: Sort(l)
                self.mkt_sort(l),
            self.mkt_forall(BinderKind::Explicit, atoms::a,
                // a: T
                self.mkt_bound(BVar { offset: 0 }),
                // -> Eq(T, a, a)
                self.mkt_apps(self.mkt_eq(l), &[
                    self.mkt_bound(BVar { offset: 1 }),
                    self.mkt_bound(BVar { offset: 0 }),
                    self.mkt_bound(BVar { offset: 0 }),
                ])))
        }

        fn mkt_eq_rec_ty<'a>(&'a self, l: Level<'a>, r: Level<'a>) -> Term<'a> {
            self.mkt_forall(BinderKind::Implicit, atoms::T,
                // T: Sort(l)
                self.mkt_sort(l),
            self.mkt_forall(BinderKind::Implicit, atoms::a,
                // a: T
                self.mkt_bound(BVar { offset: 0 }),
            self.mkt_forall(BinderKind::Implicit, atoms::M,
                // M: Π(b: T) -> Sort(r)
                self.mkt_forall(BinderKind::Explicit, atoms::b,
                    self.mkt_bound(BVar { offset: 1 }),
                    self.mkt_sort(r)),
            self.mkt_forall(BinderKind::Explicit, atoms::m_refl,
                // m_refl: M(a)
                self.mkt_apply(
                    self.mkt_bound(BVar { offset: 0 }),
                    self.mkt_bound(BVar { offset: 1 })),
            self.mkt_forall(BinderKind::Implicit, atoms::b,
                // b: T
                self.mkt_bound(BVar { offset: 3 }),
            self.mkt_forall(BinderKind::Explicit, atoms::mp,
                // mp: Eq(T, a, b)
                self.mkt_apps(self.mkt_eq(l), &[
                    self.mkt_bound(BVar { offset: 4 }),
                    self.mkt_bound(BVar { offset: 3 }),
                    self.mkt_bound(BVar { offset: 0 }),
                ]),
                // -> M(b)
                self.mkt_apply(
                    self.mkt_bound(BVar { offset: 3 }),
                    self.mkt_bound(BVar { offset: 1 }))))))))
        }
    }
}

