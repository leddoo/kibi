use sti::arena::Arena;
use sti::vec::Vec;

use super::level::*;

pub use crate::string_table::{Atom, atoms};
pub use crate::env::SymbolId;
pub use super::local_ctx::ScopeId;


pub type Term<'a> = impel::Term<'a>;

sti::define_key!(pub, u32, TermVarId);


#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum TermKind {
    Sort,

    Bound,
    Local,
    Global,
    IVar,

    Forall,
    Lambda,
    Let,
    Apply,
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
    Let(Let<'a>),
    Apply(Apply<'a>),

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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
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
pub struct Let<'a> {
    pub name: Atom,
    pub ty:   Term<'a>,
    pub val:  Term<'a>,
    pub body: Term<'a>,
}

#[derive(Clone, Copy, Debug)]
pub struct Apply<'a> {
    pub fun: Term<'a>,
    pub arg: Term<'a>,
}


impl<'a> Binder<'a> {
    #[inline(always)]
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

impl<'a> Let<'a> {
    #[inline(always)]
    pub fn update(&self, t: Term<'a>, alloc: &'a Arena, new_ty: Term<'a>, new_val: Term<'a>, new_body: Term<'a>) -> Term<'a> {
        if !new_ty.ptr_eq(self.ty) || !new_val.ptr_eq(self.val) || !new_body.ptr_eq(self.body) {
            let b = Self {
                name: self.name,
                ty: new_ty, val: new_val,
                body: new_body,
            };

            alloc.mkt_let_b(b)
        }
        else { t }
    }
}

impl<'a> Apply<'a> {
    #[inline(always)]
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
    pub fn is_let(self) -> bool { self.kind() == TermKind::Let }

    #[inline(always)]
    pub fn is_apply(self) -> bool { self.kind() == TermKind::Apply }


    #[inline(always)]
    pub fn is_nat(self) -> bool { if let Some(g) = self.try_global() { g.id == SymbolId::Nat } else { false } }

    #[inline(always)]
    pub fn is_nat_zero(self) -> bool { if let Some(g) = self.try_global() { g.id == SymbolId::Nat_zero } else { false } }

    #[inline(always)]
    pub fn is_nat_succ(self) -> bool { if let Some(g) = self.try_global() { g.id == SymbolId::Nat_succ } else { false } }


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

            (Let(b1), Let(b2)) =>
                b1.ty.syntax_eq(b2.ty) && b1.val.syntax_eq(b2.val) &&
                b1.body.syntax_eq(b2.body),

            (Apply(a1), Apply(a2)) =>
                a1.fun.syntax_eq(a2.fun) && a1.arg.syntax_eq(a2.arg),

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

                _ => return None,
            })
        }).is_some()
    }


    pub fn closed_no_local(self) -> bool {
        self.closed() && !self.has_locals()
    }

    pub fn closed_no_local_no_ivar(self) -> bool {
        self.closed() && !self.has_locals() && !self.has_ivars()
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

            TermData::Let(b) => {
                b.ty.find_ex(offset, f).or_else(||
                b.val.find_ex(offset, f).or_else(||
                b.body.find_ex(offset + 1, f)))
            }

            TermData::Apply(a) => {
                a.fun.find_ex(offset, f).or_else(||
                a.arg.find_ex(offset, f))
            }
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
            TermData::Lambda(b) =>
                b.update(self, alloc,
                    b.ty.replace_ex(offset, alloc, f),
                    b.val.replace_ex(offset + 1, alloc, f)),

            TermData::Let(b) =>
                b.update(self, alloc,
                    b.ty.replace_ex(offset, alloc, f),
                    b.val.replace_ex(offset, alloc, f),
                    b.body.replace_ex(offset + 1, alloc, f)),

            TermData::Apply(a) => {
                a.update(self, alloc,
                    a.fun.replace_ex(offset, alloc, f),
                    a.arg.replace_ex(offset, alloc, f))
            }
        }
    }


    pub fn lift_loose_bvars(self, delta: u32, alloc: &'a Arena) -> Term<'a> {
        self.lift_bvars(0, delta, alloc)
    }

    pub fn lift_bvars(self, cut_off: u32, delta: u32, alloc: &'a Arena) -> Term<'a> {
        self.replace_ex(cut_off, alloc, &mut |at, offset, alloc| {
            if at.max_succ_bvar() < offset.saturating_add(1) {
                return Some(at);
            }

            let bvar = at.try_bvar()?;
            debug_assert!(bvar.offset >= offset);
            return Some(alloc.mkt_bound(BVar { offset: bvar.offset + delta }));
        })
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
        self.replace(alloc, |at, offset, alloc| {
            if at.max_succ_bvar() < offset.saturating_add(1) {
                return Some(at);
            }

            let bvar = at.try_bvar()?;
            if bvar.offset == offset {
                if subst.closed() || offset == 0 { Some(subst) }
                else { Some(subst.lift_loose_bvars(offset, alloc)) }
            }
            else { None }
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

    pub fn app_args_rev<'res>(self, arena: &'res Arena) -> (Term<'a>, Vec<Term<'a>, &'res Arena>) {
        let mut f = self;
        let mut args = Vec::new_in(arena);
        while let Some(app) = f.try_apply() {
            f = app.fun;
            args.push(app.arg);
        }
        return (f, args);
    }

    pub fn app_args<'res>(self, arena: &'res Arena) -> (Term<'a>, Vec<Term<'a>, &'res Arena>) {
        let (f, mut args) = self.app_args_rev(arena);
        args.reverse();
        return (f, args);
    }


    pub fn try_ivar_app<'res>(self, arena: &'res Arena) -> Option<(TermVarId, Vec<ScopeId, &'res Arena>)> {
        let mut args = Vec::new_in(arena);
        let var = rec(self, 0, &mut args)?;
        return Some((var, args));

        fn rec(at: Term, num_args: usize, result: &mut Vec<ScopeId, &Arena>) -> Option<TermVarId> {
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


    #[inline]
    pub fn forall_ret(self) -> (Term<'a>, usize) {
        let mut r = self;
        let mut num_params = 0;
        while let Some(pi) = r.try_forall() {
            r = pi.val;
            num_params += 1;
        }
        return (r, num_params);
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
    fn mkt_let_b<'a>(&'a self, binder: Let<'a>) -> Term<'a>;
    fn mkt_let<'a>(&'a self, name: Atom, ty: Term<'a>, val: Term<'a>, body: Term<'a>) -> Term<'a>;
    fn mkt_apply_a<'a>(&'a self, apply: Apply<'a>) -> Term<'a>;
    fn mkt_apply<'a>(&'a self, fun: Term<'a>, arg: Term<'a>) -> Term<'a>;
    fn mkt_apps<'a>(&'a self, fun: Term<'a>, args: &[Term<'a>]) -> Term<'a>;

    fn mkt_nat_val<'a>(&'a self, n: u32) -> Term<'a>;
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

        pub const NAT:      Term<'static> = Term(&Data { data: TermData::Global(Global { id: SymbolId::Nat,      levels: &[] }), max_succ_bvar: 0, max_succ_local: 0 });
        pub const NAT_ZERO: Term<'static> = Term(&Data { data: TermData::Global(Global { id: SymbolId::Nat_zero, levels: &[] }), max_succ_bvar: 0, max_succ_local: 0 });
        pub const NAT_SUCC: Term<'static> = Term(&Data { data: TermData::Global(Global { id: SymbolId::Nat_succ, levels: &[] }), max_succ_bvar: 0, max_succ_local: 0 });

        pub const ADD_ADD: Term<'static> = Term(&Data { data: TermData::Global(Global { id: SymbolId::Add_add, levels: &[] }), max_succ_bvar: 0, max_succ_local: 0 });


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
                TermData::Let(_)        => TermKind::Let,
                TermData::Apply(_)      => TermKind::Apply,
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
        pub fn try_let(self) -> Option<Let<'a>> {
            if let TermData::Let(x) = self.0.data { Some(x) } else { None }
        }

        #[inline(always)]
        pub fn try_apply(self) -> Option<Apply<'a>> {
            if let TermData::Apply(x) = self.0.data { Some(x) } else { None }
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
            self.mkt_forall_b(Binder { kind, name, ty, val: ret })
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
            self.mkt_lambda_b(Binder { kind, name, ty, val })
        }

        #[inline(always)]
        fn mkt_let_b<'a>(&'a self, binder: Let<'a>) -> Term<'a> {
            Term(self.alloc_new(Data {
                data: TermData::Let(binder),
                max_succ_bvar:
                    binder.ty.0.max_succ_bvar.max(
                    binder.val.0.max_succ_bvar.max(
                    binder.body.0.max_succ_bvar.saturating_sub(1))),
                max_succ_local:
                    binder.ty.0.max_succ_local.max(
                    binder.val.0.max_succ_local.max(
                    binder.body.0.max_succ_local)),
            }))
        }

        #[inline(always)]
        fn mkt_let<'a>(&'a self, name: Atom, ty: Term<'a>, val: Term<'a>, body: Term<'a>) -> Term<'a> {
            self.mkt_let_b(Let { name, ty, val, body })
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

        fn mkt_nat_val<'a>(&'a self, n: u32) -> Term<'a> {
            let mut result = Term::NAT_ZERO;
            for _ in 0..n {
                result = self.mkt_apply(Term::NAT_SUCC, result);
            }
            return result;
        }
    }
}

