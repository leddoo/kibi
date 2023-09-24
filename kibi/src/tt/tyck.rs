use sti::traits::CopyIt;
use sti::arena::Arena;
use sti::arena_pool::ArenaPool;

use super::*;
use crate::env::{Env, SymbolKind, symbol};


pub struct TyCk<'me, 'out> {
    alloc: &'out Arena,
    env: &'me Env<'out>,
    lctx: &'me mut LocalCtx<'out>,
    num_levels: usize,
}

// @todo: scope.
#[derive(Clone, Copy, Debug)]
pub struct Error<'out> {
    pub at: Term<'out>,
    pub kind: ErrorKind<'out>,
}

#[derive(Clone, Copy, Debug)]
pub enum ErrorKind<'out> {
    LooseBVar,
    LooseLocal,
    TermIVar,
    GlobalNotReady,
    GlobalLevelMismatch,
    TypeExpected { found: Term<'out> },
    TypeInvalid { found: Term<'out>, expected: Term<'out> },
    LetValTypeInvalid { found: Term<'out> },
    AppArgTypeInvalid { found: Term<'out>, expected: Term<'out> },
    LevelParamIndexInvalid,
    LevelIVar,
}


impl<'me, 'out> TyCk<'me, 'out> {
    #[inline]
    pub fn new(env: &'me Env<'out>, lctx: &'me mut LocalCtx<'out>, num_levels: usize, alloc: &'out Arena) -> Self {
        Self { alloc, env, lctx, num_levels }
    }


    pub fn check_well_typed(&mut self, t: Term<'out>) -> Result<(), Error<'out>> {
        spall::trace_scope!("kibi/tyck/well_typed");

        if t.has_locals() { return Err(Error { at: t, kind: ErrorKind::LooseLocal }); }

        self.infer_type(t)?;
        return Ok(());
    }

    pub fn check_is_type(&mut self, t: Term<'out>) -> Result<(), Error<'out>> {
        spall::trace_scope!("kibi/tyck/is_type");

        if t.has_locals() { return Err(Error { at: t, kind: ErrorKind::LooseLocal }); }

        self.ensure_type(t)?;
        return Ok(());
    }

    pub fn check_has_type(&mut self, t: Term<'out>, expected: Term<'out>) -> Result<(), Error<'out>> {
        spall::trace_scope!("kibi/tyck/has_type");

        if t.has_locals() { return Err(Error { at: t, kind: ErrorKind::LooseLocal }); }

        let ty = self.infer_type(t)?;
        if !self.def_eq(ty, expected) {
            return Err(Error { at: t, kind: ErrorKind::TypeInvalid { found: ty, expected } });
        }
        return Ok(());
    }


    pub fn infer_type(&mut self, t: Term<'out>) -> Result<Term<'out>, Error<'out>> {
        let result = match t.data() {
            TermData::Sort(l) => {
                self.check_level(l, t)?;
                self.alloc.mkt_sort(l.succ(self.alloc), TERM_SOURCE_NONE)
            }

            TermData::Bound(_) =>
                return Err(Error { at: t, kind: ErrorKind::LooseBVar }),

            TermData::Local(it) =>
                self.lctx.lookup(it).ty,

            TermData::Global(it) => {
                let symbol = self.env.symbol(it.id);
                match symbol.kind {
                    SymbolKind::Root => unreachable!(),

                    SymbolKind::Predeclared |
                    SymbolKind::Pending(_) =>
                        return Err(Error { at: t, kind: ErrorKind::GlobalNotReady }),

                    SymbolKind::Axiom   (symbol::Axiom    { ty, num_levels, .. }) |
                    SymbolKind::Def     (symbol::Def      { ty, num_levels, .. }) |
                    SymbolKind::IndAxiom(symbol::IndAxiom { ty, num_levels, .. }) => {
                        if it.levels.len() != num_levels {
                            return Err(Error { at: t, kind: ErrorKind::GlobalLevelMismatch });
                        }
                        for l in it.levels.copy_it() {
                            self.check_level(l, t)?;
                        }
                        ty.instantiate_level_params(it.levels, self.alloc)
                    }
                }
            }

            TermData::IVar(_) =>
                return Err(Error { at: t, kind: ErrorKind::TermIVar }),

            TermData::Forall(it) => {
                let (ty, l_ty) = self.ensure_type(it.ty)?;

                let id = self.lctx.push(it.name, ty, ScopeKind::Binder(it.kind));
                let ret = it.val.instantiate(self.alloc.mkt_local(id, TERM_SOURCE_NONE), self.alloc);
                let (_, l_ret) = self.ensure_type(ret)?;
                self.lctx.pop(id);

                let l = l_ty.imax(l_ret, self.alloc);
                self.alloc.mkt_sort(l, TERM_SOURCE_NONE)
            }

            TermData::Lambda(it) => {
                let (ty, _) = self.ensure_type(it.ty)?;

                let id = self.lctx.push(it.name, ty, ScopeKind::Binder(it.kind));
                let val = it.val.instantiate(self.alloc.mkt_local(id, TERM_SOURCE_NONE), self.alloc);
                let ret = self.infer_type(val)?;
                let ret = self.lctx.abstract_forall(ret, id, TERM_SOURCE_NONE, self.alloc);
                self.lctx.pop(id);

                ret
            }

            TermData::Let(it) => {
                let (ty, _) = self.ensure_type(it.ty)?;

                let val_ty = self.infer_type(it.val)?;
                if !self.def_eq(val_ty, ty) {
                    return Err(Error { at: t, kind:
                        ErrorKind::LetValTypeInvalid { found: val_ty } });
                }

                let id = self.lctx.push(it.name, ty, ScopeKind::Local(it.val));
                let body = it.body.instantiate(self.alloc.mkt_local(id, TERM_SOURCE_NONE), self.alloc);
                let res = self.infer_type(body)?;
                let res = self.lctx.abstract_let(res, id, true, TERM_SOURCE_NONE, self.alloc);
                self.lctx.pop(id);

                res
            }

            TermData::Apply(it) => {
                let (_, pi) = self.ensure_forall(it.fun)?;

                let arg_ty = self.infer_type(it.arg)?;
                if !self.def_eq(arg_ty, pi.ty) {
                    return Err(Error { at: t, kind:
                        ErrorKind::AppArgTypeInvalid { found: arg_ty, expected: pi.ty } });
                }

                pi.val.instantiate(it.arg, self.alloc)
            }
        };
        assert!(result.closed());
        return Ok(result);
    }

    pub fn ensure_type(&mut self, t: Term<'out>) -> Result<(Term<'out>, Level<'out>), Error<'out>> {
        let ty = self.infer_type(t)?;
        if let Some(l) = self.whnf_sort(ty) {
            Ok((t, l))
        }
        else { Err(Error { at: t, kind: ErrorKind::TypeExpected { found: ty } }) }
    }

    pub fn ensure_forall(&mut self, t: Term<'out>) -> Result<(Term<'out>, Binder<'out>), Error<'out>> {
        let ty = self.infer_type(t)?;
        if let Some(b) = self.whnf_forall(ty) {
            Ok((t, b))
        }
        else { Err(Error { at: t, kind: ErrorKind::TypeExpected { found: ty } }) }
    }


    #[inline]
    pub fn whnf(&self, t: Term<'out>) -> Term<'out> {
        debug_assert!(t.closed());

        let (t, done) = self.whnf_no_unfold(t);
        if done {
            return t;
        }

        if let Some(result) = self.unfold(t) {
            return self.whnf(result);
        }

        return t;
    }

    #[inline]
    pub fn whnf_sort(&self, t: Term<'out>) -> Option<Level<'out>> {
        if let Some(l) = t.try_sort() { return Some(l) }
        self.whnf(t).try_sort()
    }

    #[inline]
    pub fn whnf_forall(&self, t: Term<'out>) -> Option<Binder<'out>> {
        if let Some(b) = t.try_forall() { return Some(b) }
        self.whnf(t).try_forall()
    }

    // reductions: local.
    // supports ptr_eq for change detection.
    fn whnf_basic(&self, t: Term<'out>) -> (Term<'out>, bool) {
        match t.data() {
            TermData::Sort (_) =>
                (t, true),

            TermData::Bound (_) =>
                unreachable!(),

            TermData::Local (id) => {
                let entry = self.lctx.lookup(id);
                if let ScopeKind::Local(value) = entry.kind {
                    self.whnf_basic(value)
                }
                else { (t, true) }
            }

            TermData::Global (it) => {
                let symbol = self.env.symbol(it.id);
                match symbol.kind {
                    SymbolKind::Root |
                    SymbolKind::Predeclared |
                    SymbolKind::Pending(_) => unreachable!(),

                    SymbolKind::Axiom(_)    => (t, true),
                    SymbolKind::Def(_)      => (t, false),
                    SymbolKind::IndAxiom(_) => (t, true),
                }
            }

            TermData::IVar(_) =>
                unreachable!(),

            TermData::Lambda (_) |
            TermData::Forall (_) =>
                (t, true),

            TermData::Let (it) => {
                if it.body.closed() {
                    self.whnf_basic(it.body)
                }
                else { (t, false) }
            }

            TermData::Apply (_) =>
                (t, false),
        }
    }

    // @cleanup: dedup?
    // reductions: eta, let, beta, recursor.
    // supports ptr_eq for change detection.
    fn whnf_no_unfold(&self, t: Term<'out>) -> (Term<'out>, bool) {
        assert!(t.closed());

        let (t, done) = self.whnf_basic(t);
        if done {
            return (t, true);
        }

        // eta (λ x, f x)
        if let Some(binder) = t.try_lambda() {
            if let Some(app) = binder.val.try_apply() {
                if let Some(bvar) = app.arg.try_bvar() {
                    if bvar.offset == 0 && app.fun.closed() {
                        return self.whnf_no_unfold(app.fun);
                    }
                }
            }
        }

        // let.
        if let Some(b) = t.try_let() {
            let body = b.body.instantiate(b.val, self.alloc);
            return self.whnf_no_unfold(body);
        }

        // is app?
        let (fun, num_args) = t.app_fun();
        if num_args == 0 {
            return (t, false); // if were done, would have returned above.
        }

        // head reduction.
        let old_fun = fun;
        let (fun, fun_done) = self.whnf_no_unfold(fun);
        let changed = !fun.ptr_eq(old_fun);

        // beta.
        if fun.is_lambda() {
            let result = {
                let temp = ArenaPool::tls_get_temp();
                let (_, args) = t.app_args(&*temp);

                let mut result = fun;
                let mut i = 0;
                while let Some(lam) = result.try_lambda() {
                    if i < args.len() {
                        result = lam.val.instantiate(args[i], self.alloc);
                        i += 1;
                    }
                    else { break }
                }

                self.alloc.mkt_apps(result, &args[i..], TERM_SOURCE_NONE)
            };
            return self.whnf_no_unfold(result);
        }

        // recursor.
        if let Some(result) = self.try_reduce_recursor(t, fun, num_args) {
            return self.whnf_no_unfold(result);
        }

        if changed {
            let result = t.replace_app_fun(fun, self.alloc);
            assert!(result.closed());
            return (result, fun_done);
        }

        return (t, fun_done);
    }

    // @cleanup: dedup?
    fn try_reduce_recursor(&self, t: Term<'out>, fun: Term<'out>, num_args: usize) -> Option<Term<'out>> {
        assert!(t.closed());

        // ensure is eliminator.
        let global = fun.try_global()?;
        let SymbolKind::IndAxiom(ind) = self.env.symbol(global.id).kind else {
            return None;
        };
        if ind.kind != symbol::IndAxiomKind::Eliminator {
            return None;
        }

        let info = ind.info;
        let min_args = info.min_args_for_reduce as usize;
        if num_args < min_args {
            return None;
        }

        let temp = ArenaPool::tls_get_rec();
        let (_, args) = t.app_args(&*temp);


        let mp = args[min_args - 1];
        let mp = self.whnf(mp);

        let (mp_fun, _) = mp.app_fun();
        let mp_global = mp_fun.try_global()?;
        let SymbolKind::IndAxiom(mp_ind) = self.env.symbol(mp_global.id).kind else {
            return None;
        };
        if !core::ptr::eq(mp_ind.info, ind.info) {
            return None;
        }
        let symbol::IndAxiomKind::Constructor(ctor_idx) = mp_ind.kind else {
            debug_assert!(mp_ind.kind == symbol::IndAxiomKind::Eliminator);
            return None;
        };

        let (_, mp_args) = mp.app_args(&*temp);


        let mut result = ind.info.comp_rules[ctor_idx as usize];

        // Name.rec   ps Ms ms cxs (ctor_i ps as) ⇝ ms_i as mvs
        // comp_i = λ ps Ms ms                as,   ms_i as mvs

        let rec_args  = &args[.. (info.num_params + info.num_motives + info.num_minors) as usize];
        let app_args  = &args[min_args..];
        let ctor_args = &mp_args[info.num_params as usize ..];

        for arg in rec_args.iter().copied() {
            let Some(lam) = result.try_lambda() else { unreachable!() };
            result = lam.val.instantiate(arg, self.alloc);
        }

        for arg in ctor_args.iter().copied() {
            let Some(lam) = result.try_lambda() else { unreachable!() };
            result = lam.val.instantiate(arg, self.alloc);
        }

        let result = result.instantiate_level_params(global.levels, self.alloc);

        let result = self.alloc.mkt_apps(result, app_args, TERM_SOURCE_NONE);
        assert!(result.closed());
        return Some(result);
    }


    // @cleanup: dedup?
    fn unfold(&self, t: Term<'out>) -> Option<Term<'out>> {
        let (fun, _) = t.app_fun();

        let g = fun.try_global()?;

        let symbol = self.env.symbol(g.id);
        match symbol.kind {
            SymbolKind::Root |
            SymbolKind::Predeclared |
            SymbolKind::Pending(_) => unreachable!(),

            SymbolKind::Axiom(_) => None,

            SymbolKind::Def(it) => {
                debug_assert_eq!(g.levels.len(), it.num_levels as usize);
                let val = it.val.instantiate_level_params(g.levels, self.alloc);
                Some(t.replace_app_fun(val, self.alloc))
            }

            SymbolKind::IndAxiom(_) => None,
        }
    }


    // @todo: optimize. (eg: unfold def w/ higher depth)
    pub fn def_eq(&mut self, a: Term<'out>, b: Term<'out>) -> bool {
        assert!(a.closed() && b.closed());

        // basic checks.
        if let Some(result) = self.def_eq_basic(a, b) {
            return result;
        }

        // whnf without unfolding.
        let (a_old, b_old) = (a, b);
        let (a, _) = self.whnf_no_unfold(a);
        let (b, _) = self.whnf_no_unfold(b);

        // try basic checks again.
        if !a.ptr_eq(a_old) || !b.ptr_eq(b_old) {
            if let Some(result) = self.def_eq_basic(a, b) {
                return result;
            }
        }

        // unfold defs & retry on change.
        if let Some(a) = self.unfold(a) {
            return self.def_eq(a, b);
        }
        if let Some(b) = self.unfold(b) {
            return self.def_eq(a, b);
        }

        // note: exprs are now in whnf.
        let (fun1, num_args1) = a.app_fun();
        let (fun2, num_args2) = b.app_fun();

        // app.
        if num_args1 > 0 && num_args1 == num_args2 {
            if self.def_eq(fun1, fun2) && self.def_eq_app_args(a, b) {
                return true;
            }
        }

        // proof irrelevance.
        let ta = self.infer_type(a).unwrap();
        if let Some(l) = self.infer_type(ta).unwrap().try_sort() {
            if l.is_zero() {
                let tb = self.infer_type(b).unwrap();
                if self.def_eq(ta, tb) {
                    return true;
                }
            }
        }

        // failed.
        return false;
    }

    fn def_eq_basic(&mut self, a: Term<'out>, b: Term<'out>) -> Option<bool> {
        if a.syntax_eq(b) {
            return Some(true);
        }

        match (a.data(), b.data()) {
            (TermData::Sort(l1), TermData::Sort(l2)) => {
                Some(self.level_def_eq(l1, l2))
            }

            (TermData::Global(g1), TermData::Global(g2)) => {
                if g1.id == g2.id && self.levels_def_eq(g1.levels, g2.levels) {
                    return Some(true);
                }
                None
            }

            (TermData::Forall(b1), TermData::Forall(b2)) |
            (TermData::Lambda(b1), TermData::Lambda(b2)) => {
                // param eq.
                if !self.def_eq(b1.ty, b2.ty) {
                    return Some(false);
                }

                let id = self.lctx.push(b1.name, b1.ty, ScopeKind::Binder(b1.kind));
                let local = self.alloc.mkt_local(id, TERM_SOURCE_NONE);

                // value eq.
                let val1 = b1.val.instantiate(local, self.alloc);
                let val2 = b2.val.instantiate(local, self.alloc);
                let result = self.def_eq(val1, val2);

                self.lctx.pop(id);

                Some(result)
            }

            _ => None,
        }
    }

    /// - assumes: `a.num_args = b.num_args`.
    fn def_eq_app_args(&mut self, a: Term<'out>, b: Term<'out>) -> bool {
        let Some(a) = a.try_apply() else { return true };
        let Some(b) = b.try_apply() else { return true };

        if !self.def_eq(a.arg, b.arg) {
            return false;
        }

        return self.def_eq_app_args(a.fun, b.fun);
    }


    pub fn check_level(&mut self, l: Level<'out>, at: Term<'out>) -> Result<(), Error<'out>> {
        match l.data() {
            LevelData::Zero => (),

            LevelData::Succ(it) => {
                self.check_level(it, at)?;
            }

            LevelData::Max (it) |
            LevelData::IMax(it) => {
                self.check_level(it.lhs, at)?;
                self.check_level(it.rhs, at)?;
            }

            LevelData::Param(it) => {
                if it.index as usize >= self.num_levels {
                    return Err(Error { at, kind: ErrorKind::LevelParamIndexInvalid });
                };
            }

            LevelData::IVar(_) =>
                return Err(Error { at, kind: ErrorKind::LevelIVar }),
        }
        Ok(())
    }

    #[inline]
    pub fn level_def_eq(&mut self, a: Level<'out>, b: Level<'out>) -> bool {
        a.syntax_eq(b)
    }

    #[inline]
    pub fn levels_def_eq(&mut self, a: &[Level<'out>], b: &[Level<'out>]) -> bool {
        if a.len() != b.len() { return false }

        for i in 0..a.len() {
            if !self.level_def_eq(a[i], b[i]) {
                return false;
            }
        }

        return true;
    }
}

