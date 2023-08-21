use sti::arena::Arena;

use crate::env::*;

use super::syntax::*;
use super::LocalCtx;
use super::infer_ctx::InferCtx;


pub struct TyCtx<'me, 'a> {
    pub alloc: &'a Arena,
    pub env: &'me Env<'a>,

    pub lctx: &'me mut LocalCtx<'a>,

    pub ictx: Option<&'me mut InferCtx<'a>>,
}

impl<'me, 'a> TyCtx<'me, 'a> {
    pub fn new(lctx: &'me mut LocalCtx<'a>, ictx: Option<&'me mut InferCtx<'a>>, env: &'me Env<'a>, alloc: &'a Arena) -> Self {
        Self { alloc, env, lctx, ictx }
    }


    #[inline(always)]
    pub fn save_lctx<R, F: FnOnce(&mut Self) -> R>(&mut self, f: F) -> R {
        let save = self.lctx.save();
        let result = f(self);
        self.lctx.restore(save);
        return result;
    }


    //
    // infer type
    //

    pub fn infer_type(&mut self, t: TermRef<'a>) -> Option<TermRef<'a>> {
        assert!(t.closed());

        let result = match t.kind {
            TermKind::Sort (l) => {
                self.alloc.mkt_sort(l.succ(self.alloc))
            }

            TermKind::Bound (_) => {
                unreachable!()
            }

            TermKind::Local (id) => {
                self.lctx.lookup(id).ty
            }

            TermKind::Global (g) => {
                let symbol = self.env.symbol(g.id);
                match symbol.kind {
                    SymbolKind::Root => unreachable!(),

                    SymbolKind::BuiltIn(b) => {
                        match b {
                            symbol::BuiltIn::Nat => {
                                debug_assert_eq!(g.levels.len(), 0);
                                Term::SORT_1
                            }

                            symbol::BuiltIn::NatZero => {
                                debug_assert_eq!(g.levels.len(), 0);
                                Term::NAT
                            }

                            symbol::BuiltIn::NatSucc => {
                                debug_assert_eq!(g.levels.len(), 0);
                                Term::NAT_SUCC_TY
                            }

                            symbol::BuiltIn::NatRec => {
                                debug_assert_eq!(g.levels.len(), 1);
                                let r = &g.levels[0];
                                self.alloc.mkt_nat_rec_ty(r)
                            }

                            symbol::BuiltIn::Eq => {
                                debug_assert_eq!(g.levels.len(), 1);
                                let l = &g.levels[0];
                                self.alloc.mkt_eq_ty(l)
                            }

                            symbol::BuiltIn::EqRefl => {
                                debug_assert_eq!(g.levels.len(), 1);
                                let l = &g.levels[0];
                                self.alloc.mkt_eq_refl_ty(l)
                            }

                            symbol::BuiltIn::EqRec => {
                                debug_assert_eq!(g.levels.len(), 2);
                                let l = &g.levels[0];
                                let r = &g.levels[1];
                                self.alloc.mkt_eq_rec_ty(l, r)
                            }
                        }
                    }

                    SymbolKind::Def(d) => {
                        if g.levels.len() != 0 {
                            unimplemented!()
                        }
                        d.ty
                    }
                }
            }

            TermKind::Var(var) => {
                let ictx = self.ictx.as_mut().unwrap();
                ictx.term_type(var)
            }

            TermKind::Lambda (b) => {
                self.infer_type_as_sort(b.ty)?;

                self.save_lctx(|this| {
                    let id = this.lctx.extend(b.ty, None);
                    let value = b.val.instantiate(this.alloc.mkt_local(id), this.alloc);

                    let value_ty = this.infer_type(value)?;
                    Some(this.alloc.mkt_forall(b.name, b.ty, value_ty.abstracc(id, this.alloc)))
                })?
            }

            TermKind::Forall (b) => {
                let param_level = self.infer_type_as_sort(b.ty)?;

                self.save_lctx(|this| {
                    let id = this.lctx.extend(b.ty, None);
                    let value = b.val.instantiate(this.alloc.mkt_local(id), this.alloc);

                    let value_level = this.infer_type_as_sort(value)?;
                    Some(this.alloc.mkt_sort(param_level.imax(value_level, this.alloc)))
                })?
            }

            TermKind::Apply (app) => {
                let fun_ty = self.infer_type_as_forall(app.fun)?;
                /* @temp: type checking.
                let arg_ty = self.infer_type(app.arg)?;

                if self.check_types {
                    if !self.expr_def_eq(fun_ty.param, arg_ty) {
                        return None;
                    }
                }
                */

                fun_ty.val.instantiate(app.arg, self.alloc)
            }

            TermKind::Nat => Term::SORT_1,
            TermKind::NatZero => Term::NAT,
            TermKind::NatSucc => Term::NAT_SUCC_TY,
            TermKind::NatRec(r) => self.alloc.mkt_nat_rec_ty(r),

            TermKind::Eq(l) => self.alloc.mkt_eq_ty(l),
            TermKind::EqRefl(l) => self.alloc.mkt_eq_refl_ty(l),
            TermKind::EqRec(l, r) => self.alloc.mkt_eq_rec_ty(l, r),
        };
        assert!(result.closed());
        // TODO: assert all locals are in current local context.

        Some(result)
    }

    pub fn infer_type_as_sort(&mut self, t: TermRef<'a>) -> Option<LevelRef<'a>> {
        let ty = self.infer_type(t)?;
        let ty = self.whnf(ty);
        if let TermKind::Sort(l) = ty.kind {
            return Some(l);
        }
        return None;
    }

    pub fn infer_type_as_forall(&mut self, t: TermRef<'a>) -> Option<term::Binder<'a>> {
        let ty = self.infer_type(t)?;
        let ty = self.whnf(ty);
        if let TermKind::Forall(b) = ty.kind {
            return Some(b);
        }
        return None;
    }


    //
    // weak head normal form.
    //

    // reductions: local.
    // supports ptr_eq for change detection.
    pub fn whnf_basic(&self, e: TermRef<'a>) -> (TermRef<'a>, bool) {
        match e.kind {
            TermKind::Sort (_) =>
                (e, true),

            TermKind::Bound (_) =>
                unreachable!(),

            TermKind::Local (id) => {
                let entry = self.lctx.lookup(id);
                if let Some(value) = entry.value {
                    self.whnf_basic(value)
                }
                else { (e, true) }
            }

            TermKind::Global (_) => {
                // @temp: reject axioms & opaque defs.
                (e, false)
            }

            TermKind::Var(_) => {
                unimplemented!()
            }

            TermKind::Lambda (_) |
            TermKind::Forall (_) =>
                (e, true),

            TermKind::Apply (_) =>
                (e, false),

            TermKind::Nat |
            TermKind::NatZero |
            TermKind::NatSucc |
            TermKind::NatRec(_) |
            TermKind::Eq(_) |
            TermKind::EqRefl(_) |
            TermKind::EqRec(_, _) => (e, true)
        }
    }

    // reductions: eta, let, beta, recursor.
    // supports ptr_eq for change detection.
    pub fn whnf_no_unfold(&mut self, e: TermRef<'a>) -> (TermRef<'a>, bool) {
        let (e, done) = self.whnf_basic(e);
        if done {
            return (e, true);
        }

        // eta (λ x, f x)
        if let TermKind::Lambda(binder) = e.kind {
            if let TermKind::Apply(app) = binder.val.kind {
                if let TermKind::Bound(i) = app.arg.kind {
                    if i.0 == 0 && app.fun.closed() {
                        return self.whnf_no_unfold(app.fun);
                    }
                }
            }
        }

        /*
        // let.
        if let TermKind::Let(b) = e.kind {
            let body = b.body.instantiate(b.value);
            return self.whnf_no_unfold(body);
        }
        */

        // is app?
        let (fun, num_args) = e.app_fun();
        if num_args == 0 || !fun.closed() {
            return (e, false); // if were done, would have returned above.
        }

        // head reduction.
        let old_fun = fun;
        let (fun, _) = self.whnf_no_unfold(fun);
        let changed = !fun.ptr_eq(old_fun);

        // beta.
        if fun.is_lambda() {
            let (_, args) = e.app_args();

            let mut result = fun;
            let mut i = 0;
            while let TermKind::Lambda(b) = result.kind {
                if i < args.len() {
                    result = b.val.instantiate(args[i], self.alloc);
                    i += 1;
                }
                else { break }
            }

            let result = self.alloc.mkt_apps(result, &args[i..]);
            return self.whnf_no_unfold(result);
        }

        // recursor.
        if let Some(result) = self.try_reduce_recursor(e, fun, num_args) {
            return self.whnf_no_unfold(result);
        }

        if changed {
            let result = e.replace_app_fun(fun, self.alloc);
            assert!(result.closed());
            return (result, false);
        }

        // TODO: use fun_done here?
        return (e, false);
    }

    fn try_reduce_recursor(&mut self, t: TermRef<'a>, fun: TermRef<'a>, num_args: usize) -> Option<TermRef<'a>> {
        assert!(t.closed());

        'next: { if let TermKind::NatRec(l) = fun.kind {
            if num_args < 4 { break 'next; }

            let (_, rec_args) = t.app_args();

            let mp = rec_args[0];
            let mp = self.whnf(mp);

            let (ctor, ctor_args) = mp.app_args();

            let result = match ctor.kind {
                TermKind::NatZero => {
                    assert_eq!(ctor_args.len(), 0);
                    rec_args[2]
                }

                TermKind::NatSucc => {
                    assert_eq!(ctor_args.len(), 1);

                    // Nat.rec M mz ms (Nat.succ n)
                    // ms: Π (n: Nat) (ih: M n), M n.succ

                    // result = ms n (Nat.rec M mz ms n)

                    let m  = rec_args[1];
                    let mz = rec_args[2];
                    let ms = rec_args[3];
                    let n = ctor_args[0];

                    self.alloc.mkt_apps(ms, &[
                        n,
                        self.alloc.mkt_apps(self.alloc.mkt_nat_rec(l), &[
                            n,
                            m,
                            mz,
                            ms,
                        ]),
                    ])
                }

                _ => break 'next,
            };
            assert!(result.closed());
            return Some(result);
        }}

        None
    }

    // supports ptr_eq for change detection.
    pub fn whnf(&mut self, t: TermRef<'a>) -> TermRef<'a> {
        assert!(t.closed());

        let (t, done) = self.whnf_no_unfold(t);
        if done {
            return t;
        }

        if let Some(result) = self.unfold(t) {
            return self.whnf(result);
        }

        return t;
    }


    pub fn reduce(&mut self, t: TermRef<'a>) -> TermRef<'a> {
        assert!(t.closed());

        let result = self.whnf(t);

        let result = match result.kind {
            TermKind::Sort(_) |
            TermKind::Bound(_) |
            TermKind::Local(_) |
            TermKind::Global(_) |
            TermKind::Var(_) => result,

            TermKind::Forall(b) |
            TermKind::Lambda(b) => {
                let new_ty = self.reduce(b.ty);

                let new_val = self.save_lctx(|this| {
                    let id = this.lctx.extend(b.ty, None);
                    let val = b.val.instantiate(this.alloc.mkt_local(id), this.alloc);

                    let new_val = this.reduce(val);
                    if new_val.ptr_eq(val) { b.val } else { new_val }
                });

                if let Some(b) = b.update(new_ty, new_val) {
                    if result.is_forall() { self.alloc.mkt_forall_b(b) }
                    else                  { self.alloc.mkt_lambda_b(b) }
                }
                else { result }
            }

            TermKind::Apply(a) => {
                let new_a = a.update(
                    self.reduce(a.fun),
                    self.reduce(a.arg));

                if let Some(a) = new_a {
                    self.alloc.mkt_apply_a(a)
                }
                else { result }
            }

            TermKind::Nat |
            TermKind::NatZero |
            TermKind::NatSucc |
            TermKind::NatRec(_) |
            TermKind::Eq(_) |
            TermKind::EqRefl(_) |
            TermKind::EqRec(_, _) => result,
        };
        assert!(result.closed());

        return result;
    }


    //
    // algorithmic equality
    //

    pub fn level_def_eq_basic(&mut self, a: LevelRef<'a>, b: LevelRef<'a>) -> bool {
        if a.syntax_eq(b) {
            return true;
        }

        use LevelKind::*;
        match (a.kind, b.kind) {
            (Zero, Zero) =>
                true,

            (Succ(l1), Succ(l2)) =>
                self.level_def_eq_basic(l1, l2),

            (Max (p1), Max (p2)) |
            (IMax(p1), IMax(p2)) =>
                self.level_def_eq_basic(p1.lhs, p2.lhs) &&
                self.level_def_eq_basic(p1.rhs, p2.rhs),

            /*
            (LevelKind::Lvar(i1), LevelKind::Lvar(i2)) => {
                if i1 == i2 {
                    return true;
                }

                self.assign_level(*i1, self.cx.mkl_lvar(*i2));
                true
            }

            (LevelKind::Lvar(id), _) => {
                self.assign_level(*id, b.clone());
                true
            }

            (_, LevelKind::Lvar(id)) => {
                self.assign_level(*id, a.clone());
                true
            }
            */

            _ => false,
        }
    }

    pub fn level_def_eq(&mut self, a: LevelRef<'a>, b: LevelRef<'a>) -> bool {
        self.level_def_eq_basic(a, b)
        /*
        if let Some(ivars) = &self.ivars {
            // NOTE: need to fully instantiate first; can't instantiate lvars
            //  ad-hoc while recursing.
            //  eg: `(max (lvar v) x) =?= x` fails even if `v = x`.
            //  instantiating first results in `(max x x)`, which,
            //  on construction, is turned into `x`.
            //  this is because we haven't implemented the le based equality
            //  (`a <= b && b <= a`).
            let a = ivars.instantiate_level(a);
            let b = ivars.instantiate_level(b);
            self._level_def_eq(a, b)
        }
        else {
            self._level_def_eq(a, b)
        }
        */
    }

    pub fn level_list_def_eq(&mut self, a: LevelList<'a>, b: LevelList<'a>) -> bool {
        if a.len() != b.len() {
            return false;
        }
        for i in 0..a.len() {
            if !self.level_def_eq(&a[i], &b[i]) {
                return false;
            }
        }
        true
    }


    pub fn def_eq_basic(&mut self, a: TermRef<'a>, b: TermRef<'a>) -> Option<bool> {
        assert!(a.closed());
        assert!(b.closed());

        /*
        if let Some(id) = a.try_evar() {
            if let Some(a) = self.ivars.as_mut().unwrap().expr_value(id) {
                return self.expr_def_eq_basic(a, b);
            }
        }
        if let Some(id) = b.try_evar() {
            if let Some(b) = self.ivars.as_mut().unwrap().expr_value(id) {
                return self.expr_def_eq_basic(a, b);
            }
        }
        */

        if a.syntax_eq(b) {
            return Some(true);
        }

        use TermKind::*;
        match (a.kind, b.kind) {
            (Sort(l1), Sort(l2)) => {
                Some(self.level_def_eq(l1, l2))
            }

            (Global(g1), Global(g2)) => {
                if g1.id == g2.id && self.level_list_def_eq(g1.levels, g2.levels) {
                    return Some(true);
                }
                None
            }

            (Forall(b1), Forall(b2)) |
            (Lambda(b1), Lambda(b2)) => {
                Some(self.save_lctx(|tc| {
                    // param eq.
                    if !tc.def_eq(b1.ty, b2.ty) {
                        return false;
                    }

                    let id = tc.lctx.extend(b1.ty, None);
                    let local = tc.alloc.mkt_local(id);

                    // value eq.
                    let val1 = b1.val.instantiate(local, tc.alloc);
                    let val2 = b2.val.instantiate(local, tc.alloc);
                    tc.def_eq(val1, val2)
                }))
            }

            /*
            (Evar(i1), Evar(i2)) => {
                if i1 == i2 {
                    return Some(true);
                }

                Some(self.assign_expr(*i1, self.cx.mke_evar(*i2)))
            }

            (ExprKind::Evar(id), _) => {
                Some(self.assign_expr(*id, b))
            }

            (_, ExprKind::Evar(id)) => {
                Some(self.assign_expr(*id, a))
            }
            */

            _ => None,
        }
    }

    /// - assumes `a` and `b` are well typed.
    pub fn def_eq(&mut self, a: TermRef<'a>, b: TermRef<'a>) -> bool {
        // @todo: optimize. (eg: unfold def w/ higher depth)

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
            if self.def_eq(fun1, fun2) && self.app_args_def_eq(a, b) {
                return true;
            }
        }

        // proof irrelevance.
        let ta = self.infer_type(a).unwrap();
        if let Some(l) = self.infer_type_as_sort(ta) {
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

    /// - assumes: `a.num_args = b.num_args`.
    pub fn app_args_def_eq(&mut self, a: TermRef<'a>, b: TermRef<'a>) -> bool {
        let TermKind::Apply(a) = a.kind else { return true };
        let TermKind::Apply(b) = b.kind else { return true };

        if !self.def_eq(a.arg, b.arg) {
            return false;
        }

        return self.app_args_def_eq(a.fun, b.fun);
    }

    fn unfold(&self, t: TermRef<'a>) -> Option<TermRef<'a>> {
        let (fun, _) = t.app_fun();

        let TermKind::Global(g) = fun.kind else { return None };

        let symbol = self.env.symbol(g.id);
        match symbol.kind {
            SymbolKind::Root => unreachable!(),

            SymbolKind::BuiltIn(_) => None,

            SymbolKind::Def(d) => {
                debug_assert_eq!(g.levels.len(), d.num_levels as usize);
                let val = d.val.instantiate_levels(g.levels, self.alloc);
                Some(t.replace_app_fun(val, self.alloc))
            }
        }
    }
}

