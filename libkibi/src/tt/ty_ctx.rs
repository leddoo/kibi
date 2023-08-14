use super::syntax::*;
use super::LocalCtx;


pub struct TyCtx<'a, 'l> {
    pub alloc: super::Alloc<'a>,

    pub lctx: &'l mut LocalCtx<'a>,
}

impl<'a, 'l> TyCtx<'a, 'l> {
    pub fn new(alloc: super::Alloc<'a>, lctx: &'l mut LocalCtx<'a>) -> Self {
        Self { alloc, lctx }
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

            TermKind::BVar (_) => {
                unreachable!()
            }

            TermKind::Local (id) => {
                self.lctx.lookup(id).ty
            }

            TermKind::Global (_) => {
                //self.env.global_type(g.id, g.levels.data())
                unimplemented!()
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
                /* @temp
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

            TermKind::Eq(_) => todo!(),
            TermKind::EqRefl(_) => todo!(),
            TermKind::EqRec(_, _) => todo!(),
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

            TermKind::BVar (_) =>
                unreachable!(),

            TermKind::Local (id) => {
                let entry = self.lctx.lookup(id);
                if let Some(value) = entry.value {
                    self.whnf_basic(value)
                }
                else { (e, true) }
            }

            TermKind::Global (_) => {
                // @temp
                (e, false)
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
                if let TermKind::BVar(i) = app.arg.kind {
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
        if num_args == 0 {
            return (e, false); // if were done, would have returned above.
        }

        // reduce head.
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
            return (e.replace_app_fun(fun, self.alloc), false);
        }

        // TODO: use fun_done here?
        (e, false)
    }

    fn try_reduce_recursor(&mut self, t: TermRef<'a>, fun: TermRef<'a>, num_args: usize) -> Option<TermRef<'a>> {
        'next: { if let TermKind::NatRec(l) = fun.kind {
            if num_args < 4 { break 'next; }

            let (_, rec_args) = t.app_args();

            let mp = rec_args[rec_args.len() - 1];
            let mp = self.whnf(mp);

            let (ctor, ctor_args) = mp.app_args();

            match ctor.kind {
                TermKind::NatZero => {
                    assert_eq!(ctor_args.len(), 0);
                    return Some(rec_args[1]);
                }

                TermKind::NatSucc => {
                    assert_eq!(ctor_args.len(), 1);

                    // Nat.rec M mz ms (Nat.succ n)
                    // ms: Π (n: Nat) (ih: M n), M n.succ

                    // result = ms n (Nat.rec M mz ms n)

                    let m  = rec_args[0];
                    let mz = rec_args[1];
                    let ms = rec_args[2];
                    let n = ctor_args[0];

                    return Some(self.alloc.mkt_apps(ms, &[
                        n,
                        self.alloc.mkt_apps(self.alloc.mkt_nat_rec(l), &[
                            m,
                            mz,
                            ms,
                            n,
                        ]),
                    ]));
                }

                _ => unreachable!()
            }
        }}

        None
    }

    // supports ptr_eq for change detection.
    pub fn whnf(&mut self, e: TermRef<'a>) -> TermRef<'a> {
        let (e, done) = self.whnf_no_unfold(e);
        if done {
            return e;
        }

        /*
        if let Some(result) = self.unfold(e) {
            return self.whnf(result);
        }
        */

        return e;
    }


    pub fn reduce(&mut self, term: TermRef<'a>) -> TermRef<'a> {
        let result = self.whnf(term);
        match result.kind {
            TermKind::Sort(_) |
            TermKind::BVar(_) |
            TermKind::Local(_) |
            TermKind::Global(_) => result,

            TermKind::Forall(b) |
            TermKind::Lambda(b) => {
                let new_b = b.update(
                    self.reduce(b.ty),
                    self.reduce(b.val));

                if let Some(b) = new_b {
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
        }
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
                if g1.id == g2.id {
                    return Some(self.level_list_def_eq(g1.levels, g2.levels));
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

        /*
        // unfold defs & retry on change.
        // TODO: unfold def(s) with highest depth.
        if let Some(a) = self.unfold(a) {
            return self.def_eq(a, b);
        }
        if let Some(b) = self.unfold(b) {
            return self.def_eq(a, b);
        }
        */

        // note: exprs are now in whnf.
        let (fun1, num_args1) = a.app_fun();
        let (fun2, num_args2) = b.app_fun();

        // @todo(speed): shouldn't we try these before
        // unfolding all the way?
        // something like whnf_no_unfold'ing args &
        // running def_eq_basic.

        // app with same global.
        if let (TermKind::Global(g1), TermKind::Global(g2)) = (fun1.kind, fun2.kind) {
            if g1.id == g2.id {
                return num_args1 == num_args2
                    && self.level_list_def_eq(g1.levels, g2.levels)
                    && self.app_args_def_eq(a, b);
            }
        }

        // regular app.
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
}

