use crate::tt::*;

use super::*;


impl<'me, 'err, 'a> Elab<'me, 'err, 'a> {
    pub fn def_eq_basic(&mut self, a: TermRef<'a>, b: TermRef<'a>) -> Option<bool> {
        assert!(a.closed());
        assert!(b.closed());

        // instantiate inference vars.
        if let TermKind::IVar(var) = a.kind {
            if let Some(a) = var.value(self) {
                return self.def_eq_basic(a, b);
            }
        }
        if let TermKind::IVar(var) = b.kind {
            if let Some(b) = var.value(self) {
                return self.def_eq_basic(a, b);
            }
        }

        // handles same ivar.
        if a.syntax_eq(b) {
            return Some(true);
        }

        if let Some((var, args)) = a.try_ivar_app() {
            // @mega@temp
            if let Some(value) = var.value(self) {
                let a = a.replace_app_fun(value, self.alloc);
                return self.def_eq_basic(a, b);
            }
            if let Some(result) = var.assign(&args, b, self) {
                return Some(result);
            }
        }

        if let Some((var, args)) = b.try_ivar_app() {
            // @mega@temp
            if let Some(value) = var.value(self) {
                let b = b.replace_app_fun(value, self.alloc);
                return self.def_eq_basic(a, b);
            }
            if let Some(result) = var.assign(&args, a, self) {
                return Some(result);
            }
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
                // param eq.
                if !self.def_eq(b1.ty, b2.ty) {
                    return Some(false);
                }

                let id = self.lctx.push(b1.ty, None);
                let local = self.alloc.mkt_local(id);

                // value eq.
                let val1 = b1.val.instantiate(local, self.alloc);
                let val2 = b2.val.instantiate(local, self.alloc);

                self.lctx.pop(id);

                Some(self.def_eq(val1, val2))
            }

            (NatRec(l1), NatRec(l2)) |
            (Eq    (l1), Eq    (l2)) |
            (EqRefl(l1), EqRefl(l2)) => {
                Some(self.level_def_eq(l1, l2))
            }

            (EqRec(l1, r1), EqRec(l2, r2)) => {
                Some(self.level_def_eq(l1, l2) && self.level_def_eq(r1, r2))
            }

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
}

