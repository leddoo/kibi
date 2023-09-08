use sti::arena_pool::ArenaPool;

use crate::tt::*;

use super::*;


impl<'me, 'err, 'a> Elab<'me, 'err, 'a> {
    pub fn is_def_eq(&mut self, a: Term<'a>, b: Term<'a>) -> bool {
        let save = self.save();

        let r = self.ensure_def_eq(a, b);
        if !r {
            self.restore(save);
        }

        return r;
    }

    /// - assumes `a` and `b` are well typed.
    pub fn ensure_def_eq(&mut self, a: Term<'a>, b: Term<'a>) -> bool {
        // @todo: optimize. (eg: unfold def w/ higher depth)

        //println!("{}\n=?=\n{}\n", self.pp(a, 80), self.pp(b, 80));

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
            return self.ensure_def_eq(a, b);
        }
        if let Some(b) = self.unfold(b) {
            return self.ensure_def_eq(a, b);
        }

        // note: exprs are now in whnf.
        let (fun1, num_args1) = a.app_fun();
        let (fun2, num_args2) = b.app_fun();

        // app.
        if num_args1 > 0 && num_args1 == num_args2 {
            if self.ensure_def_eq(fun1, fun2) && self.app_args_def_eq(a, b) {
                return true;
            }
        }

        // proof irrelevance.
        let ta = self.infer_type(a).unwrap();
        if let Some(l) = self.infer_type_as_sort(ta) {
            if l.is_zero() {
                let tb = self.infer_type(b).unwrap();
                if self.ensure_def_eq(ta, tb) {
                    return true;
                }
            }
        }

        // failed.
        return false;
    }

    fn def_eq_basic(&mut self, a: Term<'a>, b: Term<'a>) -> Option<bool> {
        assert!(a.closed());
        assert!(b.closed());
        //println!("{}\n=?=\n{}\n", self.pp(a, 80), self.pp(b, 80));

        // instantiate inference vars.
        if let Some(var) = a.try_ivar() {
            if let Some(a) = var.value(self) {
                return self.def_eq_basic(a, b);
            }
        }
        if let Some(var) = b.try_ivar() {
            if let Some(b) = var.value(self) {
                return self.def_eq_basic(a, b);
            }
        }

        // handles same ivar.
        if a.syntax_eq(b) {
            return Some(true);
        }

        let temp = ArenaPool::tls_get_temp();

        if let Some((var, args)) = a.try_ivar_app(&*temp) {
            // @mega@temp
            if let Some(value) = var.value(self) {
                let a = a.replace_app_fun(value, self.alloc);
                return self.def_eq_basic(a, b);
            }
            if let Some(result) = var.assign(&args, b, self) {
                return Some(result);
            }
        }

        if let Some((var, args)) = b.try_ivar_app(&*temp) {
            // @mega@temp
            if let Some(value) = var.value(self) {
                let b = b.replace_app_fun(value, self.alloc);
                return self.def_eq_basic(a, b);
            }
            if let Some(result) = var.assign(&args, a, self) {
                return Some(result);
            }
        }

        use TermData::*;
        match (a.data(), b.data()) {
            (Sort(l1), Sort(l2)) => {
                Some(self.ensure_level_def_eq(l1, l2))
            }

            (Global(g1), Global(g2)) => {
                if g1.id == g2.id && self.ensure_levels_def_eq(g1.levels, g2.levels) {
                    return Some(true);
                }
                None
            }

            (Forall(b1), Forall(b2)) |
            (Lambda(b1), Lambda(b2)) => {
                // param eq.
                if !self.ensure_def_eq(b1.ty, b2.ty) {
                    return Some(false);
                }

                let id = self.lctx.push(b1.kind, b1.name, b1.ty, None);
                let local = self.alloc.mkt_local(id);

                // value eq.
                let val1 = b1.val.instantiate(local, self.alloc);
                let val2 = b2.val.instantiate(local, self.alloc);

                self.lctx.pop(id);

                Some(self.ensure_def_eq(val1, val2))
            }

            _ => None,
        }
    }

    /// - assumes: `a.num_args = b.num_args`.
    fn app_args_def_eq(&mut self, a: Term<'a>, b: Term<'a>) -> bool {
        let Some(a) = a.try_apply() else { return true };
        let Some(b) = b.try_apply() else { return true };

        if !self.ensure_def_eq(a.arg, b.arg) {
            return false;
        }

        return self.app_args_def_eq(a.fun, b.fun);
    }
}

