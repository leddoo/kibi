use sti::arena_pool::ArenaPool;

use crate::tt::*;

use super::*;


impl<'me, 'err, 'a> Elab<'me, 'err, 'a> {
    // supports ptr_eq for change detection.
    pub fn whnf(&mut self, t: Term<'a>) -> Term<'a> {
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

    pub fn whnf_forall(&mut self, t: Term<'a>) -> Option<term::Binder<'a>> {
        if let Some(binder) = t.try_forall() { return Some(binder) }
        self.whnf(t).try_forall()
    }

    pub fn whnf_sort(&mut self, t: Term<'a>) -> Option<Level<'a>> {
        if let Some(level) = t.try_sort() { return Some(level) }
        self.whnf(t).try_sort()
    }


    // reductions: local.
    // supports ptr_eq for change detection.
    pub fn whnf_basic(&self, e: Term<'a>) -> (Term<'a>, bool) {
        match e.data() {
            TermData::Sort (_) =>
                (e, true),

            TermData::Bound (_) =>
                unreachable!(),

            TermData::Local (id) => {
                let entry = self.lctx.lookup(id);
                if let Some(value) = entry.value {
                    self.whnf_basic(value)
                }
                else { (e, true) }
            }

            TermData::Global (_) => {
                // @temp: reject axioms & opaque defs.
                (e, false)
            }

            TermData::IVar(var) => {
                if let Some(value) = var.value(self) {
                    self.whnf_basic(value)
                }
                else { (e, false) } // could get assigned, ig.
            }

            TermData::Lambda (_) |
            TermData::Forall (_) =>
                (e, true),

            TermData::Apply (_) =>
                (e, false),
        }
    }

    // reductions: eta, let, beta, recursor.
    // supports ptr_eq for change detection.
    pub fn whnf_no_unfold(&mut self, e: Term<'a>) -> (Term<'a>, bool) {
        let (e, done) = self.whnf_basic(e);
        if done {
            return (e, true);
        }

        // eta (λ x, f x)
        if let Some(binder) = e.try_lambda() {
            if let Some(app) = binder.val.try_apply() {
                if let Some(bvar) = app.arg.try_bvar() {
                    if bvar.offset == 0 && app.fun.closed() {
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
            // @todo: wait, how can `fun` not be closed?
            // also, shouldn't we be asserting `closed`
            // on entry for these functions?
            return (e, false); // if were done, would have returned above.
        }

        // head reduction.
        let old_fun = fun;
        let (fun, _) = self.whnf_no_unfold(fun);
        let changed = !fun.ptr_eq(old_fun);

        // beta.
        if fun.is_lambda() {
            let temp = ArenaPool::tls_get_temp();
            let (_, args) = e.app_args(&*temp);

            let mut result = fun;
            let mut i = 0;
            while let Some(lam) = result.try_lambda() {
                if i < args.len() {
                    result = lam.val.instantiate(args[i], self.alloc);
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

    fn try_reduce_recursor(&mut self, t: Term<'a>, fun: Term<'a>, num_args: usize) -> Option<Term<'a>> {
        assert!(t.closed());

        let _ = (fun, num_args);

        None
    }


    pub fn unfold(&self, t: Term<'a>) -> Option<Term<'a>> {
        let (fun, _) = t.app_fun();

        let g = fun.try_global()?;

        let symbol = self.env.symbol(g.id);
        match symbol.kind {
            SymbolKind::Root |
            SymbolKind::Predeclared |
            SymbolKind::Pending => unreachable!(),

            SymbolKind::IndAxiom(_) => None,

            SymbolKind::Def(d) => {
                debug_assert_eq!(g.levels.len(), d.num_levels as usize);
                if let Some(val) = d.val {
                    let val = val.instantiate_level_params(g.levels, self.alloc);
                    Some(t.replace_app_fun(val, self.alloc))
                }
                else { None }
            }
        }
    }


    pub fn reduce(&mut self, t: Term<'a>) -> Term<'a> {
        self.reduce_ex(t, true)
    }

    pub fn reduce_ex(&mut self, t: Term<'a>, unfold: bool) -> Term<'a> {
        assert!(t.closed());

        let result = if unfold { self.whnf(t) } else { self.whnf_no_unfold(t).0 };

        let result = match result.data() {
            TermData::Bound(_) => unreachable!(),

            TermData::Forall(b) |
            TermData::Lambda(b) => {
                let new_ty = self.reduce_ex(b.ty, unfold);

                let save = self.lctx.save();

                let id = self.lctx.push(b.kind, b.name, b.ty, None);
                let val = b.val.instantiate(self.alloc.mkt_local(id), self.alloc);

                let new_val = self.reduce_ex(val, unfold);
                let new_val = new_val.abstracc(id, self.alloc);
                let new_val = if new_val.ptr_eq(val) { b.val } else { new_val };

                self.lctx.restore(save);

                b.update(result, self.alloc, new_ty, new_val)
            }

            TermData::Apply(a) =>
                a.update(result, self.alloc,
                    self.reduce_ex(a.fun, unfold),
                    self.reduce_ex(a.arg, unfold)),

            TermData::Sort(_)   | TermData::Local(_)  | TermData::Global(_) |
            TermData::IVar(_) =>
                result,
        };
        assert!(result.closed());

        return result;
    }

}

