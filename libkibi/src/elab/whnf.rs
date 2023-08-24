use crate::tt::*;

use super::*;


impl<'me, 'err, 'a> Elab<'me, 'err, 'a> {
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

    pub fn whnf_forall(&mut self, t: TermRef<'a>) -> Option<&'a term::Binder<'a>> {
        if let TermKind::Forall(b) = &self.whnf(t).kind {
            return Some(b);
        }
        return None;
    }


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

            TermKind::IVar(var) => {
                if let Some(value) = var.value(self) {
                    self.whnf_basic(value)
                }
                else { (e, false) } // could get assigned, ig.
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

            let mp = rec_args[3];
            let mp = self.whnf(mp);

            let (ctor, ctor_args) = mp.app_args();

            let result = match ctor.kind {
                TermKind::NatZero => {
                    assert_eq!(ctor_args.len(), 0);
                    rec_args[1]
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

                    self.alloc.mkt_apps(ms, &[
                        n,
                        self.alloc.mkt_apps(self.alloc.mkt_nat_rec(l), &[
                            m,
                            mz,
                            ms,
                            n,
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


    pub fn unfold(&self, t: TermRef<'a>) -> Option<TermRef<'a>> {
        let (fun, _) = t.app_fun();

        let TermKind::Global(g) = fun.kind else { return None };

        let symbol = self.env.symbol(g.id);
        match symbol.kind {
            SymbolKind::Root => unreachable!(),

            SymbolKind::BuiltIn(_) => None,

            SymbolKind::Def(d) => {
                debug_assert_eq!(g.levels.len(), d.num_levels as usize);
                let val = d.val.instantiate_level_params(g.levels, self.alloc);
                Some(t.replace_app_fun(val, self.alloc))
            }
        }
    }


    pub fn reduce(&mut self, t: TermRef<'a>) -> TermRef<'a> {
        self.reduce_ex(t, true)
    }

    pub fn reduce_ex(&mut self, t: TermRef<'a>, unfold: bool) -> TermRef<'a> {
        assert!(t.closed());

        let result = if unfold { self.whnf(t) } else { self.whnf_no_unfold(t).0 };

        let result = match result.kind {
            TermKind::Bound(_) => unreachable!(),

            TermKind::Forall(b) |
            TermKind::Lambda(b) => {
                let new_ty = self.reduce_ex(b.ty, unfold);

                let save = self.lctx.save();

                let id = self.lctx.push(b.ty, None);
                let val = b.val.instantiate(self.alloc.mkt_local(id), self.alloc);

                let new_val = self.reduce_ex(val, unfold);
                let new_val = new_val.abstracc(id, self.alloc);
                let new_val = if new_val.ptr_eq(val) { b.val } else { new_val };

                self.lctx.restore(save);

                b.update(result, self.alloc, new_ty, new_val)
            }

            TermKind::Apply(a) =>
                a.update(result, self.alloc,
                    self.reduce_ex(a.fun, unfold),
                    self.reduce_ex(a.arg, unfold)),

            TermKind::Sort(_)   | TermKind::Local(_)  | TermKind::Global(_) |
            TermKind::IVar(_)   | TermKind::Nat       | TermKind::NatZero   |
            TermKind::NatSucc   | TermKind::NatRec(_) | TermKind::Eq(_)     |
            TermKind::EqRefl(_) | TermKind::EqRec(_, _) =>
                result,
        };
        assert!(result.closed());

        return result;
    }

}

