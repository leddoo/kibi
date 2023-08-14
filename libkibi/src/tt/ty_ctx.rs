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

                    let value_ty = this.infer_type(&value)?;
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
                let fun_ty = self.infer_type_as_forall(&app.fun)?;
                /* @temp
                let arg_ty = self.infer_type(&app.arg)?;

                if self.check_types {
                    if !self.expr_def_eq(&fun_ty.param, &arg_ty) {
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
                        return self.whnf_no_unfold(&app.fun);
                    }
                }
            }
        }

        /*
        // let.
        if let TermKind::Let(b) = e.kind {
            let body = b.body.instantiate(&b.value);
            return self.whnf_no_unfold(&body);
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
                    result = b.val.instantiate(&args[i], self.alloc);
                    i += 1;
                }
                else { break }
            }

            let result = self.alloc.mkt_apps(result, &args[i..]);
            return self.whnf_no_unfold(result);
        }

        // recursor.
        if let Some(result) = self.try_reduce_recursor(&e, &fun, num_args) {
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
        if let Some(result) = self.unfold(&e) {
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
}

