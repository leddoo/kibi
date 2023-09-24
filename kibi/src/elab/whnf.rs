use sti::arena_pool::ArenaPool;

use crate::tt::*;
use crate::env::SymbolKind;

use super::*;


impl<'me, 'c, 'out> Elaborator<'me, 'c, 'out> {
    // supports ptr_eq for change detection.
    pub fn whnf(&mut self, t: Term<'out>) -> Term<'out> {
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

    pub fn whnf_forall(&mut self, t: Term<'out>) -> Option<term::Binder<'out>> {
        if let Some(binder) = t.try_forall() { return Some(binder) }
        self.whnf(t).try_forall()
    }

    pub fn whnf_sort(&mut self, t: Term<'out>) -> Option<Level<'out>> {
        if let Some(level) = t.try_sort() { return Some(level) }
        self.whnf(t).try_sort()
    }


    // reductions: local.
    // supports ptr_eq for change detection.
    pub fn whnf_basic(&self, e: Term<'out>) -> (Term<'out>, bool) {
        match e.data() {
            TermData::Sort (_) =>
                (e, true),

            TermData::Bound (_) =>
                unreachable!(),

            TermData::Local (id) => {
                let entry = self.lctx.lookup(id);
                if let ScopeKind::Local(value) = entry.kind {
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

            TermData::Let (_) =>
                (e, false),

            TermData::Apply (_) =>
                (e, false),
        }
    }

    // reductions: eta, let, beta, recursor.
    // supports ptr_eq for change detection.
    pub fn whnf_no_unfold(&mut self, e: Term<'out>) -> (Term<'out>, bool) {
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

        // let.
        if let Some(b) = e.try_let() {
            let body = b.body.instantiate(b.val, self.alloc);
            return self.whnf_no_unfold(body);
        }

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
            let result = {
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

                self.alloc.mkt_apps(result, &args[i..], e.source())
            };
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

    fn try_reduce_recursor(&mut self, t: Term<'out>, fun: Term<'out>, num_args: usize) -> Option<Term<'out>> {
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
            //println!("not enough args");
            return None;
        }

        //println!("elim thing !! {}", self.pp(t, 80));

        let temp = ArenaPool::tls_get_rec();
        let (_, args) = t.app_args(&*temp);

        //println!("args:");
        //for arg in args.iter().copied() { println!("  {}", self.pp(arg, 80)); }


        let mp = args[min_args - 1];
        let mp = self.whnf(mp);

        let (mp_fun, _) = mp.app_fun();
        let mp_global = mp_fun.try_global()?;
        let SymbolKind::IndAxiom(mp_ind) = self.env.symbol(mp_global.id).kind else {
            //println!("not an inductive");
            return None;
        };
        if !core::ptr::eq(mp_ind.info, ind.info) {
            //println!("not same inductive");
            return None;
        }
        let symbol::IndAxiomKind::Constructor(ctor_idx) = mp_ind.kind else {
            debug_assert!(mp_ind.kind == symbol::IndAxiomKind::Eliminator);
            return None;
        };

        let (_, mp_args) = mp.app_args(&*temp);

        //println!("major premise ({ctor_idx}) args:");
        //for arg in mp_args.iter().copied() { println!("  {}", self.pp(arg, 80)); }


        let mut result = ind.info.comp_rules[ctor_idx as usize];
        //println!("comp: {}\n", self.pp(result, 80));

        // Name.rec   ps Ms ms cxs (ctor_i ps as) ⇝ ms_i as mvs
        // comp_i = λ ps Ms ms                as,   ms_i as mvs

        let rec_args  = &args[.. (info.num_params + info.num_motives + info.num_minors) as usize];
        let app_args  = &args[min_args..];
        let ctor_args = &mp_args[info.num_params as usize ..];

        for arg in rec_args.iter().copied() {
            //println!("arg {}", self.pp(arg, 80));
            let Some(lam) = result.try_lambda() else { unreachable!() };
            result = lam.val.instantiate(arg, self.alloc);
            //println!("result: {}\n", self.pp(result, 80));
        }

        for arg in ctor_args.iter().copied() {
            //println!("ctor_arg {}", self.pp(arg, 80));
            let Some(lam) = result.try_lambda() else { unreachable!() };
            result = lam.val.instantiate(arg, self.alloc);
            //println!("result: {}\n", self.pp(result, 80));
        }

        let result = result.instantiate_level_params(global.levels, self.alloc);

        let result = self.alloc.mkt_apps(result, app_args, t.source());

        //println!("success? {}\n", self.pp(result, 80));

        return Some(result);
    }


    pub fn unfold(&self, t: Term<'out>) -> Option<Term<'out>> {
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


    pub fn reduce(&mut self, t: Term<'out>) -> Term<'out> {
        self.reduce_ex(t, true)
    }

    pub fn reduce_ex(&mut self, t: Term<'out>, unfold: bool) -> Term<'out> {
        assert!(t.closed());

        let result = if unfold { self.whnf(t) } else { self.whnf_no_unfold(t).0 };

        let result = match result.data() {
            TermData::Bound(_) => unreachable!(),

            TermData::Forall(b) |
            TermData::Lambda(b) => {
                let new_ty = self.reduce_ex(b.ty, unfold);

                let save = self.lctx.save();

                let id = self.lctx.push(b.name, b.ty, ScopeKind::Binder(b.kind));
                let val = b.val.instantiate(self.alloc.mkt_local(id, TERM_SOURCE_NONE), self.alloc);

                let new_val = self.reduce_ex(val, unfold);
                let new_val = new_val.abstracc(id, self.alloc);
                let new_val = if new_val.ptr_eq(val) { b.val } else { new_val };

                self.lctx.restore(save);

                b.update(result, self.alloc, new_ty, new_val)
            }

            TermData::Let(b) => {
                let new_val = self.reduce_ex(b.val, unfold);
                let body = b.body.instantiate(new_val, self.alloc);
                self.reduce_ex(body, unfold)
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

