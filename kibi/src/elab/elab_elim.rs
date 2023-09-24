use sti::traits::CopyIt;
use sti::arena_pool::ArenaPool;

use crate::ast::*;
use crate::tt::*;
use crate::tt::inductive::{ElimArgKind, ElimInfo};

use super::*;


impl<'me, 'c, 'out> Elaborator<'me, 'c, 'out> {
    pub fn try_elab_as_elim(&mut self,
        app_expr: ExprId,
        func: Term<'out>,
        func_ty: Term<'out>,
        args: &[ExprId],
        expected_ty: Term<'out>
    ) -> (Option<(Term<'out>, Term<'out>)>,)
    {
        let Some(info) = self.elim_info(func) else { return (None,) };

        /* @temp: named & explicit args.
        let motive_arg = &args[info.motive];
        let expr::CallArg::Positional(motive_arg) = motive_arg else { unimplemented!() };
        let ExprKind::Hole = motive_arg.kind else {
            //println!("motive not hole");
            return (None,) 
        };
        */

        //println!();
        //println!("!!! elab as elim {:?}", func);

        let temp = ArenaPool::tls_get_rec();

        let mut motive = None;
        let mut targets = Vec::new_in(&*temp);
        let mut postponed = Vec::with_cap_in(&*temp, args.len());

        let source = (self.item_id.some(), app_expr.some());

        // apply args to func.
        // create vars for motive and non-target args.
        let mut arg_iter = args.copy_it();
        let mut result    = func;
        let mut result_ty = func_ty;
        let mut param_idx = 0;
        while let Some(pi) = result_ty.try_forall() {
            if 0==1 {
                eprintln!("param {:?} {:?} {:?}",
                    &self.strings[pi.name],
                    pi.kind,
                    pi.ty);
            }

            let arg = match pi.kind {
                BinderKind::Explicit => {
                    if let Some(arg) = arg_iter.next() { Some(arg) }
                    else { break }
                }

                BinderKind::Implicit => None
            };

            //println!("{:?}\n", info.args[param_idx]);

            let arg = match info.args[param_idx] {
                ElimArgKind::Motive => {
                    if let Some(arg) = arg {
                        assert!(matches!(self.parse.exprs[arg].kind, ExprKind::Hole));
                    }

                    //println!("motive: {}", self.pp(pi.ty, 80));

                    let var = self.new_term_var_of_type(pi.ty);
                    motive = Some(var);
                    var
                }

                ElimArgKind::Target | ElimArgKind::Extra => {
                    let arg = if let Some(arg) = arg {
                        self.elab_expr_checking_type(arg, Some(pi.ty)).0
                    }
                    else {
                        self.new_term_var_of_type(pi.ty)
                    };

                    if info.args[param_idx] == ElimArgKind::Target {
                        targets.push(arg);
                    }

                    arg
                }

                ElimArgKind::Postpone => {
                    if let Some(arg) = arg {
                        let var = self.new_term_var_of_type(pi.ty);
                        postponed.push((arg, var, pi.ty));
                        var
                    }
                    else {
                        self.new_term_var_of_type(pi.ty)
                    }
                }
            };

            //println!("arg: {}", self.pp(arg, 80));

            result     = self.alloc.mkt_apply(result, arg, source);
            result_ty  = pi.val.instantiate(arg, self.alloc);
            param_idx += 1;
        }
        let result    = result;
        let result_ty = result_ty;

        let Some(motive) = motive else {
            // todo: uh, can this happen?
            eprintln!("no motive");
            return (Some(self.mkt_ax_error(expected_ty, source)),);
        };

        // add remaining locals to context.
        let mut rem = result_ty;
        let mut rem_locals = Vec::new_in(&*temp);
        while let Some(pi) = rem.try_forall() {
            let id = self.lctx.push(pi.name, pi.ty, ScopeKind::Binder(pi.kind));
            rem_locals.push(id);

            let local = self.alloc.mkt_local(id, TERM_SOURCE_NONE);
            if info.args[param_idx] == ElimArgKind::Target {
                targets.push(local);
            }
            param_idx += 1;

            rem = pi.val.instantiate(local, self.alloc);
        }

        // adjust expected_ty.
        let mut expected_ty = expected_ty;

        // under applied.
        if rem_locals.len() > 0 {
            debug_assert!(arg_iter.len() == 0);

            let old_scope = self.lctx.current;

            for rem in rem_locals.iter().copied() {
                let Some(pi) = expected_ty.try_forall() else {
                    // @todo: better source, what went wrong here?
                    self.error(app_expr, ElabError::TempTBD);
                    return (Some(self.mkt_ax_error(expected_ty, source)),);
                };

                expected_ty = pi.val.instantiate(self.alloc.mkt_local(rem, TERM_SOURCE_NONE), self.alloc);
            }

            self.lctx.current = old_scope;
        }

        // over applied.
        let mut result = result;
        let result_ty_valid = arg_iter.len() == 0;
        if arg_iter.len() > 0 {
            debug_assert!(rem_locals.len() == 0);

            for arg in arg_iter.rev() {
                let (arg, arg_ty) = self.elab_expr(arg);

                result = self.alloc.mkt_apply(result, arg, TERM_SOURCE_NONE);

                let val = self.abstract_eq(expected_ty, arg);
                expected_ty = self.alloc.mkt_forall(
                    BinderKind::Explicit, Atom::NULL, arg_ty, val, TERM_SOURCE_NONE);
            }
        }
        let result = result;

        //println!("expected: {}", self.pp(expected_ty, 80));

        // create motive.
        let mut motive_val = expected_ty;
        for target in targets.iter().copied().rev() {
            motive_val = self.instantiate_term_vars(motive_val);
            //println!("val: {}", self.pp(motive_val, 80));

            let target    = self.instantiate_term_vars(target);
            let target_ty = self.infer_type(target).unwrap();
            //println!("abstract out {}", self.pp(target, 80));

            let val = self.abstract_eq(motive_val, target);
            // @todo: use motive binder names.
            motive_val = self.alloc.mkt_lambda(
                BinderKind::Explicit, Atom::NULL, target_ty, val, source);
        }

        if 0==1 {
            let val = self.instantiate_term_vars(motive_val);
            eprintln!("motive: {}", self.pp(val, 80));
        }

        // assign.
        if !self.ensure_def_eq(motive, motive_val) {
            let motive     = self.instantiate_term_vars(motive);
            let motive_val = self.instantiate_term_vars(motive_val);
            eprintln!("motive failed");
            eprintln!("motive:     {}", self.pp(motive,     80));
            eprintln!("motive_val: {}", self.pp(motive_val, 80));
            return (Some(self.mkt_ax_error(expected_ty, source)),);
        }

        // elab remaining args.
        for (arg_expr, var, expected_ty) in postponed.iter().copied() {
            let expected_ty = self.instantiate_term_vars(expected_ty);
            let (arg, _) = self.elab_expr_checking_type(arg_expr, Some(expected_ty));

            if !self.ensure_def_eq(var, arg) {
                // @todo: context.
                self.error(arg_expr, ElabError::TempArgFailed);
                return (Some(self.mkt_ax_error(expected_ty, source)),);
            }
        }

        let result = self.instantiate_term_vars(result);
        let result_ty =
            if result_ty_valid {
                self.instantiate_term_vars(result_ty)
            }
            else { self.infer_type(result).unwrap() };

        (Some((result, result_ty)),)
    }

    fn elim_info(&self, func: Term<'out>) -> Option<ElimInfo<'out>> {
        let global = func.try_global()?;

        if let SymbolKind::IndAxiom(ind) = &self.env.symbol(global.id).kind {
            if ind.kind == symbol::IndAxiomKind::Eliminator {
                return Some(ind.info.elim_info);
            }
        }

        None
    }
}

