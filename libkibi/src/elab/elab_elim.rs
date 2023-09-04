use sti::arena_pool::ArenaPool;

use crate::ast::*;
use crate::tt::*;
use crate::tt::inductive::{ElimArgKind, ElimInfo};

use super::*;


impl<'me, 'err, 'a> Elab<'me, 'err, 'a> {
    pub fn try_elab_as_elim(&mut self,
        func: Term<'a>,
        func_ty: Term<'a>,
        args: &[expr::CallArg<'a>],
        expected_ty: Term<'a>
    ) -> (Option<Option<(Term<'a>, Term<'a>)>>,)
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

        let mut postponed = Vec::with_cap_in(args.len(), &*temp);

        // apply args to func.
        // create vars for motive and non-target args.
        let mut arg_iter = args.iter();
        let mut result    = func;
        let mut result_ty = func_ty;
        let mut param_idx = 0;
        while let Some(pi) = result_ty.try_forall() {
            if 0==1 {
                println!("param {:?} {:?} {:?}",
                    &self.strings[pi.name],
                    pi.kind,
                    pi.ty);
            }

            let arg = match pi.kind {
                BinderKind::Explicit => {
                    if let Some(arg) = arg_iter.next() {
                        let expr::CallArg::Positional(arg) = arg else { unimplemented!() };
                        Some(arg)
                    }
                    else { break }
                }

                BinderKind::Implicit => None
            };

            //println!("{:?}\n", info.args[param_idx]);

            let arg = match info.args[param_idx] {
                ElimArgKind::Motive => {
                    if let Some(arg) = arg {
                        assert!(matches!(arg.kind, ExprKind::Hole));
                    }

                    //println!("motive: {}", self.pp(pi.ty, 80));

                    let var = self.new_term_var_of_type(pi.ty);
                    motive = Some(var);
                    var
                }

                ElimArgKind::Target | ElimArgKind::Extra => {
                    let arg = if let Some(arg) = arg {
                        let Some((arg, _)) = self.elab_expr_checking_type(arg, Some(pi.ty)) else {
                            return (Some(None),);
                        };
                        arg
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

            result     = self.alloc.mkt_apply(result, arg);
            result_ty  = pi.val.instantiate(arg, self.alloc);
            param_idx += 1;
        }

        let Some(motive) = motive else {
            println!("no motive");
            return (Some(None),);
        };

        // adjust expected_ty.
        let mut expected_ty = expected_ty;

        // under applied.
        if result_ty.is_forall() {
            println!("under applied");
            debug_assert!(arg_iter.len() == 0);

            let old_scope = self.lctx.current;

            while let Some(pi) = result_ty.try_forall() {
                let Some(ex_pi) = self.whnf_forall(expected_ty) else {
                    println!("error");
                    return (Some(None),);
                };

                let id = self.lctx.push(pi.kind, pi.name, pi.ty, None);
                expected_ty = ex_pi.val.instantiate(
                    self.alloc.mkt_local(id), self.alloc);
            }

            self.lctx.current = old_scope;
        }
        // over applied.
        else if arg_iter.len() > 0 {
            println!("over applied");
            // elab and add remaining args.
            // revert result & expected_ty.
            unimplemented!()
        }

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
                BinderKind::Explicit, Atom::NULL, target_ty, val);
        }

        if 0==1 {
            let val = self.instantiate_term_vars(motive_val);
            println!("motive: {}", self.pp(val, 80));
        }

        // assign.
        if !self.def_eq(motive, motive_val) {
            let motive     = self.instantiate_term_vars(motive);
            let motive_val = self.instantiate_term_vars(motive_val);
            println!("motive failed");
            println!("motive:     {}", self.pp(motive,     80));
            println!("motive_val: {}", self.pp(motive_val, 80));
            return (Some(None),);
        }

        if arg_iter.len() != 0 {
            unimplemented!()
        }

        // elab remaining args.
        for (arg, var, expected_ty) in postponed.iter().copied() {
            let expected_ty = self.instantiate_term_vars(expected_ty);
            let Some((arg, _)) = self.elab_expr_checking_type(arg, Some(expected_ty)) else {
                return (Some(None),);
            };

            if !self.def_eq(var, arg) {
                println!("arg failed");
                return (Some(None),);
            }
        }

        //println!("{:?}", self.ictx.instantiate_term(result));

        (Some(Some((result, result_ty))),)
    }

    fn elim_info(&self, func: Term<'a>) -> Option<ElimInfo<'a>> {
        let global = func.try_global()?;

        if let SymbolKind::IndAxiom(ind) = &self.env.symbol(global.id).kind {
            if ind.kind == symbol::IndAxiomKind::Eliminator {
                return Some(ind.info.elim_info);
            }
        }

        None
    }
}

