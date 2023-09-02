use sti::arena_pool::ArenaPool;

use crate::ast::*;
use crate::tt::*;

use super::*;


#[derive(Clone, Copy, Debug, PartialEq)]
enum ElimArgKind {
    Motive,
    Target,
    Extra,
    Postpone,
}

struct ElimInfo<'a> {
    #[allow(dead_code)]
    motive: usize,
    args: &'a [ElimArgKind],
}

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

            let arg = match info.args[param_idx] {
                ElimArgKind::Motive => {
                    if let Some(arg) = arg {
                        assert!(matches!(arg.kind, ExprKind::Hole));
                    }

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

        //println!("expected: {:?}", expected_ty);

        // create motive.
        let mut motive_val = expected_ty;
        for target in targets.iter().copied() {
            let target_ty = self.infer_type(target).unwrap();
            //println!("abstract out {:?}", target);
            let val = self.abstract_eq(motive_val, target);
            // @todo: use motive binder names.
            motive_val = self.alloc.mkt_lambda(
                BinderKind::Explicit, Atom::NULL, target_ty, val);
        }

        if 0==1 {
            let val = self.instantiate_term_vars(motive_val);
            let mut pp = TermPP::new(&self.env, &self.strings, self.alloc);
            let val = pp.pp_term(val);
            let val = pp.render(val, 50);
            let val = val.layout_string();
            println!("motive: {}", val);
        }

        // assign.
        if !self.def_eq(motive, motive_val) {
            println!("motive failed");
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

    fn elim_info(&self, func: Term<'a>) -> Option<ElimInfo<'static>> {
        if func.kind() == TermKind::NatRec {
            return Some(ElimInfo {
                motive: 0,
                args: &[
                    ElimArgKind::Motive,   // M
                    ElimArgKind::Postpone, // m_zero
                    ElimArgKind::Postpone, // m_succ
                    ElimArgKind::Target,   // n
                ],
            });
        }

        if func.kind() == TermKind::EqRec {
            return Some(ElimInfo {
                motive: 2,
                args: &[
                    ElimArgKind::Postpone, // T
                    ElimArgKind::Postpone, // a
                    ElimArgKind::Motive,   // M
                    ElimArgKind::Postpone, // m_refl
                    ElimArgKind::Target,   // b
                    ElimArgKind::Extra,    // mp
                ],
            });
        }

        None
    }
}

