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
    motive: usize,
    args: &'a [ElimArgKind],
}

impl<'me, 'err, 'a> Elab<'me, 'err, 'a> {
    pub fn try_elab_as_elim(&mut self,
        func: TermRef<'a>,
        func_ty: TermRef<'a>,
        args: &[expr::CallArg<'a>],
        expected_ty: TermRef<'a>
    ) -> (Option<Option<(TermRef<'a>, TermRef<'a>)>>,)
    {
        let Some(info) = self.elim_info(func) else { return (None,) };

        let motive_arg = &args[info.motive];
        let expr::CallArg::Positional(motive_arg) = motive_arg else { unimplemented!() };
        let ExprKind::Hole = motive_arg.kind else {
            //println!("motive not hole");
            return (None,) 
        };

        //println!("!!! elab as elim {:?}", func);

        let mut motive = None;

        let mut arg_terms = Vec::with_cap(args.len());

        let mut postponed = Vec::with_cap(args.len());

        // apply args to func.
        // create vars for motive and non-target args.
        let mut result    = func;
        let mut result_ty = func_ty;
        for (i, arg) in args.iter().enumerate() {
            let TermKind::Forall(b) = result_ty.kind else {
                break;
            };

            let expr::CallArg::Positional(arg) = arg else { unimplemented!() };

            let arg = match info.args[i] {
                ElimArgKind::Motive => {
                    let var = self.new_term_var_of_type(b.ty);
                    motive = Some(var);
                    var
                }

                ElimArgKind::Target | ElimArgKind::Extra => {
                    let Some((arg, _)) = self.elab_expr_checking_type(arg, Some(b.ty)) else {
                        return (Some(None),);
                    };
                    arg
                }

                ElimArgKind::Postpone => {
                    let var = self.new_term_var_of_type(b.ty);
                    postponed.push((arg, var, b.ty));
                    var
                }
            };
            arg_terms.push(arg);

            result    = self.alloc.mkt_apply(result, arg);
            result_ty = b.val.instantiate(arg, self.alloc);
        }

        let Some(motive) = motive else {
            println!("no motive");
            return (Some(None),);
        };

        // adjust expected_ty.
        let mut expected_ty = expected_ty;

        // under applied.
        if let TermKind::Forall(_) = result_ty.kind {
            println!("under applied");
            debug_assert!(arg_terms.len() == args.len());

            let old_scope = self.lctx.current;

            while let TermKind::Forall(b) = result_ty.kind {
                let Some(ex_b) = self.whnf_forall(expected_ty) else {
                    println!("error");
                    return (Some(None),);
                };

                let id = self.lctx.push(b.ty, None);
                expected_ty = ex_b.val.instantiate(
                    self.alloc.mkt_local(id), self.alloc);
            }

            self.lctx.current = old_scope;
        }
        // over applied.
        else if arg_terms.len() < args.len() {
            println!("over applied");
            // elab and add remaining args.
            // revert result & expected_ty.
            unimplemented!()
        }

        //println!("expected: {:?}", expected_ty);

        // create motive.
        let mut motive_val = expected_ty;
        for (i, target) in arg_terms.iter().enumerate() {
            if info.args[i] == ElimArgKind::Target {
                let target_ty = self.infer_type(target).unwrap();
                //println!("abstract out {:?}", target);
                let val = self.abstract_eq(motive_val, target);
                motive_val = self.alloc.mkt_lambda(0, target_ty, val);
            }
        }

        if 0==1 {
            let val = self.instantiate_term(motive_val);
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

        if arg_terms.len() != args.len() {
            unimplemented!()
        }

        // elab remaining args.
        for (arg, var, expected_ty) in postponed.iter().copied() {
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

    fn elim_info(&self, func: TermRef<'a>) -> Option<ElimInfo<'static>> {
        if let TermKind::NatRec(_) = func.kind {
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

        if let TermKind::EqRec(_, _) = func.kind {
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

