use sti::traits::CopyIt;
use sti::arena_pool::ArenaPool;

use crate::ast::*;
use crate::tt::*;

use super::*;


impl<'me, 'c, 'out, 'a> Elaborator<'me, 'c, 'out, 'a> {
    pub fn elab_app(&mut self, app_expr: ExprId, func: ExprOrTerm<'a>, args: &[ExprId], expected_ty: Option<Term<'a>>) -> Option<(Term<'a>, Term<'a>)> {
        let (func, func_ty) = match func {
            ExprOrTerm::Expr(expr) => self.elab_expr(expr)?,
            ExprOrTerm::Term(term) => (term, self.infer_type(term).unwrap()),
        };

        if let Some(expected_ty) = expected_ty {
            if let Some(result) = self.try_elab_as_elim(app_expr, func, func_ty, args, expected_ty).0 {
                return result;
            }
        }

        let temp = ArenaPool::tls_get_rec();

        let mut impl_args = Vec::new_in(&*temp);

        let mut args = args.copy_it();
        let mut result    = func;
        let mut result_ty = func_ty;
        let mut expected_ty = expected_ty;
        while let Some(pi) = self.whnf_forall(result_ty) {
            let arg = match pi.kind {
                BinderKind::Explicit => {
                    // propagate expected type.
                    if let Some(expected) = expected_ty {
                        let mut args_remaining = args.len();
                        let mut f_ty = result_ty;
                        while let Some(pi) = f_ty.try_forall() {
                            if pi.kind == BinderKind::Explicit {
                                // not enough args.
                                if args_remaining == 0 {
                                    // prevent def_eq below.
                                    args_remaining = 1;
                                    expected_ty = None;
                                    break;
                                }
                                args_remaining -= 1;
                            }
                            f_ty = pi.val;
                        }
                        if args_remaining == 0 && f_ty.closed() {
                            if self.is_def_eq(f_ty, expected) {
                                expected_ty = None;
                            }
                        }
                    }

                    let Some(arg) = args.next() else { break };

                    let (arg, _) = self.elab_expr_checking_type(arg, Some(pi.ty))?;
                    arg
                }

                BinderKind::Implicit => {
                    let var = self.new_term_var_of_type(pi.ty);

                    // impl implicit
                    // @todo: also for explicit holes.
                    let (head, _) = pi.ty.app_fun();
                    if let Some(global) = head.try_global() {
                        if self.traits.is_trait(global.id) {
                            impl_args.push((global.id, var));
                        }
                    }

                    var
                }
            };

            result    = self.alloc.mkt_apply(result, arg);
            result_ty = pi.val.instantiate(arg, self.alloc);
        }
        if args.next().is_some() {
            self.error(app_expr, ElabError::TooManyArgs);
            return None;
        }

        for (trayt, ivar) in impl_args.iter().copied() {
            if !self.resolve_impl(trayt, ivar) {
                // @todo: better source, context.
                self.error(app_expr, ElabError::TraitResolutionFailed { trayt });
                return None;
            }
        }

        Some((result, result_ty))
    }
}

