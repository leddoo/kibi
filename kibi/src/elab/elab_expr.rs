use sti::traits::CopyIt;
use sti::arena_pool::ArenaPool;

use crate::ast::*;
use crate::tt::{self, *};

use super::*;


impl<'me, 'err, 'a> Elab<'me, 'err, 'a> {
    pub fn elab_expr(&mut self, expr: ExprId) -> Option<(Term<'a>, Term<'a>)> {
        self.elab_expr_ex(expr, None)
    }

    pub fn elab_expr_checking_type(&mut self, expr: ExprId, expected_ty: Option<Term<'a>>) -> Option<(Term<'a>, Term<'a>)> {
        let (term, ty) = self.elab_expr_ex(expr, expected_ty)?;

        if let Some(expected) = expected_ty {
            if !self.ensure_def_eq(ty, expected) {
                let expected = self.instantiate_term_vars(expected);
                let ty       = self.instantiate_term_vars(ty);
                let expected = self.reduce_ex(expected, false);
                let ty       = self.reduce_ex(ty, false);
                self.error(expr, |alloc| {
                    let mut pp = TermPP::new(self.env, &self.strings, alloc);
                    let expected = pp.pp_term(expected);
                    let found    = pp.pp_term(ty);
                    ElabError::TypeMismatch { expected, found }
                });
                return None;
            }
        }

        Some((term, ty))
    }

    pub fn elab_expr_as_type(&mut self, expr: ExprId) -> Option<(Term<'a>, tt::Level<'a>)> {
        let (term, ty) = self.elab_expr_ex(expr, None)?;

        let ty = self.whnf(ty);
        if let Some(l) = ty.try_sort() {
            return Some((term, l));
        }

        let (ty_var, l) = self.new_ty_var();
        if self.ensure_def_eq(term, ty_var) {
            return Some((ty_var, l));
        }

        self.error(expr, |alloc| {
            let mut pp = TermPP::new(self.env, &self.strings, alloc);
            let found = pp.pp_term(ty);
            ElabError::TypeExpected { found }
        });
        return None;
    }


    fn elab_expr_ex(&mut self, expr: ExprId, expected_ty: Option<Term<'a>>) -> Option<(Term<'a>, Term<'a>)> {
        let result = self.elab_expr_core(expr, expected_ty);

        #[cfg(debug_assertions)]
        if let Some((res, ty)) = result {
            let n = self.ivars.assignment_gen;
            let inferred = self.infer_type(res).unwrap();
            if !self.ensure_def_eq(ty, inferred) {
                println!("---\nbug: elab_expr_core returned term\n{}\nwith type\n{}\nbut has type\n{}\n---",
                    self.pp(res, 80),
                    self.pp(ty, 80),
                    self.pp(inferred, 80));
                assert!(false);
            }
            assert_eq!(n, self.ivars.assignment_gen);
        }

        return result;
    }

    fn elab_expr_core(&mut self, expr_id: ExprId, expected_ty: Option<Term<'a>>) -> Option<(Term<'a>, Term<'a>)> {
        let expr = self.parse.exprs[expr_id];
        Some(match expr.kind {
            ExprKind::Hole => {
                self.new_term_var()
            }

            ExprKind::Ident(name) => {
                if let Some(local) = self.lookup_local(name) {
                    let ty = self.lctx.lookup(local).ty;
                    (self.alloc.mkt_local(local), ty)
                }
                else {
                    let symbol = self.lookup_symbol_ident(expr_id.into(), name)?;
                    self.elab_symbol(expr_id.into(), symbol, &[])?
                }
            }

            ExprKind::Path(path) => {
                let symbol = self.lookup_symbol_path(expr_id.into(), path.local, path.parts)?;
                self.elab_symbol(expr_id.into(), symbol, &[])?
            }

            ExprKind::Levels(it) => {
                let symbol = match it.symbol {
                    IdentOrPath::Ident(name) => {
                        if self.lookup_local(name).is_some() {
                            self.error(expr_id, |alloc|
                                ElabError::SymbolShadowedByLocal(
                                    alloc.alloc_str(&self.strings[name])));
                        }

                        self.lookup_symbol_ident(expr_id.into(), name)?
                    }

                    IdentOrPath::Path(path) => {
                        self.lookup_symbol_path(expr_id.into(), path.local, path.parts)?
                    }
                };

                self.elab_symbol(expr_id.into(), symbol, it.levels)?
            }

            ExprKind::Sort(l) => {
                let l = self.elab_level(l)?;
                (self.alloc.mkt_sort(l),
                 self.alloc.mkt_sort(l.succ(self.alloc)))
            }

            ExprKind::Forall(it) => {
                let temp = ArenaPool::tls_get_rec();
                let locals = self.elab_binders(it.binders, &*temp)?;

                let (mut result, mut level) = self.elab_expr_as_type(it.ret)?;

                for (id, _, l) in locals.iter().rev().copied() {
                    level = l.imax(level, self.alloc);

                    result = self.mk_binder(result, id, true);
                    self.lctx.pop(id);
                }
                self.locals.truncate(self.locals.len() - locals.len());

                (result, self.alloc.mkt_sort(level))
            }

            ExprKind::Lambda(it) => {
                let temp = ArenaPool::tls_get_rec();
                let locals = self.elab_binders(it.binders, &*temp)?;

                let mut expected_ty = expected_ty;
                for (id, ty, _) in locals.iter().copied() {
                    if let Some(expected) = expected_ty {
                        if let Some(pi) = self.whnf_forall(expected) {
                            if self.is_def_eq(ty, pi.ty) {
                                expected_ty = Some(
                                    pi.val.instantiate(
                                        self.alloc.mkt_local(id), self.alloc));
                            }
                            else { expected_ty = None }
                        }
                        else { expected_ty = None }
                    }
                }

                let (mut result, mut result_ty) = self.elab_expr_checking_type(it.value, expected_ty)?;

                for (id, _, _) in locals.iter().rev().copied() {
                    result    = self.mk_binder(result,    id, false);
                    result_ty = self.mk_binder(result_ty, id, true);
                    self.lctx.pop(id);
                }
                self.locals.truncate(self.locals.len() - locals.len());

                (result, result_ty)
            }
            
            ExprKind::Parens(it) => {
                return self.elab_expr_ex(it, expected_ty);
            }

            ExprKind::Call(it) => {
                let (func, func_ty) = self.elab_expr(it.func)?;

                if let Some(expected_ty) = expected_ty {
                    if let Some(result) = self.try_elab_as_elim(func, func_ty, it.args, expected_ty).0 {
                        return result;
                    }
                }

                let temp = ArenaPool::tls_get_rec();

                let mut impl_args = Vec::new_in(&*temp);

                let mut args = it.args.copy_it();
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
                    self.error(expr_id, |_| { ElabError::TooManyArgs });
                    return None;
                }

                for (trayt, ivar) in impl_args.iter().copied() {
                    if !self.resolve_impl(trayt, ivar) {
                        println!("error: no matching impl found");
                        return None;
                    }
                }

                (result, result_ty)
            }

            ExprKind::Number(n) => {
                let n = self.parse.numbers[n];
                let n = u32::from_str_radix(n, 10).unwrap();
                (self.alloc.mkt_nat_val(n), Term::NAT)
            }

            _ => {
                println!("unimp expr kind {:?}", expr);
                return None
            }
        })
    }

}

