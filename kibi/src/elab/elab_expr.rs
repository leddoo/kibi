use sti::arena_pool::ArenaPool;

use crate::ast::*;
use crate::tt::{self, *};

use super::*;


impl<'me, 'c, 'out, 'a> Elaborator<'me, 'c, 'out, 'a> {
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
                self.error(expr, {
                    let mut pp = TermPP::new(self.env, &self.strings, self.alloc_out);
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

        self.error(expr, {
            let mut pp = TermPP::new(self.env, &self.strings, self.alloc_out);
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
                eprintln!("---\nbug: elab_expr_core returned term\n{}\nwith type\n{}\nbut has type\n{}\n---",
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
                            self.error(expr_id,
                                ElabError::SymbolShadowedByLocal(
                                    self.alloc_out.alloc_str(&self.strings[name])));
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
                self.elab_app(expr_id, ExprOrTerm::Expr(it.func), it.args, expected_ty)?
            }

            ExprKind::Number(n) => {
                let n = self.parse.numbers[n];
                let n = u32::from_str_radix(n, 10).unwrap();
                (self.alloc.mkt_nat_val(n), Term::NAT)
            }

            ExprKind::Eq(a, b) => {
                let eq = self.alloc.mkt_global(
                    SymbolId::EQ,
                    &self.alloc.alloc_new([self.new_level_var()])[..]);
                self.elab_app(expr_id, ExprOrTerm::Term(eq), &[a, b], expected_ty)?
            }

            _ => {
                eprintln!("unimp expr kind {:?}", expr);
                self.error(expr_id, ElabError::TempUnimplemented);
                return None
            }
        })
    }

}

