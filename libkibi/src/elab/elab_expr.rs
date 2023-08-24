use crate::ast::*;
use crate::tt::{self, *};

use super::*;


impl<'me, 'err, 'a> Elab<'me, 'err, 'a> {
    pub fn elab_expr(&mut self, expr: &Expr<'a>) -> Option<(TermRef<'a>, TermRef<'a>)> {
        self.elab_expr_ex(expr, None)
    }


    pub fn elab_expr_checking_type(&mut self, expr: &Expr<'a>, expected_ty: Option<TermRef<'a>>) -> Option<(TermRef<'a>, TermRef<'a>)> {
        let (term, ty) = self.elab_expr_ex(expr, expected_ty)?;

        if let Some(expected) = expected_ty {
            if !self.def_eq(ty, expected) {
                let expected = self.reduce_ex(expected, false);
                let ty       = self.reduce_ex(ty, false);
                self.error(expr.source, |alloc| {
                    let mut pp = TermPP::new(self.env, alloc);
                    let expected = pp.pp_term(self.instantiate_term(expected));
                    let found    = pp.pp_term(self.instantiate_term(ty));
                    ElabError::TypeMismatch { expected, found }
                });
                return None;
            }
        }

        Some((term, ty))
    }

    pub fn elab_expr_as_type(&mut self, expr: &Expr<'a>) -> Option<(TermRef<'a>, tt::LevelRef<'a>)> {
        let (term, ty) = self.elab_expr_ex(expr, None)?;

        let ty = self.whnf(ty);
        if let TermKind::Sort(l) = ty.kind {
            return Some((term, l));
        }

        let (ty_var, l) = self.new_ty_var();
        if self.def_eq(term, ty_var) {
            return Some((ty_var, l));
        }

        self.error(expr.source, |alloc| {
            let mut pp = TermPP::new(self.env, alloc);
            let found = pp.pp_term(ty);
            ElabError::TypeExpected { found }
        });
        return None;
    }


    pub fn elab_expr_ex(&mut self, expr: &Expr<'a>, expected_ty: Option<TermRef<'a>>) -> Option<(TermRef<'a>, TermRef<'a>)> {
        Some(match &expr.kind {
            ExprKind::Hole => {
                self.new_term_var()
            }

            ExprKind::Ident(name) => {
                if let Some(local) = self.lookup_local(name) {
                    let ty = self.lctx.lookup(local).ty;
                    (self.alloc.mkt_local(local), ty)
                }
                else {
                    let symbol = self.lookup_symbol_ident(expr.source, name)?;
                    self.elab_symbol(expr.source, symbol, &[])?
                }
            }

            ExprKind::Path(path) => {
                let symbol = self.lookup_symbol_path(expr.source, path.local, path.parts)?;
                self.elab_symbol(expr.source, symbol, &[])?
            }

            ExprKind::Levels(it) => {
                let symbol = match &it.symbol {
                    IdentOrPath::Ident(name) => {
                        if self.lookup_local(*name).is_some() {
                            self.error(expr.source, |alloc|
                                ElabError::SymbolShadowedByLocal(
                                    alloc.alloc_str(*name)));
                        }

                        self.lookup_symbol_ident(expr.source, *name)?
                    }

                    IdentOrPath::Path(path) => {
                        self.lookup_symbol_path(expr.source, path.local, path.parts)?
                    }
                };

                self.elab_symbol(expr.source, symbol, it.levels)?
            }

            ExprKind::Sort(l) => {
                let l = self.elab_level(l)?;
                (self.alloc.mkt_sort(l),
                 self.alloc.mkt_sort(l.succ(self.alloc)))
            }

            ExprKind::Forall(it) => {
                // @temp: sti temp arena.
                let mut levels = Vec::new();

                // @cleanup: elab_binders.
                let locals_begin = self.locals.len();
                for param in it.binders.iter() {
                    let (ty, l) = self.elab_expr_as_type(param.ty.as_ref()?)?;
                    let id = self.lctx.push(ty, None);
                    let name = param.name.unwrap_or("");
                    self.locals.push((name, id));
                    levels.push(l);
                }
                let locals_end = self.locals.len();

                let (mut result, mut level) = self.elab_expr_as_type(it.ret)?;

                for l in levels.iter().rev() {
                    level = l.imax(level, self.alloc);
                }

                assert_eq!(self.locals.len(), locals_end);
                for i in (locals_begin..locals_end).rev() {
                    let (_, id) = self.locals[i];
                    result = self.mk_binder(result, id, true);
                    self.lctx.pop(id);
                }
                self.locals.truncate(locals_begin);

                (result, self.alloc.mkt_sort(level))
            }

            ExprKind::Lambda(it) => {
                let mut expected_ty = expected_ty;

                // @cleanup: elab_binders.
                let locals_begin = self.locals.len();
                for param in it.binders.iter() {
                    let (ty, _) = self.elab_expr_as_type(param.ty.as_ref()?)?;
                    let id = self.lctx.push(ty, None);
                    let name = param.name.unwrap_or("");
                    self.locals.push((name, id));

                    if let Some(expected) = expected_ty {
                        if let Some(b) = self.whnf_forall(expected) {
                            if self.def_eq(ty, b.ty) {
                                expected_ty = Some(
                                    b.val.instantiate(
                                        self.alloc.mkt_local(id), self.alloc));
                            }
                            else { expected_ty = None }
                        }
                        else { expected_ty = None }
                    }
                }
                let locals_end = self.locals.len();

                let (mut result, mut result_ty) = self.elab_expr_ex(it.value, expected_ty)?;

                assert_eq!(self.locals.len(), locals_end);
                for i in (locals_begin..locals_end).rev() {
                    let (_, id) = self.locals[i];
                    result    = self.mk_binder(result,    id, false);
                    result_ty = self.mk_binder(result_ty, id, true);
                    self.lctx.pop(id);
                }
                self.locals.truncate(locals_begin);

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

                let mut result    = func;
                let mut result_ty = func_ty;
                for arg in it.args.iter() {
                    let expr::CallArg::Positional(arg) = arg else { unimplemented!() };

                    let Some(b) = self.whnf_forall(result_ty) else {
                        return None;
                    };

                    let (arg, _) = self.elab_expr_checking_type(arg, Some(b.ty))?;

                    result    = self.alloc.mkt_apply(result, arg);
                    result_ty = b.val.instantiate(arg, self.alloc);
                }

                (result, result_ty)
            }

            ExprKind::Number(n) => {
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

