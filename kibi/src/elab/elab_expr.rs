use sti::traits::{CopyIt, FromIn};
use sti::arena_pool::ArenaPool;

use crate::ast::*;
use crate::tt::{self, *};

use super::*;


impl<'me, 'c, 'out> Elaborator<'me, 'c, 'out> {
    pub fn elab_expr(&mut self, expr: ExprId) -> (Term<'out>, Term<'out>) {
        self.elab_expr_ex(expr, None)
    }

    pub fn elab_expr_checking_type(&mut self, expr: ExprId, expected_ty: Option<Term<'out>>) -> (Term<'out>, Term<'out>) {
        let (term, ty) = self.elab_expr_ex(expr, expected_ty);

        // @cleanup: dedup.
        if let Some(expected) = expected_ty {
            let source = expr.some();
            if !self.ensure_def_eq(ty, expected) {
                let expected = self.instantiate_term_vars(expected);
                let ty       = self.instantiate_term_vars(ty);
                let expected = self.reduce_ex(expected, false);
                let ty       = self.reduce_ex(ty, false);
                self.error(expr, {
                    let mut pp = TermPP::new(self.env, &self.strings, &self.lctx, self.alloc);
                    let expected = pp.pp_term(expected);
                    let found    = pp.pp_term(ty);
                    ElabError::TypeMismatch { expected, found }
                });
                return self.mkt_ax_error(expected, source);
            }
        }

        return (term, ty);
    }

    pub fn elab_expr_as_type(&mut self, expr: ExprId) -> (Term<'out>, tt::Level<'out>) {
        let (term, ty) = self.elab_expr_ex(expr, None);

        let ty = self.whnf(ty);
        if let Some(l) = ty.try_sort() {
            return (term, l);
        }

        let (ty_var, l) = self.new_ty_var();
        if !self.ensure_def_eq(term, ty_var) {
            self.error(expr, {
                let mut pp = TermPP::new(self.env, &self.strings, &self.lctx, self.alloc);
                let found = pp.pp_term(ty);
                ElabError::TypeExpected { found }
            });
        }
        return (ty_var, l);
    }


    fn elab_expr_ex(&mut self, expr: ExprId, expected_ty: Option<Term<'out>>) -> (Term<'out>, Term<'out>) {
        #[cfg(debug_assertions)]
        let old_num_locals = self.locals.len();

        let (term, ty) = self.elab_expr_core(expr, expected_ty);

        #[cfg(debug_assertions)]
        if self.locals.len() != old_num_locals {
            assert!(false);
        }

        // @todo: dedup (validate_type)
        #[cfg(debug_assertions)]
        {
            let n = self.ivars.assignment_gen;
            let inferred = self.infer_type(term).unwrap();
            if !self.ensure_def_eq(ty, inferred) {
                eprintln!("---\nbug: elab_expr_core returned term\n{}\nwith type\n{}\nbut has type\n{}\n---",
                    self.pp(term, 80),
                    self.pp(ty, 80),
                    self.pp(inferred, 80));
                assert!(false);
            }
            assert_eq!(n, self.ivars.assignment_gen);
        }

        // expr info.
        debug_assert!(self.elab.expr_infos[expr].is_none());
        self.elab.expr_infos[expr] = Some(ExprInfo { term, ty });

        return (term, ty);
    }

    fn elab_expr_core(&mut self, expr_id: ExprId, expected_ty: Option<Term<'out>>) -> (Term<'out>, Term<'out>) {
        //if let Some(ex) = expected_ty { eprintln!("expect: {}", self.pp(ex, 1000000)); }

        let source = expr_id.some();

        let expr = self.parse.exprs[expr_id];
        match expr.kind {
            ExprKind::Hole => {
                self.new_term_var()
            }

            ExprKind::Ident(ident) => {
                let result = self.elab_ident_or_path(expr_id, IdentOrPath::Ident(ident), &[]);
                result.unwrap_or_else(|| self.mkt_ax_error_from_expected(expected_ty, source))
            }

            ExprKind::Path(path) => {
                let result = self.elab_ident_or_path(expr_id, IdentOrPath::Path(path), &[]);
                result.unwrap_or_else(|| self.mkt_ax_error_from_expected(expected_ty, source))
            }

            ExprKind::Levels(it) => {
                let result = self.elab_ident_or_path(expr_id, it.symbol, it.levels);
                result.unwrap_or_else(|| self.mkt_ax_error_from_expected(expected_ty, source))
            }

            ExprKind::Sort(l) => {
                let l = self.elab_level(l);
                let l = l.unwrap_or_else(|| self.new_level_var());
                (self.alloc.mkt_sort(l, source),
                 self.alloc.mkt_sort(l.succ(self.alloc), source))
            }

            ExprKind::Forall(it) => {
                let temp = ArenaPool::tls_get_rec();
                let locals = self.elab_binders(it.binders, &*temp);

                let (mut result, mut level) = self.elab_expr_as_type(it.value);

                for (id, _, l) in locals.iter().rev().copied() {
                    level = l.imax(level, self.alloc);

                    result = self.mk_binder(result, id, true, source);
                    self.lctx.pop(id);
                }
                self.locals.truncate(self.locals.len() - locals.len());

                (result, self.alloc.mkt_sort(level, source))
            }

            ExprKind::Lambda(it) => {
                let temp = ArenaPool::tls_get_rec();
                let locals = self.elab_binders(it.binders, &*temp);

                let mut expected_ty = expected_ty;
                for (id, ty, _) in locals.iter().copied() {
                    if let Some(expected) = expected_ty {
                        if let Some(pi) = self.whnf_forall(expected) {
                            if self.is_def_eq(ty, pi.ty) {
                                expected_ty = Some(
                                    pi.val.instantiate(
                                        self.alloc.mkt_local(id, TERM_SOURCE_NONE), self.alloc));
                            }
                            else { expected_ty = None }
                        }
                        else { expected_ty = None }
                    }
                }

                let (mut result, mut result_ty) = self.elab_expr_checking_type(it.value, expected_ty);

                for (id, _, _) in locals.iter().rev().copied() {
                    result    = self.mk_binder(result,    id, false, source);
                    result_ty = self.mk_binder(result_ty, id, true,  source);
                    self.lctx.pop(id);
                }
                self.locals.truncate(self.locals.len() - locals.len());

                (result, result_ty)
            }

            ExprKind::Let(it) => {
                let ty = if let Some(ty) = it.ty.to_option() {
                    self.elab_expr_as_type(ty).0
                }
                else { self.new_ty_var().0 };

                let val = self.elab_expr_checking_type(it.val, Some(ty)).0;

                let name = it.name.value.to_option().unwrap_or(Atom::NULL);
                let id = self.lctx.push(name, ty, ScopeKind::Local(val));
                self.locals.push(Local { name, lid: id, vid: None.into(), mutable: false });

                let none = self.elab.token_infos.insert(it.name.source, TokenInfo::Local(self.item_id, id));
                debug_assert!(none.is_none());

                let (body, body_ty) = self.elab_expr(it.body);

                let result    = self.mk_let(body,    id, None.into(), false, source);
                let result_ty = self.mk_let(body_ty, id, None.into(), true,  source);
                self.lctx.pop(id);
                self.locals.truncate(self.locals.len() - 1);

                (result, result_ty)
            }

            ExprKind::By(it) => {
                let Some(expected) = expected_ty else {
                    self.error(expr_id, ElabError::TempStr("expected type must be known"));
                    return self.mkt_ax_error_from_expected(expected_ty, expr_id.some());
                };

                self.elab_by(it, expected)
            }
            
            ExprKind::Parens(it) => {
                return self.elab_expr_ex(it, expected_ty);
            }

            ExprKind::Call(it) => {
                self.elab_app(expr_id, ExprOrTerm::Expr(it.func), it.args, expected_ty)
            }

            ExprKind::Number(n) => {
                let n = self.parse.numbers[n];
                let n = u32::from_str_radix(n, 10).unwrap();
                (self.alloc.mkt_nat_val(n, source), Term::NAT)
            }

            ExprKind::Ref(it) => {
                // @todo: use expected type.
                let (value, ty) = self.elab_expr(it.expr);
                (self.alloc.mkt_ref_from_value(it.kind.into(), ty, value, source),
                 self.alloc.mkt_ref(Term::Region_infer, it.kind.into(), ty, source))
            }

            ExprKind::Deref(it) => {
                let kind = self.new_term_var_of_type(Term::Ref_Kind);
                let ty = expected_ty.unwrap_or_else(|| self.new_ty_var().0);
                let expected = self.alloc.mkt_ref(Term::Region_infer, kind, ty, source);
                let reff = self.elab_expr_checking_type(it, Some(expected)).0;

                let value = self.alloc.mkt_ref_read(kind, ty, reff, source);
                (value, ty)
            }

            ExprKind::Eq(a, b) => {
                let eq = self.alloc.mkt_global(
                    SymbolId::Eq,
                    &self.alloc.alloc_new([self.new_level_var()])[..],
                    source);
                self.elab_app(expr_id, ExprOrTerm::Term(eq), &[a, b], expected_ty)
            }

            ExprKind::Op2(expr::Op2 { op: expr::Op2Kind::Add, lhs, rhs }) => {
                self.elab_app(expr_id, ExprOrTerm::Term(Term::ADD_ADD), &[lhs, rhs], expected_ty)
            }

            ExprKind::Do(it) => {
                self.elab_do(expr_id, expr.flags, it, expected_ty)
            }

            ExprKind::If(it) => {
                let (cond, _) = self.elab_expr_checking_type(it.cond, Some(Term::BOOL));

                let (then, result_ty) = self.elab_expr(it.then);

                let els = if let Some(els) = it.els.to_option() {
                    self.elab_expr_checking_type(els, Some(result_ty)).0
                }
                else {
                    if !self.ensure_def_eq(result_ty, Term::UNIT) {
                        // @todo: type mismatch or special error.
                        self.error(expr_id, ElabError::TempArgFailed);
                        return self.mkt_ax_error(result_ty, source);
                    }
                    Term::UNIT_MK
                };

                let result = self.alloc.mkt_apps(Term::ITE, &[ result_ty, cond, then, els ], source);
                (result, result_ty)
            }

            _ => {
                self.error(expr_id, ElabError::TempUnimplemented);
                return self.mkt_ax_error_from_expected(expected_ty, source);
            }
        }
    }


    pub fn elab_ident_or_path(&mut self, expr_id: ExprId, name: IdentOrPath, levels: &[LevelId]) -> Option<(Term<'out>, Term<'out>)> {
        let source = expr_id.some();

        let path = match &name {
            IdentOrPath::Ident(ident) => {
                if let Some(local) = self.lookup_local(ident.value) {
                    if levels.len() != 0 {
                        self.error(expr_id, ElabError::LevelCountMismatch {
                            expected: 0,
                            found: levels.len() as u32,
                        });
                        return None;
                    }
                    else {
                        let ty = self.lctx.lookup(local).ty;
                        return Some((self.alloc.mkt_local(local, source), ty));
                    }
                }
                else {
                    core::slice::from_ref(ident)
                }
            }

            IdentOrPath::Path(path) => path.parts,
        };

        let symbol_id = self.elab_path(path)?;

        let symbol = self.env.symbol(symbol_id);
        Some(match symbol.kind {
            SymbolKind::Root |
            SymbolKind::Predeclared |
            SymbolKind::Pending(_) => unreachable!(),

            SymbolKind::Axiom(it) => {
                let num_levels = it.num_levels as usize;

                // @cleanup: dedup.
                let levels = if levels.len() == 0 {
                    Vec::from_in(self.alloc,
                        (0..num_levels).map(|_| self.new_level_var())
                    ).leak()
                }
                else {
                    if levels.len() != num_levels {
                        self.error(expr_id,
                            ElabError::LevelCountMismatch {
                                expected: it.num_levels as u32, found: levels.len() as u32 });
                        return None;
                    }

                    let mut ls = Vec::with_cap_in(self.alloc, levels.len());
                    for l in levels.copy_it() {
                        ls.push(self.elab_level(l)?);
                    }
                    ls.leak()
                };

                (self.alloc.mkt_global(symbol_id, levels, source),
                 it.ty.instantiate_level_params(levels, self.alloc))
            }

            SymbolKind::Def(it) => {
                let num_levels = it.num_levels as usize;

                // @cleanup: dedup.
                let levels = if levels.len() == 0 {
                    Vec::from_in(self.alloc,
                        (0..num_levels).map(|_| self.new_level_var())
                    ).leak()
                }
                else {
                    if levels.len() != num_levels {
                        self.error(expr_id,
                            ElabError::LevelCountMismatch {
                                expected: it.num_levels as u32, found: levels.len() as u32 });
                        return None;
                    }

                    let mut ls = Vec::with_cap_in(self.alloc, levels.len());
                    for l in levels.copy_it() {
                        ls.push(self.elab_level(l)?);
                    }
                    ls.leak()
                };

                (self.alloc.mkt_global(symbol_id, levels, source),
                 it.ty.instantiate_level_params(levels, self.alloc))
            }

            SymbolKind::IndAxiom(it) => {
                let num_levels = it.num_levels as usize;

                // @cleanup: dedup.
                let levels = if levels.len() == 0 {
                    Vec::from_in(self.alloc,
                        (0..num_levels).map(|_| self.new_level_var())
                    ).leak()
                }
                else {
                    if levels.len() != num_levels {
                        self.error(expr_id,
                            ElabError::LevelCountMismatch {
                                expected: it.num_levels as u32, found: levels.len() as u32 });
                        return None;
                    }

                    let mut ls = Vec::with_cap_in(self.alloc, levels.len());
                    for l in levels.copy_it() {
                        ls.push(self.elab_level(l)?);
                    }
                    ls.leak()
                };

                (self.alloc.mkt_global(symbol_id, levels, source),
                 it.ty.instantiate_level_params(levels, self.alloc))
            }
        })
    }

    pub fn elab_path(&mut self, parts: &[Ident]) -> Option<SymbolId> {
        let base  = parts[0];
        let parts = &parts[1..];

        let Some(mut symbol_id) = self.env.lookup(self.root_symbol, base.value) else {
            self.error(base.source,
                ElabError::UnresolvedName(
                    self.alloc.alloc_str(&self.strings[base.value])));
            return None;
        };
        let none = self.elab.token_infos.insert(base.source, TokenInfo::Symbol(symbol_id));
        debug_assert!(none.is_none());

        for part in parts.copy_it() {
            let Some(child) = self.env.lookup(symbol_id, part.value) else {
                self.error(part.source,
                    ElabError::UnresolvedName(
                        self.alloc.alloc_str(&self.strings[part.value])));
                return None;
            };
            symbol_id = child;

            let none = self.elab.token_infos.insert(part.source, TokenInfo::Symbol(symbol_id));
            debug_assert!(none.is_none());
        }

        Some(symbol_id)
    }

    #[inline]
    pub fn lookup_local(&self, name: Atom) -> Option<ScopeId> {
        for l in self.locals.copy_it().rev() {
            if l.name == name {
                return Some(l.lid);
            }
        }
        None
    }

    #[inline]
    pub fn lookup_local_idx(&self, name: Atom) -> Option<(ScopeId, usize)> {
        for (i, l) in self.locals.copy_it().enumerate().rev() {
            if l.name == name {
                return Some((l.lid, i));
            }
        }
        None
    }
}

