use sti::growing_arena::GrowingArena;
use sti::vec::Vec;

use crate::AllocStrExt;
use crate::error::*;
use crate::ast::{self, *};
use crate::tt::{self, *};
use crate::env::*;


pub struct Elab<'me, 'err, 'a> {
    pub alloc: tt::Alloc<'a>,
    pub errors: &'me ErrorCtx<'err>,
    pub env: &'me mut Env<'a>,

    ns: NamespaceId,

    lctx: LocalCtx<'a>,
    locals: Vec<(&'a str, LocalId)>,
}

impl<'me, 'err, 'a> Elab<'me, 'err, 'a> {
    #[inline(always)]
    pub fn new(env: &'me mut Env<'a>, ns: NamespaceId, errors: &'me ErrorCtx<'err>, arena: &'a GrowingArena) -> Self {
        let alloc = tt::Alloc::new(arena);
        Self {
            alloc,
            errors,
            env,
            ns,
            lctx: LocalCtx::new(alloc),
            locals: Vec::new(),
        }
    }

    pub fn elab_level(&mut self, level: &ast::Level<'a>) -> Option<tt::LevelRef<'a>> {
        Some(match &level.kind {
            ast::LevelKind::Nat(n) => {
                self.alloc.mkl_nat(*n)
            }

            ast::LevelKind::Add((l, offset)) => {
                let l = self.elab_level(l)?;
                l.offset(*offset, self.alloc)
            }

            ast::LevelKind::Max((lhs, rhs)) => {
                let lhs = self.elab_level(lhs)?;
                let rhs = self.elab_level(rhs)?;
                self.alloc.mkl_max(lhs, rhs)
            }

            ast::LevelKind::IMax((lhs, rhs)) => {
                let lhs = self.elab_level(lhs)?;
                let rhs = self.elab_level(rhs)?;
                self.alloc.mkl_imax(lhs, rhs)
            }

            ast::LevelKind::Var(_) => todo!(),
        })
    }

    pub fn elab_expr(&mut self, expr: &Expr<'a>) -> Option<(TermRef<'a>, TermRef<'a>)> {
        self.elab_expr_ex(expr, None)
    }

    pub fn elab_expr_ex(&mut self, expr: &Expr<'a>, expected_ty: Option<TermRef<'a>>) -> Option<(TermRef<'a>, TermRef<'a>)> {
        Some(match &expr.kind {
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

            ExprKind::Forall(_) => {
                unimplemented!()
            }

            ExprKind::Lambda(it) => {
                let save = self.lctx.save();
                let num_locals = self.locals.len();

                // @cleanup: elab_binders.
                for param in it.binders.iter() {
                    let (ty, _) = self.elab_expr_as_type(param.ty.as_ref()?)?;
                    let id = self.lctx.extend(ty, None);
                    let name = param.name.unwrap_or("");
                    self.locals.push((name, id));
                }

                let (mut result, mut result_ty) = self.elab_expr(it.value)?;

                for i in (num_locals..self.locals.len()).rev() {
                    let (_, id) = self.locals[i];
                    result    = self.lctx.abstract_lambda(result, id);
                    result_ty = self.lctx.abstract_forall(result_ty, id);
                }
                self.lctx.restore(save);
                self.locals.truncate(num_locals);

                (result, result_ty)
            }
            
            ExprKind::Parens(it) => {
                return self.elab_expr_ex(it, expected_ty);
            }

            ExprKind::Call(it) => {
                let (mut result, mut result_ty) = self.elab_expr(it.func)?;

                for arg in it.args.iter() {
                    let expr::CallArg::Positional(arg) = arg else { unimplemented!() };

                    let TermKind::Forall(b) = result_ty.kind else { return None };

                    let (arg, _) = self.elab_expr_checking_type(arg, Some(b.ty))?;

                    result = self.alloc.mkt_apply(result, arg);
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

    fn elab_expr_checking_type(&mut self, expr: &Expr<'a>, expected_ty: Option<TermRef<'a>>) -> Option<(TermRef<'a>, TermRef<'a>)> {
        let (term, ty) = self.elab_expr_ex(expr, expected_ty)?;

        if let Some(expected) = expected_ty {
            let mut tc = self.tc();
            if !tc.def_eq(ty, expected) {
                self.error(expr.source, |alloc| {
                    let mut pp = TermPP::new(alloc, self.env);
                    let expected = pp.pp_term(expected);
                    let found    = pp.pp_term(ty);
                    ElabError::TypeMismatch { expected, found }
                });
                return None;
            }
        }

        Some((term, ty))
    }

    fn elab_expr_as_type(&mut self, expr: &Expr<'a>) -> Option<(TermRef<'a>, tt::LevelRef<'a>)> {
        let (term, ty) = self.elab_expr_ex(expr, None)?;

        let mut tc = self.tc();

        let ty = tc.whnf(ty);
        if let TermKind::Sort(l) = ty.kind {
            return Some((term, l));
        }

        self.error(expr.source, |alloc| {
            let mut pp = TermPP::new(alloc, self.env);
            let found = pp.pp_term(ty);
            ElabError::TypeExpected { found }
        });
        return None;
    }


    pub fn elab_def(&mut self, def: &item::Def<'a>) -> Option<SymbolId> {
        assert_eq!(self.locals.len(), 0);
        let save = self.lctx.save();

        // @cleanup: elab_binders.
        for param in def.params.iter() {
            let (ty, _) = self.elab_expr_as_type(param.ty.as_ref()?)?;
            let id = self.lctx.extend(ty, None);
            let name = param.name.unwrap_or("");
            self.locals.push((name, id));
        }

        let mut ty = None;
        if let Some(t) = &def.ty {
            ty = Some(self.elab_expr_as_type(&t)?.0);
        }

        let (mut val, val_ty) = self.elab_expr_checking_type(&def.value, ty)?;
        assert_eq!(self.locals.len(), def.params.len());

        let mut ty = ty.unwrap_or(val_ty);
        for (_, id) in self.locals.iter().copied().rev() {
            ty  = self.lctx.abstract_forall(ty,  id);
            val = self.lctx.abstract_lambda(val, id);
        }

        let (parent_ns, name) = match &def.name {
            IdentOrPath::Ident(name) => (self.ns, *name),

            IdentOrPath::Path(path) => {
                let (name, parts) = path.parts.split_last().unwrap();
                // @temp
                let ns = self.lookup_namespace_path(SourceRange::UNKNOWN, path.local, parts)?;
                (ns, *name)
            }
        };

        let symbol = self.env.new_symbol(parent_ns, name,
            SymbolKind::Def(symbol::Def {
                num_levels: 0,
                ty,
                val,
            })
        )?;

        self.lctx.restore(save);
        self.locals.truncate(0);

        Some(symbol)
    }


    fn lookup_local(&self, name: &str) -> Option<LocalId> {
        for (n, id) in self.locals.iter().rev().copied() {
            if n == name {
                return Some(id);
            }
        }
        None
    }

    fn lookup_symbol_ident(&self, source: SourceRange, name: &str) -> Option<SymbolId> {
        let Some(entry) = self.env.lookup(self.ns, name) else {
            self.error(source, |alloc|
                ElabError::UnresolvedName { base: "", name: alloc.alloc_str(name) });
            return None;
        };
        Some(entry.symbol)
    }

    fn lookup_symbol_path(&self, source: SourceRange, local: bool, parts: &[&str]) -> Option<SymbolId> {
        if local {
            let mut result = self.lookup_symbol_ident(source, parts[0])?;

            for part in &parts[1..] {
                let symbol = self.env.symbol(result);

                let Some(entry) = self.env.lookup(symbol.own_ns, part) else {
                    // @todo: proper base.
                    self.error(source, |alloc|
                        ElabError::UnresolvedName { base: "", name: alloc.alloc_str(part) });
                    return None;
                };

                result = entry.symbol;
            }

            Some(result)
        }
        else {
            unimplemented!()
        }
    }

    fn lookup_namespace_path(&self, source: SourceRange, local: bool, parts: &[&str]) -> Option<NamespaceId> {
        let symbol = self.lookup_symbol_path(source, local, parts)?;
        return Some(self.env.symbol(symbol).own_ns);
    }


    fn elab_symbol(&mut self, source: SourceRange, id: SymbolId, levels: &[ast::Level<'a>]) -> Option<(TermRef<'a>, TermRef<'a>)> {
        let symbol = self.env.symbol(id);
        Some(match symbol.kind {
            SymbolKind::BuiltIn(b) => {
                match b {
                    symbol::BuiltIn::Nat => {
                        if levels.len() != 0 {
                            self.error(source, |_|
                                ElabError::LevelMismatch {
                                    expected: 0, found: levels.len() as u32 });
                            return None;
                        }
                        (Term::NAT, Term::SORT_1)
                    }

                    symbol::BuiltIn::NatZero => {
                        if levels.len() != 0 {
                            self.error(source, |_|
                                ElabError::LevelMismatch {
                                    expected: 0, found: levels.len() as u32 });
                            return None;
                        }
                        (Term::NAT_ZERO, Term::NAT)
                    }

                    symbol::BuiltIn::NatSucc => {
                        if levels.len() != 0 {
                            self.error(source, |_|
                                ElabError::LevelMismatch {
                                    expected: 0, found: levels.len() as u32 });
                            return None;
                        }
                        (Term::NAT_SUCC, Term::NAT_SUCC_TY)
                    }

                    symbol::BuiltIn::NatRec => {
                        if levels.len() != 1 {
                            self.error(source, |_|
                                ElabError::LevelMismatch {
                                    expected: 1, found: levels.len() as u32 });
                            return None;
                        }

                        let l = self.elab_level(&levels[0])?;
                        (self.alloc.mkt_nat_rec(l),
                         self.alloc.mkt_nat_rec_ty(l))
                    }
                }
            }

            SymbolKind::Def(def) => {
                if def.num_levels != 0 || levels.len() != 0 {
                    unimplemented!()
                }

                (self.alloc.mkt_global(id, &[]), def.ty)
            }
        })
    }


    #[inline(always)]
    pub fn tc<'l>(&mut self) -> TyCtx<'a, '_> {
        TyCtx::new(self.alloc, &mut self.lctx)
    }


    fn error<F: FnOnce(&'err GrowingArena) -> ElabError<'err>>(&self, source: SourceRange, f: F) {
        self.errors.with(|errors| {
            errors.report(Error { source, kind: ErrorKind::Elab(f(errors.alloc)) });
        });
    }
}

