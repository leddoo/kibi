use sti::arena::Arena;
use sti::vec::Vec;

use crate::error::*;
use crate::ast::{self, *};
use crate::tt::{self, *};
use crate::env::*;


pub struct Elab<'me, 'err, 'a> {
    pub alloc: &'a Arena,
    pub errors: &'me ErrorCtx<'err>,
    pub env: &'me mut Env<'a>,

    root_symbol: SymbolId,

    lctx: LocalCtx<'a>,
    locals: Vec<(&'a str, ScopeId)>,
    level_vars: Vec<&'a str>,

    ictx: InferCtx<'a>,
}

impl<'me, 'err, 'a> Elab<'me, 'err, 'a> {
    #[inline(always)]
    pub fn new(env: &'me mut Env<'a>, root_symbol: SymbolId, errors: &'me ErrorCtx<'err>, alloc: &'a Arena) -> Self {
        Self {
            alloc,
            errors,
            env,
            root_symbol,
            lctx: LocalCtx::new(alloc),
            locals: Vec::new(),
            level_vars: Vec::new(),
            ictx: InferCtx::new(alloc),
        }
    }

    // @temp: `Compiler` rework.
    pub fn check_no_unassigned_variables(&self) -> Option<()> {
        for var in self.ictx.level_ids() {
            if self.ictx.level_value(var).is_none() {
                println!("{:?} unassigned", var);
                return None;
            }
        }

        for var in self.ictx.term_ids() {
            if self.ictx.term_value(var).is_none() {
                println!("{:?} unassigned", var);
                return None;
            }
        }

        Some(())
    }

    pub fn elab_level(&mut self, level: &ast::Level<'a>) -> Option<tt::LevelRef<'a>> {
        Some(match &level.kind {
            ast::LevelKind::Hole => {
                self.ictx.new_level_var()
            }

            ast::LevelKind::Ident(name) => {
                for i in 0..self.level_vars.len() {
                    if *name == self.level_vars[i] {
                        return Some(self.alloc.mkl_param(*name, i as u32));
                    }
                }
                self.error(level.source, |alloc|
                    ElabError::UnresolvedLevel(
                        alloc.alloc_str(name)));
                return None;
            }

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
        })
    }

    pub fn elab_expr(&mut self, expr: &Expr<'a>) -> Option<(TermRef<'a>, TermRef<'a>)> {
        self.elab_expr_ex(expr, None)
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
                    result = self.ictx.instantiate_term(result);

                    let (_, id) = self.locals[i];
                    result = self.lctx.abstract_forall(result, id);
                    self.lctx.pop(id);
                }
                self.locals.truncate(locals_begin);

                // @temp: ictx.abstract_forall.
                result = self.ictx.instantiate_term(result);

                (result, self.alloc.mkt_sort(level))
            }

            ExprKind::Lambda(it) => {
                // @cleanup: elab_binders.
                let locals_begin = self.locals.len();
                for param in it.binders.iter() {
                    let (ty, _) = self.elab_expr_as_type(param.ty.as_ref()?)?;
                    let id = self.lctx.push(ty, None);
                    let name = param.name.unwrap_or("");
                    self.locals.push((name, id));
                }
                let locals_end = self.locals.len();

                let (mut result, mut result_ty) = self.elab_expr(it.value)?;

                assert_eq!(self.locals.len(), locals_end);
                for i in (locals_begin..locals_end).rev() {
                    result    = self.ictx.instantiate_term(result);
                    result_ty = self.ictx.instantiate_term(result_ty);

                    let (_, id) = self.locals[i];
                    result    = self.lctx.abstract_lambda(result, id);
                    result_ty = self.lctx.abstract_forall(result_ty, id);
                    self.lctx.pop(id);
                }
                self.locals.truncate(locals_begin);

                // @temp: ictx.abstract_forall.
                result    = self.ictx.instantiate_term(result);
                result_ty = self.ictx.instantiate_term(result_ty);

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
                    let mut pp = TermPP::new(self.env, alloc);
                    let expected = pp.pp_term(self.ictx.instantiate_term(expected));
                    let found    = pp.pp_term(self.ictx.instantiate_term(ty));
                    ElabError::TypeMismatch { expected, found }
                });
                return None;
            }
        }

        Some((term, ty))
    }

    fn elab_expr_as_type(&mut self, expr: &Expr<'a>) -> Option<(TermRef<'a>, tt::LevelRef<'a>)> {
        let (term, ty) = self.elab_expr_ex(expr, None)?;

        let ty = self.tc().whnf(ty);
        if let TermKind::Sort(l) = ty.kind {
            return Some((term, l));
        }

        let (ty_var, l) = self.new_ty_var();
        if self.tc().def_eq(term, ty_var) {
            return Some((ty_var, l));
        }

        self.error(expr.source, |alloc| {
            let mut pp = TermPP::new(self.env, alloc);
            let found = pp.pp_term(ty);
            ElabError::TypeExpected { found }
        });
        return None;
    }


    pub fn elab_def(&mut self, def: &item::Def<'a>) -> Option<SymbolId> {
        assert_eq!(self.locals.len(), 0);
        assert_eq!(self.level_vars.len(), 0);

        for level in def.levels {
            self.level_vars.push(level);
        }

        // @cleanup: elab_binders.
        for param in def.params.iter() {
            let (ty, _) = self.elab_expr_as_type(param.ty.as_ref()?)?;
            let id = self.lctx.push(ty, None);
            let name = param.name.unwrap_or("");
            self.locals.push((name, id));
        }

        // type.
        let mut ty = None;
        if let Some(t) = &def.ty {
            ty = Some(self.elab_expr_as_type(&t)?.0);
        }

        // value.
        let (mut val, val_ty) = self.elab_expr_checking_type(&def.value, ty)?;
        assert_eq!(self.locals.len(), def.params.len());

        let mut ty = ty.unwrap_or(val_ty);

        for (_, id) in self.locals.iter().copied().rev() {
            ty  = self.ictx.instantiate_term(ty);
            val = self.ictx.instantiate_term(val);

            ty  = self.lctx.abstract_forall(ty,  id);
            val = self.lctx.abstract_lambda(val, id);
        }
        ty  = self.ictx.instantiate_term(ty);
        val = self.ictx.instantiate_term(val);

        let (parent, name) = match &def.name {
            IdentOrPath::Ident(name) => (self.root_symbol, *name),

            IdentOrPath::Path(path) => {
                let (name, parts) = path.parts.split_last().unwrap();
                // @temp: missing source range.
                let parent = self.lookup_symbol_path(SourceRange::UNKNOWN, path.local, parts)?;
                (parent, *name)
            }
        };

        if !ty.closed() || !val.closed() || ty.has_locals() || val.has_locals() {
            let mut pp = TermPP::new(self.env, self.alloc);
            let ty  = pp.pp_term(self.ictx.instantiate_term(ty));
            let val = pp.pp_term(self.ictx.instantiate_term(val));
            println!("{}", pp.render(ty,  50).layout_string());
            println!("{}", pp.render(val, 50).layout_string());
        }

        assert!(ty.closed());
        assert!(val.closed());

        assert!(!ty.has_locals());
        assert!(!val.has_locals());

        if ty.has_vars() || val.has_vars() {
            println!("unresolved inference variables");
            let mut pp = TermPP::new(self.env, self.alloc);
            let ty  = pp.pp_term(self.ictx.instantiate_term(ty));
            let val = pp.pp_term(self.ictx.instantiate_term(val));
            println!("{}", pp.render(ty,  50).layout_string());
            println!("{}", pp.render(val, 50).layout_string());
            return None;
        }

        let symbol = self.env.new_symbol(parent, name,
            SymbolKind::Def(symbol::Def {
                num_levels: def.levels.len() as u32,
                ty,
                val,
            })
        )?;

        Some(symbol)
    }


    fn lookup_local(&self, name: &str) -> Option<ScopeId> {
        for (n, id) in self.locals.iter().rev().copied() {
            if n == name {
                return Some(id);
            }
        }
        None
    }

    fn lookup_symbol_ident(&self, source: SourceRange, name: &str) -> Option<SymbolId> {
        let Some(symbol) = self.env.lookup(self.root_symbol, name) else {
            self.error(source, |alloc|
                ElabError::UnresolvedName { base: "", name: alloc.alloc_str(name) });
            return None;
        };
        Some(symbol)
    }

    fn lookup_symbol_path(&self, source: SourceRange, local: bool, parts: &[&str]) -> Option<SymbolId> {
        if local {
            let mut result = self.lookup_symbol_ident(source, parts[0])?;

            for part in &parts[1..] {
                let Some(symbol) = self.env.lookup(result, part) else {
                    // @todo: proper base.
                    self.error(source, |alloc|
                        ElabError::UnresolvedName { base: "", name: alloc.alloc_str(part) });
                    return None;
                };

                result = symbol;
            }

            Some(result)
        }
        else {
            unimplemented!()
        }
    }


    fn elab_symbol(&mut self, source: SourceRange, id: SymbolId, levels: &[ast::Level<'a>]) -> Option<(TermRef<'a>, TermRef<'a>)> {
        let symbol = self.env.symbol(id);
        Some(match symbol.kind {
            SymbolKind::Root => unreachable!(),

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
                        let r = if levels.len() == 0 {
                            self.ictx.new_level_var()
                        }
                        else {
                            if levels.len() != 1 {
                                self.error(source, |_|
                                    ElabError::LevelMismatch {
                                        expected: 1, found: levels.len() as u32 });
                                return None;
                            }
                            self.elab_level(&levels[0])?
                        };

                        (self.alloc.mkt_nat_rec(r),
                         self.alloc.mkt_nat_rec_ty(r))
                    }

                    symbol::BuiltIn::Eq => {
                        let l = if levels.len() == 0 {
                            self.ictx.new_level_var()
                        }
                        else {
                            if levels.len() != 1 {
                                self.error(source, |_|
                                    ElabError::LevelMismatch {
                                        expected: 1, found: levels.len() as u32 });
                                return None;
                            }
                            self.elab_level(&levels[0])?
                        };

                        (self.alloc.mkt_eq(l),
                         self.alloc.mkt_eq_ty(l))
                    }

                    symbol::BuiltIn::EqRefl => {
                        let l = if levels.len() == 0 {
                            self.ictx.new_level_var()
                        }
                        else {
                            if levels.len() != 1 {
                                self.error(source, |_|
                                    ElabError::LevelMismatch {
                                        expected: 1, found: levels.len() as u32 });
                                return None;
                            }
                            self.elab_level(&levels[0])?
                        };

                        (self.alloc.mkt_eq_refl(l),
                         self.alloc.mkt_eq_refl_ty(l))
                    }

                    symbol::BuiltIn::EqRec => {
                        let (l, r) = if levels.len() == 0 {
                            (self.ictx.new_level_var(),
                             self.ictx.new_level_var())
                        }
                        else {
                            if levels.len() != 2 {
                                self.error(source, |_|
                                    ElabError::LevelMismatch {
                                        expected: 2, found: levels.len() as u32 });
                                return None;
                            }
                            (self.elab_level(&levels[0])?,
                             self.elab_level(&levels[1])?)
                        };

                        (self.alloc.mkt_eq_rec(l, r),
                         self.alloc.mkt_eq_rec_ty(l, r))
                    }
                }
            }

            SymbolKind::Def(def) => {
                let num_levels = def.num_levels as usize;

                let levels = if levels.len() == 0 {
                    let mut ls = Vec::with_cap_in(num_levels, self.alloc);
                    for _ in 0..num_levels {
                        ls.push(self.ictx.new_level_var());
                    }
                    ls.leak()
                }
                else {
                    if levels.len() != num_levels {
                        self.error(source, |_|
                            ElabError::LevelMismatch {
                                expected: def.num_levels, found: levels.len() as u32 });
                        return None;
                    }

                    let mut ls = Vec::with_cap_in(levels.len(), self.alloc);
                    for l in levels {
                        ls.push(self.elab_level(l)?);
                    }
                    ls.leak()
                };

                (self.alloc.mkt_global(id, levels),
                 def.ty.instantiate_level_params(levels, self.alloc))
            }
        })
    }


    fn new_term_var(&mut self) -> (TermRef<'a>, TermRef<'a>) {
        let l = self.ictx.new_level_var();
        let tyty = self.alloc.mkt_sort(l);
        let ty = self.ictx.new_term_var(tyty, self.lctx.current());
        (self.ictx.new_term_var(ty, self.lctx.current()), ty)
    }

    fn new_ty_var(&mut self) -> (TermRef<'a>, tt::LevelRef<'a>) {
        let l = self.ictx.new_level_var();
        let ty = self.alloc.mkt_sort(l);
        (self.ictx.new_term_var(ty, self.lctx.current()), l)
    }


    #[inline(always)]
    pub fn tc(&mut self) -> TyCtx<'_, 'a> {
        TyCtx::new(&mut self.lctx, &mut self.ictx, self.env, self.alloc)
    }


    fn error<F: FnOnce(&'err Arena) -> ElabError<'err>>(&self, source: SourceRange, f: F) {
        self.errors.with(|errors| {
            errors.report(Error { source, kind: ErrorKind::Elab(f(errors.alloc)) });
        });
    }
}

