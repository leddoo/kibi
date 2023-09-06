use sti::arena_pool::ArenaPool;

use crate::ast::{self, *};
use crate::tt::*;

use super::*;


impl<'me, 'err, 'a> Elab<'me, 'err, 'a> {
    pub fn elab_axiom(&mut self, axiom: &item::Axiom<'a>) -> Option<SymbolId> {
        assert_eq!(self.locals.len(), 0);
        assert_eq!(self.level_params.len(), 0);

        let temp = ArenaPool::tls_get_rec();

        for level in axiom.levels {
            self.level_params.push(*level);
        }

        let locals = self.elab_binders(axiom.params, &*temp)?;

        // type.
        let mut ty = self.elab_expr_as_type(&axiom.ty)?.0;

        assert_eq!(self.locals.len(), locals.len());
        for (_, id) in self.locals.iter().copied().rev() {
            ty = self.mk_binder(ty,  id, true);
        }

        if self.locals.len() == 0 {
            ty = self.instantiate_term_vars(ty);
        }

        debug_assert!(ty.syntax_eq(self.instantiate_term_vars(ty)));

        let (parent, name) = match &axiom.name {
            IdentOrPath::Ident(name) => (self.root_symbol, *name),

            IdentOrPath::Path(path) => {
                let (name, parts) = path.parts.split_last().unwrap();
                // @temp: missing source range.
                let parent = self.lookup_symbol_path(SourceRange::UNKNOWN, path.local, parts)?;
                (parent, *name)
            }
        };

        if !ty.closed() || ty.has_locals() {
            let mut pp = TermPP::new(self.env, &self.strings, self.alloc);
            let ty  = pp.pp_term(self.instantiate_term_vars(ty));
            println!("{}", pp.render(ty,  50).layout_string());
        }

        assert!(ty.closed());

        assert!(!ty.has_locals());

        if ty.has_ivars() {
            println!("unresolved inference variables");
            let mut pp = TermPP::new(self.env, &self.strings, self.alloc);
            let ty  = self.instantiate_term_vars(ty);
            let ty  = pp.pp_term(ty);
            println!("{}", pp.render(ty,  50).layout_string());
            return None;
        }

        let symbol = self.env.new_symbol(parent, name,
            SymbolKind::Def(symbol::Def {
                num_levels: axiom.levels.len() as u32,
                ty,
                val: None,
            })
        )?;

        Some(symbol)
    }

    pub fn elab_def_core(&mut self, levels: &[Atom], params: &[ast::Binder<'a>], ty: Option<&Expr<'a>>, value: &Expr<'a>) -> Option<(Term<'a>, Term<'a>)> {
        assert_eq!(self.locals.len(), 0);
        assert_eq!(self.level_params.len(), 0);

        let temp = ArenaPool::tls_get_rec();

        for level in levels {
            self.level_params.push(*level);
        }

        let locals = self.elab_binders(params, &*temp)?;

        // type.
        let ty =
            if let Some(t) = &ty {
                Some(self.elab_expr_as_type(&t)?.0)
            }
            else { None };

        // value.
        let (mut val, val_ty) = self.elab_expr_checking_type(&value, ty)?;


        let mut ty = ty.unwrap_or(val_ty);

        assert_eq!(self.locals.len(), locals.len());
        for (_, id) in self.locals.iter().copied().rev() {
            ty  = self.mk_binder(ty,  id, true);
            val = self.mk_binder(val, id, false);
        }

        if self.locals.len() == 0 {
            ty  = self.instantiate_term_vars(ty);
            val = self.instantiate_term_vars(val);
        }

        debug_assert!(ty.syntax_eq(self.instantiate_term_vars(ty)));
        debug_assert!(val.syntax_eq(self.instantiate_term_vars(val)));

        if !ty.closed() || !val.closed() || ty.has_locals() || val.has_locals() {
            let mut pp = TermPP::new(self.env, &self.strings, self.alloc);
            let ty  = pp.pp_term(self.instantiate_term_vars(ty));
            let val = pp.pp_term(self.instantiate_term_vars(val));
            println!("{}", pp.render(ty,  50).layout_string());
            println!("{}", pp.render(val, 50).layout_string());
        }

        assert!(ty.closed());
        assert!(val.closed());

        assert!(!ty.has_locals());
        assert!(!val.has_locals());

        if ty.has_ivars() || val.has_ivars() {
            println!("unresolved inference variables");
            let mut pp = TermPP::new(self.env, &self.strings, self.alloc);
            let ty  = self.instantiate_term_vars(ty);
            let val = self.instantiate_term_vars(val);
            let ty  = pp.pp_term(ty);
            let val = pp.pp_term(val);
            println!("{}", pp.render(ty,  50).layout_string());
            println!("{}", pp.render(val, 50).layout_string());
            return None;
        }

        Some((ty, val))
    }

    pub fn elab_def(&mut self, def: &item::Def<'a>) -> Option<SymbolId> {
        let (ty, val) = self.elab_def_core(def.levels, def.params, def.ty.as_ref(), &def.value)?;

        let (parent, name) = match &def.name {
            IdentOrPath::Ident(name) => (self.root_symbol, *name),

            IdentOrPath::Path(path) => {
                let (name, parts) = path.parts.split_last().unwrap();
                // @temp: missing source range.
                let parent = self.lookup_symbol_path(SourceRange::UNKNOWN, path.local, parts)?;
                (parent, *name)
            }
        };

        let symbol = self.env.new_symbol(parent, name,
            SymbolKind::Def(symbol::Def {
                num_levels: def.levels.len() as u32,
                ty,
                val: Some(val),
            })
        )?;

        Some(symbol)
    }
}

