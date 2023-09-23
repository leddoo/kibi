use sti::traits::{CopyIt, FromIn};
use sti::arena_pool::ArenaPool;

use crate::ast::{self, *};
use crate::tt::*;

use super::*;


impl<'me, 'c, 'out> Elaborator<'me, 'c, 'out> {
    pub fn elab_axiom(&mut self, item_id: ItemId, axiom: &item::Axiom) -> Option<SymbolId> {
        spall::trace_scope!("kibi/elab/axiom"; "{}",
            axiom.name.display(self.strings));

        assert_eq!(self.locals.len(), 0);
        assert_eq!(self.level_params.len(), 0);

        let temp = ArenaPool::tls_get_rec();

        for level in axiom.levels {
            self.level_params.push(level.value);
        }

        let locals = self.elab_binders(axiom.params, &*temp);

        // type.
        let mut ty = self.elab_expr_as_type(axiom.ty).0;

        assert_eq!(self.locals.len(), locals.len());
        for l in self.locals.iter().copied().rev() {
            ty = self.mk_binder(ty, l.id, true);
        }

        if self.locals.len() == 0 {
            ty = self.instantiate_term_vars(ty);
        }

        debug_assert!(ty.syntax_eq(self.instantiate_term_vars(ty)));

        let (parent, name) = match &axiom.name {
            IdentOrPath::Ident(name) => (self.root_symbol, *name),

            IdentOrPath::Path(path) => {
                let (name, parts) = path.parts.split_last().unwrap();
                let parent = self.elab_path(parts)?;
                (parent, *name)
            }
        };

        if !ty.closed() || ty.has_locals() {
            let mut pp = TermPP::new(self.env, &self.strings, &self.lctx, self.alloc);
            let ty  = pp.pp_term(self.instantiate_term_vars(ty));
            eprintln!("{}", pp.render(ty,  50).layout_string());
        }

        assert!(ty.closed());

        assert!(!ty.has_locals());

        if ty.has_ivars() {
            eprintln!("unresolved inference variables");
            let mut pp = TermPP::new(self.env, &self.strings, &self.lctx, self.alloc);
            let ty  = self.instantiate_term_vars(ty);
            let ty  = pp.pp_term(ty);
            eprintln!("{}", pp.render(ty,  50).layout_string());
            //return None;
        }

        let _ = self.check_no_unassigned_variables(item_id.into())?;

        let symbol = self.env.new_symbol(parent, name.value,
            SymbolKind::Axiom(symbol::Axiom {
                num_levels: axiom.levels.len(),
                ty,
            })
        )?;

        Some(symbol)
    }

    pub fn elab_def_core(&mut self, item_id: ItemId, levels: &[Ident], params: &[ast::Binder], ty: OptExprId, value: ExprId) -> (Term<'out>, Term<'out>) {
        assert_eq!(self.locals.len(), 0);
        assert_eq!(self.level_params.len(), 0);

        let temp = ArenaPool::tls_get_rec();

        for level in levels {
            self.level_params.push(level.value);
        }

        let locals = self.elab_binders(params, &*temp);

        // type.
        let ty =
            if let Some(t) = ty.to_option() {
                Some(self.elab_expr_as_type(t).0)
            }
            else { None };

        // value.
        let (mut val, val_ty) = self.elab_expr_checking_type(value, ty);


        let mut aux_level_args = &[][..];
        if self.aux_defs.len() > 0 {
            aux_level_args = Vec::from_in(self.alloc,
                self.level_params.copy_it().enumerate().map(|(i, param)|
                    self.alloc.mkl_param(param, i as u32))).leak();
        }

        // declare aux defs.
        let mut aux_symbols = Vec::with_cap(self.aux_defs.len());
        let aux_defs = self.aux_defs.take();
        for aux in aux_defs.iter() {
            // @temp: arena; in current item; count from 1 maybe.
            let n = self.env.symbol(self.root_symbol).children.len();
            let name = format!("{}_{n}", &self.strings[aux.name]);
            let name = self.strings.insert(&name);

            let symbol = self.env.new_symbol(self.root_symbol, name,
                SymbolKind::Pending(None)).unwrap();
            aux_symbols.push(symbol);

            let global = self.alloc.mkt_global(symbol, aux_level_args);
            unsafe { aux.ivar.assign_core(global, self) }
        }


        // assign unassigned ivars.
        let mut had_unassigned_ivars = false;
        for ivar in self.ivars.level_vars.range() {
            if ivar.value(self).is_none() {
                had_unassigned_ivars = true;
                unsafe { ivar.assign_core(tt::Level::L1, self) }
            }
        }
        for ivar in self.ivars.term_vars.range() {
            if ivar.value(self).is_none() {
                had_unassigned_ivars = true;
                let error = self.mkt_ax_error(ivar.ty(self)).0;
                unsafe { ivar.assign_core(error, self) }
            }
        }
        if had_unassigned_ivars {
            self.error(item_id, ElabError::UnassignedIvars);
        }


        // resolve aux symbols.
        for (i, aux) in aux_defs.iter().enumerate() {
            let symbol = aux_symbols[i];

            let ty  = self.instantiate_term_vars(aux.ty);
            let val = self.instantiate_term_vars(aux.value);

            println!("{:?}: {}", &self.strings[self.env.symbol(symbol).name], self.pp(val, 80));

            self.env.resolve_pending(symbol, SymbolKind::Def(symbol::Def {
                num_levels: self.level_params.len(),
                ty,
                val,
            }));
        }


        let mut ty = ty.unwrap_or(val_ty);

        assert_eq!(self.locals.len(), locals.len());
        for l in self.locals.iter().copied().rev() {
            ty  = self.mk_binder(ty,  l.id, true);
            val = self.mk_binder(val, l.id, false);
        }

        if self.locals.len() == 0 {
            ty  = self.instantiate_term_vars(ty);
            val = self.instantiate_term_vars(val);
        }

        debug_assert!(ty.syntax_eq(self.instantiate_term_vars(ty)));
        debug_assert!(val.syntax_eq(self.instantiate_term_vars(val)));

        if !ty.closed() || !val.closed() || ty.has_locals() || val.has_locals() {
            let mut pp = TermPP::new(self.env, &self.strings, &self.lctx, self.alloc);
            let ty  = pp.pp_term(self.instantiate_term_vars(ty));
            let val = pp.pp_term(self.instantiate_term_vars(val));
            eprintln!("{}", pp.render(ty,  50).layout_string());
            eprintln!("{}", pp.render(val, 50).layout_string());
        }

        assert!(ty.closed());
        assert!(val.closed());

        assert!(!ty.has_locals());
        assert!(!val.has_locals());

        if ty.has_ivars() || val.has_ivars() {
            eprintln!("unresolved inference variables");
            let mut pp = TermPP::new(self.env, &self.strings, &self.lctx, self.alloc);
            let ty  = self.instantiate_term_vars(ty);
            let val = self.instantiate_term_vars(val);
            let ty  = pp.pp_term(ty);
            let val = pp.pp_term(val);
            eprintln!("{}", pp.render(ty,  50).layout_string());
            eprintln!("{}", pp.render(val, 50).layout_string());
        }

        assert!(self.check_no_unassigned_variables(item_id.into()).is_some());

        return (ty, val);
    }

    pub fn elab_def(&mut self, item_id: ItemId, def: &item::Def) -> Option<SymbolId> {
        spall::trace_scope!("kibi/elab/def"; "{}",
            def.name.display(self.strings));

        eprintln!("!!! {}", def.name.display(self.strings));

        let (parent, name) = match def.name {
            IdentOrPath::Ident(name) => (self.root_symbol, name),

            IdentOrPath::Path(path) => {
                let (name, parts) = path.parts.split_last().unwrap();
                let parent = self.elab_path(parts)?;
                (parent, *name)
            }
        };

        let (ty, val) = self.elab_def_core(item_id, def.levels, def.params, def.ty, def.value);

        let symbol = self.env.new_symbol(parent, name.value,
            SymbolKind::Def(symbol::Def {
                num_levels: def.levels.len(),
                ty,
                val,
            })
        )?;

        let none = self.elab.token_infos.insert(name.source, TokenInfo::Symbol(symbol));
        debug_assert!(none.is_none());

        Some(symbol)
    }
}

