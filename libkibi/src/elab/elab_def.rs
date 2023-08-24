use crate::ast::*;
use crate::tt::*;

use super::*;


impl<'me, 'err, 'a> Elab<'me, 'err, 'a> {
    pub fn elab_def(&mut self, def: &item::Def<'a>) -> Option<SymbolId> {
        assert_eq!(self.locals.len(), 0);
        assert_eq!(self.level_params.len(), 0);

        for level in def.levels {
            self.level_params.push(level);
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
            ty  = self.mk_binder(ty,  id, true);
            val = self.mk_binder(val, id, false);
        }

        if self.locals.len() == 0 {
            ty  = self.instantiate_term(ty);
            val = self.instantiate_term(val);
        }

        debug_assert!(ty.syntax_eq(self.instantiate_term(ty)));
        debug_assert!(val.syntax_eq(self.instantiate_term(val)));

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
            let ty  = pp.pp_term(self.instantiate_term(ty));
            let val = pp.pp_term(self.instantiate_term(val));
            println!("{}", pp.render(ty,  50).layout_string());
            println!("{}", pp.render(val, 50).layout_string());
        }

        assert!(ty.closed());
        assert!(val.closed());

        assert!(!ty.has_locals());
        assert!(!val.has_locals());

        if ty.has_ivars() || val.has_ivars() {
            println!("unresolved inference variables");
            let mut pp = TermPP::new(self.env, self.alloc);
            let ty  = self.instantiate_term(ty);
            let val = self.instantiate_term(val);
            let ty  = pp.pp_term(ty);
            let val = pp.pp_term(val);
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
}

