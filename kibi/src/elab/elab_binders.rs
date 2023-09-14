use crate::string_table::Atom;
use crate::ast;
use crate::tt;

use super::*;


impl<'me, 'c, 'out> Elaborator<'me, 'c, 'out> {
    pub fn elab_binders<'res>(&mut self, binders: &[ast::Binder], alloc: &'res Arena)
    -> Option<Vec<(ScopeId, tt::Term<'out>, tt::Level<'out>), &'res Arena>> {
        let mut locals = Vec::with_cap_in(alloc, binders.len());

        for binder in binders.iter() {
            match binder {
                ast::Binder::Ident(ident) => {
                    let (ty, l) = self.new_ty_var();

                    let name = ident.value.to_option().unwrap_or(Atom::NULL);
                    let id = self.lctx.push(tt::BinderKind::Explicit, name, ty, None);
                    self.locals.push((name, id));
                    locals.push((id, ty, l));

                    let none = self.elab.token_infos.insert(ident.source, TokenInfo::Local(self.item_id, id));
                    debug_assert!(none.is_none());
                }

                ast::Binder::Typed(b) => {
                    let (ty, l) = self.elab_expr_as_type(b.ty)?;
                    let kind =
                        if b.implicit { tt::BinderKind::Implicit }
                        else          { tt::BinderKind::Explicit };

                    for ident in b.names {
                        let name = ident.value.to_option().unwrap_or(Atom::NULL);
                        let id = self.lctx.push(kind, name, ty, None);
                        self.locals.push((name, id));
                        locals.push((id, ty, l));

                        // @arrow_uses_null_ident
                        if ident.value != Atom::NULL.some() {
                            let none = self.elab.token_infos.insert(ident.source, TokenInfo::Local(self.item_id, id));
                            debug_assert!(none.is_none());
                        }
                    }
                }
            }
        }

        return Some(locals);
    }
}

