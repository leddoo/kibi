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
                ast::Binder::Ident(name) => {
                    let (ty, l) = self.new_ty_var();
                    let name = name.to_option().unwrap_or(Atom::NULL);
                    let id = self.lctx.push(tt::BinderKind::Explicit, name, ty, None);
                    self.locals.push((name, id));
                    locals.push((id, ty, l));
                }

                ast::Binder::Typed(b) => {
                    let (ty, l) = self.elab_expr_as_type(b.ty)?;
                    let kind =
                        if b.implicit { tt::BinderKind::Implicit }
                        else          { tt::BinderKind::Explicit };

                    for name in b.names {
                        let name = name.to_option().unwrap_or(Atom::NULL);
                        let id = self.lctx.push(kind, name, ty, None);
                        self.locals.push((name, id));
                        locals.push((id, ty, l));
                    }
                }
            }
        }

        return Some(locals);
    }
}

