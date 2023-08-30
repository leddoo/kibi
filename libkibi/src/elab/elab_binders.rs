use crate::string_table::Atom;
use crate::ast;
use crate::tt;

use super::*;


impl<'me, 'err, 'a> Elab<'me, 'err, 'a> {
    pub fn elab_binders(&mut self, binders: &[ast::Binder<'a>])
    -> Option<Vec<(ScopeId, tt::Term<'a>, tt::Level<'a>)>> {
        // @temp: arena
        let mut locals = Vec::new();

        for binder in binders.iter() {
            match binder {
                ast::Binder::Ident(name) => {
                    let (ty, l) = self.new_ty_var();
                    let name = name.to_option().unwrap_or(Atom::NULL);
                    let id = self.lctx.push(name, ty, None);
                    self.locals.push((name, id));
                    locals.push((id, ty, l));
                }

                ast::Binder::Typed(b) => {
                    let (ty, l) = self.elab_expr_as_type(b.ty)?;
                    for name in b.names {
                        let name = name.to_option().unwrap_or(Atom::NULL);
                        let id = self.lctx.push(name, ty, None);
                        self.locals.push((name, id));
                        locals.push((id, ty, l));
                    }
                }
            }
        }

        return Some(locals);
    }
}

