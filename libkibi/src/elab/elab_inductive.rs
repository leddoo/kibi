use crate::ast::adt::Inductive;
use crate::tt::*;

use super::*;


impl<'me, 'err, 'a> Elab<'me, 'err, 'a> {
    pub fn elab_inductive(&mut self, ind: &Inductive<'a>) -> Option<SymbolId> {
        assert_eq!(self.locals.len(), 0);
        assert_eq!(self.level_params.len(), 0);

        for level in ind.levels {
            self.level_params.push(*level);
        }

        let params = self.elab_binders(ind.params)?;

        let ty = if let Some(ty) = &ind.ty {
            self.elab_expr_as_type(ty)?.0
        }
        else { Term::SORT_1 };

        let has_indices = self.whnf_forall(ty).is_some();

        let name_id = self.lctx.push(BinderKind::Explicit, ind.name, ty, None);
        self.locals.push((ind.name, name_id));

        let name_term = self.alloc.mkt_local(name_id);

        // @speed: arena.
        let mut ctors = Vec::with_cap(ind.ctors.len());

        for ctor in ind.ctors {
            let args = self.elab_binders(&ctor.args)?;

            let mut ty = match &ind.ty {
                Some(ty) => self.elab_expr_as_type(ty)?.0,
                None => {
                    if has_indices {
                        println!("error: ctor needs type cause indices mkay");
                        return None;
                    }
                    name_term
                }
            };

            for (id, _, _) in args.iter().rev().copied() {
                ty = self.mk_binder(ty, id, true);
                self.lctx.pop(id);
            }
            self.locals.truncate(self.locals.len() - args.len());

            ctors.push((ctor.name, ty));
        }

        //println!("ctors: {:#?}", ctors);

        assert_eq!(self.locals.len(), params.len() + 1);

        // @temp
        Some(SymbolId::ROOT)
    }
}

