use sti::arena_pool::ArenaPool;

use crate::ast::adt::Inductive;
use crate::tt::*;

use super::*;


impl<'me, 'err, 'a> Elab<'me, 'err, 'a> {
    pub fn elab_inductive(&mut self, ind: &Inductive<'a>) -> Option<SymbolId> {
        assert_eq!(self.locals.len(), 0);
        assert_eq!(self.level_params.len(), 0);

        let temp = ArenaPool::tls_get_rec();

        for level in ind.levels {
            self.level_params.push(*level);
        }

        let symbol = self.env.new_symbol(self.root_symbol,
            ind.name, SymbolKind::Pending)?;

        // check params.
        let params = self.elab_binders(ind.params, &*temp)?;

        // check type.
        let type_former =
            if let Some(ty) = &ind.ty { self.elab_expr_as_type(ty)?.0 }
            else { Term::SORT_1 };

        let has_indices = self.whnf_forall(type_former).is_some();

        // check type former has no ivars.
        if type_former.has_ivars() {
            println!("error: type has ivars");
            return None;
        }

        // check params have no ivars.
        for (param, ty, _) in params.iter().copied() {
            let ty = self.instantiate_term_vars(ty);
            if ty.has_ivars() {
                println!("error: type has ivars");
                return None;
            }
            self.lctx.lookup_mut(param).ty = ty;
        }


        // create a local for the inductive type,
        // for the idents in the ctors to bind to.
        let ind_local_id =
            self.lctx.push(BinderKind::Explicit, ind.name, type_former, None);
        self.locals.push((ind.name, ind_local_id));

        let ind_local = self.alloc.mkt_local(ind_local_id);

        // elab ctors.
        // @speed: arena.
        let mut ctors = Vec::with_cap_in(ind.ctors.len(), &*temp);
        for ctor in ind.ctors {
            let args = self.elab_binders(&ctor.args, &*temp)?;

            let mut ty = match &ctor.ty {
                Some(ty) => self.elab_expr_as_type(ty)?.0,
                None => {
                    if has_indices {
                        println!("error: ctor needs type cause indices mkay");
                        return None;
                    }
                    ind_local
                }
            };

            for (arg, _, _) in args.iter().rev().copied() {
                ty = self.mk_binder(ty, arg, true);
                self.lctx.pop(arg);
            }
            self.locals.truncate(self.locals.len() - args.len());


            let ty = self.instantiate_term_vars(ty);

            if ty.has_ivars() {
                println!("error: ctor type has ivars");
                return None;
            }

            ctors.push((ctor.name, ty));
        }

        // @speed: arena.
        let mut param_ids = Vec::with_cap_in(params.len(), &*temp);
        for (id, _, _) in params.iter().copied() {
            param_ids.push(id);
        }

        // check spec.
        let spec = inductive::MutualSpec {
            levels: ind.levels,
            params: &param_ids,
            types: &[
                inductive::TypeSpec {
                    symbol,
                    local: ind_local_id,
                    ctors: &ctors,
                }
            ],
        };
        inductive::Check::check(self, spec)?;

        return Some(symbol);
    }
}

