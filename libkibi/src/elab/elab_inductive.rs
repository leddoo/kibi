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

        // check params.
        let params = self.elab_binders(ind.params)?;

        // check type.
        let (mut type_former, mut level) =
            if let Some(ty) = &ind.ty { self.elab_expr_as_type(ty)? }
            else { (Term::SORT_1, Level::L1) };

        let has_indices = self.whnf_forall(type_former).is_some();

        let type_former_for_lctx = type_former;


        // abstract type over params.
        for (param, _, param_l) in params.iter().rev().copied() {
            type_former = self.mk_binder(type_former, param, true);
            level = param_l.imax(level, self.alloc);
        }

        let type_former = self.instantiate_term_vars(type_former);
        if type_former.has_ivars() {
            println!("error: type has ivars");
            return None;
        }

        // register type former.
        let symbol = self.env.new_symbol(self.root_symbol, ind.name,
            SymbolKind::IndTy(symbol::IndTy {
                num_levels: ind.levels.len().try_into().unwrap(),
                own_type: self.alloc.mkt_sort(level),
                type_former,
            }))?;


        // prepare type former applied with params.
        let type_former_with_params = {
            // @speed: arena.
            let mut levels = Vec::with_cap(ind.levels.len());
            for (i, level) in ind.levels.iter().copied().enumerate() {
                levels.push(self.alloc.mkl_param(level, i as u32));
            }
            let levels = levels.move_into(self.alloc).leak();

            let global = self.alloc.mkt_global(symbol, levels);

            let mut result = global;
            for (param, _, _) in params.iter().copied() {
                result = self.alloc.mkt_apply(result, self.alloc.mkt_local(param));
            }
            result
        };


        // add a fake type former to the local context.
        // this one only takes the indices.
        let fake_type_former_id =
            self.lctx.push(BinderKind::Explicit, ind.name,
                type_former_for_lctx, None);
        self.locals.push((ind.name, fake_type_former_id));

        let fake_type_former = self.alloc.mkt_local(fake_type_former_id);


        // elab ctors.
        // @speed: arena.
        let mut ctors = Vec::with_cap(ind.ctors.len());
        for ctor in ind.ctors {
            let args = self.elab_binders(&ctor.args)?;

            let mut ty = match &ctor.ty {
                Some(ty) => self.elab_expr_as_type(ty)?.0,
                None => {
                    if has_indices {
                        println!("error: ctor needs type cause indices mkay");
                        return None;
                    }
                    fake_type_former
                }
            };

            for (arg, _, _) in args.iter().rev().copied() {
                ty = self.mk_binder(ty, arg, true);
                self.lctx.pop(arg);
            }
            self.locals.truncate(self.locals.len() - args.len());

            // replace fake type former.
            ty = ty.replace(self.alloc, |at, _, _| {
                let local = at.try_local()?;
                (local == fake_type_former_id).then_some(type_former_with_params)
            });

            for (param, _, _) in params.iter().rev().copied() {
                ty = self.mk_binder(ty, param, true);
            }

            let ty = self.instantiate_term_vars(ty);

            if ty.has_ivars() {
                println!("error: ctor type has ivars");
                return None;
            }
            assert!(ty.closed_no_local());

            ctors.push((ctor.name, ty));
        }

        // validate lctx.
        self.lctx.pop(fake_type_former_id);
        assert_eq!(self.locals.len(), params.len() + 1);

        return Some(symbol);
    }
}

