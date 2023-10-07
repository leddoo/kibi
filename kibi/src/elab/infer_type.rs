use crate::tt::*;

use super::*;


impl<'me, 'c, 'out> Elaborator<'me, 'c, 'out> {
    pub fn infer_type(&mut self, t: Term<'out>) -> Option<Term<'out>> {
        let save = self.lctx.save();
        let result = self.infer_type_core(t);
        self.lctx.restore(save);

        #[cfg(debug_assertions)]
        if let Some(result) = result {
            assert!(self.lctx.all_locals_in_scope(result, self.lctx.current));
        }
        return result;
    }

    pub fn infer_type_core(&mut self, t: Term<'out>) -> Option<Term<'out>> {
        assert!(t.closed());

        let result = match t.data() {
            TermData::Sort (l) => {
                self.alloc.mkt_sort(l.succ(self.alloc), TERM_SOURCE_NONE)
            }

            TermData::Bound (_) => {
                unreachable!()
            }

            TermData::Local (id) => {
                self.lctx.lookup(id).ty
            }

            TermData::Global (g) => {
                let symbol = self.env.symbol(g.id);
                let (num_levels, ty) = match symbol.kind {
                    SymbolKind::Root |
                    SymbolKind::Predeclared |
                    SymbolKind::Pending(None) => unreachable!(),

                    SymbolKind::Pending(Some(it)) | 
                    SymbolKind::Axiom(it) => (it.num_levels, it.ty),

                    SymbolKind::Def(it) => (it.num_levels, it.ty),

                    SymbolKind::IndAxiom(it) => (it.num_levels, it.ty),
                };

                debug_assert_eq!(g.levels.len(), num_levels);
                if g.levels.len() != 0 {
                    ty.instantiate_level_params(g.levels, self.alloc)
                }
                else { ty }
            }

            TermData::IVar(var) => {
                var.ty(self)
            }

            TermData::Lambda (b) => {
                self.infer_type_as_sort(b.ty)?;

                let id = self.lctx.push(b.name, b.ty, ScopeKind::Binder(b.kind));
                let value = b.val.instantiate(self.alloc.mkt_local(id, TERM_SOURCE_NONE), self.alloc);

                let value_ty = self.infer_type_core(value)?;
                self.lctx.pop(id);

                self.alloc.mkt_forall(b.kind, b.name, b.ty, value_ty.abstracc(id, self.alloc), TERM_SOURCE_NONE)
            }

            TermData::Forall (b) => {
                let param_level = self.infer_type_as_sort(b.ty)?;

                let id = self.lctx.push(b.name, b.ty, ScopeKind::Binder(b.kind));
                let value = b.val.instantiate(self.alloc.mkt_local(id, TERM_SOURCE_NONE), self.alloc);

                let value_level = self.infer_type_as_sort(value)?;
                self.lctx.pop(id);

                self.alloc.mkt_sort(param_level.imax(value_level, self.alloc), TERM_SOURCE_NONE)
            }

            TermData::Let (b) => {
                let id = self.lctx.push(b.name, b.ty, ScopeKind::Local(b.val));

                let body = b.body.instantiate(self.alloc.mkt_local(id, TERM_SOURCE_NONE), self.alloc);

                let result = self.infer_type_core(body)?;
                self.lctx.pop(id);

                result
            }

            TermData::Apply (app) => {
                let fun_ty = self.infer_type_as_forall(app.fun)?;
                /* @temp: type checking.
                let arg_ty = self.infer_type(app.arg)?;

                if self.check_types {
                    if !self.expr_def_eq(fun_ty.param, arg_ty) {
                        return None;
                    }
                }
                */

                fun_ty.val.instantiate(app.arg, self.alloc)
            }
        };
        assert!(result.closed());
        // TODO: assert all locals are in current local context.

        Some(result)
    }

    pub fn infer_type_as_sort(&mut self, t: Term<'out>) -> Option<Level<'out>> {
        let ty = self.infer_type(t)?;
        let ty = self.whnf(ty);
        return Some(ty.try_sort()?);
    }

    pub fn infer_type_as_forall(&mut self, t: Term<'out>) -> Option<term::Binder<'out>> {
        let ty = self.infer_type(t)?;
        let ty = self.whnf(ty);
        return Some(ty.try_forall()?);
    }
}

