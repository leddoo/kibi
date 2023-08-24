use crate::tt::*;

use super::*;


impl<'me, 'err, 'a> Elab<'me, 'err, 'a> {
    pub fn infer_type(&mut self, t: TermRef<'a>) -> Option<TermRef<'a>> {
        assert!(t.closed());

        let result = match t.kind {
            TermKind::Sort (l) => {
                self.alloc.mkt_sort(l.succ(self.alloc))
            }

            TermKind::Bound (_) => {
                unreachable!()
            }

            TermKind::Local (id) => {
                self.lctx.lookup(id).ty
            }

            TermKind::Global (g) => {
                let symbol = self.env.symbol(g.id);
                match symbol.kind {
                    SymbolKind::Root => unreachable!(),

                    SymbolKind::BuiltIn(b) => {
                        match b {
                            symbol::BuiltIn::Nat => {
                                debug_assert_eq!(g.levels.len(), 0);
                                Term::SORT_1
                            }

                            symbol::BuiltIn::NatZero => {
                                debug_assert_eq!(g.levels.len(), 0);
                                Term::NAT
                            }

                            symbol::BuiltIn::NatSucc => {
                                debug_assert_eq!(g.levels.len(), 0);
                                Term::NAT_SUCC_TY
                            }

                            symbol::BuiltIn::NatRec => {
                                debug_assert_eq!(g.levels.len(), 1);
                                let r = &g.levels[0];
                                self.alloc.mkt_nat_rec_ty(r)
                            }

                            symbol::BuiltIn::Eq => {
                                debug_assert_eq!(g.levels.len(), 1);
                                let l = &g.levels[0];
                                self.alloc.mkt_eq_ty(l)
                            }

                            symbol::BuiltIn::EqRefl => {
                                debug_assert_eq!(g.levels.len(), 1);
                                let l = &g.levels[0];
                                self.alloc.mkt_eq_refl_ty(l)
                            }

                            symbol::BuiltIn::EqRec => {
                                debug_assert_eq!(g.levels.len(), 2);
                                let l = &g.levels[0];
                                let r = &g.levels[1];
                                self.alloc.mkt_eq_rec_ty(l, r)
                            }
                        }
                    }

                    SymbolKind::Def(d) => {
                        if g.levels.len() != 0 {
                            debug_assert_eq!(g.levels.len() as u32, d.num_levels);
                            d.ty.instantiate_level_params(g.levels, self.alloc)
                        }
                        else { d.ty }
                    }
                }
            }

            TermKind::IVar(var) => {
                self.term_type(var)
            }

            TermKind::Lambda (b) => {
                self.infer_type_as_sort(b.ty)?;

                let id = self.lctx.push(b.ty, None);
                let value = b.val.instantiate(self.alloc.mkt_local(id), self.alloc);

                let value_ty = self.infer_type(value)?;
                self.lctx.pop(id);

                self.alloc.mkt_forall(b.name, b.ty, value_ty.abstracc(id, self.alloc))
            }

            TermKind::Forall (b) => {
                let param_level = self.infer_type_as_sort(b.ty)?;

                let id = self.lctx.push(b.ty, None);
                let value = b.val.instantiate(self.alloc.mkt_local(id), self.alloc);

                let value_level = self.infer_type_as_sort(value)?;
                self.lctx.pop(id);

                self.alloc.mkt_sort(param_level.imax(value_level, self.alloc))
            }

            TermKind::Apply (app) => {
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

            TermKind::Nat => Term::SORT_1,
            TermKind::NatZero => Term::NAT,
            TermKind::NatSucc => Term::NAT_SUCC_TY,
            TermKind::NatRec(r) => self.alloc.mkt_nat_rec_ty(r),

            TermKind::Eq(l) => self.alloc.mkt_eq_ty(l),
            TermKind::EqRefl(l) => self.alloc.mkt_eq_refl_ty(l),
            TermKind::EqRec(l, r) => self.alloc.mkt_eq_rec_ty(l, r),
        };
        assert!(result.closed());
        // TODO: assert all locals are in current local context.

        Some(result)
    }

    pub fn infer_type_as_sort(&mut self, t: TermRef<'a>) -> Option<LevelRef<'a>> {
        let ty = self.infer_type(t)?;
        let ty = self.whnf(ty);
        if let TermKind::Sort(l) = ty.kind {
            return Some(l);
        }
        return None;
    }

    pub fn infer_type_as_forall(&mut self, t: TermRef<'a>) -> Option<term::Binder<'a>> {
        let ty = self.infer_type(t)?;
        let ty = self.whnf(ty);
        if let TermKind::Forall(b) = ty.kind {
            return Some(b);
        }
        return None;
    }
}

