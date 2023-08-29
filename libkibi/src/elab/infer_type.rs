use crate::tt::*;

use super::*;


impl<'me, 'err, 'a> Elab<'me, 'err, 'a> {
    pub fn infer_type(&mut self, t: TermRef<'a>) -> Option<TermRef<'a>> {
        assert!(t.closed());

        let result = match t.data {
            TermData::Sort (l) => {
                self.alloc.mkt_sort(l.succ(self.alloc))
            }

            TermData::Bound (_) => {
                unreachable!()
            }

            TermData::Local (id) => {
                self.lctx.lookup(id).ty
            }

            TermData::Global (g) => {
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
                                let r = g.levels[0];
                                self.alloc.mkt_nat_rec_ty(r)
                            }

                            symbol::BuiltIn::Eq => {
                                debug_assert_eq!(g.levels.len(), 1);
                                let l = g.levels[0];
                                self.alloc.mkt_eq_ty(l)
                            }

                            symbol::BuiltIn::EqRefl => {
                                debug_assert_eq!(g.levels.len(), 1);
                                let l = g.levels[0];
                                self.alloc.mkt_eq_refl_ty(l)
                            }

                            symbol::BuiltIn::EqRec => {
                                debug_assert_eq!(g.levels.len(), 2);
                                let l = g.levels[0];
                                let r = g.levels[1];
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

            TermData::IVar(var) => {
                var.ty(self)
            }

            TermData::Lambda (b) => {
                self.infer_type_as_sort(b.ty)?;

                let id = self.lctx.push(b.name, b.ty, None);
                let value = b.val.instantiate(self.alloc.mkt_local(id), self.alloc);

                let value_ty = self.infer_type(value)?;
                self.lctx.pop(id);

                self.alloc.mkt_forall(b.name, b.ty, value_ty.abstracc(id, self.alloc))
            }

            TermData::Forall (b) => {
                let param_level = self.infer_type_as_sort(b.ty)?;

                let id = self.lctx.push(b.name, b.ty, None);
                let value = b.val.instantiate(self.alloc.mkt_local(id), self.alloc);

                let value_level = self.infer_type_as_sort(value)?;
                self.lctx.pop(id);

                self.alloc.mkt_sort(param_level.imax(value_level, self.alloc))
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

            TermData::Nat => Term::SORT_1,
            TermData::NatZero => Term::NAT,
            TermData::NatSucc => Term::NAT_SUCC_TY,
            TermData::NatRec(r) => self.alloc.mkt_nat_rec_ty(r),

            TermData::Eq(l) => self.alloc.mkt_eq_ty(l),
            TermData::EqRefl(l) => self.alloc.mkt_eq_refl_ty(l),
            TermData::EqRec(l, r) => self.alloc.mkt_eq_rec_ty(l, r),
        };
        assert!(result.closed());
        // TODO: assert all locals are in current local context.

        Some(result)
    }

    pub fn infer_type_as_sort(&mut self, t: TermRef<'a>) -> Option<Level<'a>> {
        let ty = self.infer_type(t)?;
        let ty = self.whnf(ty);
        if let TermData::Sort(l) = ty.data {
            return Some(l);
        }
        return None;
    }

    pub fn infer_type_as_forall(&mut self, t: TermRef<'a>) -> Option<term::Binder<'a>> {
        let ty = self.infer_type(t)?;
        let ty = self.whnf(ty);
        if let TermData::Forall(b) = ty.data {
            return Some(b);
        }
        return None;
    }
}

