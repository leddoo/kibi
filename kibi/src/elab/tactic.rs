use sti::traits::CopyIt;
use sti::arena_pool::ArenaPool;

use crate::ast::{TacticId, TacticKind};
use crate::tt::*;

use super::*;

impl<'me, 'c, 'out> Elaborator<'me, 'c, 'out> {
    pub fn elab_by(&mut self, tactics: &[TacticId], expected_ty: Term<'out>) -> (Term<'out>, Term<'out>) {
        let ivar = self.with_saved_goals(|this| {
            this.with_ivar_scope(|this| {
                let ivar = this.new_term_var_id(expected_ty, this.lctx.current);
                this.goals.push(ivar);

                for tactic in tactics.copy_it() {
                    if this.elab_tactic(tactic).is_none() {
                        break;
                    }
                }

                ivar
            })
        });
        (ivar.value(self).unwrap(), expected_ty)
    }

    fn elab_tactic(&mut self, tactic_id: TacticId) -> Option<()> {
        let tactic = &self.parse.tactics[tactic_id];
        let (goal, info) = match tactic.kind {
            TacticKind::Error => return Some(()),

            TacticKind::Goal => {
                let goal = self.peek_goal(tactic_id)?.1;
                (goal, TacticInfoKind::None)
            }

            TacticKind::Sorry => {
                let (goal, ty) = self.next_goal(tactic_id)?;
                let sorry = self.mkt_ax_sorry(ty, TERM_SOURCE_NONE);
                assert!(goal.assign(&[], sorry, self).unwrap());
                (ty, TacticInfoKind::Term(sorry))
            }

            TacticKind::Assumption => todo!(),

            TacticKind::Refl => {
                let (goal, ty) = self.next_goal(tactic_id)?;

                // @speed: try direct match first ~ util.
                let ty = self.whnf(ty);
                let Some([t, lhs, _]) = ty.try_eq_app() else {
                    self.error(tactic_id, ElabError::TempStr("goal is not eq"));
                    return Some(());
                };

                let l_t = self.infer_type_as_sort(t).unwrap();
                let eq_refl =
                    self.alloc.mkt_global(
                        SymbolId::Eq_refl,
                        &self.alloc.alloc_new([l_t])[..],
                        TERM_SOURCE_NONE);
                let value = self.alloc.mkt_apps(eq_refl, &[t, lhs], TERM_SOURCE_NONE);

                if goal.assign(&[], value, self) != Some(true) {
                    self.error(tactic_id, ElabError::TempStr("tactic failed"));
                    return Some(());
                }

                return Some(());
            }

            // @todo: avoid double errors.
            TacticKind::Rewrite(it) => {
                let (goal_ivar, goal_ty) = self.peek_goal(tactic_id)?;

                let (mut thm, mut thm_ty) = self.elab_expr(it.with);
                while let Some(pi) = self.whnf_forall(thm_ty) {
                    let ivar = self.new_term_var_of_type(pi.ty);
                    thm = self.alloc.mkt_apply(thm, ivar, TERM_SOURCE_NONE);
                    thm_ty = pi.val.instantiate(ivar, self.alloc);
                }

                // @speed: try direct match first ~ util.
                let thm_ty = self.whnf(thm_ty);
                let Some([t, lhs, rhs]) = thm_ty.try_eq_app() else {
                    self.error(tactic_id, ElabError::TempStr("equality proof expected"));
                    return Some(());
                };

                let (lhs, rhs) = if !it.symm { (rhs, lhs) } else { (lhs, rhs) };

                let goal_abst = self.abstract_def_eq(goal_ty, rhs);
                if goal_abst.closed() {
                    self.error(tactic_id, ElabError::TempStr("pattern not found in goal"));
                    return Some(());
                }

                // construct proof term:
                // `goal = Eq::nd_rec(t, lhs, motive, rest, rhs, thm)`
                // `motive = lam b _ => goal_abst[b]`
                // `rest: goal_abst[lhs]`

                // @todo: do we need a type correct check?
                let motive =
                    self.alloc.mkt_lambda(BinderKind::Explicit, Atom::NULL,
                        t, goal_abst, TERM_SOURCE_NONE);

                let rest_id = self.new_term_var_id(
                    goal_abst.instantiate(lhs, self.alloc),
                    goal_ivar.scope(self));
                let rest = self.alloc.mkt_ivar(rest_id, TERM_SOURCE_NONE);

                let l_t = self.infer_type_as_sort(t).unwrap();
                let l_r = self.infer_type_as_sort(goal_ty).unwrap();
                let thm =
                    if !it.symm {
                        let eq_symm = 
                            self.alloc.mkt_global(
                                SymbolId::Eq_symm,
                                &self.alloc.alloc_new([l_t])[..],
                                TERM_SOURCE_NONE);
                        self.alloc.mkt_apps(eq_symm, &[
                            t, rhs, lhs, thm,
                        ], TERM_SOURCE_NONE)
                    }
                    else { thm };
                let eq_nd_rec =
                    self.alloc.mkt_global(
                        SymbolId::Eq_nd_rec,
                        &self.alloc.alloc_new([l_t, l_r])[..],
                        TERM_SOURCE_NONE);
                let value = self.alloc.mkt_apps(eq_nd_rec, &[
                    t, lhs, motive, rest, rhs, thm
                ], TERM_SOURCE_NONE);

                let value = self.instantiate_term_vars(value);
                //println!("value: {}", self.pp(value, 150));

                if goal_ivar.assign(&[], value, self) != Some(true) {
                    assert!(false);
                }

                // collect remaining ivars (goals).
                let temp = ArenaPool::tls_get_temp();
                let remaining = collect_ivars(value, &*temp);

                // add to goals.
                let old_goals = Vec::from_slice_in(&*temp, &self.goals[self.current_goal..]);
                self.goals.truncate(self.current_goal);
                self.goals.extend_from_slice(&remaining);
                self.goals.push(rest_id);
                self.goals.extend_from_slice(&old_goals);

                return Some(());
            }

            TacticKind::By(it) => {
                let (goal, ty) = self.next_goal(tactic_id)?;
                let value = self.elab_by(it, ty).0;
                assert!(goal.assign(&[], value, self).unwrap());
                (ty, TacticInfoKind::Term(value))
            }
        };

        debug_assert!(self.elab.tactic_infos[tactic_id].is_none());
        self.elab.tactic_infos[tactic_id] = Some(TacticInfo { goal, kind: info });

        Some(())
    }

    #[inline]
    fn next_goal(&mut self, source: impl Into<DiagnosticSource>) -> Option<(TermVarId, Term<'out>)> {
        while self.current_goal < self.goals.len() {
            let result = self.goals[self.current_goal];
            self.current_goal += 1;

            if result.value(self).is_none() {
                return Some((result, result.ty(self)));
            }
        }

        self.error(source, ElabError::TempStr("no goals left"));
        return None;
    }

    #[inline]
    fn peek_goal(&mut self, source: impl Into<DiagnosticSource>) -> Option<(TermVarId, Term<'out>)> {
        let result = self.next_goal(source);
        if result.is_some() {
            self.current_goal -= 1;
        }
        return result;
    }
}

// @temp: put this somewhere else. utils(tm)?
fn collect_ivars<'res>(t: Term, alloc: &'res Arena) -> Vec<TermVarId, &'res Arena> {
    let mut result = Vec::new_in(alloc);
    collect_ivars_ex(t, &mut result);
    return result;
}
fn collect_ivars_ex<'res>(t: Term, result: &mut Vec<TermVarId, &'res Arena>) {
    match t.data() {
        TermData::Sort(_) => (),
        TermData::Bound(_) => (),
        TermData::Local(_) => (),
        TermData::Global(_) => (),

        TermData::IVar(ivar) => {
            if !result.contains(&ivar) {
                result.push(ivar);
            }
        }

        TermData::Forall(it) |
        TermData::Lambda(it) => {
            collect_ivars_ex(it.ty,  result);
            collect_ivars_ex(it.val, result);
        }

        TermData::Let(it) => {
            collect_ivars_ex(it.ty,   result);
            collect_ivars_ex(it.val,  result);
            collect_ivars_ex(it.body, result);
        }

        TermData::Apply(it) => {
            collect_ivars_ex(it.fun, result);
            collect_ivars_ex(it.arg, result);
        }
    }
}

