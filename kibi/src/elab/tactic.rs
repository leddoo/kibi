use sti::traits::CopyIt;
use sti::arena_pool::ArenaPool;

use crate::ast::{TacticId, TacticKind};
use crate::tt::*;

use super::*;

impl<'me, 'c, 'out> Elaborator<'me, 'c, 'out> {
    pub fn elab_by(&mut self, tactics: &[TacticId], expected_ty: Term<'out>) -> (Term<'out>, Term<'out>) {
        let old_locals = self.locals.len();
        let old_scope  = self.lctx.current;

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

        self.locals.truncate(old_locals);
        self.lctx.current = old_scope;

        (ivar.value(self).unwrap(), expected_ty)
    }

    fn elab_tactic(&mut self, tactic_id: TacticId) -> Option<()> {
        let scope = self.lctx.current;

        // @todo: persistent list.
        let mut goals = Vec::with_cap_in(self.alloc, self.goals.len() - self.current_goal);
        for goal in &self.goals[self.current_goal..] {
            if goal.value(self).is_none() {
                goals.push(goal.ty(self));
            }
        }
        let goals = goals.leak();

        let tactic = &self.parse.tactics[tactic_id];
        let info = match tactic.kind {
            TacticKind::Error => return Some(()),

            TacticKind::Goal => {
                TacticInfoKind::None
            }

            TacticKind::Sorry => {
                let (goal, ty) = self.next_goal(tactic_id)?;
                let sorry = self.mkt_ax_sorry(ty, TERM_SOURCE_NONE);
                self.assign_goal(goal, sorry);
                TacticInfoKind::Term(sorry)
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

                TacticInfoKind::Term(value)
            }

            // @todo: avoid double errors.
            TacticKind::Rewrite(it) => {
                let (goal, goal_ty) = self.peek_goal(tactic_id)?;

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
                    goal.scope(self));
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
                self.assign_goal(goal, value);

                // collect remaining ivars (goals).
                let temp = ArenaPool::tls_get_temp();
                let remaining = collect_ivars(value, &*temp);

                // add to goals.
                let old_goals = Vec::from_slice_in(&*temp, &self.goals[self.current_goal..]);
                self.goals.truncate(self.current_goal);
                self.goals.extend_from_slice(&remaining);
                self.goals.push(rest_id);
                self.goals.extend_from_slice(&old_goals);

                TacticInfoKind::Term(value)
            }

            TacticKind::By(it) => {
                let (goal, ty) = self.next_goal(tactic_id)?;
                let value = self.elab_by(it, ty).0;
                self.assign_goal(goal, value);
                TacticInfoKind::Term(value)
            }

            TacticKind::Intro(name) => {
                let (goal, goal_ty) = self.peek_goal(tactic_id)?;
                let Some(pi) = self.whnf_forall(goal_ty) else {
                    self.error(tactic_id, ElabError::TempStr("expected type is not a function"));
                    return Some(());
                };

                let id = self.lctx.push(name.value, pi.ty, ScopeKind::Binder(pi.kind));
                self.locals.push(Local { name: name.value, id, mutable: false });

                let new_ty = pi.val.instantiate(self.alloc.mkt_local(id, TERM_SOURCE_NONE), self.alloc);
                let new_goal = self.new_term_var_id(new_ty, self.lctx.current);

                let value = self.alloc.mkt_lambda(pi.kind, name.value, pi.ty,
                    self.alloc.mkt_ivar(new_goal, TERM_SOURCE_NONE), TERM_SOURCE_NONE);
                self.assign_goal(goal, value);

                self.goals[self.current_goal] = new_goal;

                TacticInfoKind::Term(value)
            }
        };

        debug_assert!(self.elab.tactic_infos[tactic_id].is_none());
        self.elab.tactic_infos[tactic_id] = Some(TacticInfo { scope, goals, kind: info });

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

    #[inline]
    fn assign_goal(&mut self, goal: TermVarId, value: Term<'out>) {
        #[cfg(debug_assertions)] {
            let old_assignment_gen = self.ivars.assignment_gen;
            let goal_ty = goal.ty(self);
            let value_ty = self.infer_type(value).unwrap();
            if !self.ensure_def_eq(value_ty, goal_ty) {
                assert!(false);
            }
            assert_eq!(self.ivars.assignment_gen, old_assignment_gen);
        }

        unsafe { goal.assign_core(value, self) }
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

