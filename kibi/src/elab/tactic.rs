use sti::traits::CopyIt;

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
        match tactic.kind {
            TacticKind::Error => Some(()),

            TacticKind::Goal => {
                Some(())
            }

            TacticKind::Sorry => {
                let (goal, ty) = self.next_goal(tactic_id)?;
                let sorry = self.mkt_ax_sorry(ty, TERM_SOURCE_NONE);
                assert!(goal.assign(&[], sorry, self).unwrap());
                Some(())
            }

            TacticKind::Assumption => todo!(),

            TacticKind::Refl => todo!(),

            TacticKind::Rewrite(_) => todo!(),

            TacticKind::By(it) => {
                let (goal, ty) = self.next_goal(tactic_id)?;
                let value = self.elab_by(it, ty).0;
                assert!(goal.assign(&[], value, self).unwrap());
                Some(())
            }
        }
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
}

