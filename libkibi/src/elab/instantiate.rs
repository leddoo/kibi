use crate::tt::*;

use super::*;


impl<'me, 'err, 'a> Elab<'me, 'err, 'a> {
    pub fn instantiate_level_vars(&self, l: LevelRef<'a>) -> LevelRef<'a> {
        l.replace(self.alloc, |at, _| {
            if let LevelKind::IVar(var) = at.kind {
                if let Some(value) = var.value(self) {
                    return Some(self.instantiate_level_vars(value));
                }
            }
            None
        })
    }

    pub fn instantiate_term_vars(&self, t: TermRef<'a>) -> TermRef<'a> {
        t.replace(self.alloc, |at, _, alloc| {
            if let TermKind::Apply(app) = at.kind {
                let was_ivar = app.fun.is_ivar();

                let new_fun = self.instantiate_term_vars(app.fun);
                let new_arg = self.instantiate_term_vars(app.arg);

                if was_ivar {
                    if let TermKind::Lambda(b) = new_fun.kind {
                        return Some(b.val.instantiate(new_arg, alloc));
                    }
                }
                return Some(app.update(at, alloc, new_fun, new_arg));
            }

            if let TermKind::IVar(var) = at.kind {
                if let Some(value) = var.value(self) {
                    return Some(self.instantiate_term_vars(value));
                }
            }

            at.replace_levels_flat(alloc, |l, _| {
                let new_l = self.instantiate_level_vars(l);
                (!new_l.ptr_eq(l)).then_some(new_l)
            })
        })
    }
}

