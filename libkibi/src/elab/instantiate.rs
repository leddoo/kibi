use crate::tt::*;

use super::*;


impl<'me, 'err, 'a> Elab<'me, 'err, 'a> {
    pub fn instantiate_level(&self, l: LevelRef<'a>) -> LevelRef<'a> {
        l.replace(self.alloc, |at, _| {
            if let LevelKind::IVar(var) = at.kind {
                if let Some(value) = var.value(self) {
                    return Some(self.instantiate_level(value));
                }
            }
            None
        })
    }

    pub fn instantiate_term(&self, t: TermRef<'a>) -> TermRef<'a> {
        t.replace(self.alloc, |at, _, alloc| {
            if let TermKind::IVar(var) = at.kind {
                if let Some(value) = var.value(self) {
                    return Some(self.instantiate_term(value));
                }
            }

            at.replace_levels_flat(alloc, |l, _| {
                let new_l = self.instantiate_level(l);
                (!new_l.ptr_eq(l)).then_some(new_l)
            })
        })
    }
}

