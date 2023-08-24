use crate::tt::*;

use super::*;


impl<'me, 'err, 'a> Elab<'me, 'err, 'a> {
    pub fn level_def_eq(&mut self, a: LevelRef<'a>, b: LevelRef<'a>) -> bool {
        if self.has_level_vars() {
            // we currently don't implement the proper level equivalence test.
            // instead we just do syntax eq + var assignment.
            // but that means, we need to instantiate all level vars first.
            // eg: `max(?v, 0) =?= 0` fails even if `?v = 0`,
            // because `max` and `0` are not syntactically equal.
            let a = self.instantiate_level(a);
            let b = self.instantiate_level(b);
            self.level_def_eq_basic(a, b)
        }
        else {
            self.level_def_eq_basic(a, b)
        }
    }

    pub fn level_def_eq_basic(&mut self, a: LevelRef<'a>, b: LevelRef<'a>) -> bool {
        if a.syntax_eq(b) {
            return true;
        }

        use LevelKind::*;
        match (a.kind, b.kind) {
            (Zero, Zero) =>
                true,

            (Succ(l1), Succ(l2)) =>
                self.level_def_eq_basic(l1, l2),

            (Max (p1), Max (p2)) |
            (IMax(p1), IMax(p2)) =>
                self.level_def_eq_basic(p1.lhs, p2.lhs) &&
                self.level_def_eq_basic(p1.rhs, p2.rhs),

            (IVar(i1), IVar(i2)) => {
                if i1 == i2 {
                    return true;
                }

                self.assign_level(i1, b)
            }

            (IVar(id), _) => {
                self.assign_level(id, b)
            }

            (_, IVar(id)) => {
                self.assign_level(id, a)
            }

            _ => false,
        }
    }

    pub fn level_list_def_eq(&mut self, a: LevelList<'a>, b: LevelList<'a>) -> bool {
        if a.len() != b.len() {
            return false;
        }
        for i in 0..a.len() {
            if !self.level_def_eq(&a[i], &b[i]) {
                return false;
            }
        }
        true
    }

}

