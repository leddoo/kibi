use crate::tt::*;

use super::*;


impl<'me, 'c, 'out> Elaborator<'me, 'c, 'out> {
    pub fn ensure_level_def_eq(&mut self, a: Level<'out>, b: Level<'out>) -> bool {
        if self.ivars.level_vars.len() > 0 {
            // we currently don't implement the proper level equivalence test.
            // instead we just do syntax eq + var assignment.
            // but that means, we need to instantiate all level vars first.
            // eg: `max(?v, 0) =?= 0` fails even if `?v = 0`,
            // because `max` and `0` are not syntactically equal.
            let a = self.instantiate_level_vars(a);
            let b = self.instantiate_level_vars(b);
            self.level_def_eq_basic(a, b)
        }
        else {
            self.level_def_eq_basic(a, b)
        }
    }

    fn level_def_eq_basic(&mut self, a: Level<'out>, b: Level<'out>) -> bool {
        if a.syntax_eq(b) {
            return true;
        }

        use LevelData::*;
        match (a.data(), b.data()) {
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

                i1.assign(b, self)
            }

            (IVar(i1), _) => {
                i1.assign(b, self)
            }

            (_, IVar(i2)) => {
                i2.assign(a, self)
            }

            _ => false,
        }
    }

    pub fn ensure_levels_def_eq(&mut self, a: &[Level<'out>], b: &[Level<'out>]) -> bool {
        if a.len() != b.len() {
            return false;
        }
        for i in 0..a.len() {
            if !self.ensure_level_def_eq(a[i], b[i]) {
                return false;
            }
        }
        true
    }
}

