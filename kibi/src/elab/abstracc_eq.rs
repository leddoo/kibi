use crate::tt::*;

use super::*;


impl<'me, 'c, 'out> Elaborator<'me, 'c, 'out> {
    pub fn abstract_eq(&mut self, t: Term<'out>, pat: Term<'out>) -> Term<'out> {
        let pat = self.instantiate_term_vars(pat);

        if let Some(local) = pat.try_local() {
            t.abstracc(local, self.alloc)
        }
        else {
            self.abstract_def_eq(t, pat)
        }
    }

    fn abstract_def_eq(&mut self, t: Term<'out>, pat: Term<'out>) -> Term<'out> {
        //println!("abstracc_eq: {} / {}", self.pp(t, 80), self.pp(pat, 80));
        t.replace(self.alloc, |at, offset, alloc| {
            // this is *really* slow.
            //if self.is_def_eq(at, pat) {

            if at.syntax_eq(pat) {
                return Some(alloc.mkt_bound(BVar { offset }, at.source()));
            }
            None
        })
    }
}

