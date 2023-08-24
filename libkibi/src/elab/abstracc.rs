use crate::tt::*;

use super::*;


impl<'me, 'err, 'a> Elab<'me, 'err, 'a> {
    pub fn abstract_eq(&mut self, t: TermRef<'a>, pat: TermRef<'a>) -> TermRef<'a> {
        let pat = self.ictx.instantiate_term(pat);

        if let TermKind::Local(id) = pat.kind {
            t.abstracc(id, self.alloc)
        }
        else {
            println!("WARN: may not work");
            self.abstract_def_eq(t, pat)
        }
    }

    fn abstract_def_eq(&mut self, t: TermRef<'a>, pat: TermRef<'a>) -> TermRef<'a> {
        t.replace(self.alloc, |at, offset, alloc| {
            if at.syntax_eq(pat) {
                return Some(alloc.mkt_bound(BVar(offset)));
            }
            None
        })
    }
}

