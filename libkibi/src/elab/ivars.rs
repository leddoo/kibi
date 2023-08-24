use super::*;


impl<'me, 'err, 'a> Elab<'me, 'err, 'a> {
    pub fn new_term_var_of_type(&mut self, ty: TermRef<'a>) -> TermRef<'a> {
        self.ictx.new_term_var(ty, self.lctx.current())
    }

    pub fn new_term_var(&mut self) -> (TermRef<'a>, TermRef<'a>) {
        let l = self.ictx.new_level_var();
        let tyty = self.alloc.mkt_sort(l);
        let ty = self.ictx.new_term_var(tyty, self.lctx.current());
        (self.ictx.new_term_var(ty, self.lctx.current()), ty)
    }

    pub fn new_ty_var(&mut self) -> (TermRef<'a>, tt::LevelRef<'a>) {
        let l = self.ictx.new_level_var();
        let ty = self.alloc.mkt_sort(l);
        (self.ictx.new_term_var(ty, self.lctx.current()), l)
    }
}

