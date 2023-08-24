use crate::tt::*;

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

    pub fn new_ty_var(&mut self) -> (TermRef<'a>, LevelRef<'a>) {
        let l = self.ictx.new_level_var();
        let ty = self.alloc.mkt_sort(l);
        (self.ictx.new_term_var(ty, self.lctx.current()), l)
    }

    #[must_use]
    pub fn assign_level(&mut self, var: LevelVarId, value: LevelRef<'a>) -> bool {
        let value = self.ictx.instantiate_level(value);

        // occurs check.
        if value.find(|at| {
            if let LevelKind::IVar(id) = at.kind {
                return Some(id == var);
            }
            None
        }).is_some() {
            return false;
        }

        unsafe { self.ictx.assign_level(var, value) }
        return true;
    }

    // process `var(args) := value`
    #[must_use]
    pub fn assign_term(&mut self, var: TermVarId, args: &[ScopeId], mut value: TermRef<'a>) -> Option<bool> {
        //println!("{:?}({:?}) := {:?}", var, args, value);

        // abstract out `args`.
        for arg in args {
            value = self.lctx.abstract_lambda(value, *arg);
        }

        let Some(value) = self.check_value_for_assign(value, var) else {
            return (args.len() == 0).then_some(false);
        };

        if args.len() > 0 {
            // type correct check.
            println!("@todo: check lambda type correct");
        }

        // type check.
        let var_ty = self.ictx.term_type(var);
        let value_ty = self.infer_type(value).unwrap();
        if !self.def_eq(var_ty, value_ty) {
            println!("type check failed");
            println!("{:?}", var_ty);
            println!("{:?}", value_ty);
            return Some(false);
        }

        unsafe { self.ictx.assign_term(var, value) }
        return Some(true);
    }

    fn check_value_for_assign(&mut self, value: TermRef<'a>, var: TermVarId) -> Option<TermRef<'a>> {
        Some(match value.kind {
            TermKind::Local(id) => {
                // scope check.
                let scope = self.ictx.term_scope(var);
                if !self.lctx.scope_contains(scope, id) {
                    println!("scope check failed (for local)");
                    return None;
                }

                value
            }

            TermKind::IVar(other) => {
                // instantiate:
                if let Some(value) = self.ictx.term_value(other) {
                    return self.check_value_for_assign(value, var);
                }

                // occurs check.
                if other == var {
                    println!("occurs check failed");
                    return None;
                }

                // scope check.
                let var_scope   = self.ictx.term_scope(var);
                let other_scope = self.ictx.term_scope(other);
                if !self.lctx.scope_is_prefix(other_scope, var_scope) {
                    // scope approx.
                    println!("scope check failed (for ivar)");
                    println!("@todo");
                }

                value
            }

            TermKind::Forall(b) |
            TermKind::Lambda(b) =>
                b.update(value, self.alloc,
                    self.check_value_for_assign(b.ty,  var)?,
                    self.check_value_for_assign(b.val, var)?),

            TermKind::Apply(a) =>
                a.update(value, self.alloc,
                    self.check_value_for_assign(a.fun, var)?,
                    self.check_value_for_assign(a.arg, var)?),

            TermKind::Sort(_)   | TermKind::Bound(_) | TermKind::Global(_) |
            TermKind::Nat       | TermKind::NatZero  | TermKind::NatSucc   |
            TermKind::NatRec(_) | TermKind::Eq(_)    | TermKind::EqRefl(_) |
            TermKind::EqRec(_, _) =>
                value,
        })
    }

}

