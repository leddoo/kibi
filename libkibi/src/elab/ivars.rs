use crate::tt::*;
use local_ctx::OptScopeId;

use super::*;


sti::define_key!(u32, pub LevelVarId);

pub struct LevelVar<'a> {
    value: Option<LevelRef<'a>>,
}


sti::define_key!(u32, pub TermVarId);

pub struct TermVar<'a> {
    scope: OptScopeId,
    ty: TermRef<'a>,
    value: Option<TermRef<'a>>,
}


impl<'me, 'err, 'a> Elab<'me, 'err, 'a> {
    pub fn new_level_var_id(&mut self) -> LevelVarId {
        self.level_vars.push(LevelVar {
            value: None,
        })
    }

    pub fn new_level_var(&mut self) -> LevelRef<'a> {
        let id = self.new_level_var_id();
        self.alloc.mkl_ivar(id)
    }


    pub fn new_term_var_id(&mut self, ty: TermRef<'a>, scope: OptScopeId) -> TermVarId {
        self.term_vars.push(TermVar {
            scope,
            ty,
            value: None,
        })
    }

    pub fn new_term_var_core(&mut self, ty: TermRef<'a>, scope: OptScopeId) -> TermRef<'a> {
        let id = self.new_term_var_id(ty, scope);
        self.alloc.mkt_ivar(id)
    }

    pub fn new_term_var_of_type(&mut self, ty: TermRef<'a>) -> TermRef<'a> {
        self.new_term_var_core(ty, self.lctx.current())
    }

    pub fn new_term_var(&mut self) -> (TermRef<'a>, TermRef<'a>) {
        let l = self.new_level_var();
        let tyty = self.alloc.mkt_sort(l);
        let ty = self.new_term_var_core(tyty, self.lctx.current());
        (self.new_term_var_core(ty, self.lctx.current()), ty)
    }

    pub fn new_ty_var(&mut self) -> (TermRef<'a>, LevelRef<'a>) {
        let l = self.new_level_var();
        let ty = self.alloc.mkt_sort(l);
        (self.new_term_var_core(ty, self.lctx.current()), l)
    }
}


impl LevelVarId {
    #[inline(always)]
    pub fn value<'a>(self, elab: &Elab<'_, '_, 'a>) -> Option<LevelRef<'a>> {
        elab.level_vars[self].value
    }


    #[track_caller]
    pub unsafe fn assign_core<'a>(self, value: LevelRef<'a>, elab: &mut Elab<'_, '_, 'a>) {
        debug_assert!(self.value(elab).is_none());
        elab.level_vars[self].value = Some(value);
    }

    #[track_caller]
    #[must_use]
    pub fn assign<'a>(self, value: LevelRef<'a>, elab: &mut Elab<'_, '_, 'a>) -> bool {
        let value = elab.instantiate_level(value);

        // occurs check.
        if value.find(|at| {
            if let LevelKind::IVar(id) = at.kind {
                return Some(id == self);
            }
            None
        }).is_some() {
            return false;
        }

        unsafe { self.assign_core(value, elab) }
        return true;
    }

}

impl TermVarId {
    #[inline(always)]
    pub fn scope(self, elab: &Elab) -> OptScopeId {
        elab.term_vars[self].scope
    }

    #[inline(always)]
    pub fn ty<'a>(self, elab: &Elab<'_, '_, 'a>) -> TermRef<'a> {
        elab.term_vars[self].ty
    }

    #[inline(always)]
    pub fn value<'a>(self, elab: &Elab<'_, '_, 'a>) -> Option<TermRef<'a>> {
        elab.term_vars[self].value
    }


    #[track_caller]
    #[inline(always)]
    pub unsafe fn assign_core<'a>(self, value: TermRef<'a>, elab: &mut Elab<'_, '_, 'a>) {
        debug_assert!(self.value(elab).is_none());
        debug_assert!(value.closed());
        debug_assert!(elab.lctx.all_locals_in_scope(value, self.scope(elab)));
        debug_assert!(elab.all_term_vars_in_scope(value, self.scope(elab)));
        elab.term_vars[self].value = Some(value);
    }

    // process `var(args) := value`
    #[must_use]
    pub fn assign<'a>(self, args: &[ScopeId], mut value: TermRef<'a>, elab: &mut Elab<'_, '_, 'a>) -> Option<bool> {
        //println!("{:?}({:?}) := {:?}", var, args, value);

        // abstract out `args`.
        for arg in args {
            value = elab.lctx.abstract_lambda(value, *arg);
        }

        let Some(value) = elab.check_value_for_assign(value, self) else {
            return (args.len() == 0).then_some(false);
        };

        if args.len() > 0 {
            // type correct check.
            println!("@todo: check lambda type correct");
        }

        // type check.
        let var_ty = self.ty(elab);
        let value_ty = elab.infer_type(value).unwrap();
        if !elab.def_eq(var_ty, value_ty) {
            println!("type check failed");
            println!("{:?}", var_ty);
            println!("{:?}", value_ty);
            return Some(false);
        }

        unsafe { self.assign_core(value, elab) }
        return Some(true);
    }
}


impl<'me, 'err, 'a> Elab<'me, 'err, 'a> {
    pub fn term_var_in_scope(&self, var: TermVarId, scope: OptScopeId) -> bool {
        self.lctx.scope_is_prefix(scope, var.scope(self))
    }

    pub fn all_term_vars_in_scope(&self, t: TermRef<'a>, scope: OptScopeId) -> bool {
        t.find(|at, _| {
            if let TermKind::IVar(id) = at.kind {
                return Some(!self.term_var_in_scope(id, scope));
            }
            None
        }).is_none()
    }

    fn check_value_for_assign(&mut self, value: TermRef<'a>, var: TermVarId) -> Option<TermRef<'a>> {
        Some(match value.kind {
            TermKind::Local(id) => {
                // scope check.
                let scope = var.scope(self);
                if !self.lctx.local_in_scope(id, scope) {
                    println!("scope check failed (for local)");
                    return None;
                }

                value
            }

            TermKind::IVar(other) => {
                // instantiate:
                if let Some(value) = other.value(self) {
                    return self.check_value_for_assign(value, var);
                }

                // occurs check.
                if other == var {
                    println!("occurs check failed");
                    return None;
                }

                // scope check.
                let var_scope   = var.scope(self);
                let other_scope = var.scope(self);
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

