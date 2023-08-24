use sti::keyed::KRange;

use crate::tt::*;
use local_ctx::OptScopeId;

use super::*;


sti::define_key!(u32, pub LevelVarId);
sti::define_key!(u32, pub TermVarId);

pub struct LevelVar<'a> {
    value: Option<LevelRef<'a>>,
}

pub struct TermVar<'a> {
    scope: OptScopeId,
    ty: TermRef<'a>,
    value: Option<TermRef<'a>>,
}


impl<'me, 'err, 'a> Elab<'me, 'err, 'a> {
    #[inline(always)]
    pub fn level_var_ids(&self) -> KRange<LevelVarId> { self.level_vars.range() }

    #[inline(always)]
    pub fn term_var_ids(&self) -> KRange<TermVarId> { self.term_vars.range() }


    #[inline(always)]
    pub fn has_level_vars(&self) -> bool { self.level_vars.len() > 0 }

    #[inline(always)]
    pub fn has_term_vars(&self) -> bool { self.term_vars.len() > 0 }

    #[inline(always)]
    pub fn has_any_vars(&self) -> bool { self.has_level_vars() || self.has_term_vars() }


    // levels.

    pub fn new_level_var_id(&mut self) -> LevelVarId {
        self.level_vars.push(LevelVar {
            value: None,
        })
    }

    pub fn new_level_var(&mut self) -> LevelRef<'a> {
        let id = self.new_level_var_id();
        self.alloc.mkl_ivar(id)
    }


    #[inline(always)]
    pub fn level_value(&self, id: LevelVarId) -> Option<LevelRef<'a>> {
        self.level_vars[id].value
    }

    #[track_caller]
    #[inline(always)]
    pub unsafe fn assign_level_core(&mut self, id: LevelVarId, value: LevelRef<'a>) {
        let entry = &mut self.level_vars[id];
        assert!(entry.value.is_none());
        entry.value = Some(value);
    }



    // terms.

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

    #[inline(always)]
    pub fn term_scope(&self, id: TermVarId) -> OptScopeId {
        self.term_vars[id].scope
    }

    #[inline(always)]
    pub fn term_value(&self, id: TermVarId) -> Option<TermRef<'a>> {
        self.term_vars[id].value
    }

    #[inline(always)]
    pub fn term_type(&self, id: TermVarId) -> TermRef<'a> {
        self.term_vars[id].ty
    }

    #[track_caller]
    #[inline(always)]
    pub unsafe fn assign_term_core(&mut self, id: TermVarId, value: TermRef<'a>) {
        assert!(value.closed());

        let entry = &mut self.term_vars[id];
        assert!(entry.value.is_none());
        entry.value = Some(value);
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

    #[must_use]
    pub fn assign_level(&mut self, var: LevelVarId, value: LevelRef<'a>) -> bool {
        let value = self.instantiate_level(value);

        // occurs check.
        if value.find(|at| {
            if let LevelKind::IVar(id) = at.kind {
                return Some(id == var);
            }
            None
        }).is_some() {
            return false;
        }

        unsafe { self.assign_level_core(var, value) }
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
        let var_ty = self.term_type(var);
        let value_ty = self.infer_type(value).unwrap();
        if !self.def_eq(var_ty, value_ty) {
            println!("type check failed");
            println!("{:?}", var_ty);
            println!("{:?}", value_ty);
            return Some(false);
        }

        unsafe { self.assign_term_core(var, value) }
        return Some(true);
    }

    fn check_value_for_assign(&mut self, value: TermRef<'a>, var: TermVarId) -> Option<TermRef<'a>> {
        Some(match value.kind {
            TermKind::Local(id) => {
                // scope check.
                let scope = self.term_scope(var);
                if !self.lctx.scope_contains(scope, id) {
                    println!("scope check failed (for local)");
                    return None;
                }

                value
            }

            TermKind::IVar(other) => {
                // instantiate:
                if let Some(value) = self.term_value(other) {
                    return self.check_value_for_assign(value, var);
                }

                // occurs check.
                if other == var {
                    println!("occurs check failed");
                    return None;
                }

                // scope check.
                let var_scope   = self.term_scope(var);
                let other_scope = self.term_scope(other);
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

