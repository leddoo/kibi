use crate::tt::*;
use local_ctx::OptScopeId;

use super::*;


pub struct LevelVar<'a> {
    value: Option<Level<'a>>,
    assignment_gen: u32,
}


pub struct TermVar<'a> {
    scope: OptScopeId,
    ty: Term<'a>,
    value: Option<Term<'a>>,
    assignment_gen: u32,
}


pub(super) struct IVarCtx<'a> {
    // @todo: non-pub.
    pub level_vars: KVec<LevelVarId, ivars::LevelVar<'a>>,
    pub term_vars:  KVec<TermVarId,  ivars::TermVar<'a>>,
    pub assignment_gen: u32,
}

impl<'a> IVarCtx<'a> {
    #[inline]
    pub fn new() -> Self {
        Self {
            level_vars: KVec::new(),
            term_vars: KVec::new(),
            assignment_gen: 0,
        }
    }

    pub fn clear(&mut self) {
        self.level_vars.inner_mut_unck().clear();
        self.term_vars.inner_mut_unck().clear();
        self.assignment_gen = 0;
    }
}


pub(super) struct SavePoint {
    num_level_vars: u32,
    num_term_vars:  u32,
    assignment_gen: u32,
}

impl<'a> IVarCtx<'a> {
    pub fn save(&self) -> SavePoint {
        SavePoint {
            num_level_vars: self.level_vars.len() as u32,
            num_term_vars:  self.term_vars.len() as u32,
            assignment_gen: self.assignment_gen,
        }
    }

    pub fn restore(&mut self, save: SavePoint) {
        self.level_vars.inner_mut_unck().truncate(save.num_level_vars as usize);
        self.term_vars.inner_mut_unck().truncate(save.num_term_vars as usize);

        if self.assignment_gen > save.assignment_gen {
            //println!("restore assignments");

            for level in self.level_vars.inner_mut_unck().iter_mut() {
                if level.assignment_gen > save.assignment_gen {
                    level.value = None;
                }
            }

            for term in self.term_vars.inner_mut_unck().iter_mut() {
                if term.assignment_gen > save.assignment_gen {
                    term.value = None;
                }
            }

            self.assignment_gen = save.assignment_gen;
        }
    }
}


impl<'me, 'out, 'a> Elab<'me, 'out, 'a> {
    pub fn new_level_var_id(&mut self) -> LevelVarId {
        self.ivars.level_vars.push(LevelVar {
            value: None,
            assignment_gen: 0,
        })
    }

    pub fn new_level_var(&mut self) -> Level<'a> {
        let id = self.new_level_var_id();
        self.alloc.mkl_ivar(id)
    }


    pub fn new_term_var_id(&mut self, ty: Term<'a>, scope: OptScopeId) -> TermVarId {
        self.ivars.term_vars.push(TermVar {
            scope,
            ty,
            value: None,
            assignment_gen: 0,
        })
    }

    pub fn new_term_var_core(&mut self, ty: Term<'a>, scope: OptScopeId) -> Term<'a> {
        let id = self.new_term_var_id(ty, scope);
        self.alloc.mkt_ivar(id)
    }

    pub fn new_term_var_of_type(&mut self, ty: Term<'a>) -> Term<'a> {
        self.new_term_var_core(ty, self.lctx.current())
    }

    pub fn new_term_var(&mut self) -> (Term<'a>, Term<'a>) {
        let l = self.new_level_var();
        let tyty = self.alloc.mkt_sort(l);
        let ty = self.new_term_var_core(tyty, self.lctx.current());
        (self.new_term_var_core(ty, self.lctx.current()), ty)
    }

    pub fn new_ty_var(&mut self) -> (Term<'a>, Level<'a>) {
        let l = self.new_level_var();
        let ty = self.alloc.mkt_sort(l);
        (self.new_term_var_core(ty, self.lctx.current()), l)
    }
}


impl LevelVarId {
    #[inline(always)]
    pub fn value<'a>(self, elab: &Elab<'_, '_, 'a>) -> Option<Level<'a>> {
        elab.ivars.level_vars[self].value
    }


    #[track_caller]
    #[inline]
    pub unsafe fn assign_core<'a>(self, value: Level<'a>, elab: &mut Elab<'_, '_, 'a>) {
        debug_assert!(self.value(elab).is_none());
        let var = &mut elab.ivars.level_vars[self];
        var.value = Some(value);
        var.assignment_gen = elab.ivars.assignment_gen;
        elab.ivars.assignment_gen += 1;
    }

    #[track_caller]
    #[must_use]
    pub fn assign<'a>(self, value: Level<'a>, elab: &mut Elab<'_, '_, 'a>) -> bool {
        let value = elab.instantiate_level_vars(value);

        // occurs check.
        if value.find(|at| Some(at.try_ivar()? == self)).is_some() {
            return false;
        }

        unsafe { self.assign_core(value, elab) }
        return true;
    }

}

impl TermVarId {
    #[inline(always)]
    pub fn scope(self, elab: &Elab) -> OptScopeId {
        elab.ivars.term_vars[self].scope
    }

    #[inline(always)]
    pub fn ty<'a>(self, elab: &Elab<'_, '_, 'a>) -> Term<'a> {
        elab.ivars.term_vars[self].ty
    }

    #[inline(always)]
    pub fn value<'a>(self, elab: &Elab<'_, '_, 'a>) -> Option<Term<'a>> {
        elab.ivars.term_vars[self].value
    }


    #[track_caller]
    #[inline]
    pub unsafe fn assign_core<'a>(self, value: Term<'a>, elab: &mut Elab<'_, '_, 'a>) {
        debug_assert!(self.value(elab).is_none());
        debug_assert!(value.closed());
        debug_assert!(elab.lctx.all_locals_in_scope(value, self.scope(elab)));
        debug_assert!(elab.all_term_vars_in_scope(value, self.scope(elab)));
        let var = &mut elab.ivars.term_vars[self];
        var.value = Some(value);
        var.assignment_gen = elab.ivars.assignment_gen;
        elab.ivars.assignment_gen += 1;
    }

    // process `var(args) := value`
    #[must_use]
    pub fn assign<'a>(self, args: &[ScopeId], mut value: Term<'a>, elab: &mut Elab<'_, '_, 'a>) -> Option<bool> {
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
        if !elab.ensure_def_eq(var_ty, value_ty) {
            println!("type check failed");
            let var_ty   = elab.instantiate_term_vars(var_ty);
            let value_ty = elab.instantiate_term_vars(value_ty);
            println!("{}", elab.pp(var_ty,   80));
            println!("{}", elab.pp(value_ty, 80));
            return Some(false);
        }

        //println!("{:?} := {}", self, elab.pp(value, 80));

        unsafe { self.assign_core(value, elab) }
        return Some(true);
    }
}


impl<'me, 'err, 'a> Elab<'me, 'err, 'a> {
    pub fn term_var_in_scope(&self, var: TermVarId, scope: OptScopeId) -> bool {
        self.lctx.scope_is_prefix(var.scope(self), scope)
    }

    pub fn all_term_vars_in_scope(&self, t: Term<'a>, scope: OptScopeId) -> bool {
        t.find(|at, _| {
            let var = at.try_ivar()?;
            return Some(!self.term_var_in_scope(var, scope));
        }).is_none()
    }

    fn check_value_for_assign(&mut self, value: Term<'a>, var: TermVarId) -> Option<Term<'a>> {
        Some(match value.data() {
            TermData::Local(id) => {
                // scope check.
                let scope = var.scope(self);
                if !self.lctx.local_in_scope(id, scope) {
                    println!("scope check failed (for local)");
                    return None;
                }

                value
            }

            TermData::IVar(other) => {
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
                if !self.term_var_in_scope(other, var.scope(self)) {
                    // scope approx.
                    let scope = self.lctx.scope_common_prefix(
                        var.scope(self), other.scope(self));

                    let ty = self.check_value_for_assign(other.ty(self), var)?;

                    let new_other = self.new_term_var_core(ty, scope);
                    unsafe { other.assign_core(new_other, self) }

                    return Some(new_other);
                }

                value
            }

            TermData::Forall(b) |
            TermData::Lambda(b) =>
                b.update(value, self.alloc,
                    self.check_value_for_assign(b.ty,  var)?,
                    self.check_value_for_assign(b.val, var)?),

            TermData::Apply(a) =>
                a.update(value, self.alloc,
                    self.check_value_for_assign(a.fun, var)?,
                    self.check_value_for_assign(a.arg, var)?),

            TermData::Sort(_)   | TermData::Bound(_) | TermData::Global(_) =>
                value,
        })
    }
}

