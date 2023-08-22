use sti::arena::Arena;
use sti::keyed::{KVec, KRange};

use super::syntax::*;
use super::local_ctx::OptScopeId;


sti::define_key!(u32, pub LevelVarId);
sti::define_key!(u32, pub TermVarId);


pub struct InferCtx<'a> {
    alloc: &'a Arena,

    level_vars: KVec<LevelVarId, LevelVar<'a>>,
    term_vars:  KVec<TermVarId,  TermVar<'a>>,
}

struct LevelVar<'a> {
    value: Option<LevelRef<'a>>,
}

struct TermVar<'a> {
    scope: OptScopeId,
    ty: TermRef<'a>,
    value: Option<TermRef<'a>>,
}

impl<'a> InferCtx<'a> {
    pub fn new(alloc: &'a Arena) -> Self {
        Self {
            alloc,
            level_vars: KVec::new(),
            term_vars:  KVec::new(),
        }
    }

    #[inline(always)]
    pub fn level_ids(&self) -> KRange<LevelVarId> { self.level_vars.range() }

    #[inline(always)]
    pub fn term_ids(&self) -> KRange<TermVarId> { self.term_vars.range() }


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
    pub fn assign_level(&mut self, id: LevelVarId, value: LevelRef<'a>) {
        let entry = &mut self.level_vars[id];
        assert!(entry.value.is_none());
        entry.value = Some(value);
    }

    pub fn instantiate_level(&self, l: LevelRef<'a>) -> LevelRef<'a> {
        l.replace(self.alloc, |at, _| {
            if let LevelKind::IVar(id) = at.kind {
                return self.level_value(id);
            }
            None
        })
    }


    // terms.

    pub fn new_term_var_id(&mut self, ty: TermRef<'a>, scope: OptScopeId) -> TermVarId {
        self.term_vars.push(TermVar {
            scope,
            ty,
            value: None,
        })
    }

    pub fn new_term_var(&mut self, ty: TermRef<'a>, scope: OptScopeId) -> TermRef<'a> {
        let id = self.new_term_var_id(ty, scope);
        self.alloc.mkt_ivar(id)
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
    pub fn assign_term(&mut self, id: TermVarId, value: TermRef<'a>) {
        let entry = &mut self.term_vars[id];
        assert!(entry.value.is_none());
        entry.value = Some(value);
    }

    pub fn instantiate_term(&self, t: TermRef<'a>) -> TermRef<'a> {
        t.replace(self.alloc, |at, _, alloc| {
            if let TermKind::IVar(id) = at.kind {
                return self.term_value(id);
            }

            at.replace_levels_flat(alloc, |l, _| {
                let new_l = self.instantiate_level(l);
                (!new_l.ptr_eq(l)).then_some(new_l)
            })
        })
    }
}

