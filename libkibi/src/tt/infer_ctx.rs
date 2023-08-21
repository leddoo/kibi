use sti::keyed::{KVec, KRange};

use super::syntax::*;


sti::define_key!(u32, pub LevelVarId);
sti::define_key!(u32, pub TermVarId);


pub struct InferCtx<'a> {
    level_vars: KVec<LevelVarId, LevelVar<'a>>,
    term_vars:  KVec<TermVarId,  TermVar<'a>>,
}

struct LevelVar<'a> {
    value: Option<LevelRef<'a>>,
}

struct TermVar<'a> {
    value: Option<TermRef<'a>>,
    ty: TermRef<'a>,
}

impl<'a> InferCtx<'a> {
    pub fn new() -> Self {
        Self {
            level_vars: KVec::new(),
            term_vars:  KVec::new(),
        }
    }

    pub fn new_level_var(&mut self) -> LevelVarId {
        self.level_vars.push(LevelVar {
            value: None,
        })
    }

    pub fn new_term_var(&mut self, ty: TermRef<'a>) -> TermVarId {
        self.term_vars.push(TermVar {
            value: None,
            ty,
        })
    }


    #[inline(always)]
    pub fn level_ids(&self) -> KRange<LevelVarId> {
        self.level_vars.range()
    }

    #[inline(always)]
    pub fn term_ids(&self) -> KRange<TermVarId> {
        self.term_vars.range()
    }


    #[inline(always)]
    pub fn level_value(&self, id: LevelVarId) -> Option<LevelRef<'a>> {
        self.level_vars[id].value
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
    pub fn assign_level(&mut self, id: LevelVarId, value: LevelRef<'a>) {
        let entry = &mut self.level_vars[id];
        assert!(entry.value.is_none());
        entry.value = Some(value);
    }

    #[track_caller]
    #[inline(always)]
    pub fn assign_term(&mut self, id: TermVarId, value: TermRef<'a>) {
        let entry = &mut self.term_vars[id];
        assert!(entry.value.is_none());
        entry.value = Some(value);
    }
}

