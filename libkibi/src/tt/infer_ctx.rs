use sti::keyed::KVec;

use super::syntax::*;


sti::define_key!(u32, pub LevelVarId);
sti::define_key!(u32, pub TermVarId);


pub struct InferCtx<'a> {
    level_vars: KVec<LevelVarId, LevelVar<'a>>,
    term_vars:  KVec<TermVarId,  TermVar<'a>>,
}

pub struct LevelVar<'a> {
    pub value: Option<LevelRef<'a>>,
}

pub struct TermVar<'a> {
    pub value: Option<TermRef<'a>>,
    pub ty: TermRef<'a>,
}

impl<'a> InferCtx<'a> {
    pub fn new() -> Self {
        Self {
            level_vars: KVec::new(),
            term_vars:  KVec::new(),
        }
    }

    #[inline(always)]
    pub fn level_var(&self, id: LevelVarId) -> &LevelVar<'a> {
        &self.level_vars[id]
    }

    #[inline(always)]
    pub fn term_var(&self, id: TermVarId) -> &TermVar<'a> {
        &self.term_vars[id]
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


    #[track_caller]
    #[inline(always)]
    pub fn assign_level_var(&mut self, id: LevelVarId, value: LevelRef<'a>) {
        let entry = &mut self.level_vars[id];
        assert!(entry.value.is_none());
        entry.value = Some(value);
    }

    #[track_caller]
    #[inline(always)]
    pub fn assign_term_var(&mut self, id: TermVarId, value: TermRef<'a>) {
        let entry = &mut self.term_vars[id];
        assert!(entry.value.is_none());
        entry.value = Some(value);
    }
}

