use sti::arena::Arena;
use sti::keyed::{KVec, KRange};

use super::syntax::*;
use super::local_ctx::{LocalCtx, OptScopeId};


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
    pub unsafe fn assign_level(&mut self, id: LevelVarId, value: LevelRef<'a>) {
        let entry = &mut self.level_vars[id];
        assert!(entry.value.is_none());
        entry.value = Some(value);
    }

    pub fn instantiate_level(&self, l: LevelRef<'a>) -> LevelRef<'a> {
        l.replace(self.alloc, |at, _| {
            if let LevelKind::IVar(id) = at.kind {
                if let Some(value) = self.level_value(id) {
                    return Some(self.instantiate_level(value));
                }
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
    pub unsafe fn assign_term(&mut self, id: TermVarId, value: TermRef<'a>) {
        assert!(value.closed());

        let entry = &mut self.term_vars[id];
        assert!(entry.value.is_none());
        entry.value = Some(value);
    }

    pub fn instantiate_term(&self, t: TermRef<'a>) -> TermRef<'a> {
        t.replace(self.alloc, |at, _, alloc| {
            if let TermKind::IVar(id) = at.kind {
                if let Some(value) = self.term_vars[id].value {
                    return Some(self.instantiate_term(value));
                }
            }

            at.replace_levels_flat(alloc, |l, _| {
                let new_l = self.instantiate_level(l);
                (!new_l.ptr_eq(l)).then_some(new_l)
            })
        })
    }

    // @cleanup: put these in `elab/abstracc.rs`
    // and ig instantiate goes into `elab/instantiate.rs`.
    // ig then there's no reason to keep this struct around.
    // esp cause most logic just doesn't live in here.
    // it's not a thing!

    pub fn abstracc(&mut self, t: TermRef<'a>, id: ScopeId, lctx: &LocalCtx<'a>) -> TermRef<'a> {
        self.abstracc_ex(t, id, 0, lctx)
    }

    pub fn abstracc_ex(&mut self, t: TermRef<'a>, id: ScopeId, offset: u32, lctx: &LocalCtx<'a>) -> TermRef<'a> {
        t.replace_ex(offset, self.alloc, &mut |at, offset, alloc| {
            if let TermKind::Local(l) = at.kind {
                if l == id {
                    return Some(alloc.mkt_bound(BVar(offset)));
                }
            }

            if let TermKind::IVar(var) = at.kind {
                if let Some(value) = self.term_vars[var].value {
                    return Some(self.abstracc_ex(value, id, offset, lctx));
                }

                // elim ivar if `id` in scope.
                if self.term_vars[var].scope == id.some() {
                    // `(?n[id]: T) := (?m(id): (ty(id) -> t[id]))

                    // @temp: see if constant approx fixes this.
                    /*
                    let ty = self.term_vars[var].ty;
                    let m_ty = self.mk_binder(ty, id, true, lctx);

                    let m_scope = lctx.lookup(id).parent;
                    let m = self.new_term_var(m_ty, m_scope);

                    let val = self.alloc.mkt_apply(m, alloc.mkt_local(id));
                    unsafe { self.assign_term(var, val) }

                    let val = self.alloc.mkt_apply(m, alloc.mkt_bound(BVar(offset)));
                    return Some(val);
                }
                else {
                    debug_assert!(!lctx.scope_contains(self.term_vars[var].scope, id));
                    */
                }
            }

            at.replace_levels_flat(alloc, |l, _| {
                let new_l = self.instantiate_level(l);
                (!new_l.ptr_eq(l)).then_some(new_l)
            })
        })
    }

    pub fn mk_binder(&mut self, val: TermRef<'a>, id: ScopeId, is_forall: bool, lctx: &LocalCtx<'a>) -> TermRef<'a> {
        let val = self.abstracc(val, id, lctx);

        // instantiate type after val, cause abstracc may
        // assign ivars (elim locals).
        let ty = self.instantiate_term(lctx.lookup(id).ty);

        // @temp: name.
        if is_forall { self.alloc.mkt_forall(0, ty, val) }
        else         { self.alloc.mkt_lambda(0, ty, val) }
    }
}

