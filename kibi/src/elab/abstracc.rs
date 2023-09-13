use crate::tt::*;

use super::*;


impl<'me, 'out, 'a> Elab<'me, 'out, 'a> {
    pub fn abstracc(&self, t: Term<'a>, id: ScopeId) -> Term<'a> {
        self.abstracc_ex(t, id, 0)
    }

    pub fn abstracc_ex(&self, t: Term<'a>, id: ScopeId, offset: u32) -> Term<'a> {
        t.replace_ex(offset, self.alloc, &mut |at, offset, alloc| {
            if let Some(local) = at.try_local() {
                if local == id {
                    return Some(alloc.mkt_bound(BVar { offset }));
                }
            }

            if let Some(var) = at.try_ivar() {
                if let Some(value) = var.value(self) {
                    return Some(self.abstracc_ex(value, id, offset));
                }

                // elim ivar if `id` in scope.
                if var.scope(self) == id.some() {
                    // `(?n[id]: T) := (?m(id): (ty(id) -> t[id]))

                    // @temp: see if constant approx fixes this.
                    /*
                    let ty = self.term_vars[var].ty;
                    let m_ty = self.mk_binder(ty, id, true, lctx);

                    let m_scope = lctx.lookup(id).parent;
                    let m = self.new_term_var(m_ty, m_scope);

                    let val = self.alloc.mkt_apply(m, alloc.mkt_local(id));
                    unsafe { var.assign_core(val, self) }

                    let val = self.alloc.mkt_apply(m, alloc.mkt_bound(BVar(offset)));
                    return Some(val);
                }
                else {
                    debug_assert!(!lctx.scope_contains(self.term_vars[var].scope, id));
                    */
                }
            }

            at.replace_levels_flat(alloc, |l, _| {
                let new_l = self.instantiate_level_vars(l);
                (!new_l.ptr_eq(l)).then_some(new_l)
            })
        })
    }

    pub fn mk_binder(&self, val: Term<'a>, id: ScopeId, is_forall: bool) -> Term<'a> {
        let val = self.abstracc(val, id);

        // instantiate type after val, cause abstracc may
        // assign ivars (elim locals).
        let entry = self.lctx.lookup(id);
        let ty = self.instantiate_term_vars(entry.ty);

        if is_forall { self.alloc.mkt_forall(entry.binder_kind, entry.name, ty, val) }
        else         { self.alloc.mkt_lambda(entry.binder_kind, entry.name, ty, val) }
    }

    pub fn mk_binder_with_kind(&self, kind: BinderKind, val: Term<'a>, id: ScopeId, is_forall: bool) -> Term<'a> {
        let val = self.abstracc(val, id);

        // instantiate type after val, cause abstracc may
        // assign ivars (elim locals).
        let entry = self.lctx.lookup(id);
        let ty = self.instantiate_term_vars(entry.ty);

        if is_forall { self.alloc.mkt_forall(kind, entry.name, ty, val) }
        else         { self.alloc.mkt_lambda(kind, entry.name, ty, val) }
    }
}

