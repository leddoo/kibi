use sti::arena::Arena;
use sti::keyed::KVec;

use crate::string_table::Atom;

use super::syntax::*;


// @todo: debug version with (global) generational indices.
sti::define_key!(u32, pub ScopeId, opt: pub OptScopeId);


pub struct LocalCtx<'a> {
    alloc: &'a Arena,

    scopes: KVec<ScopeId, Scope<'a>>,
    pub current: OptScopeId,
}

pub struct Scope<'a> {
    pub parent: OptScopeId,
    pub name:   Atom,
    pub ty:    TermRef<'a>,
    pub value: Option<TermRef<'a>>,
}

#[derive(Clone)]
pub struct SavePoint {
    num_scopes: usize,
    current: OptScopeId,
}


impl<'a> LocalCtx<'a> {
    #[inline(always)]
    pub fn new(alloc: &'a Arena) -> Self {
        Self {
            alloc,
            scopes: KVec::new(),
            current: None.into(),
        }
    }


    #[track_caller]
    pub fn push(&mut self, name: Atom, ty: TermRef<'a>, value: Option<TermRef<'a>>) -> ScopeId {
        assert!(ty.closed());
        if let Some(v) = value { assert!(v.closed()); }

        let parent = self.current;
        let id = self.scopes.push(Scope { parent, name, ty, value });
        self.current = id.some();
        id
    }

    #[track_caller]
    #[inline(always)]
    pub fn pop(&mut self, id: ScopeId) {
        assert_eq!(self.current, id.some());
        self.current = self.scopes[id].parent;
    }


    #[inline(always)]
    pub fn current(&self) -> OptScopeId {
        self.current
    }

    #[track_caller]
    #[inline(always)]
    pub fn lookup(&self, id: ScopeId) -> &Scope<'a> {
        &self.scopes[id]
    }


    pub fn scope_is_prefix(&self, prefix: OptScopeId, of: OptScopeId) -> bool {
        let mut curr = of;
        loop {
            if curr == prefix {
                return true;
            }

            if let Some(at) = curr.to_option() {
                curr = self.scopes[at].parent;
            }
            else {
                return false;
            }
        }
    }

    pub fn local_in_scope(&self, local: ScopeId, scope: OptScopeId) -> bool {
        let mut curr = scope;
        while let Some(at) = curr.to_option() {
            if at == local {
                return true;
            }
            curr = self.scopes[at].parent;
        }
        return false;
    }

    pub fn all_locals_in_scope(&self, t: TermRef<'a>, scope: OptScopeId) -> bool {
        t.find(|at, _| {
            if let TermKind::Local(id) = at.kind {
                return Some(!self.local_in_scope(id, scope));
            }
            None
        }).is_none()
    }


    #[track_caller]
    #[inline(always)]
    pub fn abstract_forall(&self, ret: TermRef<'a>, id: ScopeId) -> TermRef<'a> {
        let entry = self.lookup(id);
        let ret = ret.abstracc(id, self.alloc);
        self.alloc.mkt_forall(entry.name, entry.ty, ret)
    }

    #[track_caller]
    #[inline(always)]
    pub fn abstract_lambda(&self, value: TermRef<'a>, id: ScopeId) -> TermRef<'a> {
        let entry = self.lookup(id);
        let value = value.abstracc(id, self.alloc);
        self.alloc.mkt_lambda(entry.name, entry.ty, value)
    }


    #[inline(always)]
    pub fn save(&self) -> SavePoint {
        SavePoint {
            num_scopes: self.scopes.len(),
            current:    self.current,
        }
    }

    #[track_caller]
    #[inline(always)]
    pub fn restore(&mut self, save: SavePoint) {
        assert!(save.num_scopes <= self.scopes.len());
        // @temp: sti kvec truncate.
        unsafe { self.scopes.inner_mut().truncate(save.num_scopes) }
        self.current = save.current;
    }
}

