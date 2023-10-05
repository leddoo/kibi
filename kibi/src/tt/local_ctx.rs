use sti::arena::Arena;
use sti::keyed::KVec;

use crate::string_table::Atom;

use super::term::*;


sti::define_key!(pub, u32, ScopeId, opt: OptScopeId);


#[derive(Debug)]
pub struct LocalCtx<'a> {
    pub scopes: KVec<ScopeId, Scope<'a>>,
    pub current: OptScopeId,
}

#[derive(Clone, Debug)]
pub struct Scope<'a> {
    pub parent: OptScopeId,
    pub name:  Atom,
    pub ty:    Term<'a>,
    pub kind:  ScopeKind<'a>,
}

#[derive(Clone, Copy, Debug)]
pub enum ScopeKind<'a> {
    Binder(BinderKind),
    Local(Term<'a>),
}

impl<'a> ScopeKind<'a> {
    #[track_caller]
    #[inline(always)]
    pub fn as_binder(self) -> BinderKind { if let ScopeKind::Binder(b) = self { b } else { unreachable!() } }

    #[track_caller]
    #[inline(always)]
    pub fn as_local(self) -> Term<'a> { if let ScopeKind::Local(v) = self { v } else { unreachable!() } }
}

#[derive(Clone)]
pub struct SavePoint {
    num_scopes: usize,
    current: OptScopeId,
}


impl<'a> LocalCtx<'a> {
    #[inline(always)]
    pub fn new() -> Self {
        Self {
            scopes: KVec::new(),
            current: None.into(),
        }
    }

    pub fn clear(&mut self) {
        self.scopes.inner_mut_unck().clear();
        self.current = None.into();
    }

    #[inline(always)]
    pub fn len(&self) -> usize {
        self.scopes.len()
    }


    #[track_caller]
    pub fn push(&mut self, name: Atom, ty: Term<'a>, kind: ScopeKind<'a>) -> ScopeId {
        assert!(ty.closed());
        if let ScopeKind::Local(v) = kind {
            assert!(v.closed());
        }

        let parent = self.current;
        let id = self.scopes.push(Scope { parent, name, ty, kind });
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

    #[track_caller]
    #[inline(always)]
    pub fn lookup_mut(&mut self, id: ScopeId) -> &mut Scope<'a> {
        &mut self.scopes[id]
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

    pub fn scope_common_prefix(&self, a: OptScopeId, b: OptScopeId) -> OptScopeId {
        // if either is root, result is root.
        let Some(mut a) = a.to_option() else { return a };
        let Some(mut b) = b.to_option() else { return b };

        loop {
            if a < b {
                let new_b = self.scopes[b].parent;
                let Some(new_b) = new_b.to_option() else { return new_b };
                b = new_b;
            }
            else {
                let new_a = self.scopes[a].parent;
                let Some(new_a) = new_a.to_option() else { return new_a };
                a = new_a;
            }

            if a == b {
                return a.some();
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

    pub fn all_locals_in_scope(&self, t: Term<'a>, scope: OptScopeId) -> bool {
        t.find(|at, _| {
            let local = at.try_local()?;
            return Some(!self.local_in_scope(local, scope));
        }).is_none()
    }


    #[track_caller]
    #[inline(always)]
    pub fn abstract_forall(&self, ret: Term<'a>, id: ScopeId, source: TermSource, alloc: &'a Arena) -> Term<'a> {
        let entry = self.lookup(id);
        let ret = ret.abstracc(id, alloc);
        let kind = entry.kind.as_binder();
        alloc.mkt_forall(kind, entry.name, entry.ty, ret, source)
    }

    #[track_caller]
    #[inline(always)]
    pub fn abstract_lambda(&self, value: Term<'a>, id: ScopeId, source: TermSource, alloc: &'a Arena) -> Term<'a> {
        let entry = self.lookup(id);
        let value = value.abstracc(id, alloc);
        let kind = entry.kind.as_binder();
        alloc.mkt_lambda(kind, entry.name, entry.ty, value, source)
    }

    #[track_caller]
    #[inline(always)]
    pub fn abstract_let(&self, body: Term<'a>, id: ScopeId, vid: OptLocalVarId, discard_unused: bool, source: TermSource, alloc: &'a Arena) -> Term<'a> {
        if discard_unused && body.closed() {
            return body;
        }
        let entry = self.lookup(id);
        let body = body.abstracc(id, alloc);
        alloc.mkt_let(entry.name, vid, entry.ty, entry.kind.as_local(), body, source)
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
        self.scopes.inner_mut_unck().truncate(save.num_scopes);
        self.current = save.current;
    }


    pub fn clone_in<'out>(&self, alloc: &'out Arena) -> LocalCtx<'out> {
        let mut scopes = KVec::with_cap(self.scopes.len());
        for (_, scope) in self.scopes.iter() {
            scopes.push(Scope {
                parent: scope.parent,
                name:   scope.name,
                ty:     scope.ty.clone_in(alloc),
                kind: match scope.kind {
                    ScopeKind::Binder(it) => ScopeKind::Binder(it),
                    ScopeKind::Local(it)  => ScopeKind::Local(it.clone_in(alloc)),
                },
            });
        }
        LocalCtx {
            scopes,
            current: self.current,
        }
    }
}

