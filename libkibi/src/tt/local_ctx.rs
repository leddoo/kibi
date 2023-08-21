use sti::arena::Arena;
use sti::vec::Vec;
use sti::keyed::Key;

use super::syntax::*;


// @todo: debug version with (global) generational indices.
sti::define_key!(u32, pub LocalId);


#[derive(Clone)]
pub struct LocalCtx<'a> {
    alloc: &'a Arena,
    entries: Vec<Entry<'a>>,
}

#[derive(Clone)]
pub struct Entry<'a> {
    pub ty:    TermRef<'a>,
    pub value: Option<TermRef<'a>>,
}

#[derive(Clone)]
pub struct SavePoint(usize);


impl<'a> LocalCtx<'a> {
    #[inline(always)]
    pub fn new(alloc: &'a Arena) -> Self {
        Self { alloc, entries: Vec::new() }
    }


    #[track_caller]
    pub fn extend(&mut self, ty: TermRef<'a>, value: Option<TermRef<'a>>) -> LocalId {
        assert!(ty.closed());
        if let Some(v) = value { assert!(v.closed()); }

        let id = LocalId::from_usize(self.entries.len()).unwrap();
        self.entries.push(Entry { ty, value });
        id
    }

    #[track_caller]
    #[inline(always)]
    pub fn lookup(&self, id: LocalId) -> &Entry<'a> {
        &self.entries[id.usize()]
    }


    #[track_caller]
    #[inline(always)]
    pub fn abstract_forall(&self, ret: TermRef<'a>, id: LocalId) -> TermRef<'a> {
        // @temp: binder name.
        let entry = self.lookup(id);
        let ret = ret.abstracc(id, self.alloc);
        self.alloc.mkt_forall(0, entry.ty, ret)
    }

    #[track_caller]
    #[inline(always)]
    pub fn abstract_lambda(&self, value: TermRef<'a>, id: LocalId) -> TermRef<'a> {
        // @temp: binder name.
        let entry = self.lookup(id);
        let value = value.abstracc(id, self.alloc);
        self.alloc.mkt_lambda(0, entry.ty, value)
    }


    #[inline(always)]
    pub fn save(&self) -> SavePoint {
        SavePoint(self.entries.len())
    }

    #[track_caller]
    #[inline(always)]
    pub fn restore(&mut self, save: SavePoint) {
        assert!(save.0 <= self.entries.len());
        self.entries.truncate(save.0);
    }
}

