use sti::rc::Rc;
use sti::vec::Vec;
use sti::keyed::Key;

use super::term::*;


// @todo: debug version with (global) generational indices.
sti::define_key!(u32, pub LocalId);


#[derive(Clone)]
pub struct LocalCtx<'a> {
    entries: Rc<Vec<Entry<'a>>>,
}

#[derive(Clone)]
pub struct Entry<'a> {
    pub ty:    TermRef<'a>,
    pub value: TermRef<'a>,
}

#[derive(Clone, Copy)]
pub struct SavePoint(usize);


impl<'a> LocalCtx<'a> {
    #[inline(always)]
    pub fn new() -> Self {
        Self { entries: Rc::new(Vec::new()) }
    }


    pub fn extend(&mut self, ty: TermRef<'a>, value: TermRef<'a>) -> LocalId {
        // @temp
        if self.entries.try_mut().is_none() {
            println!("clone lctx");
        }

        let entries = self.entries.make_mut();
        let id = LocalId::from_usize(entries.len()).unwrap();
        entries.push(Entry { ty, value });
        id
    }

    #[track_caller]
    #[inline(always)]
    pub fn lookup(&self, id: LocalId) -> &Entry {
        &self.entries[id.usize()]
    }


    #[inline(always)]
    pub fn save(&self) -> SavePoint {
        SavePoint(self.entries.len())
    }

    #[track_caller]
    pub fn restore(&mut self, save: SavePoint) {
        // @temp
        if self.entries.try_mut().is_none() {
            println!("clone lctx");
        }

        let entries = self.entries.make_mut();
        assert!(save.0 <= entries.len());
        entries.truncate(save.0);
    }
}

