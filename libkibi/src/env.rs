use sti::vec::Vec;
use sti::keyed::KVec;

use crate::tt::*;


pub struct Env<'a> {
    symbols: KVec<SymbolId, Symbol<'a>>,
}


sti::define_key!(u32, pub SymbolId, opt: OptSymbolId);

impl SymbolId { pub const ROOT: SymbolId = SymbolId(0); }


#[derive(Debug)]
pub struct Symbol<'a> {
    pub parent: SymbolId,

    pub kind: SymbolKind<'a>,
    pub name: &'a str,

    pub children: Vec<(&'a str, SymbolId)>,
}

#[derive(Debug)]
pub enum SymbolKind<'a> {
    Root,
    BuiltIn(symbol::BuiltIn),
    Def(symbol::Def<'a>),
}


pub mod symbol {
    use super::*;

    #[derive(Clone, Copy, Debug, PartialEq)]
    pub enum BuiltIn {
        Nat,
        NatZero,
        NatSucc,
        NatRec,
        Eq,
        EqRefl,
        EqRec,
    }

    #[derive(Clone, Copy, Debug)]
    pub struct Def<'a> {
        pub num_levels: u32,
        pub ty:  TermRef<'a>,
        pub val: TermRef<'a>,
    }
}



impl<'a> Env<'a> {
    pub fn new() -> Env<'static> {
        let mut symbols = KVec::new();
        let root = symbols.push(Symbol {
            parent: SymbolId::ROOT,
            kind: SymbolKind::Root,
            name: "",
            children: Vec::new(),
        });
        assert_eq!(root, SymbolId::ROOT);

        let mut env = Env {
            symbols,
        };


        // @temp: how to handle built-ins, if we have any?
        {
            let nat = env.new_symbol(SymbolId::ROOT, "Nat",
                SymbolKind::BuiltIn(symbol::BuiltIn::Nat)).unwrap();

            env.new_symbol(nat, "zero",
                SymbolKind::BuiltIn(symbol::BuiltIn::NatZero)).unwrap();

            env.new_symbol(nat, "succ",
                SymbolKind::BuiltIn(symbol::BuiltIn::NatSucc)).unwrap();

            env.new_symbol(nat, "rec",
                SymbolKind::BuiltIn(symbol::BuiltIn::NatRec)).unwrap();


            let eq = env.new_symbol(SymbolId::ROOT, "Eq",
                SymbolKind::BuiltIn(symbol::BuiltIn::Eq)).unwrap();

            env.new_symbol(eq, "refl",
                SymbolKind::BuiltIn(symbol::BuiltIn::EqRefl)).unwrap();

            env.new_symbol(eq, "rec",
                SymbolKind::BuiltIn(symbol::BuiltIn::EqRec)).unwrap();
        }

        return env;
    }


    #[inline(always)]
    pub fn new_symbol(&mut self, parent: SymbolId, name: &'a str, kind: SymbolKind<'a>) -> Option<SymbolId> {
        if self.lookup(parent, name).is_some() {
            return None;
        }

        let symbol = self.symbols.next_key();

        let id = self.symbols.push(Symbol {
            parent,
            kind,
            name,
            children: Vec::new(),
        });
        debug_assert_eq!(id, symbol);

        self.symbols[parent].children.push((name, symbol));

        return Some(symbol);
    }

    #[inline(always)]
    pub fn symbol(&self, id: SymbolId) -> &Symbol<'a> {
        &self.symbols[id]
    }


    pub fn lookup(&self, parent: SymbolId, name: &str) -> Option<SymbolId> {
        let p = &self.symbols[parent];
        for (child_name, child) in p.children.iter().copied() {
            if name == child_name {
                return Some(child);
            }
        }
        return None;
    }
}

