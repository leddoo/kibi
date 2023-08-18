use sti::vec::Vec;
use sti::keyed::KVec;

use crate::tt::*;


pub struct Env<'a> {
    symbols: KVec<SymbolId, Symbol<'a>>,
    namespaces: KVec<NamespaceId, Namespace<'a>>,
}


sti::define_key!(u32, pub SymbolId, opt: OptSymbolId);

#[derive(Debug)]
pub struct Symbol<'a> {
    pub parent_ns: NamespaceId,
    pub own_ns:    NamespaceId,

    pub kind: SymbolKind<'a>,
    pub name: &'a str,
}

#[derive(Debug)]
pub enum SymbolKind<'a> {
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
    }

    #[derive(Clone, Copy, Debug)]
    pub struct Def<'a> {
        pub num_levels: u32,
        pub ty:  TermRef<'a>,
        pub val: TermRef<'a>,
    }
}



sti::define_key!(u32, pub NamespaceId, opt: OptNamespaceId);

pub struct Namespace<'a> {
    pub symbol: OptSymbolId,
    pub entries: Vec<NsEntry<'a>>,
}

pub struct NsEntry<'a> {
    pub name:  &'a str,
    pub symbol: SymbolId,
}


impl NamespaceId { pub const ROOT: NamespaceId = NamespaceId(0); }



impl<'a> Env<'a> {
    pub fn new() -> Env<'static> {
        let mut namespaces = KVec::new();
        let root_ns = namespaces.push(Namespace {
            symbol: None.into(),
            entries: Vec::new(),
        });
        assert_eq!(root_ns, NamespaceId::ROOT);

        Env {
            symbols: KVec::new(),
            namespaces,
        }
    }

    #[inline(always)]
    pub fn new_symbol(&mut self, ns: NamespaceId, name: &'a str, kind: SymbolKind<'a>) -> Option<SymbolId> {
        if self.lookup(ns, name).is_some() {
            return None;
        }

        let symbol = self.symbols.next_key();
        let own_ns = self.new_namespace(symbol.some());

        let id = self.symbols.push(Symbol {
            parent_ns: ns,
            own_ns,
            name,
            kind,
        });
        debug_assert_eq!(id, symbol);

        self.namespaces[ns].entries.push(NsEntry { name, symbol });

        return Some(symbol);
    }

    #[inline(always)]
    pub fn new_namespace(&mut self, symbol: OptSymbolId) -> NamespaceId {
        self.namespaces.push(Namespace {
            symbol,
            entries: Vec::new(),
        })
    }


    pub fn create_nat(&mut self) -> SymbolId {
        let nat = self.new_symbol(NamespaceId::ROOT, "Nat",
            SymbolKind::BuiltIn(symbol::BuiltIn::Nat)).unwrap();

        let nat_ns = self.symbols[nat].own_ns;

        self.new_symbol(nat_ns, "zero",
            SymbolKind::BuiltIn(symbol::BuiltIn::NatZero)).unwrap();

        self.new_symbol(nat_ns, "succ",
            SymbolKind::BuiltIn(symbol::BuiltIn::NatSucc)).unwrap();

        self.new_symbol(nat_ns, "rec",
            SymbolKind::BuiltIn(symbol::BuiltIn::NatRec)).unwrap();

        return nat;
    }

    pub fn create_initial(&mut self, nat: SymbolId) -> NamespaceId {
        let mut entries = Vec::new();
        entries.push(NsEntry {
            name: "Nat",
            symbol: nat,
        });
        self.namespaces.push(Namespace {
            symbol: None.into(),
            entries,
        })
    }


    #[inline(always)]
    pub fn symbol(&self, id: SymbolId) -> &Symbol<'a> {
        &self.symbols[id]
    }

    #[inline(always)]
    pub fn namespace(&self, id: NamespaceId) -> &Namespace<'a> {
        &self.namespaces[id]
    }

    pub fn lookup(&self, ns: NamespaceId, name: &str) -> Option<&NsEntry<'a>> {
        let ns = &self.namespaces[ns];
        for entry in &ns.entries {
            if entry.name == name {
                return Some(entry);
            }
        }
        return None;
    }
}

