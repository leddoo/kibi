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
    pub own_ns:    OptNamespaceId,

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

    #[derive(Debug)]
    pub enum BuiltIn {
        Nat,
        NatZero,
        NatSucc,
        NatRec,
    }

    #[derive(Debug)]
    pub struct Def<'a> {
        pub num_levels: u32,
        pub ty:  TermRef<'a>,
        pub val: TermRef<'a>,
    }
}



sti::define_key!(u32, pub NamespaceId, opt: OptNamespaceId);

pub struct Namespace<'a> {
    symbol: OptSymbolId,
    entries: Vec<NsEntry<'a>>,
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

    pub fn create_nat(&mut self) -> SymbolId {
        let root_ns = NamespaceId::ROOT;
        let nat_ns = self.namespaces.next_key();

        let nat = self.symbols.push(Symbol {
            parent_ns: root_ns,
            own_ns: nat_ns.some(),
            name: "Nat",
            kind: SymbolKind::BuiltIn(symbol::BuiltIn::Nat),
        });

        let nat_zero = self.symbols.push(Symbol {
            parent_ns: nat_ns,
            own_ns: None.into(),
            name: "zero",
            kind: SymbolKind::BuiltIn(symbol::BuiltIn::NatZero),
        });

        let nat_succ = self.symbols.push(Symbol {
            parent_ns: nat_ns,
            own_ns: None.into(),
            name: "succ",
            kind: SymbolKind::BuiltIn(symbol::BuiltIn::NatSucc),
        });

        let nat_rec = self.symbols.push(Symbol {
            parent_ns: nat_ns,
            own_ns: None.into(),
            name: "rec",
            kind: SymbolKind::BuiltIn(symbol::BuiltIn::NatRec),
        });

        let mut entries = Vec::new();
        entries.push(NsEntry {
            name: "Self",
            symbol: nat,
        });
        entries.push(NsEntry {
            name: "zero",
            symbol: nat_zero,
        });
        entries.push(NsEntry {
            name: "succ",
            symbol: nat_succ,
        });
        entries.push(NsEntry {
            name: "rec",
            symbol: nat_rec,
        });

        let ns = self.namespaces.push(Namespace {
            symbol: nat.some(),
            entries,
        });
        assert_eq!(ns, nat_ns);

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

