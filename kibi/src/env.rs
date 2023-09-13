use sti::keyed::KVec;
use sti::hash::HashMap;

use crate::string_table::{Atom, atoms};
use crate::tt::*;
use crate::tt::inductive::InductiveInfo;


pub struct Env<'a> {
    symbols: KVec<SymbolId, Symbol<'a>>,
}


sti::define_key!(pub, u32, SymbolId, opt: OptSymbolId);


#[derive(Debug)]
pub struct Symbol<'a> {
    pub parent: SymbolId,

    pub kind: SymbolKind<'a>,
    pub name: Atom,

    pub children: HashMap<Atom, SymbolId>,
}

#[derive(Debug)]
pub enum SymbolKind<'a> {
    Root,
    Predeclared,
    Pending,
    IndAxiom(symbol::IndAxiom<'a>),
    Def(symbol::Def<'a>),
}


impl SymbolId {
    pub const ROOT: SymbolId = SymbolId(0);

    pub const NAT: SymbolId = SymbolId(1);
    pub const NAT_ZERO: SymbolId = SymbolId(2);
    pub const NAT_SUCC: SymbolId = SymbolId(3);

    pub const EQ: SymbolId = SymbolId(4);
}


pub mod symbol {
    use super::*;

    #[derive(Clone, Copy, Debug, PartialEq)]
    pub enum IndAxiomKind {
        TypeFormer,
        Constructor(u32),
        Eliminator,
    }

    #[derive(Clone, Copy, Debug)]
    pub struct IndAxiom<'a> {
        pub kind: IndAxiomKind,
        pub info: &'a InductiveInfo<'a>,
        pub num_levels: u32,
        pub ty: Term<'a>,
        pub mutual_infos: &'a [InductiveInfo<'a>],
    }

    #[derive(Clone, Copy, Debug)]
    pub struct Def<'a> {
        pub num_levels: u32,
        pub ty:  Term<'a>,
        pub val: Option<Term<'a>>,
    }
}



impl<'a> Env<'a> {
    pub fn new() -> Env<'static> {
        let mut symbols = KVec::new();
        let root = symbols.push(Symbol {
            parent: SymbolId::ROOT,
            kind: SymbolKind::Root,
            name: Atom::NULL,
            children: HashMap::new(),
        });
        assert_eq!(root, SymbolId::ROOT);


        let nat = symbols.push(Symbol {
            parent: SymbolId::ROOT,
            kind: SymbolKind::Predeclared,
            name: atoms::Nat,
            children: HashMap::new(),
        });
        symbols[SymbolId::ROOT].children.insert(atoms::Nat, nat);
        assert_eq!(nat, SymbolId::NAT);

        let nat_zero = symbols.push(Symbol {
            parent: SymbolId::NAT,
            kind: SymbolKind::Predeclared,
            name: atoms::zero,
            children: HashMap::new(),
        });
        symbols[SymbolId::NAT].children.insert(atoms::zero, nat_zero);
        assert_eq!(nat_zero, SymbolId::NAT_ZERO);

        let nat_succ = symbols.push(Symbol {
            parent: SymbolId::NAT,
            kind: SymbolKind::Predeclared,
            name: atoms::succ,
            children: HashMap::new(),
        });
        symbols[SymbolId::NAT].children.insert(atoms::succ, nat_succ);
        assert_eq!(nat_succ, SymbolId::NAT_SUCC);


        let eq = symbols.push(Symbol {
            parent: SymbolId::ROOT,
            kind: SymbolKind::Predeclared,
            name: atoms::Eq,
            children: HashMap::new(),
        });
        symbols[SymbolId::ROOT].children.insert(atoms::Eq, eq);
        assert_eq!(eq, SymbolId::EQ);


        return Env { symbols };
    }


    #[inline(always)]
    pub fn new_symbol(&mut self, parent: SymbolId, name: Atom, kind: SymbolKind<'a>) -> Option<SymbolId> {
        let mut predeclared = None;
        if let Some(symbol) = self.lookup(parent, name) {
            if matches!(self.symbols[symbol].kind, SymbolKind::Predeclared) {
                predeclared = Some(symbol);
            }
            else { return None }
        }

        match &kind {
            SymbolKind::Root |
            SymbolKind::Predeclared => unreachable!(),

            SymbolKind::Pending => (),

            SymbolKind::IndAxiom(it) => {
                assert!(it.ty.closed_no_local_no_ivar());
            }

            SymbolKind::Def(it) => {
                assert!(it.ty.closed_no_local_no_ivar());
                if let Some(val) = it.val {
                    assert!(val.closed_no_local_no_ivar());
                }
            }
        }

        if let Some(symbol) = predeclared {
            self.symbols[symbol].kind = kind;
            return Some(symbol);
        }
        else {
            let id = self.symbols.push(Symbol {
                parent,
                kind,
                name,
                children: HashMap::new(),
            });

            self.symbols[parent].children.insert(name, id);

            return Some(id);
        }
    }

    #[inline(always)]
    pub fn symbol(&self, id: SymbolId) -> &Symbol<'a> {
        &self.symbols[id]
    }

    pub fn lookup(&self, parent: SymbolId, name: Atom) -> Option<SymbolId> {
        let p = &self.symbols[parent];
        p.children.get(&name).copied()
    }

    pub fn resolve_pending(&mut self, id: SymbolId, kind: SymbolKind<'a>) {
        match &kind {
            SymbolKind::Root |
            SymbolKind::Predeclared |
            SymbolKind::Pending => unreachable!(),

            SymbolKind::IndAxiom(it) => {
                assert!(it.ty.closed_no_local_no_ivar());
            }

            SymbolKind::Def(it) => {
                assert!(it.ty.closed_no_local_no_ivar());
                if let Some(val) = it.val {
                    assert!(val.closed_no_local_no_ivar());
                }
            }
        }

        let symbol = &mut self.symbols[id];
        assert!(matches!(symbol.kind, SymbolKind::Pending));
        symbol.kind = kind;
    }
}

