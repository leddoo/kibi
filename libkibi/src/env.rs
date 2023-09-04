use sti::keyed::KVec;
use sti::hash::HashMap;

use crate::string_table::{Atom, atoms};
use crate::tt::*;
use crate::tt::inductive::InductiveInfo;


pub struct Env<'a> {
    symbols: KVec<SymbolId, Symbol<'a>>,
}


sti::define_key!(u32, pub SymbolId, opt: OptSymbolId);

impl SymbolId { pub const ROOT: SymbolId = SymbolId(0); }


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
    Pending,
    BuiltIn(symbol::BuiltIn),
    IndAxiom(symbol::IndAxiom<'a>),
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

    #[derive(Clone, Copy, Debug, PartialEq)]
    pub enum IndAxiomKind {
        TypeFormer,
        Constructor,
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

        let mut env = Env { symbols };


        // @temp: how to handle built-ins, if we have any?
        {
            let nat = env.new_symbol(SymbolId::ROOT, atoms::Nat,
                SymbolKind::BuiltIn(symbol::BuiltIn::Nat)).unwrap();

            env.new_symbol(nat, atoms::zero,
                SymbolKind::BuiltIn(symbol::BuiltIn::NatZero)).unwrap();

            env.new_symbol(nat, atoms::succ,
                SymbolKind::BuiltIn(symbol::BuiltIn::NatSucc)).unwrap();

            env.new_symbol(nat, atoms::rec,
                SymbolKind::BuiltIn(symbol::BuiltIn::NatRec)).unwrap();


            let eq = env.new_symbol(SymbolId::ROOT, atoms::Eq,
                SymbolKind::BuiltIn(symbol::BuiltIn::Eq)).unwrap();

            env.new_symbol(eq, atoms::refl,
                SymbolKind::BuiltIn(symbol::BuiltIn::EqRefl)).unwrap();

            env.new_symbol(eq, atoms::rec,
                SymbolKind::BuiltIn(symbol::BuiltIn::EqRec)).unwrap();
        }

        return env;
    }


    #[inline(always)]
    pub fn new_symbol(&mut self, parent: SymbolId, name: Atom, kind: SymbolKind<'a>) -> Option<SymbolId> {
        if self.lookup(parent, name).is_some() {
            return None;
        }

        match &kind {
            SymbolKind::Root => unreachable!(),
            SymbolKind::BuiltIn(_) => (),
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

        let symbol = self.symbols.next_key();

        let id = self.symbols.push(Symbol {
            parent,
            kind,
            name,
            children: HashMap::new(),
        });
        debug_assert_eq!(id, symbol);

        self.symbols[parent].children.insert(name, symbol);

        return Some(symbol);
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
            SymbolKind::BuiltIn(_) |
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

