use sti::arena::Arena;
use sti::keyed::KVec;
use sti::hash::HashMap;

use crate::string_table::{Atom, atoms};
use crate::diagnostics::{Diagnostic, Diagnostics, DiagnosticSource, DiagnosticKind, TyCkError};
use crate::tt::*;
use crate::tt::inductive::InductiveInfo;
use crate::tt::tyck::TyCk;


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
    Pending(Option<symbol::Axiom<'a>>),
    Axiom(symbol::Axiom<'a>),
    Def(symbol::Def<'a>),
    IndAxiom(symbol::IndAxiom<'a>),
}


#[allow(non_upper_case_globals)]
impl SymbolId {
    pub const ROOT: SymbolId = SymbolId(0);

    pub const Nat: SymbolId = SymbolId(1);
    pub const Nat_zero: SymbolId = SymbolId(2);
    pub const Nat_succ: SymbolId = SymbolId(3);

    pub const Eq:        SymbolId = SymbolId(4);
    pub const Eq_refl:   SymbolId = SymbolId(5);
    pub const Eq_rec:    SymbolId = SymbolId(6);
    pub const Eq_nd_rec: SymbolId = SymbolId(7);
    pub const Eq_symm:   SymbolId = SymbolId(8);

    pub const Add:     SymbolId = SymbolId(9);
    pub const Add_add: SymbolId = SymbolId(10);

    pub const Unit:    SymbolId = SymbolId(11);
    pub const Unit_mk: SymbolId = SymbolId(12);

    pub const Bool:       SymbolId = SymbolId(13);
    pub const Bool_false: SymbolId = SymbolId(14);
    pub const Bool_true:  SymbolId = SymbolId(15);
    pub const ite:        SymbolId = SymbolId(16);

    pub const ax_sorry:   SymbolId = SymbolId(17);
    pub const ax_uninit:  SymbolId = SymbolId(18);
    pub const ax_unreach: SymbolId = SymbolId(19);
    pub const ax_error:   SymbolId = SymbolId(20);
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
    pub struct Axiom<'a> {
        pub num_levels: usize,
        pub ty: Term<'a>,
    }


    #[derive(Clone, Copy, Debug)]
    pub struct Def<'a> {
        pub kind: DefKind<'a>,
        pub num_levels: usize,
        pub ty:  Term<'a>,
        pub val: Term<'a>,
    }

    #[derive(Clone, Copy, Debug)]
    pub enum DefKind<'a> {
        Primary(DefKindPrimary<'a>),
        Aux(DefKindAux<'a>),
    }

    #[derive(Clone, Copy, Debug)]
    pub struct DefKindPrimary<'a> {
        pub aux_defs: &'a [SymbolId],
        pub num_local_vars: usize,
    }

    #[derive(Clone, Copy, Debug)]
    pub struct DefKindAux<'a> {
        pub parent: SymbolId,
        pub param_vids: Option<&'a [LocalVarId]>,
    }


    #[derive(Clone, Copy, Debug)]
    pub struct IndAxiom<'a> {
        pub kind: IndAxiomKind,
        pub info: &'a InductiveInfo<'a>,
        pub num_levels: usize,
        pub ty: Term<'a>,
        pub mutual_infos: &'a [InductiveInfo<'a>],
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

        env.predeclare(SymbolId::ROOT, atoms::Nat, SymbolId::Nat);
        env.predeclare(SymbolId::Nat, atoms::zero, SymbolId::Nat_zero);
        env.predeclare(SymbolId::Nat, atoms::succ, SymbolId::Nat_succ);

        env.predeclare(SymbolId::ROOT, atoms::Eq,     SymbolId::Eq);
        env.predeclare(SymbolId::Eq,   atoms::refl,    SymbolId::Eq_refl);
        env.predeclare(SymbolId::Eq,   atoms::rec,    SymbolId::Eq_rec);
        env.predeclare(SymbolId::Eq,   atoms::nd_rec, SymbolId::Eq_nd_rec);
        env.predeclare(SymbolId::Eq,   atoms::symm,   SymbolId::Eq_symm);

        env.predeclare(SymbolId::ROOT, atoms::Add, SymbolId::Add);
        env.predeclare(SymbolId::Add, atoms::add, SymbolId::Add_add);

        env.predeclare(SymbolId::ROOT, atoms::Unit, SymbolId::Unit);
        env.predeclare(SymbolId::Unit, atoms::mk, SymbolId::Unit_mk);

        env.predeclare(SymbolId::ROOT, atoms::Bool, SymbolId::Bool);
        env.predeclare(SymbolId::Bool, atoms::_false, SymbolId::Bool_false);
        env.predeclare(SymbolId::Bool, atoms::_true, SymbolId::Bool_true);
        env.predeclare(SymbolId::ROOT, atoms::ite, SymbolId::ite);

        env.predeclare(SymbolId::ROOT, atoms::ax_sorry, SymbolId::ax_sorry);
        env.predeclare(SymbolId::ROOT, atoms::ax_uninit, SymbolId::ax_uninit);
        env.predeclare(SymbolId::ROOT, atoms::ax_unreach, SymbolId::ax_unreach);
        env.predeclare(SymbolId::ROOT, atoms::ax_error, SymbolId::ax_error);

        return env
    }

    #[inline]
    fn predeclare(&mut self, parent: SymbolId, name: Atom, symbol: SymbolId) {
        let id = self.symbols.push(Symbol {
            parent,
            kind: SymbolKind::Predeclared,
            name,
            children: HashMap::new(),
        });
        assert_eq!(id, symbol);

        let none = self.symbols[parent].children.insert(name, symbol);
        assert!(none.is_none());
    }


    #[must_use]
    #[track_caller]
    pub fn new_symbol<'out>(&mut self, parent: SymbolId, name: Atom, kind: SymbolKind<'a>, alloc: &'out Arena, diagnostics: &mut Diagnostics<'out>) -> Option<SymbolId> {
        let mut predeclared = None;
        if let Some(symbol) = self.lookup(parent, name) {
            if matches!(self.symbols[symbol].kind, SymbolKind::Predeclared) {
                predeclared = Some(symbol);
            }
            // @todo: error.
            else { return None }
        }

        match &kind {
            SymbolKind::Root |
            SymbolKind::Predeclared => unreachable!(),

            SymbolKind::Pending(None) => (),

            SymbolKind::Pending(Some(it)) |
            SymbolKind::Axiom(it) => {
                self.check_is_type(it.ty, it.num_levels, alloc, diagnostics)?;
            }

            SymbolKind::Def(it) => {
                self.check_is_type(it.ty, it.num_levels, alloc, diagnostics)?;
                self.check_has_type(it.val, it.ty, it.num_levels, alloc, diagnostics)?;
            }

            SymbolKind::IndAxiom(it) => {
                self.check_is_type(it.ty, it.num_levels, alloc, diagnostics)?;
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

    #[must_use]
    #[track_caller]
    pub fn resolve_pending<'out>(&mut self, id: SymbolId, kind: SymbolKind<'a>, alloc: &'out Arena, diagnostics: &mut Diagnostics<'out>) -> Option<()> {
        match &kind {
            SymbolKind::Root |
            SymbolKind::Predeclared |
            SymbolKind::Pending(_) |
            SymbolKind::Axiom(_) => unreachable!(),

            SymbolKind::Def(it) => {
                self.check_is_type(it.ty, it.num_levels, alloc, diagnostics)?;
                self.check_has_type(it.val, it.ty, it.num_levels, alloc, diagnostics)?;
            }

            SymbolKind::IndAxiom(it) => {
                self.check_is_type(it.ty, it.num_levels, alloc, diagnostics)?;
            }
        }

        let symbol = &mut self.symbols[id];
        assert!(matches!(symbol.kind, SymbolKind::Pending(_)));
        symbol.kind = kind;
        return Some(());
    }

    #[track_caller]
    pub unsafe fn resolve_pending_unck(&mut self, id: SymbolId, kind: SymbolKind<'a>) {
        match &kind {
            SymbolKind::Root |
            SymbolKind::Predeclared |
            SymbolKind::Pending(_) |
            SymbolKind::Axiom(_) => unreachable!(),

            SymbolKind::Def(_) => {}
            SymbolKind::IndAxiom(_) => {}
        }

        let symbol = &mut self.symbols[id];
        assert!(matches!(symbol.kind, SymbolKind::Pending(_)));
        symbol.kind = kind;
    }

    pub fn reserve_id(&mut self) -> SymbolId {
        self.symbols.push(Symbol {
            parent: SymbolId::MAX,
            kind: SymbolKind::Pending(None),
            name: Atom::NULL,
            children: HashMap::new(),
        })
    }

    #[must_use]
    pub fn attach_id(&mut self, id: SymbolId, parent: SymbolId, name: Atom) -> Option<()> {
        if self.symbols[id].parent != SymbolId::MAX { panic!("id already attached"); }

        let p = &mut self.symbols[parent];
        // @speed: try_insert_new.
        if p.children.get(&name).is_some() {
            // @todo: error.
            return None;
        }
        p.children.insert(name, id);

        let s = &mut self.symbols[id];
        s.parent = parent;
        s.name = name;

        Some(())
    }


    #[must_use]
    pub fn validate_symbol<'out>(&mut self, id: SymbolId, alloc: &'out Arena, diagnostics: &mut Diagnostics<'out>) -> Option<()> {
        match &self.symbols[id].kind {
            SymbolKind::Root |
            SymbolKind::Predeclared => unreachable!(),

            SymbolKind::Pending(None) => (),

            SymbolKind::Pending(Some(it)) |
            SymbolKind::Axiom(it) => {
                self.check_is_type(it.ty, it.num_levels, alloc, diagnostics)?;
            }

            SymbolKind::Def(it) => {
                self.check_is_type(it.ty, it.num_levels, alloc, diagnostics)?;
                self.check_has_type(it.val, it.ty, it.num_levels, alloc, diagnostics)?;
            }

            SymbolKind::IndAxiom(it) => {
                self.check_is_type(it.ty, it.num_levels, alloc, diagnostics)?;
            }
        }
        return Some(());
    }

    #[must_use]
    fn check_is_type<'out>(&self, t: Term, num_levels: usize, alloc: &'out Arena, diagnostics: &mut Diagnostics<'out>) -> Option<()> {
        let temp = sti::arena_pool::ArenaPool::tls_get_temp();
        let mut lctx = LocalCtx::new();
        let mut tc = TyCk::new(self, &mut lctx, num_levels, &*temp);
        if let Err(e) = tc.check_is_type(t) {
            Self::report_tyck_error(e, &lctx, alloc, diagnostics);
            return None;
        }
        Some(())
    }

    #[must_use]
    fn check_has_type<'out>(&self, t: Term, ty: Term, num_levels: usize, alloc: &'out Arena, diagnostics: &mut Diagnostics<'out>) -> Option<()> {
        let temp = sti::arena_pool::ArenaPool::tls_get_temp();
        let mut lctx = LocalCtx::new();
        let mut tc = TyCk::new(self, &mut lctx, num_levels, &*temp);
        if let Err(e) = tc.check_has_type(t, ty) {
            Self::report_tyck_error(e, &lctx, alloc, diagnostics);
            return None;
        }
        Some(())
    }

    fn report_tyck_error<'out>(e: tyck::Error, lctx: &LocalCtx, alloc: &'out Arena, diagnostics: &mut Diagnostics<'out>) {
        let source = 
            if let Some(expr_id) = e.at.source().to_option() {
                DiagnosticSource::Expr(expr_id)
            }
            else { DiagnosticSource::Unknown };

        use tyck::ErrorKind as EK;
        let e = TyCkError {
            lctx: lctx.clone_in(alloc),
            err: tyck::Error {
                at: e.at.clone_in(alloc),
                kind: match e.kind {
                    EK::LooseBVar => EK::LooseBVar,
                    EK::LooseLocal => EK::LooseLocal,
                    EK::TermIVar => EK::TermIVar,
                    EK::GlobalNotReady => EK::GlobalNotReady,
                    EK::GlobalLevelMismatch => EK::GlobalLevelMismatch,
                    EK::TypeExpected { found } => EK::TypeExpected { found: found.clone_in(alloc) },
                    EK::TypeInvalid { found, expected } => EK::TypeInvalid { found: found.clone_in(alloc), expected: expected.clone_in(alloc) },
                    EK::LetValTypeInvalid { found } => EK::LetValTypeInvalid { found: found.clone_in(alloc) },
                    EK::AppArgTypeInvalid { found, expected } => EK::AppArgTypeInvalid { found: found.clone_in(alloc), expected: expected.clone_in(alloc) },
                    EK::LevelParamIndexInvalid => EK::LevelParamIndexInvalid,
                    EK::LevelIVar => EK::LevelIVar,
                },
            },
        };

        diagnostics.push(Diagnostic {
            source,
            kind: DiagnosticKind::TyCkError(e),
        });
    }
}

