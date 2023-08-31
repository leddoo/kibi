use sti::arena::Arena;
use sti::vec::Vec;
use sti::keyed::KVec;

use crate::string_table::{StringTable, Atom};
use crate::error::*;
use crate::ast::SourceRange;
use crate::tt::{ScopeId, LocalCtx};
use crate::env::*;


pub struct Elab<'me, 'err, 'a> {
    pub alloc: &'a Arena,
    pub strings: &'me StringTable<'a>,
    pub errors: &'me ErrorCtx<'err>,
    pub env: &'me mut Env<'a>,

    root_symbol: SymbolId,

    level_params: Vec<Atom>,

    lctx: LocalCtx<'a>,
    locals: Vec<(Atom, ScopeId)>,

    level_vars: KVec<LevelVarId, ivars::LevelVar<'a>>,
    term_vars:  KVec<TermVarId,  ivars::TermVar<'a>>,
}


mod ivars;
mod abstracc;
mod instantiate;
mod whnf;
mod infer_type;
mod def_eq_level;
mod def_eq_term;
mod abstracc_eq;
mod elab_symbol;
mod elab_level;
mod elab_expr;
mod elab_binders;
mod elab_elim;
mod elab_def;
mod elab_inductive;


pub use ivars::{LevelVarId, TermVarId};


impl<'me, 'err, 'a> Elab<'me, 'err, 'a> {
    pub fn new(env: &'me mut Env<'a>, root_symbol: SymbolId, errors: &'me ErrorCtx<'err>, strings: &'me StringTable<'a>, alloc: &'a Arena) -> Self {
        Self {
            alloc,
            strings,
            errors,
            env,
            root_symbol,
            lctx: LocalCtx::new(alloc),
            locals: Vec::new(),
            level_params: Vec::new(),
            level_vars: KVec::new(),
            term_vars: KVec::new(),
        }
    }

    fn error<F: FnOnce(&'err Arena) -> ElabError<'err>>(&self, source: SourceRange, f: F) {
        self.errors.with(|errors| {
            errors.report(Error { source, kind: ErrorKind::Elab(f(errors.alloc)) });
        });
    }

    // @mega@temp below this line.

    // @temp: `Compiler` rework.
    pub fn check_no_unassigned_variables(&self) -> Option<()> {
        for var in self.level_vars.range() {
            if var.value(self).is_none() {
                println!("{:?} unassigned", var);
                return None;
            }
        }

        for var in self.term_vars.range() {
            if var.value(self).is_none() {
                println!("{:?} unassigned", var);
                return None;
            }
        }

        Some(())
    }
}

