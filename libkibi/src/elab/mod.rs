use sti::arena::Arena;
use sti::vec::Vec;

use crate::error::*;
use crate::ast::SourceRange;
use crate::tt::{ScopeId, LocalCtx, InferCtx};
use crate::env::*;


pub struct Elab<'me, 'err, 'a> {
    pub alloc: &'a Arena,
    pub errors: &'me ErrorCtx<'err>,
    pub env: &'me mut Env<'a>,

    root_symbol: SymbolId,

    level_vars: Vec<&'a str>,

    lctx: LocalCtx<'a>,
    locals: Vec<(&'a str, ScopeId)>,

    // @temp
    pub ictx: InferCtx<'a>,
}


mod ivars;
mod abstracc;
mod instantiate;
mod whnf;
mod infer_type;
mod def_eq_level;
mod def_eq_term;
mod elab_symbol;
mod elab_level;
mod elab_expr;
mod elab_elim;
mod elab_def;


impl<'me, 'err, 'a> Elab<'me, 'err, 'a> {
    pub fn new(env: &'me mut Env<'a>, root_symbol: SymbolId, errors: &'me ErrorCtx<'err>, alloc: &'a Arena) -> Self {
        Self {
            alloc,
            errors,
            env,
            root_symbol,
            lctx: LocalCtx::new(alloc),
            locals: Vec::new(),
            level_vars: Vec::new(),
            ictx: InferCtx::new(alloc),
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
        for var in self.ictx.level_ids() {
            if self.ictx.level_value(var).is_none() {
                println!("{:?} unassigned", var);
                return None;
            }
        }

        for var in self.ictx.term_ids() {
            if self.ictx.term_value(var).is_none() {
                println!("{:?} unassigned", var);
                return None;
            }
        }

        Some(())
    }
}

