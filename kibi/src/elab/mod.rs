use sti::arena::Arena;
use sti::vec::Vec;
use sti::keyed::KVec;

use crate::string_table::{StringTable, Atom};
use crate::diagnostics::*;
use crate::parser::Parse;
use crate::tt::{ScopeId, LocalCtx};
use crate::env::*;
use crate::traits::Traits;


pub struct Elab<'me, 'out, 'a> {
    pub alloc: &'a Arena,
    pub strings: &'me mut StringTable<'a>,
    pub env: &'me mut Env<'a>,
    pub traits: &'me mut Traits,

    pub parse: &'me Parse<'me>,

    root_symbol: SymbolId,

    level_params: Vec<Atom>,

    // @temp: @inductive_uses_elab.
    pub(crate) lctx: LocalCtx<'a>,
    locals: Vec<(Atom, ScopeId)>,

    ivars: ivars::IVarCtx<'a>,

    foo: &'out (),
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
mod impls;



impl<'me, 'out, 'a> Elab<'me, 'out, 'a> {
    pub fn new(env: &'me mut Env<'a>, traits: &'me mut Traits, parse: &'me Parse<'me>, root_symbol: SymbolId, strings: &'me mut StringTable<'a>, alloc: &'a Arena) -> Self {
        Self {
            alloc,
            strings,
            env,
            traits,
            parse,
            root_symbol,
            lctx: LocalCtx::new(alloc),
            locals: Vec::new(),
            level_params: Vec::new(),
            ivars: ivars::IVarCtx::new(),
            foo: &(),
        }
    }

    fn error<S, F>(&self, source: S, f: F)
    where S: Into<DiagnosticSource>, F: FnOnce(&'out Arena) -> ElabError<'out> {
        let _ = (source, f);
        unimplemented!()
        /*
        self.errors.with(|errors| {
            errors.report(Diagnostic {
                parse: self.parse.id,
                source: source.into(),
                kind: DiagnosticKind::ElabError(f(errors.alloc)),
            });
        });
        */
    }

    pub fn reset(&mut self) {
        self.level_params.clear();
        self.lctx.clear();
        self.locals.clear();
        self.ivars.clear();
    }

    // @mega@temp below this line.

    // @temp: `Compiler` rework.
    pub fn check_no_unassigned_variables(&self) -> Option<()> {
        for var in self.ivars.level_vars.range() {
            if var.value(self).is_none() {
                println!("{:?} unassigned", var);
                return None;
            }
        }

        for var in self.ivars.term_vars.range() {
            if var.value(self).is_none() {
                println!("{:?} unassigned", var);
                return None;
            }
        }

        Some(())
    }

    pub fn pp_level(&self, l: crate::tt::Level, width: i32) -> String {
        let temp = sti::arena_pool::ArenaPool::tls_get_temp();
        let mut pp = crate::tt::TermPP::new(&self.env, &self.strings, &*temp);
        let val = pp.pp_level(l);
        let val = pp.render(val, width);
        let val = val.layout_string();
        return val;
    }

    pub fn pp(&self, t: crate::tt::Term, width: i32) -> String {
        let temp = sti::arena_pool::ArenaPool::tls_get_temp();
        let mut pp = crate::tt::TermPP::new(&self.env, &self.strings, &*temp);
        let val = pp.pp_term(t);
        let val = pp.render(val, width);
        let val = val.layout_string();
        return val;
    }
}


struct SavePoint {
    local_ctx: crate::tt::local_ctx::SavePoint,
    num_locals: usize,
    ivar_ctx: ivars::SavePoint,
}

impl<'me, 'out, 'a> Elab<'me, 'out, 'a> {
    fn save(&self) -> SavePoint {
        SavePoint {
            local_ctx: self.lctx.save(),
            num_locals: self.locals.len(),
            ivar_ctx: self.ivars.save(),
        }
    }

    fn restore(&mut self, save: SavePoint) {
        self.lctx.restore(save.local_ctx);
        self.locals.truncate(save.num_locals);
        self.ivars.restore(save.ivar_ctx);
    }
}

