use sti::arena::Arena;
use sti::vec::Vec;
use sti::keyed::KVec;
use sti::hash::HashMap;
use sti::string::String;

use crate::string_table::{StringTable, Atom};
use crate::diagnostics::*;
use crate::ast::{TokenId, ItemId, ExprId, TacticId};
use crate::parser::Parse;
use crate::tt::{self, ScopeId, OptScopeId, LocalCtx};
use crate::env::*;
use crate::traits::Traits;


pub struct Elab<'a> {
    pub diagnostics: Diagnostics<'a>,
    pub token_infos: HashMap<TokenId, TokenInfo>,
    pub item_infos:   KVec<ItemId,   Option<ItemInfo<'a>>>,
    pub item_ctxs:    KVec<ItemId,   Option<ItemCtx<'a>>>,
    pub expr_infos:   KVec<ExprId,   Option<ExprInfo<'a>>>,
    pub tactic_infos: KVec<TacticId, Option<TacticInfo<'a>>>,
}

#[derive(Clone, Copy, Debug)]
pub enum TokenInfo {
    Local(ItemId, ScopeId),
    Symbol(SymbolId),
}

#[derive(Clone, Copy, Debug)]
pub enum ItemInfo<'a> {
    Symbol(SymbolId),
    Reduce(tt::Term<'a>),
}

#[derive(Debug)]
pub struct ItemCtx<'a> {
    pub local_ctx: LocalCtx<'a>,
    pub ivar_ctx:  ivars::IVarCtx<'a>,
}

#[derive(Clone, Copy, Debug)]
pub struct ExprInfo<'a> {
    pub term: tt::Term<'a>,
    pub ty:   tt::Term<'a>,
}

#[derive(Clone, Copy, Debug)]
pub struct TacticInfo<'a> {
    pub scope: OptScopeId,
    pub goals: &'a [tt::Term<'a>],
    pub kind: TacticInfoKind<'a>,
}

#[derive(Clone, Copy, Debug)]
pub enum TacticInfoKind<'a> {
    None,
    Term(tt::Term<'a>),
}


pub fn elab_file<'out>(
    parse: &Parse,
    elab: &mut Elab<'out>,
    env: &mut Env<'out>, traits: &mut Traits, strings: &mut StringTable,
    alloc: &'out Arena)
{
    *elab.item_infos.inner_mut_unck() = Vec::from_fn(|| None, parse.items.len());
    *elab.item_ctxs.inner_mut_unck()  = Vec::from_fn(|| None, parse.items.len());
    *elab.expr_infos.inner_mut_unck() = Vec::from_value(None, parse.exprs.len());
    *elab.tactic_infos.inner_mut_unck() = Vec::from_value(None, parse.tactics.len());

    for item_id in parse.root_items.iter().copied() {
        let mut elaborator = Elaborator {
            alloc,
            strings, env, traits,
            parse, elab,
            item_id,
            root_symbol: SymbolId::ROOT,
            lctx: LocalCtx::new(),
            locals: Vec::new(),
            level_params: Vec::new(),
            ivars: ivars::IVarCtx::new(),
            had_unassigned_ivars: false,
            goals: Vec::new(),
            current_goal: 0,
            aux_defs: Vec::new(),
        };

        let result = elaborator.elab_item(item_id);

        // need to set item ctx before stopping,
        // cause token info hover unwraps item_id's ctx.
        elab.item_ctxs[item_id] = Some(ItemCtx {
            local_ctx: elaborator.lctx,
            ivar_ctx:  elaborator.ivars,
        });

        if result.is_none() {
            break;
        }
    }
}


pub struct Elaborator<'me, 'c, 'out> {
    pub alloc: &'out Arena,
    pub strings: &'me mut StringTable<'c>,
    pub env: &'me mut Env<'out>,
    pub traits: &'me mut Traits,

    pub parse: &'me Parse<'me>,
    pub elab: &'me mut Elab<'out>,

    item_id: ItemId,
    root_symbol: SymbolId,

    level_params: Vec<Atom>,

    // @temp: @inductive_uses_elab.
    pub(crate) lctx: LocalCtx<'out>,
    locals: Vec<Local>,

    ivars: ivars::IVarCtx<'out>,
    had_unassigned_ivars: bool,

    goals: Vec<crate::tt::TermVarId>,
    current_goal: usize,

    aux_defs: Vec<AuxDef<'out>>,
}

#[derive(Clone, Copy, Debug)]
struct Local {
    name: Atom,
    id: ScopeId,
    mutable: bool,
}

struct AuxDef<'a> {
    name: Atom,
    ivar: tt::TermVarId,
    ty:    tt::Term<'a>,
    value: tt::Term<'a>,
}


mod ivars;
mod abstracc;
mod whnf;
mod infer_type;
mod def_eq_level;
mod def_eq_term;
mod abstracc_eq;
mod elab_level;
mod elab_expr;
mod elab_binders;
mod elab_app;
mod elab_elim;
mod elab_def;
mod elab_inductive;
mod elab_item;
mod elab_do;
mod impls;
mod tactic;


pub enum ExprOrTerm<'a> {
    Expr(crate::ast::ExprId),
    Term(crate::tt::Term<'a>),
}

impl<'me, 'c, 'out> Elaborator<'me, 'c, 'out> {
    #[inline]
    pub fn error(&mut self, source: impl Into<DiagnosticSource>, error: ElabError<'out>) {
        self.elab.diagnostics.push(
            Diagnostic {
                source: source.into(),
                kind: DiagnosticKind::ElabError(error),
            });
    }

    pub fn reset(&mut self) {
        self.level_params.clear();
        self.lctx.clear();
        self.locals.clear();
        self.ivars.clear();
    }

    #[inline(always)]
    #[track_caller]
    pub fn mkt_ax_sorry(&mut self, t: tt::Term<'out>, source: tt::TermSource) -> tt::Term<'out> {
        use tt::TermAlloc;
        self.alloc.mkt_ax_sorry(self.infer_type_as_sort(t).unwrap(), t, source)
    }

    #[inline(always)]
    #[track_caller]
    pub fn mkt_ax_uninit(&mut self, t: tt::Term<'out>, source: tt::TermSource) -> tt::Term<'out> {
        use tt::TermAlloc;
        self.alloc.mkt_ax_uninit(self.infer_type_as_sort(t).unwrap(), t, source)
    }

    #[inline(always)]
    #[track_caller]
    pub fn mkt_ax_unreach(&mut self, t: tt::Term<'out>, source: tt::TermSource) -> tt::Term<'out> {
        use tt::TermAlloc;
        self.alloc.mkt_ax_unreach(self.infer_type_as_sort(t).unwrap(), t, source)
    }

    #[inline(always)]
    #[track_caller]
    pub fn mkt_ax_error(&mut self, t: tt::Term<'out>, source: tt::TermSource) -> (tt::Term<'out>, tt::Term<'out>) {
        use tt::TermAlloc;
        (self.alloc.mkt_ax_error(self.infer_type_as_sort(t).unwrap(), t, source), t)
    }

    #[inline(always)]
    #[track_caller]
    pub fn mkt_ax_error_from_expected(&mut self, expected: Option<tt::Term<'out>>, source: tt::TermSource) -> (tt::Term<'out>, tt::Term<'out>) {
        if let Some(t) = expected {
            self.mkt_ax_error(t, source)
        }
        else {
            use tt::TermAlloc;
            let (t, l) = self.new_ty_var();
            (self.alloc.mkt_ax_error(l, t, source), t)
        }
    }

    #[inline]
    fn with_saved_goals<R, F: FnOnce(&mut Self) -> R>(&mut self, f: F) -> R {
        let save = (self.goals.len(), self.current_goal);
        self.current_goal = self.goals.len();

        let result = f(self);

        self.goals.truncate(save.0);
        self.current_goal = save.1;
        return result;
    }

    // @mega@temp below this line.

    // @temp: `Compiler` rework.
    pub fn check_no_unassigned_variables(&mut self, source: DiagnosticSource) -> Option<()> {
        for var in self.ivars.level_vars.range() {
            if var.value(self).is_none() {
                self.error(source, ElabError::UnassignedIvars);
                return None;
            }
        }

        for var in self.ivars.term_vars.range() {
            if var.value(self).is_none() {
                self.error(source, ElabError::UnassignedIvars);
                return None;
            }
        }

        Some(())
    }

    pub fn pp_level(&self, l: crate::tt::Level, width: i32) -> String {
        let temp = sti::arena_pool::ArenaPool::tls_get_temp();
        let mut pp = crate::tt::TermPP::new(&self.env, &self.strings, &self.lctx, &*temp);
        let val = pp.pp_level(l);
        let val = pp.render(val, width);
        let val = val.layout_string();
        return val;
    }

    pub fn pp(&self, t: crate::tt::Term, width: i32) -> String {
        let temp = sti::arena_pool::ArenaPool::tls_get_temp();
        let mut pp = crate::tt::TermPP::new(&self.env, &self.strings, &self.lctx, &*temp);
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

impl<'me, 'c, 'out> Elaborator<'me, 'c, 'out> {
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

