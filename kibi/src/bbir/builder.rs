use sti::traits::{CopyIt, FromIn};
use sti::arena_pool::ArenaPool;
use sti::vec::Vec;
use sti::keyed::{Key, KSlice};
use sti::hash::HashMap;

use crate::env::symbol;
use crate::string_table::StringTable;
use crate::tt::*;
use crate::env::{Env, SymbolKind, symbol::DefKind};

use super::*;


fn pp(t: Term, env: &Env, strings: &StringTable, lctx: &LocalCtx) -> sti::string::String {
    let temp = sti::arena_pool::ArenaPool::tls_get_temp();
    let mut pp = crate::tt::TermPP::new(env, strings, lctx, &*temp);
    let val = pp.pp_term(t);
    let val = pp.render(val, 80);
    let val = val.layout_string();
    return val;
}


// @todo: collect errors.
pub fn build_def<'out>(id: SymbolId, env: &Env<'out>, strings: &StringTable, alloc: &'out Arena) -> Option<Function<'out>> {
    let symbol = env.symbol(id);
    let SymbolKind::Def(def) = symbol.kind else { unreachable!() };
    let DefKind::Primary(def_data) = def.kind else { unreachable!() };

    assert!(def_data.local_vars.len() >= def_data.num_params);

    for (_, local) in def_data.local_vars.iter() {
        if local.ty.has_locals() {
            return None;
        }
    }

    let temp = ArenaPool::tls_get_temp();

    let mut this = Builder {
        alloc,
        env,
        locals: def_data.local_vars,
        jps: HashMap::with_cap(def_data.aux_defs.len()),
        blocks: KVec::new(),
        stmts: Vec::new(),
        current_block: BlockId::ENTRY,
        temp: &*temp,
    };
    let entry = this.reserve_block();
    assert_eq!(entry, BlockId::ENTRY);

    // collect jps.
    for aux_id in def_data.aux_defs.copy_it() {
        let aux = env.symbol(aux_id);
        let SymbolKind::Def(aux_def) = aux.kind else { unreachable!() };
        let DefKind::Aux(aux_data) = aux_def.kind else { unreachable!() };

        let bb = this.reserve_block();
        let vars = aux_data.param_vids;

        // starts with params.
        for i in 0..def_data.num_params {
            assert_eq!(aux_data.param_vids[i].usize(), i);
        }

        // validate types.
        let mut ty = aux_def.ty;
        for vid in vars.copy_it() {
            let pi = ty.try_forall().unwrap();
            assert!(pi.ty.syntax_eq(this.locals[vid].ty));
            ty = pi.val;
        }

        this.jps.insert(aux_id, JoinPoint { bb, vars });
    }

    let entry_vars = Vec::from_in(this.temp,
        (0..def_data.num_params).map(LocalVarId::from_usize_unck));
    println!("building {}", pp(def.val, env, strings, &LocalCtx::new()));
    this.build_jp(def.val, &entry_vars, BlockId::ENTRY);

    for aux_id in def_data.aux_defs.copy_it() {
        let aux = env.symbol(aux_id);
        let SymbolKind::Def(aux_def) = aux.kind else { unreachable!() };

        let jp = &this.jps[&aux_id];
        println!("building {}", pp(aux_def.val, env, strings, &LocalCtx::new()));
        this.build_jp(aux_def.val, jp.vars, jp.bb);
    }

    dbg!(&this.blocks);

    None
}

struct Builder<'me, 'out> {
    alloc: &'out Arena,
    env: &'me Env<'out>,

    locals: &'me KSlice<LocalVarId, LocalVar<'out>>,
    jps: HashMap<SymbolId, JoinPoint<'out>>,

    blocks: KVec<BlockId, Option<Block<'out>>>,

    stmts: Vec<Stmt<'out>>,
    current_block: BlockId,

    temp: &'me Arena,
}

struct JoinPoint<'a> {
    bb: BlockId,
    vars: &'a [LocalVarId],
}

impl<'me, 'out> Builder<'me, 'out> {
    fn reserve_block(&mut self) -> BlockId {
        return self.blocks.push(None);
    }

    fn build_jp(&mut self, val: Term<'out>, locals: &[LocalVarId], bb: BlockId) {
        assert_eq!(self.stmts.len(), 0);

        self.current_block = bb;

        let mut term = val;

        // params.
        for _ in locals.copy_it() {
            let lam = term.try_lambda().unwrap();
            term = lam.val;
        }

        term = self.build_let_chain(term);

        // terminator.
        let (fun, args) = term.app_args(self.temp);
        let terminator = 'terminator: {
            if let Some(g) = fun.try_global() {
                // jump.
                if let Some(jp) = self.jps.get(&g.id) {
                    // validate jp args (fn).
                    break 'terminator Terminator::Jump { target: jp.bb };
                }
                // ite.
                else if g.id == SymbolId::ite {
                    // if jps, branch.
                    // else, handled by `build_app`.
                }
            }

            // return.
            self.build_app(term, fun, &args);
            Terminator::Return
        };

        let stmts = self.stmts.clone_in(self.alloc).leak();
        self.stmts.clear();

        let none = self.blocks[self.current_block].replace(Block { stmts, terminator });
        assert!(none.is_none());
    }

    // must produce exactly one value.
    fn build_term(&mut self, term: Term<'out>) {
        let term = self.build_let_chain(term);

        let (fun, args) = term.app_args(self.temp);
        self.build_app(term, fun, &args);
    }

    #[inline]
    fn build_let_chain(&mut self, mut term: Term<'out>) -> Term<'out> {
        while let Some(it) = term.try_let() {
            term = it.body;

            if it.val.try_ax_uninit_app().is_some() {
                continue;
            }

            self.build_term(it.val);

            if let Some(vid) = it.vid.to_option() {
                self.stmts.push(Stmt::Write(Path { base: vid, projs: &[] }));
            }
            else {
                self.stmts.push(Stmt::Pop);
            }
        }
        return term;
    }

    // must produce exactly one value.
    fn build_app(&mut self, term: Term<'out>, fun: Term<'out>, args: &[Term<'out>]) {
        match fun.data() {
            TermData::Sort(_) => {
                assert_eq!(args.len(), 0);
                self.stmts.push(Stmt::Const(fun));
            }

            TermData::Bound(_) => {
                // check args.len = 0.
                self.stmts.push(Stmt::Error);
            }

            TermData::Global(it) => {
                assert!(self.jps.get(&it.id).is_none());

                let symbol = self.env.symbol(it.id);

                match symbol.kind {
                    SymbolKind::Root |
                    SymbolKind::Predeclared |
                    SymbolKind::Pending(_) => unreachable!(),

                    SymbolKind::Axiom(ax) => {
                        if args.len() != ax.num_params {
                            self.stmts.push(Stmt::Error);
                            return;
                        }

                        match it.id {
                            SymbolId::ax_sorry | SymbolId::ax_error => {
                                self.stmts.push(Stmt::Error);
                            }

                            SymbolId::Ref => {
                                // @todo.
                                self.stmts.push(Stmt::Error);
                            }

                            SymbolId::Ref_from_value => {
                                // @todo.
                                //  - construct path.
                                self.stmts.push(Stmt::Error);
                            }

                            SymbolId::Ref_read => {
                                // @todo.
                                //  - construct path, only support based on local for now.
                                self.stmts.push(Stmt::Error);
                            }

                            SymbolId::Ref_write => {
                                // @todo.
                                //  - construct path, only support based on local for now.
                                self.stmts.push(Stmt::Error);
                            }

                            SymbolId::ax_uninit | SymbolId::ax_unreach => {
                                // technically `unreachable!()`, but the user
                                // could have used these directly.
                                self.stmts.push(Stmt::Error);
                            }

                            _ => {
                                self.stmts.push(Stmt::Error);
                            }
                        }
                    }

                    SymbolKind::IndAxiom(_) => {
                        if let Some(v) = term.try_nat_val() {
                            self.stmts.push(Stmt::ConstNat(v));
                            return;
                        }

                        // don't think we need num_params here.
                        // thinking we only wanna support nat for now?
                        // eventually, structs & stuff would prob be handled here.
                        self.stmts.push(Stmt::Error);
                    }

                    SymbolKind::Def(def) => {
                        let symbol::DefKind::Primary(data) = def.kind else {
                            self.stmts.push(Stmt::Error);
                            return;
                        };

                        if args.len() != data.num_params {
                            self.stmts.push(Stmt::Error);
                            return;
                        }

                        // todo: ite special case.

                        // call.
                        //  - build args.
                        //  - make call.
                        self.stmts.push(Stmt::Error);
                    }
                }

            }

            TermData::Forall(_) => {
                assert_eq!(args.len(), 0);
                self.stmts.push(Stmt::Const(fun));
            }

            TermData::Lambda(_) => {
                self.stmts.push(Stmt::Error);
            }

            TermData::Local(_) |
            TermData::IVar(_) |
            TermData::Let(_) |
            TermData::Apply(_) => unreachable!(),
        }
    }
}

