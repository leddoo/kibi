use sti::traits::{CopyIt, FromIn};
use sti::arena_pool::ArenaPool;
use sti::vec::Vec;
use sti::keyed::{Key, KSlice};
use sti::hash::HashMap;

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

    // @speed: arena.
    let entry_vars = Vec::from_in(this.temp, (0..def_data.num_params).map(LocalVarId::from_usize_unck));
    //println!("building {}", pp(def.val, env, strings, &LocalCtx::new()));
    this.build_jp(def.val, &entry_vars, BlockId::ENTRY);

    for aux_id in def_data.aux_defs.copy_it() {
        let aux = env.symbol(aux_id);
        let SymbolKind::Def(aux_def) = aux.kind else { unreachable!() };

        let jp = &this.jps[&aux_id];
        //println!("building {}", pp(aux_def.val, env, strings, &LocalCtx::new()));
        this.build_jp(aux_def.val, jp.vars, jp.bb);
    }

    //dbg!(&this.blocks);

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
        for _ in locals.copy_it() {
            let lam = term.try_lambda().unwrap();
            term = lam.val;
        }
        self.build_term(term, true);
    }

    fn build_term(&mut self, term: Term<'out>, is_tail: bool) {
        let mut term = term;

        // let chain.
        while let Some(it) = term.try_let() {
            self.build_term(it.val, false);

            if let Some(vid) = it.vid.to_option() {
                self.stmts.push(Stmt::Write(Path { base: vid, projs: &[] }));
            }
            else {
                self.stmts.push(Stmt::Pop);
            }

            term = it.body;
        }

        let (fun, args) = term.app_args(self.temp);

        if is_tail {
            let terminator = 'terminator: {
                if let Some(g) = fun.try_global() {
                    // jump.
                    if let Some(jp) = self.jps.get(&g.id) {
                        // validate jp args (fn).
                        break 'terminator Terminator::Jump { target: jp.bb };
                    }
                    // ite.
                    else if g.id == SymbolId::ite {
                        // only if have jp args.
                        // then also validate jp args.
                        //return;
                    }
                }

                // return.
                self.build_app(fun, &args);
                Terminator::Return
            };

            let stmts = self.stmts.clone_in(self.alloc).leak();
            self.stmts.clear();

            let none = self.blocks[self.current_block].replace(Block { stmts, terminator });
            assert!(none.is_none());
        }
        else {
            self.build_app(fun, &args);
        }
    }

    fn build_app(&mut self, fun: Term<'out>, args: &[Term<'out>]) {
        self.stmts.push(Stmt::Error);
    }
}

