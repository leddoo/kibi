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

    let mut latest_var_vals = KVec::with_cap(def_data.local_vars.len());
    for _ in 0..def_data.local_vars.len() {
        latest_var_vals.push(u32::MAX);
    }

    let temp = ArenaPool::tls_get_temp();

    let mut this = Builder {
        alloc,
        env,
        strings,
        vars: def_data.local_vars,
        jps: HashMap::with_cap(def_data.aux_defs.len()),
        locals: Vec::new(),
        latest_var_vals,
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
            assert!(pi.ty.syntax_eq(this.vars[vid].ty));
            ty = pi.val;
        }

        this.jps.insert(aux_id, JoinPoint { bb, vars });
    }

    let entry_vars = Vec::from_in(this.temp,
        (0..def_data.num_params).map(LocalVarId::from_usize_unck));
    eprintln!("building {}", pp(def.val, env, strings, &LocalCtx::new()));
    this.build_jp(def.val, &entry_vars, BlockId::ENTRY);

    for aux_id in def_data.aux_defs.copy_it() {
        let aux = env.symbol(aux_id);
        let SymbolKind::Def(aux_def) = aux.kind else { unreachable!() };

        let jp = &this.jps[&aux_id];
        eprintln!("building {}", pp(aux_def.val, env, strings, &LocalCtx::new()));
        this.build_jp(aux_def.val, jp.vars, jp.bb);
    }

    dbg!(&this.blocks);
    eprintln!();

    None
}

struct Builder<'me, 'out> {
    alloc: &'out Arena,
    env: &'me Env<'out>,
    #[allow(dead_code)] strings: &'me StringTable<'me>,

    vars: &'me KSlice<LocalVarId, LocalVar<'out>>,
    jps: HashMap<SymbolId, JoinPoint<'out>>,

    locals: Vec<OptLocalVarId>,
    latest_var_vals: KVec<LocalVarId, u32>, // NonMaxU32.

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

        self.locals.clear();
        self.locals.extend(locals.copy_map_it(|l| l.some()));

        for latest in self.latest_var_vals.inner_mut_unck().iter_mut() {
            *latest = u32::MAX;
        }

        self.current_block = bb;

        let mut term = val;

        // params.
        for (i, param) in locals.copy_it().enumerate() {
            self.latest_var_vals[param] = i as u32;

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
                    self.check_jp_args(&args, jp.vars);
                    break 'terminator Terminator::Jump { target: jp.bb };
                }
                // ite.
                else if g.id == SymbolId::ite && args.len() == 4 {
                    let cond = args[1];
                    let then = args[2];
                    let els  = args[3];

                    let (then, then_args) = then.app_args(self.temp);
                    let (els,  els_args)  = els.app_args(self.temp);
                    if let (Some(t), Some(e)) = (then.try_global(), els.try_global()) {
                        if let (Some(t), Some(e)) = (self.jps.get(&t.id), self.jps.get(&e.id)) {
                            let on_true  = t.bb;
                            let on_false = e.bb;
                            self.check_jp_args(&then_args, t.vars);
                            self.check_jp_args(&els_args,  e.vars);

                            self.build_term(cond);
                            break 'terminator Terminator::Ite { on_true, on_false };
                        }
                    }
                }
            }

            // return.
            self.build_app(term, fun, &args);
            Terminator::Return
        };

        self.locals.clear();

        let stmts = self.stmts.clone_in(self.alloc).leak();
        self.stmts.clear();

        let none = self.blocks[self.current_block].replace(Block { stmts, terminator });
        assert!(none.is_none());
    }

    // must produce exactly one value.
    fn build_term(&mut self, term: Term<'out>) {
        let old_num_locals = self.locals.len();

        let term = self.build_let_chain(term);

        let (fun, args) = term.app_args(self.temp);
        self.build_app(term, fun, &args);

        self.locals.truncate(old_num_locals);
    }

    #[inline]
    fn build_let_chain(&mut self, mut term: Term<'out>) -> Term<'out> {
        while let Some(it) = term.try_let() {
            term = it.body;

            let latest = self.locals.len() as u32;

            if it.val.try_ax_uninit_app().is_some() {
                self.locals.push(it.vid);
                if let Some(vid) = it.vid.to_option() {
                    self.latest_var_vals[vid] = latest;
                }
                continue;
            }

            self.build_term(it.val);
            self.locals.push(it.vid);

            if let Some(vid) = it.vid.to_option() {
                // @todo: validate type.
                self.stmts.push(Stmt::Write(Path { base: vid, projs: &[] }));
                self.latest_var_vals[vid] = latest;
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

            TermData::Bound(it) => {
                if args.len() != 0 {
                    self.stmts.push(Stmt::Error);
                    return;
                }

                let Some((id, index)) = self.check_bvar(it) else {
                    self.stmts.push(Stmt::Error);
                    return;
                };

                if self.latest_var_vals[id] != index {
                    self.stmts.push(Stmt::Error);
                    return;
                }

                self.stmts.push(Stmt::Read(Path { base: id, projs: &[] }));
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
                                // @todo: const ig. similar to forall ~ handle locals.
                                self.stmts.push(Stmt::Axiom);
                            }

                            SymbolId::Ref_from_value => {
                                let Some(path) = self.build_path(args[2], false) else {
                                    self.stmts.push(Stmt::Error);
                                    return;
                                };

                                self.stmts.push(Stmt::Ref(path));
                            }

                            SymbolId::Ref_read => {
                                let Some(path) = self.build_path(args[2], true) else {
                                    self.stmts.push(Stmt::Error);
                                    return;
                                };

                                self.stmts.push(Stmt::Read(path));
                            }

                            SymbolId::Ref_write => {
                                let Some(path) = self.build_path(args[1], true) else {
                                    self.stmts.push(Stmt::Error);
                                    return;
                                };

                                self.stmts.push(Stmt::Write(path));
                            }

                            SymbolId::ax_uninit | SymbolId::ax_unreach => {
                                // technically `unreachable!()`, but the user
                                // could have used these directly.
                                self.stmts.push(Stmt::Error);
                            }

                            _ => {
                                self.stmts.push(Stmt::Axiom);
                            }
                        }
                    }

                    SymbolKind::IndAxiom(_) => {
                        if it.id == SymbolId::Unit_mk {
                            self.stmts.push(Stmt::ConstUnit);
                            return;
                        }
                        if it.id == SymbolId::Bool_false {
                            self.stmts.push(Stmt::ConstBool(false));
                            return;
                        }
                        if it.id == SymbolId::Bool_true {
                            self.stmts.push(Stmt::ConstBool(true));
                            return;
                        }
                        if let Some(v) = term.try_nat_val() {
                            self.stmts.push(Stmt::ConstNat(v));
                            return;
                        }

                        // don't think we need num_params here.
                        // thinking we only wanna support nat for now?
                        // eventually, structs & stuff would prob be handled here.
                        self.stmts.push(Stmt::Axiom);
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
                        for arg in args.copy_it() {
                            self.build_term(arg);
                        }
                        self.stmts.push(Stmt::Call { func: it.id, num_args: args.len() });
                    }
                }

            }

            TermData::Forall(_) => {
                assert_eq!(args.len(), 0);
                //self.stmts.push(Stmt::Const(fun));
                self.stmts.push(Stmt::Error);
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

    fn build_path(&mut self, path: Term, add_deref: bool) -> Option<Path<'out>> {
        let mut projs = Vec::new_in(self.temp);
        if add_deref {
            projs.push(Proj::Deref);
        }

        let mut path = path;
        loop {
            let (fun, args) = path.app_args(self.temp);

            if let Some(bvar) = fun.try_bvar() {
                if args.len() != 0 {
                    return None;
                }

                let base = self.locals.rev(bvar.offset as usize).to_option()?;
                projs.reverse();
                let projs = projs.clone_in(self.alloc).leak();
                return Some(Path { base, projs });
            }
            else if let Some(g) = fun.try_global() {
                match g.id {
                    SymbolId::Ref_read => {
                        debug_assert_eq!(args.len(), 3);
                        projs.push(Proj::Deref);
                        path = args[2];
                    }

                    _ => {
                        return None;
                    }
                }
            }
        }
    }

    fn check_bvar(&self, bvar: BVar) -> Option<(LocalVarId, u32)> {
        assert!((bvar.offset as usize) < self.locals.len());
        let index = self.locals.len()-1 - bvar.offset as usize;

        let id = self.locals[index].to_option()?;
        Some((id, index as u32))
    }

    fn check_jp_args(&self, args: &[Term], jp_locals: &[LocalVarId]) {
        assert_eq!(args.len(), jp_locals.len());

        for (i, arg) in args.copy_it().enumerate() {
            let bvar = arg.try_bvar().unwrap();
            let (id, index) = self.check_bvar(bvar).unwrap();
            assert_eq!(id, jp_locals[i]);
            assert_eq!(self.latest_var_vals[id], index);
        }
    }
}

