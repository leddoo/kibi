use super::*;


// @temp
use std::collections::HashSet;


#[derive(Debug)]
pub struct CompileError {
    pub source: SourceRange,
    pub data:   CompileErrorData,
}


#[derive(Debug)]
pub enum CompileErrorData {
    UnexpectedLocal,
    InvalidAssignTarget,
}

pub type CompileResult<T> = Result<T, CompileError>;



#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
pub struct ScopeId(u32);


#[derive(Clone, Debug)]
pub struct Decl<'a> {
    pub name:  &'a str,
    pub id:    LocalId,
    pub scope: ScopeId,
}


pub struct Compiler {
}


pub struct Ctx<'a> {
    scope: ScopeId,
    decls: Vec<Decl<'a>>,
}



impl CompileError {
    #[inline]
    pub fn at(ast: &Ast, data: CompileErrorData) -> CompileError {
        CompileError { source: ast.source, data }
    }
}


impl Compiler {
    pub fn compile_chunk(&mut self, source: SourceRange, block: &ast::Block) -> CompileResult<()> {
        let mut fun = {
            let mut ctx = Ctx::new();
            let mut fun = Function::new();
            let mut bb = fun.new_block();
            self.compile_block(&mut ctx, &mut fun, &mut bb, source, block, false)?;

            let nil = fun.add_stmt_at(bb, source, StmtData::LoadNil);
            fun.add_stmt_at(bb, source, StmtData::Return { src: nil });

            fun.dump();
            fun
        };


        let (preds, post_order) = fun.preds_and_post_order();

        let post_indices = post_order.indices();

        let idoms = fun.immediate_dominators(&preds, &post_order, &post_indices);

        let dom_tree = fun.dominator_tree(&idoms);

        println!("tree {:?}", *dom_tree);

        let dom_frontiers = fun.dominance_frontiers(&preds, &idoms);

        // find phis
        let mut phis = {
            let mut visited: HashSet<(BlockId, LocalId)> = HashSet::new();

            let mut stack = vec![];
            for bb in fun.block_ids() {
                fun.block_stmts(bb, |stmt| {
                    let StmtData::SetLocal { dst: lid, src: _ } = stmt.data else { return };

                    let key = (bb, lid);
                    if !visited.contains(&key) {
                        visited.insert(key);
                        stack.push(key);
                    }
                });
            }

            let mut phis: Vec<Vec<(LocalId, Vec<(BlockId, Option<StmtId>)>, StmtId)>>
                = vec![vec![]; fun.num_blocks()];

            while let Some((from_bb, lid)) = stack.pop() {
                for to_bb in dom_frontiers[from_bb.usize()].iter() {
                    let to_bb = *to_bb;
                    let to_phis = &mut phis[to_bb.usize()];

                    let needs_phi_for_lid = to_phis.iter().find(|(l, _, _)| *l == lid).is_none();
                    if needs_phi_for_lid {
                        let preds = &preds[to_bb.usize()];

                        let map = preds.iter().map(|p| (*p, None)).collect();
                        let stmt = fun.new_phi(SourceRange::null(), &[]);
                        to_phis.push((lid, map, stmt));

                        let key = (to_bb, lid);
                        if !visited.contains(&key) {
                            visited.insert(key);
                            stack.push(key);
                        }
                    }
                }
            }

            phis
        };
        fun.slow_integrity_check();

        println!("{:?}", phis);

        // rename vars.
        {
            fn visit(bb: BlockId, mut new_names: Vec<Option<StmtId>>,
                phis: &mut Vec<Vec<(LocalId, Vec<(BlockId, Option<StmtId>)>, StmtId)>>,
                fun: &mut Function, idom_tree: &Vec<Vec<BlockId>>,
            ) {
                // update var names.
                for (lid, _map, stmt) in &phis[bb.usize()] {
                    new_names[lid.usize()] = Some(*stmt)
                }
                fun.block_stmts_mut(bb, |stmt| {
                    if let StmtData::GetLocal { src } = stmt.data {
                        let new_name = new_names[src.usize()].unwrap();
                        stmt.data = StmtData::Copy { src: new_name };
                        new_names[src.usize()] = Some(stmt.id());
                    }

                    if let StmtData::SetLocal { dst, src } = stmt.data {
                        stmt.data = StmtData::Copy { src };
                        new_names[dst.usize()] = Some(stmt.id());
                    }
                });

                // propagate to successors.
                fun.block_successors(bb, |succ| {
                    for (l, map, _) in &mut phis[succ.usize()] {
                        let entry = map.iter_mut().find(|(from, _)| *from == bb).unwrap();
                        assert!(entry.1.is_none());

                        entry.1 = Some(new_names[l.usize()].unwrap());
                    }
                });

                // propagate to dominated blocks.
                for d in idom_tree[bb.usize()].iter() {
                    visit(*d, new_names.clone(), phis, fun, idom_tree);
                }
            }

            let new_names = vec![None; fun.num_locals()];
            visit(BlockId::ENTRY, new_names, &mut phis, &mut fun, &dom_tree);
        }
        fun.slow_integrity_check();

        // insert phis.
        {
            for (bb_index, phis) in phis.into_iter().enumerate() {
                let phis = phis.iter().map(|(_lid, map, stmt_id)| {
                    let map = map.iter().map(|(bb, stmt)| (*bb, stmt.unwrap())).collect::<Vec<_>>();
                    fun.set_phi(*stmt_id, &map);
                    *stmt_id
                }).collect::<Vec<StmtId>>();

                // @temp
                for stmt_id in phis.iter().rev() {
                    fun.prepend_stmt(BlockId::from_usize(bb_index), *stmt_id);
                }
            }
        }
        fun.slow_integrity_check();

        println!("local2reg done");
        fun.dump();


        // copy propagation.
        {
            fn visit(bb: BlockId, fun: &mut Function, idom_tree: &Vec<Vec<BlockId>>) {
                // inline copies.
                fun.block_replace_args(bb, |fun, arg| {
                    if let StmtData::Copy { src } = arg.get(fun).data {
                        *arg = src;
                    }
                });

                // propagate to dominated blocks.
                for d in idom_tree[bb.usize()].iter() {
                    visit(*d, fun, idom_tree);
                }
            }
            visit(BlockId::ENTRY, &mut fun, &dom_tree);
        }
        fun.slow_integrity_check();

        println!("copy propagation done");
        fun.dump();


        // dead copy elimination.
        {
            let mut visited = vec![false; fun.num_stmts()];

            fun.all_args(|arg| visited[arg.usize()] = true);

            fun.retain_stmts(|stmt| {
                visited[stmt.id().usize()] || !stmt.is_copy()
            });
        }
        fun.slow_integrity_check();

        println!("dead copy elim done");
        fun.dump();


        let block_order = {
            fn visit(bb: BlockId, order: &mut Vec<BlockId>, visited: &mut Vec<bool>,
                fun: &Function, idom: &Vec<BlockId>, idom_tree: &Vec<Vec<BlockId>>,
            ) {
                assert!(!visited[bb.usize()]);
                visited[bb.usize()] = true;
                order.push(bb);

                fun.block_successors(bb, |succ| {
                    if !visited[succ.usize()] && idom[succ.usize()] == bb {
                        visit(succ, order, visited, fun, idom, idom_tree);
                    }
                });

                for child in &idom_tree[bb.usize()] {
                    if !visited[child.usize()] {
                        visit(*child, order, visited, fun, idom, idom_tree);
                    }
                }
            }

            let mut order   = vec![];
            let mut visited = vec![false; fun.num_blocks()];
            visit(BlockId::ENTRY, &mut order, &mut visited, &fun, &idoms, &dom_tree);
            order
        };
        fun.slow_integrity_check();

        let (block_begins, stmt_indices) = {
            let mut block_begins = vec![u32::MAX; fun.num_blocks()];
            let mut stmt_indices = vec![u32::MAX; fun.num_stmts()];

            let mut cursor = 0;
            for bb in &block_order {

                let block_begin = cursor;
                block_begins[bb.usize()] = block_begin as u32;

                fun.block_stmts(*bb, |stmt| {
                    stmt_indices[stmt.id().usize()] = cursor;
                    cursor += 1;
                });
            }
            block_begins.push(cursor as u32);

            (block_begins, stmt_indices)
        };

        println!("block order:");
        for bb in &block_order {
            println!("{}:", bb);

            fun.block_stmts(*bb, |stmt| {
                println!("  ({}) {}", stmt_indices[stmt.id().usize()], stmt);
            });
        }


        // live intervals.
        let intervals = {
            let mut bb_gen  = Vec::with_capacity(fun.num_blocks());
            let mut bb_kill = Vec::with_capacity(fun.num_blocks());

            fn pretty(set: &Vec<bool>) -> Vec<usize> {
                set.iter().enumerate()
                .filter_map(|(i, v)| v.then(|| i))
                .collect()
            }

            for bb in fun.block_ids() {
                let mut gen  = vec![false; fun.num_stmts()];
                let mut kill = vec![false; fun.num_stmts()];

                // statements in reverse.
                fun.block_stmts_rev(bb, |stmt| {
                    if stmt.has_value() {
                        kill[stmt.id().usize()] = true;
                        gen [stmt.id().usize()] = false;
                    }

                    if !stmt.is_phi() {
                        stmt.args(&fun, |arg| {
                            gen[arg.usize()] = true;
                        });
                    }
                });

                // println!("{}:", block.id);
                // println!(" gen:  {:?}", pretty(&gen));
                // println!(" kill: {:?}", pretty(&kill));

                bb_gen.push(gen);
                bb_kill.push(kill);
            }


            let mut bb_live_in  = vec![vec![false; fun.num_stmts()]; fun.num_blocks()];
            let mut bb_live_out = vec![vec![false; fun.num_stmts()]; fun.num_blocks()];
            let mut changed = true;
            while changed {
                changed = false;

                println!("live iter");

                for bb in &*post_order {
                    let gen   = &bb_gen[bb.usize()];
                    let kill  = &bb_kill[bb.usize()];

                    let mut new_live_out = vec![false; fun.num_stmts()];
                    fun.block_successors(*bb, |succ| {
                        // live_in.
                        for (i, live) in bb_live_in[succ.usize()].iter().enumerate() {
                            if *live {
                                new_live_out[i] = true;
                            }
                        }

                        // phis.
                        fun.block_stmts_ex(succ, |stmt| {
                            // @todo: try_phi Stmt variant?
                            if let Some(map) = fun.try_phi(stmt.id()) {
                                let src = map.get(*bb).unwrap();
                                new_live_out[src.usize()] = true;
                                return true;
                            }
                            false
                        });
                    });

                    let mut new_live_in = new_live_out.clone();
                    for (i, kill) in kill.iter().enumerate() {
                        if *kill {
                            new_live_in[i] = false;
                        }
                    }
                    for (i, gen) in gen.iter().enumerate() {
                        if *gen {
                            new_live_in[i] = true;
                        }
                    }

                    if new_live_in != bb_live_in[bb.usize()] {
                        changed = true;
                        bb_live_in[bb.usize()] = new_live_in;
                    }
                    if new_live_out != bb_live_out[bb.usize()] {
                        changed = true;
                        bb_live_out[bb.usize()] = new_live_out;
                    }
                }
            }

            println!("bb_live:");
            for (i, (live_in, live_out)) in bb_live_in.iter().zip(&bb_live_out).enumerate() {
                println!(" {} in:  {:?}", i, pretty(live_in));
                println!(" {} out: {:?}", i, pretty(live_out));
            }


            let mut intervals = vec![vec![]; fun.num_stmts()];
            for bb in block_order.iter() {
                //let live_in  = &bb_live_in[bb.usize()];
                let live_out = &bb_live_out[bb.usize()];

                let num_stmts = fun.num_block_stmts(*bb);

                let block_begin = block_begins[bb.usize()];
                let block_end   = block_begin + num_stmts as u32;

                let mut live = live_out.iter().map(|live| {
                    live.then(|| block_end)
                }).collect::<Vec<_>>();

                #[inline]
                fn gen(var: StmtId, stop: u32, live: &mut Vec<Option<u32>>) {
                    let id = var.usize();
                    if live[id].is_none() {
                        live[id] = Some(stop);
                    }
                }

                #[inline]
                fn kill(var: StmtId, start: u32, live: &mut Vec<Option<u32>>, intervals: &mut Vec<Vec<(u32, u32)>>) {
                    let id = var.usize();
                    if let Some(stop) = live[id] {
                        live[id] = None;

                        let interval = &mut intervals[id];
                        // try to extend.
                        if let Some((_, old_stop)) = interval.last_mut() {
                            if *old_stop == start {
                                *old_stop = stop;
                                return;
                            }
                        }
                        // need new range.
                        interval.push((start, stop));
                        return;
                    }
                }

                // statements.
                fun.block_stmts_rev(*bb, |stmt| {
                    if stmt.has_value() {
                        let start = stmt_indices[stmt.id().usize()];
                        kill(stmt.id(), start, &mut live, &mut intervals)
                    }

                    if !stmt.is_phi() {
                        stmt.args(&fun, |arg| {
                            let stop = stmt_indices[stmt.id().usize()];
                            gen(arg, stop, &mut live);
                        });
                    }
                });

                for id in fun.stmt_ids() {
                    let start = block_begin;
                    kill(id, start, &mut live, &mut intervals);
                }
            }

            println!("live intervals");
            for (bb, int) in intervals.iter().enumerate() {
                println!(" {}: {:?}", bb, int);
            }

            intervals
        };
        fun.slow_integrity_check();


        // register allocation.
        let (reg_mapping, num_regs) = {
            #[derive(Debug)]
            struct Interval<'a> {
                stmt: StmtId,
                start: u32,
                stop:  u32,
                ranges: &'a [(u32, u32)],
            }

            let mut intervals =
                intervals.iter().enumerate()
                .filter_map(|(i, ranges)| {
                    if ranges.len() == 0 { return None }
                    Some(Interval {
                        stmt:  StmtId::from_usize(i),
                        start: ranges[0].0,
                        stop:  ranges[ranges.len()-1].1,
                        ranges,
                    })
                }).collect::<Vec<_>>();
            intervals.sort_unstable_by(|a, b| a.start.cmp(&b.start));

            for int in &intervals {
                println!("{:?}", int);
            }

            struct ActiveInterval<'a> {
                ranges: &'a [(u32, u32)],
                stop:   u32,
                reg:    u32,
                live:      bool,
                allocated: bool,
                // @temp
                stmt: StmtId,
                start: u32,
            }

            let mut actives = vec![];
            let mut regs    = vec![];

            let mut mapping = vec![u32::MAX; fun.num_stmts()];

            for new_int in &intervals {
                println!("new: {:?} {}..{}", new_int.stmt, new_int.start, new_int.stop);

                // update active intervals.
                actives.retain_mut(|active: &mut ActiveInterval| {
                    println!("  active {:?} r{}({}) {}..{}", active.stmt, active.reg, active.allocated, active.start, active.stop);

                    // expire interval.
                    if active.stop <= new_int.start {
                        println!("    expired");
                        regs[active.reg as usize] = false;
                        false
                    }
                    else {
                        // active intervals.
                        if active.live {
                            debug_assert!(active.allocated);
                            debug_assert!(regs[active.reg as usize]);

                            let rng_stop = active.ranges[0].1;
                            if rng_stop <= new_int.start {
                                println!("    now inactive");
                                let next_start = active.ranges[1].0;
                                if next_start >= new_int.stop {
                                    println!("    new interval fits in hole; freeing register.");
                                    active.allocated = false;
                                    regs[active.reg as usize] = false;
                                }

                                active.ranges = &active.ranges[1..];
                                active.live   = false;
                            }
                        }
                        // inactive intervals.
                        else {
                            debug_assert!(!active.allocated || regs[active.reg as usize]);

                            // needs to activate?
                            let rng_start = active.ranges[0].0;
                            if rng_start <= new_int.start {
                                println!("    reactivating");
                                active.live      = true;
                                active.allocated = true;
                                regs[active.reg as usize] = true;
                            }
                            else {
                                // remains inactive.
                                // can free register for new interval?
                                if new_int.stop <= rng_start {
                                    if active.allocated {
                                        println!("    new interval fits in hole; freeing register.");
                                        active.allocated = false;
                                        regs[active.reg as usize] = false;
                                    }
                                }
                                else {
                                    if !active.allocated {
                                        println!("    new interval intersects next range; reclaiming register.");
                                        active.allocated = true;
                                        regs[active.reg as usize] = true;
                                    }
                                }
                            }
                        }

                        true
                    }
                });

                let reg =
                    if let Some(reg) = regs.iter().position(|used| *used == false) {
                        regs[reg] = true;
                        reg as u32
                    }
                    else {
                        let reg = regs.len();
                        regs.push(true);
                        reg as u32
                    };

                println!("-> r{}", reg);

                actives.push(ActiveInterval {
                    ranges: new_int.ranges,
                    stop:   new_int.stop,
                    reg,
                    live:      true,
                    allocated: true,

                    stmt: new_int.stmt,
                    start: new_int.start,
                });

                mapping[new_int.stmt.usize()] = reg;


                // @temp
                let mut allocated_by = vec![None; regs.len()];
                for active in &actives {
                    if active.allocated {
                        let reg = active.reg as usize;
                        assert!(allocated_by[reg].is_none());
                        allocated_by[reg] = Some(active.stmt);
                    }
                }
                for (i, used) in regs.iter().enumerate() {
                    assert!(!*used || allocated_by[i].is_some());
                }
            }

            println!("register allocation done. used {} registers.", regs.len());
            (mapping, regs.len())
        };

        // generate bytecode.
        let code = {
            let mut bcb = crate::bytecode::ByteCodeBuilder::new();

            println!("codegen");

            // @temp
            assert!(num_regs < 128);
            assert!(block_order.len() < u16::MAX as usize / 2);

            let reg = |stmt: StmtId| reg_mapping[stmt.usize()] as u8;

            let mut block_offsets = vec![u16::MAX; fun.num_blocks()];

            for (block_index, bb) in block_order.iter().enumerate() {
                println!("{}", bb);
                //block_offsets.push(bcb.current_offset() as u16);
                block_offsets[bb.usize()] = bcb.current_offset() as u16;

                fun.block_stmts(*bb, |stmt| {
                    let dst = reg(stmt.id());

                    // @temp
                    if dst == 255 && !stmt.is_terminator() {
                        return
                    }

                    // @temp: this is broken anyway.
                    if stmt.is_terminator() {
                        // phis of successors.
                        fun.block_successors(*bb, |succ| {
                            println!(" -> {}", succ);
                            fun.block_stmts_ex(succ, |stmt| {
                                if let Some(map) = fun.try_phi(stmt.id()) {
                                    let dst = reg(stmt.id());
                                    let src = reg(map.get(*bb).unwrap());
                                    println!("r{} -> r{}", src, dst);

                                    if dst != src {
                                        bcb.copy(dst as u8, src as u8);
                                    }
                                    return true;
                                }
                                false
                            });
                        });
                    }

                    let next_bb = block_order.get(block_index + 1).cloned();

                    use StmtData::*;
                    match stmt.data {
                        Copy { src } => bcb.copy(dst, reg(src)),

                        Phi { map_id: _ } => (),

                        GetLocal { src: _ } |
                        SetLocal { dst: _, src: _ } => unimplemented!(),

                        LoadNil             => bcb.load_nil(dst),
                        LoadBool  { value } => bcb.load_bool(dst, value),
                        LoatInt   { value: _ } => unimplemented!(),
                        LoadFloat { value: _ } => unimplemented!(),

                        Op1 { op: _, src: _ } => unimplemented!(),

                        Op2 { op, src1, src2 } => {
                            use self::Op2::*;
                            match op {
                                And    => { let _ = (src1, src2); unimplemented!() },
                                Or     => { let _ = (src1, src2); unimplemented!() },
                                Add    => bcb.add(dst, reg(src1), reg(src2)),
                                Sub    => bcb.sub(dst, reg(src1), reg(src2)),
                                Mul    => bcb.mul(dst, reg(src1), reg(src2)),
                                Div    => bcb.div(dst, reg(src1), reg(src2)),
                                IntDiv => unimplemented!(),
                                CmpEq  => bcb.cmp_eq(dst, reg(src1), reg(src2)),
                                CmpNe  => unimplemented!(),
                                CmpLe  => bcb.cmp_le(dst, reg(src1), reg(src2)),
                                CmpLt  => bcb.cmp_lt(dst, reg(src1), reg(src2)),
                                CmpGe  => bcb.cmp_ge(dst, reg(src1), reg(src2)),
                                CmpGt  => bcb.cmp_gt(dst, reg(src1), reg(src2)),
                                OrElse => unimplemented!(),
                            }
                        }

                        Jump { target } => {
                            if Some(target) != next_bb {
                                bcb.jump(target.usize() as u16)
                            }
                        }

                        SwitchBool { src, on_true, on_false } => {
                            if Some(on_true) != next_bb {
                                bcb.jump_true(reg(src), on_true.usize() as u16);
                            }
                            if Some(on_false) != next_bb {
                                bcb.jump_false(reg(src), on_false.usize() as u16);
                            }
                        }

                        Return { src } => {
                            bcb.ret(reg(src), 1);
                        }
                    }
                });
            }

            let mut code = bcb.build();

            let mut i = 0;
            while i < code.len() {
                let instr = &mut code[i];
                i += 1;

                use crate::bytecode::opcode::*;
                match instr.opcode() as u8 {
                    JUMP_EQ  | JUMP_LE  | JUMP_LT |
                    JUMP_NEQ | JUMP_NLE | JUMP_NLT => {
                        let extra = &mut code[i];
                        i += 1;

                        assert_eq!(extra.opcode() as u8, EXTRA);

                        let block = extra.u16() as usize;
                        extra.patch_u16(block_offsets[block]);
                    }

                    JUMP | JUMP_TRUE | JUMP_FALSE => {
                        let block = instr.u16() as usize;
                        instr.patch_u16(block_offsets[block]);
                    }

                    NOP | UNREACHABLE | COPY |
                    LOAD_NIL | LOAD_BOOL | LOAD_INT | LOAD_CONST | LOAD_ENV |
                    LIST_NEW | LIST_APPEND |
                    TABLE_NEW |
                    DEF | SET | GET | LEN |
                    ADD | SUB | MUL | DIV | INC | DEC |
                    CMP_EQ | CMP_LE | CMP_LT | CMP_GE | CMP_GT |
                    PACKED_CALL | GATHER_CALL | RET |
                    EXTRA
                    => (),

                    0 | END ..= 254 => unreachable!(),
                }
            }

            code
        };


        // temp: disassemble.
        crate::bytecode::dump(&code);

        Ok(())
    }

    pub fn compile_ast<'a>(&mut self,
        ctx: &mut Ctx<'a>, fun: &mut Function, bb: &mut BlockId,
        ast: &Ast<'a>, need_value: bool,
    ) -> CompileResult<Option<StmtId>> {
        match &ast.data {
            AstData::Nil => {
                Ok(Some(fun.add_stmt(*bb, ast, StmtData::LoadNil)))
            }

            AstData::Bool (value) => {
                Ok(Some(fun.add_stmt(*bb, ast, StmtData::LoadBool { value: *value })))
            }

            AstData::Number (value) => {
                let _ = value;
                unimplemented!()
            }

            AstData::QuotedString (value) => {
                let _ = value;
                unimplemented!()
            }

            AstData::Ident (name) => {
                Ok(Some(if let Some(decl) = ctx.find_decl(name) {
                    fun.add_stmt(*bb, ast, StmtData::GetLocal { src: decl.id })
                }
                else {
                    unimplemented!()
                }))
            }

            AstData::Tuple (tuple) => {
                let _ = tuple;
                unimplemented!()
            }

            AstData::List (list) => {
                let _ = list;
                unimplemented!()
            }

            AstData::Table (table) => {
                let _ = table;
                unimplemented!()
            }

            AstData::Block (block) => {
                self.compile_block(ctx, fun, bb, ast.source, block, need_value)
            }

            AstData::SubExpr (sub_expr) => {
                self.compile_ast(ctx, fun, bb, sub_expr, need_value)
            }

            AstData::Local (_) => {
                Err(CompileError { source: ast.source, data: CompileErrorData::UnexpectedLocal })
            }

            AstData::Op1 (op1) => {
                let src = self.compile_ast(ctx, fun, bb, &op1.child, true)?.unwrap();
                let op  = op1.kind.0;
                Ok(Some(fun.add_stmt(*bb, ast, StmtData::Op1 { op, src })))
            }

            AstData::Op2 (op2) => {
                match op2.kind {
                    ast::Op2Kind::Assign => {
                        let value = self.compile_ast(ctx, fun, bb, &op2.children[1], true)?.unwrap();
                        self.compile_assign(ctx, fun, bb, &op2.children[0], value)?;

                        Ok(if need_value {
                            Some(fun.add_stmt(*bb, ast, StmtData::LoadNil))
                        }
                        else { None })
                    }

                    ast::Op2Kind::Op2Assign(op) => {
                        let src1 = self.compile_ast(ctx, fun, bb, &op2.children[0], true)?.unwrap();
                        let src2 = self.compile_ast(ctx, fun, bb, &op2.children[1], true)?.unwrap();

                        let value = fun.add_stmt(*bb, ast, StmtData::Op2 { op, src1, src2 });
                        self.compile_assign(ctx, fun, bb, &op2.children[0], value)?;

                        Ok(if need_value {
                            Some(fun.add_stmt(*bb, ast, StmtData::LoadNil))
                        }
                        else { None })
                    }

                    ast::Op2Kind::Op2(op) => {
                        let src1 = self.compile_ast(ctx, fun, bb, &op2.children[0], true)?.unwrap();
                        let src2 = self.compile_ast(ctx, fun, bb, &op2.children[1], true)?.unwrap();
                        Ok(Some(fun.add_stmt(*bb, ast, StmtData::Op2 { op, src1, src2 })))
                    }
                }
            }

            AstData::Field (field) => {
                let _ = field;
                unimplemented!()
            }

            AstData::OptChain (opt_chain) => {
                let _ = opt_chain;
                unimplemented!()
            }

            AstData::Index (index) => {
                let _ = index;
                unimplemented!()
            }

            AstData::Call (call) => {
                let _ = call;
                unimplemented!()
            }

            AstData::If (iff) => {
                let mut bb_true = fun.new_block();
                let mut bb_false = fun.new_block();
                let after_if = fun.new_block();

                // condition.
                let cond = self.compile_ast(ctx, fun, bb, &iff.condition, true)?.unwrap();
                fun.add_stmt(*bb, ast, StmtData::SwitchBool {
                    src:      cond,
                    on_true:  bb_true,
                    on_false: bb_false,
                });
                *bb = after_if;

                // on_true
                let value_true = self.compile_ast(ctx, fun, &mut bb_true, &iff.on_true, need_value)?;
                fun.add_stmt_at(bb_true,
                    iff.on_true.source.end.to_range(),
                    StmtData::Jump { target: after_if });

                // on_false
                let (value_false, on_false_src) =
                    if let Some(on_false) = &iff.on_false {
                        let v = self.compile_ast(ctx, fun, &mut bb_false, on_false, need_value)?;
                        (v, on_false.source.end.to_range())
                    }
                    else {
                        let source = ast.source.end.to_range();
                        let v = need_value.then(|| fun.add_stmt_at(bb_false, source, StmtData::LoadNil));
                        (v, source)
                    };
                fun.add_stmt_at(bb_false, on_false_src,
                    StmtData::Jump { target: after_if });

                if need_value {
                    let result = fun.add_phi(after_if, ast, &[
                        (bb_true,  value_true.unwrap()),
                        (bb_false, value_false.unwrap()),
                    ]);
                    Ok(Some(result))
                }
                else { Ok(None) }
            }

            AstData::While (whilee) => {
                let mut bb_head  = fun.new_block();
                let mut bb_body  = fun.new_block();
                let bb_after = fun.new_block();

                fun.add_stmt(*bb, ast, StmtData::Jump { target: bb_head });
                *bb = bb_after;

                // head.
                let cond = self.compile_ast(ctx, fun, &mut bb_head, &whilee.condition, true)?.unwrap();
                fun.add_stmt(bb_head, ast, StmtData::SwitchBool {
                    src:      cond,
                    on_true:  bb_body,
                    on_false: bb_after,
                });

                // body.
                self.compile_ast(ctx, fun, &mut bb_body, &whilee.body, false)?;
                fun.add_stmt(bb_body, ast, StmtData::Jump { target: bb_head });

                if need_value {
                    let result = fun.add_stmt(bb_after, ast, StmtData::LoadNil);
                    Ok(Some(result))
                }
                else { Ok(None) }
            }

            AstData::Break => {
                unimplemented!()
            }

            AstData::Continue => {
                unimplemented!()
            }

            AstData::Return (returnn) => {
                let _ = returnn;
                unimplemented!()
            }

            AstData::Fn (fnn) => {
                let _ = fnn;
                unimplemented!()
            }
        }
    }

    pub fn compile_block<'a>(&mut self,
        ctx: &mut Ctx<'a>, fun: &mut Function, bb: &mut BlockId,
        block_source: SourceRange, block: &ast::Block<'a>, need_value: bool
    ) -> CompileResult<Option<StmtId>> {
        let scope = ctx.begin_scope();

        let mut stmts_end = block.children.len();
        if block.last_is_expr { stmts_end -= 1 }

        // visit statements.
        // handle locals.
        for i in 0..stmts_end {
            let node = &block.children[i];

            // local decls.
            if let AstData::Local(local) = &node.data {
                let lid = fun.new_local(local.name, node.source);
                ctx.add_decl(local.name, lid);

                let v =
                    if let Some(value) = &local.value {
                        self.compile_ast(ctx, fun, bb, value, true)?.unwrap()
                    }
                    else {
                        fun.add_stmt(*bb, node, StmtData::LoadNil)
                    };
                fun.add_stmt(*bb, node, StmtData::SetLocal { dst: lid, src: v });
            }
            else {
                self.compile_ast(ctx, fun, bb, node, false)?;
            }
        }

        // last statement (or expression).
        let result =
            if block.last_is_expr {
                self.compile_ast(ctx, fun, bb, &block.children[stmts_end], need_value)?
            }
            else if need_value {
                let source = block_source.end.to_range();
                // @todo: return empty tuple.
                Some(fun.add_stmt_at(*bb, source, StmtData::LoadNil))
            }
            else { None };

        ctx.end_scope(scope);
        Ok(result)
    }

    pub fn compile_assign<'a>(&mut self,
        ctx: &mut Ctx<'a>, fun: &mut Function, bb: &mut BlockId,
        ast: &Ast<'a>, value: StmtId) -> CompileResult<()>
    {
        match &ast.data {
            AstData::Ident (name) => {
                if let Some(decl) = ctx.find_decl(name) {
                    fun.add_stmt(*bb, ast, StmtData::SetLocal { dst: decl.id, src: value });
                }
                else {
                    unimplemented!()
                }

                Ok(())
            }

            AstData::Field (field) => {
                let _ = field;
                unimplemented!()
            }

            AstData::Index (index) => {
                let _ = index;
                unimplemented!()
            }

            _ => Err(CompileError::at(ast, CompileErrorData::InvalidAssignTarget)),
        }
    }
}


impl<'a> Ctx<'a> {
    fn new() -> Self {
        Ctx {
            scope: ScopeId(0),
            decls: vec![],
        }
    }

    fn add_decl(&mut self, name: &'a str, id: LocalId) {
        self.decls.push(Decl { name, id, scope: self.scope });
    }

    fn find_decl(&self, name: &str) -> Option<&Decl<'a>> {
        self.decls.iter().rev().find(|decl| decl.name == name)
    }

    fn begin_scope(&mut self) -> ScopeId {
        self.scope.0 += 1;
        self.scope
    }

    fn end_scope(&mut self, scope: ScopeId) {
        assert_eq!(self.scope, scope);
        self.decls.retain(|decl| decl.scope < self.scope);
        self.scope.0 -= 1;
    }
}


