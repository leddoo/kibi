use crate::new_parser::*;
use core::cell::Cell;

// @temp
use std::collections::HashSet;


#[derive(Debug)]
pub struct CompileError {
    pub source: SourceRange,
    pub data:   CompileErrorData,
}

impl CompileError {
    #[inline]
    pub fn at(ast: &Ast, data: CompileErrorData) -> CompileError {
        CompileError { source: ast.source, data }
    }
}


#[derive(Debug)]
pub enum CompileErrorData {
    UnexpectedLocal,
    InvalidAssignTarget,
}

pub type CompileResult<T> = Result<T, CompileError>;



pub struct Compiler {
}

impl Compiler {
    pub fn compile_chunk(&mut self, source: SourceRange, block: &ast::Block) -> CompileResult<()> {
        let mut fb = FunctionBuilder::new();
        let mut bb = fb.new_block();
        self.compile_block(&mut fb, &mut bb, source, block, false)?;

        let nil = fb.add_stmt_at(bb, source, StmtData::LoadNil);
        fb.add_stmt_at(bb, source, StmtData::Return { src: nil });

        for blocks in &fb.blocks {
            println!("{}", blocks);
        }


        let (predecessors, post_order) = {
            let mut predecessors = vec![vec![]; fb.blocks.len()];
            let mut post_order = vec![];
            let mut visited = vec![false; fb.blocks.len()];

            fn visit(fb: &FunctionBuilder, bb: BlockId,
                predecessors: &mut Vec<Vec<BlockId>>,
                post_order: &mut Vec<BlockId>,
                visited: &mut Vec<bool>,
            ) {
                let block = &fb.blocks[bb.usize()];

                block.successors(|succ| {
                    predecessors[succ.usize()].push(bb);

                    if !visited[succ.usize()] {
                        visited[succ.usize()] = true;
                        visit(fb, succ, predecessors, post_order, visited);
                    }
                });

                post_order.push(bb);
            }
            visit(&fb, BlockId::ENTRY, &mut predecessors, &mut post_order, &mut visited);

            for bb in &post_order {
                if !bb.is_entry() {
                    assert!(predecessors[bb.usize()].len() > 0);
                }
            }

            (predecessors, post_order)
        };

        let post_indices = {
            let mut indices = vec![usize::MAX; fb.blocks.len()];
            for (index, bb) in post_order.iter().enumerate() {
                indices[bb.usize()] = index;
            }
            indices
        };

        let immediate_dominators = {
            let mut doms = vec![None; fb.blocks.len()];

            #[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
            struct PostIndex(usize);

            impl PostIndex {
                #[inline(always)]
                fn usize(self) -> usize { self.0 }
            }

            let bb0 = PostIndex(post_indices[BlockId::ENTRY.usize()]);
            doms[bb0.usize()] = Some(bb0);

            let mut changed = true;
            while changed {
                changed = false;

                for bb_id in post_order.iter().rev() {
                    if bb_id.is_entry() { continue }

                    let preds = &predecessors[bb_id.usize()];
                    let bb = PostIndex(post_indices[bb_id.usize()]);

                    let mut new_dom = PostIndex(post_indices[preds[0].usize()]);

                    for pred_id in preds.iter().skip(1) {
                        let pred = PostIndex(post_indices[pred_id.usize()]);

                        // intersect.
                        if doms[pred.usize()].is_some() {
                            let mut x = new_dom;
                            let mut y = pred;

                            while x != y {
                                while x < y {
                                    x = doms[x.usize()].unwrap();
                                }
                                while y < x {
                                    y = doms[y.usize()].unwrap();
                                }
                            }

                            new_dom = x;
                        }
                    }

                    if doms[bb.usize()] != Some(new_dom) {
                        doms[bb.usize()] = Some(new_dom);
                        changed = true;
                    }
                }
            }

            fb.blocks.iter()
                .map(|block| {
                    let bb = block.id;
                    let pi = post_indices[bb.usize()];
                    let idomi = doms[pi].unwrap();
                    let idom  = post_order[idomi.usize()];
                    idom
                })
                .collect::<Vec<BlockId>>()
        };

        let idom_tree = {
            let mut tree = vec![vec![]; fb.blocks.len()];

            for block in fb.blocks.iter().skip(1) {
                let bb = block.id;
                let idom = immediate_dominators[bb.usize()];
                tree[idom.usize()].push(bb);
            }

            tree
        };

        println!("tree {:?}", idom_tree);

        let dom_frontiers = {
            let mut dfs = vec![vec![]; fb.blocks.len()];

            for block in fb.blocks.iter() {
                let bb = block.id;

                let preds = &predecessors[bb.usize()];
                if preds.len() < 2 { continue }

                let idom = immediate_dominators[bb.usize()];
                for pred in preds {
                    let mut at = *pred;
                    while at != idom {
                        let df = &mut dfs[at.usize()];
                        if !df.contains(&bb) {
                            df.push(bb);
                        }
                        at = immediate_dominators[at.usize()];
                    }
                }
            }

            dfs
        };

        // find phis
        let mut phis = {
            let mut visited: HashSet<(BlockId, LocalId)> = HashSet::new();

            let mut stack = vec![];
            for block in &fb.blocks {
                for stmt in &block.statements {
                    let StmtData::SetLocal { dst: lid, src: _ } = stmt.get().data else { continue };

                    let key = (block.id, lid);
                    if !visited.contains(&key) {
                        visited.insert(key);
                        stack.push(key);
                    }
                }
            }

            let mut phis: Vec<Vec<(LocalId, Vec<(BlockId, Option<StmtRef>)>, StmtRef)>>
                = vec![vec![]; fb.blocks.len()];

            while let Some((from_bb, lid)) = stack.pop() {
                for to_bb in dom_frontiers[from_bb.usize()].iter() {
                    let to_bb = *to_bb;
                    let to_phis = &mut phis[to_bb.usize()];

                    let needs_phi_for_lid = to_phis.iter().find(|(l, _, _)| *l == lid).is_none();
                    if needs_phi_for_lid {
                        let preds = &predecessors[to_bb.usize()];

                        let map = preds.iter().map(|p| (*p, None)).collect();
                        let stmt = fb.new_stmt_at(SourceRange::null(), StmtData::Phi { map: &[] });
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

        println!("{:?}", phis);

        // rename vars.
        {
            fn visit<'a>(bb: BlockId, mut new_names: Vec<Option<StmtRef<'a>>>,
                phis: &mut Vec<Vec<(LocalId, Vec<(BlockId, Option<StmtRef<'a>>)>, StmtRef<'a>)>>,
                fb: &FunctionBuilder<'a>, idom_tree: &Vec<Vec<BlockId>>,
            ) {
                let block = &fb.blocks[bb.usize()];

                // update var names.
                for (lid, _map, stmt) in &phis[bb.usize()] {
                    new_names[lid.usize()] = Some(*stmt)
                }
                for stmt_ref in block.statements.iter() {
                    let stmt_ref = *stmt_ref;
                    let mut stmt = stmt_ref.get();

                    if let StmtData::GetLocal { src } = stmt.data {
                        let new_name = new_names[src.usize()].unwrap();
                        stmt.data = StmtData::Copy { src: new_name };
                        stmt_ref.set(stmt);
                        new_names[src.usize()] = Some(stmt_ref);
                    }

                    if let StmtData::SetLocal { dst, src } = stmt.data {
                        stmt.data = StmtData::Copy { src };
                        stmt_ref.set(stmt);
                        new_names[dst.usize()] = Some(stmt_ref);
                    }
                }

                // propagate to successors.
                block.successors(|succ| {
                    for (l, map, _) in &mut phis[succ.usize()] {
                        let entry = map.iter_mut().find(|(from, _)| *from == bb).unwrap();
                        assert!(entry.1.is_none());

                        entry.1 = Some(new_names[l.usize()].unwrap());
                    }
                });

                // propagate to dominated blocks.
                for d in idom_tree[bb.usize()].iter() {
                    visit(*d, new_names.clone(), phis, fb, idom_tree);
                }
            }

            let new_names = vec![None; fb.next_local.usize()];
            visit(BlockId::ENTRY, new_names, &mut phis, &fb, &idom_tree);
        }

        // insert phis.
        {
            for (bb_index, phis) in phis.into_iter().enumerate() {
                let block = &mut fb.blocks[bb_index];

                let phis = phis.iter().map(|(_lid, map, stmt_ref)| {
                    let map = Vec::leak(map.iter().map(|(bb, stmt)|
                        Cell::new((*bb, stmt.unwrap()))
                    ).collect::<Vec<_>>());

                    let mut stmt = stmt_ref.get();
                    stmt.data = StmtData::Phi { map };
                    stmt_ref.set(stmt);
                    *stmt_ref
                }).collect::<Vec<StmtRef>>();

                block.statements.splice(0..0, phis);
            }
        }

        println!("local2reg done");
        for block in &fb.blocks {
            println!("{}", block);
        }


        // copy propagation.
        {
            fn visit(bb: BlockId, fb: &mut FunctionBuilder, idom_tree: &Vec<Vec<BlockId>>) {
                let block = &mut fb.blocks[bb.usize()];

                // inline copies.
                block.replace_args(|arg| {
                    if let StmtData::Copy { src } = arg.get().data {
                        *arg = src;
                    }
                });

                // propagate to dominated blocks.
                for d in idom_tree[bb.usize()].iter() {
                    visit(*d, fb, idom_tree);
                }
            }
            visit(BlockId::ENTRY, &mut fb, &idom_tree);
        }

        println!("copy propagation done");
        for block in &fb.blocks {
            println!("{}", block);
        }

        // dead copy elimination.
        {
            let mut visited = vec![false; fb.stmts.len()];

            for block in &fb.blocks {
                block.args(|arg| visited[arg.get().id.usize()] = true);
            }

            for block in &mut fb.blocks {
                block.statements.retain(|stmt_ref| {
                    let stmt = stmt_ref.get();
                    visited[stmt.id.usize()] || !stmt.is_copy()
                });
            }
        }

        println!("dead copy elim done");
        for block in &fb.blocks {
            println!("{}", block);
        }

        let block_order = {
            fn visit(bb: BlockId, order: &mut Vec<BlockId>, visited: &mut Vec<bool>,
                fb: &FunctionBuilder, idom: &Vec<BlockId>, idom_tree: &Vec<Vec<BlockId>>,
            ) {
                assert!(!visited[bb.usize()]);
                visited[bb.usize()] = true;
                order.push(bb);

                let block = &fb.blocks[bb.usize()];
                block.successors(|succ| {
                    if !visited[succ.usize()] && idom[succ.usize()] == bb {
                        visit(succ, order, visited, fb, idom, idom_tree);
                    }
                });

                for child in &idom_tree[bb.usize()] {
                    if !visited[child.usize()] {
                        visit(*child, order, visited, fb, idom, idom_tree);
                    }
                }
            }

            let mut order   = vec![];
            let mut visited = vec![false; fb.blocks.len()];
            visit(BlockId::ENTRY, &mut order, &mut visited, &fb, &immediate_dominators, &idom_tree);
            order
        };

        let (block_begins, stmt_indices) = {
            let mut block_begins = vec![u32::MAX; fb.blocks.len()];
            let mut stmt_indices = vec![u32::MAX; fb.stmts.len()];

            let mut cursor = 0;
            for bb in &block_order {
                let block = &fb.blocks[bb.usize()];

                let block_begin = cursor;
                cursor += block.statements.len();

                block_begins[block.id.usize()] = block_begin as u32;

                for (i, stmt) in block.statements.iter().enumerate() {
                    stmt_indices[stmt.id().usize()] = (block_begin + i) as u32;
                }
            }
            block_begins.push(cursor as u32);

            (block_begins, stmt_indices)
        };

        println!("block order:");
        for bb in &block_order {
            let block = &fb.blocks[bb.usize()];
            println!("{}", block.id);

            for stmt in &block.statements {
                println!("  ({}) {}", stmt_indices[stmt.id().usize()], *stmt);
            }
        }


        // live intervals.
        let intervals = {
            let mut bb_gen  = Vec::with_capacity(fb.blocks.len());
            let mut bb_kill = Vec::with_capacity(fb.blocks.len());

            fn pretty(set: &Vec<bool>) -> Vec<usize> {
                set.iter().enumerate()
                .filter_map(|(i, v)| v.then(|| i))
                .collect()
            }

            for block in &fb.blocks {
                let mut gen  = vec![false; fb.stmts.len()];
                let mut kill = vec![false; fb.stmts.len()];

                // statements in reverse.
                for stmt_ref in block.statements.iter().rev() {
                    let stmt = stmt_ref.get();

                    if stmt.has_value() {
                        kill[stmt.id.usize()] = true;
                        gen [stmt.id.usize()] = false;
                    }

                    if !stmt.is_phi() {
                        stmt.args(|arg| {
                            gen[arg.id().usize()] = true;
                        });
                    }
                }

                // println!("{}:", block.id);
                // println!(" gen:  {:?}", pretty(&gen));
                // println!(" kill: {:?}", pretty(&kill));

                bb_gen.push(gen);
                bb_kill.push(kill);
            }


            let mut bb_live_in  = vec![vec![false; fb.stmts.len()]; fb.blocks.len()];
            let mut bb_live_out = vec![vec![false; fb.stmts.len()]; fb.blocks.len()];
            let mut changed = true;
            while changed {
                changed = false;

                println!("live iter");

                for bb in &post_order {
                    let block = &fb.blocks[bb.usize()];
                    let gen   = &bb_gen[bb.usize()];
                    let kill  = &bb_kill[bb.usize()];

                    let mut new_live_out = vec![false; fb.stmts.len()];
                    block.successors(|succ| {
                        // live_in.
                        for (i, live) in bb_live_in[succ.usize()].iter().enumerate() {
                            if *live {
                                new_live_out[i] = true;
                            }
                        }

                        // phis.
                        for stmt_ref in &fb.blocks[succ.usize()].statements {
                            if let StmtData::Phi { map } = stmt_ref.get().data {
                                let entry = map.iter().find(|e| e.get().0 == block.id).unwrap();
                                let var = entry.get().1;
                                new_live_out[var.id().usize()] = true;
                            }
                            else { break }
                        }
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


            let mut intervals = vec![vec![]; fb.stmts.len()];
            for bb in block_order.iter() {
                //let live_in  = &bb_live_in[bb.usize()];
                let live_out = &bb_live_out[bb.usize()];

                let block       = &fb.blocks[bb.usize()];
                let block_begin = block_begins[bb.usize()];
                let block_end   = block_begin + block.statements.len() as u32;

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
                for stmt_ref in block.statements.iter().rev() {
                    let stmt = stmt_ref.get();

                    if stmt.has_value() {
                        let start = stmt_indices[stmt.id.usize()];
                        kill(stmt.id, start, &mut live, &mut intervals)
                    }

                    if !stmt.is_phi() {
                        stmt.args(|arg| {
                            let stop = stmt_indices[stmt.id.usize()];
                            gen(arg.id(), stop, &mut live);
                        });
                    }
                }

                for id in 0..fb.stmts.len() {
                    let start = block_begin;
                    kill(StmtId(id as u32), start, &mut live, &mut intervals);
                }
            }

            println!("live intervals");
            for (bb, int) in intervals.iter().enumerate() {
                println!(" {}: {:?}", bb, int);
            }

            intervals
        };


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
                        stmt: StmtId(i as u32),
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

            let mut mapping = vec![u32::MAX; fb.stmts.len()];

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

            let reg = |stmt: StmtRef| reg_mapping[stmt.id().usize()] as u8;

            let mut block_offsets = vec![u16::MAX; fb.blocks.len()];

            for (block_index, bb) in block_order.iter().enumerate() {
                println!("{}", bb);
                //block_offsets.push(bcb.current_offset() as u16);
                block_offsets[bb.usize()] = bcb.current_offset() as u16;

                let block = &fb.blocks[bb.usize()];

                for stmt in &block.statements[..block.statements.len()-1] {
                    let dst = reg(*stmt);

                    // @temp
                    if dst == 255 {
                        continue;
                    }

                    use StmtData::*;
                    match stmt.get().data {
                        Copy { src } => bcb.copy(dst, reg(src)),

                        Phi { map: _ } => (),

                        GetLocal { src: _ } |
                        SetLocal { dst: _, src: _ } => unimplemented!(),

                        LoadNil             => bcb.load_nil(dst),
                        LoadBool  { value } => bcb.load_bool(dst, value),
                        LoatInt   { value: _ } => unimplemented!(),
                        LoadFloat { value: _ } => unimplemented!(),

                        Not    { src: _ } => unimplemented!(),
                        BitNot { src: _ } => unimplemented!(),
                        Neg    { src: _ } => unimplemented!(),
                        Plus   { src: _ } => unimplemented!(),

                        And         { src1, src2 } => { let _ = (src1, src2); unimplemented!() },
                        Or          { src1, src2 } => { let _ = (src1, src2); unimplemented!() },
                        Add         { src1, src2 } => bcb.add(dst, reg(src1), reg(src2)),
                        Sub         { src1, src2 } => bcb.sub(dst, reg(src1), reg(src2)),
                        Mul         { src1, src2 } => bcb.mul(dst, reg(src1), reg(src2)),
                        Div         { src1, src2 } => bcb.div(dst, reg(src1), reg(src2)),
                        IntDiv      { src1: _, src2: _ } => unimplemented!(),
                        CmpEq       { src1, src2 } => bcb.cmp_eq(dst, reg(src1), reg(src2)),
                        CmpNe       { src1: _, src2: _ } => unimplemented!(),
                        CmpLe       { src1, src2 } => bcb.cmp_le(dst, reg(src1), reg(src2)),
                        CmpLt       { src1, src2 } => bcb.cmp_lt(dst, reg(src1), reg(src2)),
                        CmpGe       { src1, src2 } => bcb.cmp_ge(dst, reg(src1), reg(src2)),
                        CmpGt       { src1, src2 } => bcb.cmp_gt(dst, reg(src1), reg(src2)),
                        OrElse      { src1: _, src2: _ } => unimplemented!(),

                        Jump       { target: _ } |
                        SwitchBool { src: _, on_true: _, on_false: _ } |
                        Return     { src: _ } => unreachable!("multiple terminators")
                    }
                }

                // phis of successors.
                block.successors(|succ| {
                    println!(" -> {}", succ);
                    for stmt in &fb.blocks[succ.usize()].statements {
                        if let StmtData::Phi { map } = stmt.get().data {
                            let dst = reg(*stmt);

                            let entry = map.iter().find(|e| e.get().0 == block.id).unwrap();
                            let src = reg(entry.get().1);
                            println!("r{} -> r{}", src, dst);

                            if dst != src {
                                bcb.copy(dst as u8, src as u8);
                            }
                        }
                    }
                });


                let terminator = block.statements.last().unwrap();
                assert!(terminator.get().is_terminator());

                let next_bb = block_order.get(block_index + 1);

                use StmtData::*;
                match &terminator.get().data {
                    Jump { target } => {
                        if Some(target) != next_bb {
                            bcb.jump(target.0 as u16)
                        }
                    }

                    SwitchBool { src, on_true, on_false } => {
                        if Some(on_true) != next_bb {
                            bcb.jump_true(reg(*src), on_true.0 as u16);
                        }
                        if Some(on_false) != next_bb {
                            bcb.jump_false(reg(*src), on_false.0 as u16);
                        }
                    }

                    Return { src } => {
                        bcb.ret(reg(*src), 1);
                    }

                    _ => (),
                }
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
        {
            let mut pc = 0;
            while pc < code.len() {
                print!("{:02}: ", pc);

                let instr = code[pc];
                pc += 1;

                let mut instr_extra = || {
                    let extra = code[pc];
                    pc += 1;
                    assert_eq!(extra.opcode() as u8, crate::bytecode::opcode::EXTRA);
                    extra
                };

                use crate::bytecode::opcode::*;
                match instr.opcode() as u8 {
                    NOP => (),

                    UNREACHABLE => {
                        println!("  unreachable");
                        break;
                    }


                    COPY => {
                        let (dst, src) = instr.c2();
                        println!("  copy r{}, r{}", dst, src);
                    }


                    LOAD_NIL => {
                        let dst = instr.c1();
                        println!("  load_nil r{}", dst);
                    }

                    LOAD_BOOL => {
                        let (dst, value) = instr.c1b();
                        println!("  load_bool r{}, {}", dst, value);
                    }

                    LOAD_INT => {
                        let (dst, value) = instr.c1u16();
                        let value = value as u16 as i16 as f64;
                        println!("  load_int r{}, {}", dst, value);
                    }

                    LOAD_CONST => {
                        let (dst, index) = instr.c1u16();
                        println!("  load_const r{}, c{}", dst, index);
                    }

                    LOAD_ENV => {
                        let dst = instr.c1();
                        println!("  load_env r{}", dst);
                    }


                    LIST_NEW => {
                        let dst = instr.c1();
                        println!("  list_new r{}", dst);
                    }

                    LIST_APPEND => {
                        let (list, value) = instr.c2();
                        println!("  list_append r{}, r{}", list, value);
                    }


                    TABLE_NEW => {
                        let dst = instr.c1();
                        println!("  table_new r{}", dst);
                    }


                    DEF => {
                        // @todo-speed: remove checks.
                        let (obj, key, value) = instr.c3();
                        println!("  def r{}, r{}, r{}", obj, key, value);
                    }

                    SET => {
                        let (obj, key, value) = instr.c3();
                        println!("  set r{}, r{}, r{}", obj, key, value);
                    }

                    GET => {
                        let (dst, obj, key) = instr.c3();
                        println!("  get r{}, r{}, r{}", dst, obj, key);
                    }

                    LEN => {
                        let (dst, obj) = instr.c2();
                        println!("  len r{}, r{}", dst, obj);
                    }


                    ADD => {
                        let (dst, src1, src2) = instr.c3();
                        println!("  add r{}, r{}, r{}", dst, src1, src2);
                    }

                    SUB => {
                        let (dst, src1, src2) = instr.c3();
                        println!("  sub r{}, r{}, r{}", dst, src1, src2);
                    }

                    MUL => {
                        let (dst, src1, src2) = instr.c3();
                        println!("  mul r{}, r{}, r{}", dst, src1, src2);
                    }

                    DIV => {
                        let (dst, src1, src2) = instr.c3();
                        println!("  div r{}, r{}, r{}", dst, src1, src2);
                    }

                    INC => {
                        let dst = instr.c1();
                        println!("  inc r{}", dst);
                    }

                    DEC => {
                        let dst = instr.c1();
                        println!("  dec r{}", dst);
                    }


                    CMP_EQ => {
                        let (dst, src1, src2) = instr.c3();
                        println!("  cmp_eq r{}, r{}, r{}", dst, src1, src2);
                    }

                    CMP_LE => {
                        let (dst, src1, src2) = instr.c3();
                        println!("  cmp_le r{}, r{}, r{}", dst, src1, src2);
                    }

                    CMP_LT => {
                        let (dst, src1, src2) = instr.c3();
                        println!("  cmp_lt r{}, r{}, r{}", dst, src1, src2);
                    }

                    CMP_GE => {
                        let (dst, src1, src2) = instr.c3();
                        println!("  cmp_ge r{}, r{}, r{}", dst, src1, src2);
                    }

                    CMP_GT => {
                        let (dst, src1, src2) = instr.c3();
                        println!("  cmp_gt r{}, r{}, r{}", dst, src1, src2);
                    }


                    JUMP => {
                        let target = instr.u16();
                        println!("  jump {}", target);
                    }

                    JUMP_TRUE => {
                        let (src, target) = instr.c1u16();
                        println!("  jump_true r{}, {}", src, target);
                    }

                    JUMP_FALSE => {
                        let (src, target) = instr.c1u16();
                        println!("  jump_false r{}, {}", src, target);
                    }

                    JUMP_EQ => {
                        let (src1, src2) = instr.c2();
                        let target = instr_extra().u16();
                        println!("  jump_eq r{}, r{}, {}", src1, src2, target);
                    }

                    JUMP_LE => {
                        let (src1, src2) = instr.c2();
                        let target = instr_extra().u16();
                        println!("  jump_le r{}, r{}, {}", src1, src2, target);
                    }

                    JUMP_LT => {
                        let (src1, src2) = instr.c2();
                        let target = instr_extra().u16();
                        println!("  jump_le r{}, r{}, {}", src1, src2, target);
                    }

                    JUMP_NEQ => {
                        let (src1, src2) = instr.c2();
                        let target = instr_extra().u16();
                        println!("  jump_le r{}, r{}, {}", src1, src2, target);
                    }

                    JUMP_NLE => {
                        let (src1, src2) = instr.c2();
                        let target = instr_extra().u16();
                        println!("  jump_nle r{}, r{}, {}", src1, src2, target);
                    }

                    JUMP_NLT => {
                        let (src1, src2) = instr.c2();
                        let target = instr_extra().u16();
                        println!("  jump_nlt r{}, r{}, {}", src1, src2, target);
                    }


                    PACKED_CALL => {
                        unimplemented!()
                    }

                    GATHER_CALL => {
                        unimplemented!()
                    }

                    RET => {
                        let (rets, num_rets) = instr.c2();
                        println!("  ret r{}, {}", rets, num_rets);
                    }

                    // @todo-speed: this inserts a check to reduce dispatch table size.
                    //  may want an unreachable_unchecked() in release.
                    0 | END ..= 255 => unreachable!()
                }
            }
        }

        Ok(())
    }

    pub fn compile_ast<'a>(&mut self, fb: &mut FunctionBuilder<'a>, bb: &mut BlockId,
        ast: &Ast<'a>, need_value: bool) -> CompileResult<Option<StmtRef<'a>>>
    {
        match &ast.data {
            AstData::Nil => {
                Ok(Some(fb.add_stmt(*bb, ast, StmtData::LoadNil)))
            }

            AstData::Bool (value) => {
                Ok(Some(fb.add_stmt(*bb, ast, StmtData::LoadBool { value: *value })))
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
                Ok(Some(if let Some(decl) = fb.find_decl(name) {
                    fb.add_stmt(*bb, ast, StmtData::GetLocal { src: decl.id })
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
                self.compile_block(fb, bb, ast.source, block, need_value)
            }

            AstData::SubExpr (sub_expr) => {
                self.compile_ast(fb, bb, sub_expr, need_value)
            }

            AstData::Local (_) => {
                Err(CompileError { source: ast.source, data: CompileErrorData::UnexpectedLocal })
            }

            AstData::Op1 (op) => {
                let src = self.compile_ast(fb, bb, &op.child, true)?.unwrap();
                Ok(Some(fb.add_stmt(*bb, ast, match op.kind {
                    ast::Op1Kind::Not    => StmtData::Not    { src },
                    ast::Op1Kind::BitNot => StmtData::BitNot { src },
                    ast::Op1Kind::Neg    => StmtData::Neg    { src },
                    ast::Op1Kind::Plus   => StmtData::Plus   { src },
                })))
            }

            AstData::Op2 (op) => {
                use ast::Op2Kind as OpKind;

                if op.kind == OpKind::Assign {
                    let value = self.compile_ast(fb, bb, &op.children[1], true)?.unwrap();
                    self.compile_assign(fb, bb, &op.children[0], value)?;

                    Ok(if need_value {
                        Some(fb.add_stmt(*bb, ast, StmtData::LoadNil))
                    }
                    else { None })
                }
                else if op.kind.is_comp_assign() {
                    let src1 = self.compile_ast(fb, bb, &op.children[0], true)?.unwrap();
                    let src2 = self.compile_ast(fb, bb, &op.children[1], true)?.unwrap();

                    let value = fb.add_stmt(*bb, ast, match op.kind {
                        OpKind::AddAssign     => StmtData::Add    { src1, src2 },
                        OpKind::SubAssign     => StmtData::Sub    { src1, src2 },
                        OpKind::MulAssign     => StmtData::Mul    { src1, src2 },
                        OpKind::DivAssign     => StmtData::Div    { src1, src2 },
                        OpKind::IntDivAssign  => StmtData::IntDiv { src1, src2 },
                        OpKind::OrElseAssign  => StmtData::OrElse { src1, src2 },

                        _ => unreachable!(),
                    });

                    self.compile_assign(fb, bb, &op.children[0], value)?;

                    Ok(if need_value {
                        Some(fb.add_stmt(*bb, ast, StmtData::LoadNil))
                    }
                    else { None })
                }
                else {
                    let src1 = self.compile_ast(fb, bb, &op.children[0], true)?.unwrap();
                    let src2 = self.compile_ast(fb, bb, &op.children[1], true)?.unwrap();

                    Ok(Some(fb.add_stmt(*bb, ast, match op.kind {
                        OpKind::And     => StmtData::And    { src1, src2 },
                        OpKind::Or      => StmtData::Or     { src1, src2 },
                        OpKind::Add     => StmtData::Add    { src1, src2 },
                        OpKind::Sub     => StmtData::Sub    { src1, src2 },
                        OpKind::Mul     => StmtData::Mul    { src1, src2 },
                        OpKind::Div     => StmtData::Div    { src1, src2 },
                        OpKind::IntDiv  => StmtData::IntDiv { src1, src2 },
                        OpKind::CmpEq   => StmtData::CmpEq  { src1, src2 },
                        OpKind::CmpNe   => StmtData::CmpNe  { src1, src2 },
                        OpKind::CmpLe   => StmtData::CmpLe  { src1, src2 },
                        OpKind::CmpLt   => StmtData::CmpLt  { src1, src2 },
                        OpKind::CmpGe   => StmtData::CmpGe  { src1, src2 },
                        OpKind::CmpGt   => StmtData::CmpGt  { src1, src2 },
                        OpKind::OrElse  => StmtData::OrElse { src1, src2 },

                        OpKind::Assign |
                        OpKind::AddAssign | OpKind::SubAssign | OpKind::MulAssign |
                        OpKind::DivAssign | OpKind::IntDivAssign |
                        OpKind::OrElseAssign => unreachable!()
                    })))
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
                let mut bb_true = fb.new_block();
                let mut bb_false = fb.new_block();
                let after_if = fb.new_block();

                // condition.
                let cond = self.compile_ast(fb, bb, &iff.condition, true)?.unwrap();
                fb.add_stmt(*bb, ast, StmtData::SwitchBool {
                    src:      cond,
                    on_true:  bb_true,
                    on_false: bb_false,
                });
                *bb = after_if;

                // on_true
                let value_true = self.compile_ast(fb, &mut bb_true, &iff.on_true, need_value)?;
                fb.add_stmt_at(bb_true,
                    iff.on_true.source.end.to_range(),
                    StmtData::Jump { target: after_if });

                // on_false
                let (value_false, on_false_src) =
                    if let Some(on_false) = &iff.on_false {
                        let v = self.compile_ast(fb, &mut bb_false, on_false, need_value)?;
                        (v, on_false.source.end.to_range())
                    }
                    else {
                        let source = ast.source.end.to_range();
                        let v = need_value.then(|| fb.add_stmt_at(bb_false, source, StmtData::LoadNil));
                        (v, source)
                    };
                fb.add_stmt_at(bb_false, on_false_src,
                    StmtData::Jump { target: after_if });

                if need_value {
                    let map = Box::leak(Box::new([
                        Cell::new((bb_true,  value_true.unwrap())),
                        Cell::new((bb_false, value_false.unwrap())),
                    ]));
                    let result = fb.add_stmt(after_if, ast, StmtData::Phi { map });
                    Ok(Some(result))
                }
                else { Ok(None) }
            }

            AstData::While (whilee) => {
                let mut bb_head  = fb.new_block();
                let mut bb_body  = fb.new_block();
                let bb_after = fb.new_block();

                fb.add_stmt(*bb, ast, StmtData::Jump { target: bb_head });
                *bb = bb_after;

                // head.
                let cond = self.compile_ast(fb, &mut bb_head, &whilee.condition, true)?.unwrap();
                fb.add_stmt(bb_head, ast, StmtData::SwitchBool {
                    src:      cond,
                    on_true:  bb_body,
                    on_false: bb_after,
                });

                // body.
                self.compile_ast(fb, &mut bb_body, &whilee.body, false)?;
                fb.add_stmt(bb_body, ast, StmtData::Jump { target: bb_head });

                if need_value {
                    let result = fb.add_stmt(bb_after, ast, StmtData::LoadNil);
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

    pub fn compile_block<'a>(&mut self, fb: &mut FunctionBuilder<'a>, bb: &mut BlockId,
        block_source: SourceRange, block: &ast::Block<'a>, need_value: bool) -> CompileResult<Option<StmtRef<'a>>>
    {
        let scope = fb.begin_scope();

        let mut stmts_end = block.children.len();
        if block.last_is_expr { stmts_end -= 1 }

        // visit statements.
        // handle locals.
        for i in 0..stmts_end {
            let node = &block.children[i];

            // local decls.
            if let AstData::Local(local) = &node.data {
                let lid = fb.add_decl(local.name);

                let v = 
                    if let Some(value) = &local.value {
                        self.compile_ast(fb, bb, value, true)?.unwrap()
                    }
                    else {
                        fb.add_stmt(*bb, node, StmtData::LoadNil)
                    };
                fb.add_stmt(*bb, node, StmtData::SetLocal { dst: lid, src: v });
            }
            else {
                self.compile_ast(fb, bb, node, false)?;
            }
        }

        // last statement (or expression).
        let result =
            if block.last_is_expr {
                self.compile_ast(fb, bb, &block.children[stmts_end], need_value)?
            }
            else if need_value {
                let source = block_source.end.to_range();
                // @todo: return empty tuple.
                Some(fb.add_stmt_at(*bb, source, StmtData::LoadNil))
            }
            else { None };

        fb.end_scope(scope);
        Ok(result)
    }

    pub fn compile_assign<'a>(&mut self, fb: &mut FunctionBuilder<'a>, bb: &mut BlockId,
        ast: &Ast<'a>, value: StmtRef<'a>) -> CompileResult<()>
    {
        match &ast.data {
            AstData::Ident (name) => {
                if let Some(decl) = fb.find_decl(name) {
                    fb.add_stmt(*bb, ast, StmtData::SetLocal { dst: decl.id, src: value });
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



#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
pub struct StmtId(u32);

impl StmtId {
    #[inline(always)]
    pub fn usize(self) -> usize { self.0 as usize }
}


#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct StmtRef<'a>(&'a Cell<Stmt<'a>>);

impl<'a> StmtRef<'a> {
    #[inline(always)]
    pub fn id(self) -> StmtId { self.get().id }
}

impl<'a> core::fmt::Debug for StmtRef<'a> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.get().fmt(f)
    }
}

impl<'a> PartialEq for StmtRef<'a> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        core::ptr::eq(self.0, other.0)
    }
}

impl<'a> Eq for StmtRef<'a> {}

impl<'a> core::hash::Hash for StmtRef<'a> {
    #[inline]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        core::ptr::hash(self.0, state)
    }
}

impl<'a> core::ops::Deref for StmtRef<'a> {
    type Target = Cell<Stmt<'a>>;
    #[inline]
    fn deref(&self) -> &Self::Target { self.0 }
}

impl<'a> core::fmt::Display for StmtRef<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let stmt = self.get();

        write!(f, "r{} := ", stmt.id.0)?;

        use StmtData::*;
        match &stmt.data {
            Copy { src } => { write!(f, "copy r{}", src.get().id.0) }

            Phi { map } => {
                write!(f, "phi {{")?;
                for (i, (bb, src)) in map.iter().map(|e| e.get()).enumerate() {
                    write!(f, "{}: r{}", bb, src.get().id.0)?;

                    if i < map.len() - 1 { write!(f, ", ")?; }
                }
                write!(f, "}}")
            }

            GetLocal { src }      => { write!(f, "get_local {}", src) }
            SetLocal { dst, src } => { write!(f, "set_local {}, r{}", dst, src.get().id.0) }

            LoadNil             => { write!(f, "load_nil") }
            LoadBool  { value } => { write!(f, "load_bool {}", value) }
            LoatInt   { value } => { write!(f, "load_int {}", value) }
            LoadFloat { value } => { write!(f, "load_float {}", value) }

            Not    { src } => { write!(f, "not r{}",     src.get().id.0) }
            BitNot { src } => { write!(f, "bit_not r{}", src.get().id.0) }
            Neg    { src } => { write!(f, "neg r{}",     src.get().id.0) }
            Plus   { src } => { write!(f, "plus r{}",    src.get().id.0) }

            And    { src1, src2 } => { write!(f, "and r{}, r{}",     src1.get().id.0, src2.get().id.0) }
            Or     { src1, src2 } => { write!(f, "or r{}, r{}",      src1.get().id.0, src2.get().id.0) }
            Add    { src1, src2 } => { write!(f, "add r{}, r{}",     src1.get().id.0, src2.get().id.0) }
            Sub    { src1, src2 } => { write!(f, "sub r{}, r{}",     src1.get().id.0, src2.get().id.0) }
            Mul    { src1, src2 } => { write!(f, "mul r{}, r{}",     src1.get().id.0, src2.get().id.0) }
            Div    { src1, src2 } => { write!(f, "div r{}, r{}",     src1.get().id.0, src2.get().id.0) }
            IntDiv { src1, src2 } => { write!(f, "int_div r{}, r{}", src1.get().id.0, src2.get().id.0) }
            CmpEq  { src1, src2 } => { write!(f, "cmp_eq r{}, r{}",  src1.get().id.0, src2.get().id.0) }
            CmpNe  { src1, src2 } => { write!(f, "cmp_ne r{}, r{}",  src1.get().id.0, src2.get().id.0) }
            CmpLe  { src1, src2 } => { write!(f, "cmp_le r{}, r{}",  src1.get().id.0, src2.get().id.0) }
            CmpLt  { src1, src2 } => { write!(f, "cmp_lt r{}, r{}",  src1.get().id.0, src2.get().id.0) }
            CmpGe  { src1, src2 } => { write!(f, "cmp_ge r{}, r{}",  src1.get().id.0, src2.get().id.0) }
            CmpGt  { src1, src2 } => { write!(f, "cmp_gt r{}, r{}",  src1.get().id.0, src2.get().id.0) }
            OrElse { src1, src2 } => { write!(f, "or_else r{}, r{}", src1.get().id.0, src2.get().id.0) }

            Jump       { target }                 => { write!(f, "jump {}", target) }
            SwitchBool { src, on_true, on_false } => { write!(f, "switch_bool r{}, {}, {}", src.get().id.0, on_true, on_false) }
            Return     { src }                    => { write!(f, "return r{}", src.get().id.0) }
        }
    }
}


#[derive(Clone, Copy, Debug)]
pub struct Stmt<'a> {
    pub id:     StmtId,
    pub source: SourceRange,
    pub data:   StmtData<'a>,
}

impl<'a> core::ops::Deref for Stmt<'a> {
    type Target = StmtData<'a>;
    #[inline(always)]
    fn deref(&self) -> &Self::Target { &self.data }
}

impl<'a> core::ops::DerefMut for Stmt<'a> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut Self::Target { &mut self.data }
}


#[derive(Clone, Copy, Debug)]
pub enum StmtData<'a> {
    Copy        { src: StmtRef<'a> },

    Phi         { map: &'a [Cell<(BlockId, StmtRef<'a>)>] },

    GetLocal    { src: LocalId },
    SetLocal    { dst: LocalId, src: StmtRef<'a> },

    LoadNil,
    LoadBool    { value: bool },
    LoatInt     { value: i64 },
    LoadFloat   { value: f64 },

    Not         { src: StmtRef<'a> },
    BitNot      { src: StmtRef<'a> },
    Neg         { src: StmtRef<'a> },
    Plus        { src: StmtRef<'a> },

    And         { src1: StmtRef<'a>, src2: StmtRef<'a> },
    Or          { src1: StmtRef<'a>, src2: StmtRef<'a> },
    Add         { src1: StmtRef<'a>, src2: StmtRef<'a> },
    Sub         { src1: StmtRef<'a>, src2: StmtRef<'a> },
    Mul         { src1: StmtRef<'a>, src2: StmtRef<'a> },
    Div         { src1: StmtRef<'a>, src2: StmtRef<'a> },
    IntDiv      { src1: StmtRef<'a>, src2: StmtRef<'a> },
    CmpEq       { src1: StmtRef<'a>, src2: StmtRef<'a> },
    CmpNe       { src1: StmtRef<'a>, src2: StmtRef<'a> },
    CmpLe       { src1: StmtRef<'a>, src2: StmtRef<'a> },
    CmpLt       { src1: StmtRef<'a>, src2: StmtRef<'a> },
    CmpGe       { src1: StmtRef<'a>, src2: StmtRef<'a> },
    CmpGt       { src1: StmtRef<'a>, src2: StmtRef<'a> },
    OrElse      { src1: StmtRef<'a>, src2: StmtRef<'a> },

    Jump        { target: BlockId },
    SwitchBool  { src: StmtRef<'a>, on_true: BlockId, on_false: BlockId },
    Return      { src: StmtRef<'a> },
}

impl<'a> StmtData<'a> {
    #[inline(always)]
    pub fn is_copy(&self) -> bool {
        if let StmtData::Copy { src: _ } = self { true } else { false }
    }

    #[inline(always)]
    pub fn is_phi(&self) -> bool {
        if let StmtData::Phi { map: _ } = self { true } else { false }
    }

    #[inline(always)]
    pub fn is_terminator(&self) -> bool {
        use StmtData::*;
        match self {
            Jump { target: _ } |
            SwitchBool { src: _, on_true: _, on_false: _ } |
            Return { src: _ } => true,

            Copy { src: _ } |
            Phi { map: _ } |
            GetLocal { src: _ } |
            LoadNil | LoadBool { value: _ } | LoatInt { value: _ } | LoadFloat { value: _ } |
            Not { src: _ } | BitNot { src: _ } | Neg { src: _ } | Plus { src: _ } |
            And { src1: _, src2: _ } | Or { src1: _, src2: _ } |
            Add { src1: _, src2: _ } | Sub { src1: _, src2: _ } | Mul { src1: _, src2: _ } |
            Div { src1: _, src2: _ } | IntDiv { src1: _, src2: _ } |
            CmpEq { src1: _, src2: _ } | CmpNe { src1: _, src2: _ } |
            CmpLe { src1: _, src2: _ } | CmpLt { src1: _, src2: _ } |
            CmpGe { src1: _, src2: _ } | CmpGt { src1: _, src2: _ } |
            OrElse { src1: _, src2: _ } |
            SetLocal { dst: _, src: _ } => false,
        }
    }

    #[inline(always)]
    pub fn has_value(&self) -> bool {
        use StmtData::*;
        match self {
            Copy { src: _ } |
            Phi { map: _ } |
            GetLocal { src: _ } |
            LoadNil |
            LoadBool { value: _ } |
            LoatInt { value: _ } |
            LoadFloat { value: _ } |
            Not { src: _ } | BitNot { src: _ } | Neg { src: _ } | Plus { src: _ } |
            And { src1: _, src2: _ } | Or { src1: _, src2: _ } |
            Add { src1: _, src2: _ } | Sub { src1: _, src2: _ } | Mul { src1: _, src2: _ } |
            Div { src1: _, src2: _ } | IntDiv { src1: _, src2: _ } |
            CmpEq { src1: _, src2: _ } | CmpNe { src1: _, src2: _ } |
            CmpLe { src1: _, src2: _ } | CmpLt { src1: _, src2: _ } |
            CmpGe { src1: _, src2: _ } | CmpGt { src1: _, src2: _ } |
            OrElse { src1: _, src2: _ } => true,

            SetLocal { dst: _, src: _ } |
            Jump { target: _ } |
            SwitchBool { src: _, on_true: _, on_false: _ } |
            Return { src: _ } => false,
        }
    }

    #[inline]
    pub fn args<F: FnMut(StmtRef<'a>)>(&self, mut f: F) {
        use StmtData::*;
        match self {
            Copy { src } => { f(*src) }

            Phi { map } => { for entry in *map { f(entry.get().1) } }

            GetLocal { src: _ } => (),
            SetLocal { dst: _, src } => { f(*src) }

            LoadNil |
            LoadBool  { value: _ } |
            LoatInt   { value: _ } |
            LoadFloat { value: _ } => (),

            Not         { src } |
            BitNot      { src } |
            Neg         { src } |
            Plus        { src } => { f(*src) }

            And         { src1, src2 } |
            Or          { src1, src2 } |
            Add         { src1, src2 } |
            Sub         { src1, src2 } |
            Mul         { src1, src2 } |
            Div         { src1, src2 } |
            IntDiv      { src1, src2 } |
            CmpEq       { src1, src2 } |
            CmpNe       { src1, src2 } |
            CmpLe       { src1, src2 } |
            CmpLt       { src1, src2 } |
            CmpGe       { src1, src2 } |
            CmpGt       { src1, src2 } |
            OrElse      { src1, src2 } => { f(*src1); f(*src2) }

            Jump       { target: _ } => (),
            SwitchBool { src, on_true: _, on_false: _ } => { f(*src) }
            Return     { src }                          => { f(*src) },
        }
    }

    #[inline]
    pub fn replace_args<F: FnMut(&mut StmtRef<'a>)>(&mut self, mut f: F) {
        use StmtData::*;
        match self {
            Copy { src } => { f(src) }

            Phi { map } => {
                for entry in *map {
                    let (bb, mut arg) = entry.get();
                    f(&mut arg);
                    entry.set((bb, arg));
                }
            }

            GetLocal { src: _ } => (),
            SetLocal { dst: _, src } => { f(src) }

            LoadNil |
            LoadBool  { value: _ } |
            LoatInt   { value: _ } |
            LoadFloat { value: _ } => (),

            Not         { src } |
            BitNot      { src } |
            Neg         { src } |
            Plus        { src } => { f(src) }

            And         { src1, src2 } |
            Or          { src1, src2 } |
            Add         { src1, src2 } |
            Sub         { src1, src2 } |
            Mul         { src1, src2 } |
            Div         { src1, src2 } |
            IntDiv      { src1, src2 } |
            CmpEq       { src1, src2 } |
            CmpNe       { src1, src2 } |
            CmpLe       { src1, src2 } |
            CmpLt       { src1, src2 } |
            CmpGe       { src1, src2 } |
            CmpGt       { src1, src2 } |
            OrElse      { src1, src2 } => { f(src1); f(src2) }

            Jump       { target: _ } => (),
            SwitchBool { src, on_true: _, on_false: _ } => { f(src) }
            Return     { src }                          => { f(src) },
        }
    }
}



#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BlockId(u32);

impl BlockId {
    pub const ENTRY: BlockId = BlockId(0);

    #[inline(always)]
    pub fn is_entry(self) -> bool { self == BlockId::ENTRY }

    #[inline(always)]
    pub fn usize(self) -> usize { self.0 as usize }
}

impl core::fmt::Display for BlockId {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "bb{}", self.0)
    }
}


#[derive(Clone, Debug)]
pub struct Block<'a> {
    pub id: BlockId,
    pub statements: Vec<StmtRef<'a>>,
}

impl<'a> Block<'a> {
    pub fn new(id: BlockId) -> Self {
        Block {
            id,
            statements: vec![],
        }
    }

    #[inline]
    pub fn terminated(&self) -> bool {
        if let Some(last) = self.statements.last() {
            last.get().is_terminator()
        }
        else { false }
    }

    #[inline]
    pub fn successors<F: FnMut(BlockId)>(&self, mut f: F) {
        let Some(last) = self.statements.last() else { return };

        use StmtData::*;
        match last.get().data {
            Jump { target } => { f(target); }
            SwitchBool { src: _, on_true, on_false } => { f(on_true); f(on_false); }
            Return { src: _ } => {}

            _ => { unreachable!("called successors on unterminated block") }
        }
    }

    #[inline]
    pub fn args<F: FnMut(StmtRef<'a>)>(&self, mut f: F) {
        for stmt in &self.statements {
            stmt.get().args(&mut f);
        }
    }

    #[inline]
    pub fn replace_args<F: FnMut(&mut StmtRef<'a>)>(&mut self, mut f: F) {
        for stmt_ref in &self.statements {
            let mut stmt = stmt_ref.get();
            stmt.replace_args(&mut f);
            stmt_ref.set(stmt);
        }
    }
}

impl<'a> core::fmt::Display for Block<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:\n", self.id)?;

        for stmt in &self.statements {
            write!(f, "  {}\n", *stmt)?;
        }

        Ok(())
    }
}


#[derive(Clone, Debug)]
pub struct Function<'a> {
    pub blocks: Vec<Block<'a>>,
}


#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LocalId(u32);

impl LocalId {
    #[inline(always)]
    pub fn usize(self) -> usize { self.0 as usize }
}

impl core::fmt::Display for LocalId {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "l{}", self.0)
    }
}


#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
pub struct ScopeId(u32);


#[derive(Clone, Debug)]
pub struct Decl<'a> {
    pub name:  &'a str,
    pub id:    LocalId,
    pub scope: ScopeId,
}


pub struct FunctionBuilder<'a> {
    blocks:     Vec<Block<'a>>,
    decls:      Vec<Decl<'a>>,
    stmts:      Vec<StmtRef<'a>>,
    scope:      ScopeId,
    next_local: LocalId,
}

impl<'a> FunctionBuilder<'a> {
    pub fn new() -> Self {
        FunctionBuilder {
            blocks:     vec![],
            decls:      vec![],
            stmts:      vec![],
            scope:      ScopeId(0),
            next_local: LocalId(0),
        }
    }

    pub fn new_block(&mut self) -> BlockId {
        let id = BlockId(self.blocks.len() as u32);
        self.blocks.push(Block::new(id));
        id
    }

    pub fn new_local(&mut self) -> LocalId {
        let id = self.next_local;
        self.next_local.0 += 1;
        id
    }

    pub fn new_stmt_at(&mut self, source: SourceRange, data: StmtData<'a>) -> StmtRef<'a> {
        let id = StmtId(self.stmts.len() as u32);
        let rf = StmtRef(Box::leak(Box::new(Cell::new(Stmt { id, source, data }))));
        self.stmts.push(rf);
        rf
    }

    pub fn add_stmt_at(&mut self, bb: BlockId, source: SourceRange, data: StmtData<'a>) -> StmtRef<'a> {
        let stmt = self.new_stmt_at(source, data);

        let block = &mut self.blocks[bb.0 as usize];
        assert!(!block.terminated());
        block.statements.push(stmt);
        stmt
    }

    pub fn add_stmt(&mut self, bb: BlockId, at: &Ast, data: StmtData<'a>) -> StmtRef<'a> {
        self.add_stmt_at(bb, at.source, data)
    }

    pub fn add_decl(&mut self, name: &'a str) -> LocalId {
        let id = self.new_local();
        self.decls.push(Decl { name, id, scope: self.scope });
        id
    }

    pub fn find_decl(&self, name: &str) -> Option<&Decl<'a>> {
        self.decls.iter().rev().find(|decl| decl.name == name)
    }

    pub fn begin_scope(&mut self) -> ScopeId {
        self.scope.0 += 1;
        self.scope
    }

    pub fn end_scope(&mut self, scope: ScopeId) {
        assert_eq!(self.scope, scope);
        self.decls.retain(|decl| decl.scope < self.scope);
        self.scope.0 -= 1;
    }
}

