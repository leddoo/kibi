use derive_more::{Deref, Display};
use super::*;


#[derive(Deref)]
pub struct Predecessors {
    pub preds: Vec<Vec<BlockId>>,
}


#[derive(Deref)]
pub struct PostOrder {
    pub blocks: Vec<BlockId>,
}

#[derive(Clone, Copy, Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PostOrderIndex {
    pub value: u32,
}

impl PostOrderIndex {
    pub const NONE: PostOrderIndex = PostOrderIndex { value: u32::MAX };
}

#[derive(Deref)]
pub struct PostOrderIndices {
    pub indices: Vec<PostOrderIndex>,
}


// ### dominance ###

#[derive(Deref)]
pub struct ImmediateDominators {
    pub idom: Vec<BlockId>,
}

#[derive(Deref)]
pub struct DomTree {
    pub tree: Vec<Vec<BlockId>>,
}

#[derive(Deref)]
pub struct DominanceFrontiers {
    pub frontiers: Vec<Vec<BlockId>>,
}


// ### block order ###

#[derive(Deref)]
pub struct BlockOrder {
    pub order: Vec<BlockId>,
}

#[derive(Clone, Copy, Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StmtIndex {
    pub value: u32,
}

impl StmtIndex {
    pub const NONE: StmtIndex = StmtIndex { value: u32::MAX };
}

#[derive(Deref)]
pub struct BlockBegins {
    pub begins: Vec<StmtIndex>,
}

#[derive(Deref)]
pub struct StmtIndices {
    pub indices: Vec<StmtIndex>,
}


// ### liveness ###

pub struct BlockGenKill {
    pub gens:  Vec<Vec<bool>>,
    pub kills: Vec<Vec<bool>>,
}

pub struct BlockLiveInOut {
    pub live_ins:  Vec<Vec<bool>>,
    pub live_outs: Vec<Vec<bool>>,
}

#[derive(Deref)]
pub struct LiveIntervals {
    pub intervals: Vec<Vec<(StmtIndex, StmtIndex)>>,
}



impl Function {
    pub fn preds_and_post_order(&self) -> (Predecessors, PostOrder) {
        let mut preds = vec![vec![]; self.num_blocks()];
        let mut post_order = vec![];
        let mut visited = vec![false; self.num_blocks()];

        fn visit(fun: &Function, bb: BlockId,
            preds: &mut Vec<Vec<BlockId>>,
            post_order: &mut Vec<BlockId>,
            visited: &mut Vec<bool>,
        ) {
            fun.block_successors(bb, |succ| {
                preds[succ.usize()].push(bb);

                if !visited[succ.usize()] {
                    visited[succ.usize()] = true;
                    visit(fun, succ, preds, post_order, visited);
                }
            });

            post_order.push(bb);
        }
        visit(self, BlockId::ROOT, &mut preds, &mut post_order, &mut visited);

        for bb in &post_order {
            if !bb.is_root() {
                assert!(preds[bb.usize()].len() > 0);
            }
        }

        (Predecessors { preds }, PostOrder { blocks: post_order })
    }

    pub fn immediate_dominators(&self, preds: &Predecessors, post_order: &PostOrder, post_indices: &PostOrderIndices) -> ImmediateDominators {
        let mut doms = vec![None; self.num_blocks()];

        let bb0 = post_indices[BlockId::ROOT.usize()];
        doms[bb0.usize()] = Some(bb0);

        let mut changed = true;
        while changed {
            changed = false;

            for bb_id in post_order.iter().rev() {
                if bb_id.is_root() { continue }

                let preds = &preds[bb_id.usize()];
                let bb = post_indices[bb_id.usize()];

                let mut new_dom = post_indices[preds[0].usize()];

                for pred_id in preds.iter().skip(1) {
                    let pred = post_indices[pred_id.usize()];

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

        let idom = self.block_ids()
            .map(|bb| {
                let post_index      = post_indices[bb.usize()];
                let idom_post_index = doms[post_index.usize()].unwrap();
                let idom            = post_order[idom_post_index.usize()];
                idom
            })
            .collect::<Vec<BlockId>>();
        ImmediateDominators { idom }
    }

    pub fn dominator_tree(&self, idoms: &ImmediateDominators) -> DomTree {
        let mut tree = vec![vec![]; self.num_blocks()];

        for bb in self.block_ids().skip(1) {
            let idom = idoms[bb.usize()];
            tree[idom.usize()].push(bb);
        }

        DomTree { tree }
    }

    pub fn dominance_frontiers(&self, preds: &Predecessors, idoms: &ImmediateDominators) -> DominanceFrontiers {
        let mut frontiers = vec![vec![]; self.num_blocks()];

        for bb in self.block_ids() {
            let preds = &preds[bb.usize()];
            if preds.len() < 2 { continue }

            let idom = idoms[bb.usize()];
            for pred in preds {
                let mut at = *pred;
                while at != idom {
                    let df = &mut frontiers[at.usize()];
                    if !df.contains(&bb) {
                        df.push(bb);
                    }
                    at = idoms[at.usize()];
                }
            }
        }

        DominanceFrontiers { frontiers }
    }


    pub fn block_order_dominators_first(&self, idoms: &ImmediateDominators, dom_tree: &DomTree) -> BlockOrder {
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
        let mut visited = vec![false; self.num_blocks()];
        visit(BlockId::ROOT, &mut order, &mut visited, self, idoms, dom_tree);
        BlockOrder { order }
    }


    pub fn block_gen_kill(&self) -> BlockGenKill {
        let mut gens  = Vec::with_capacity(self.num_blocks());
        let mut kills = Vec::with_capacity(self.num_blocks());

        for bb in self.block_ids() {
            let mut gen  = vec![false; self.num_stmts()];
            let mut kill = vec![false; self.num_stmts()];

            // statements in reverse.
            self.block_stmts_rev(bb, |stmt| {
                if stmt.has_value() {
                    kill[stmt.id().usize()] = true;
                    gen [stmt.id().usize()] = false;
                }

                if !stmt.is_phi() {
                    stmt.args(self, |arg| {
                        gen[arg.usize()] = true;
                    });
                }
            });

            gens.push(gen);
            kills.push(kill);
        }

        BlockGenKill { gens, kills }
    }

    pub fn block_live_in_out(&self, post_order: &PostOrder, gen_kill: &BlockGenKill) -> BlockLiveInOut {
        let BlockGenKill { gens, kills } = gen_kill;

        let mut live_ins  = vec![vec![false; self.num_stmts()]; self.num_blocks()];
        let mut live_outs = vec![vec![false; self.num_stmts()]; self.num_blocks()];
        let mut changed = true;
        while changed {
            changed = false;

            for bb in post_order.iter() {
                let gen   = &gens[bb.usize()];
                let kill  = &kills[bb.usize()];

                let mut new_live_out = vec![false; self.num_stmts()];
                self.block_successors(*bb, |succ| {
                    // live_in.
                    for (i, live) in live_ins[succ.usize()].iter().enumerate() {
                        if *live {
                            new_live_out[i] = true;
                        }
                    }

                    // phis: gen bb's args.
                    self.block_stmts_ex(succ, |stmt| {
                        // @todo: try_phi Stmt variant?
                        if let Some(map) = self.try_phi(stmt.id()) {
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

                if new_live_in != live_ins[bb.usize()] {
                    changed = true;
                    live_ins[bb.usize()] = new_live_in;
                }
                if new_live_out != live_outs[bb.usize()] {
                    changed = true;
                    live_outs[bb.usize()] = new_live_out;
                }
            }
        }

        // @temp: hella unstable hack to make sure params are assigned the right registers.
        {
            let live_out = &mut live_outs[BlockId::ROOT.usize()];
            let mut i = 0;
            self.block_stmts_ex(BlockId::ROOT, |stmt| {
                if i < self.num_params() {
                    live_out[stmt.id().usize()] = true;
                    i += 1;
                    return true;
                }
                false
            });
        }

        BlockLiveInOut { live_ins, live_outs }
    }

    pub fn live_intervals_ex(&self,
        block_order: &BlockOrder, block_begins: &BlockBegins,
        stmt_indices: &StmtIndices,
        live_sets: &BlockLiveInOut,
        no_empty_intervals: bool,
    ) -> LiveIntervals {
        let BlockLiveInOut { live_ins: _, live_outs } = live_sets;

        let mut intervals = vec![vec![]; self.num_stmts()];
        for bb in block_order.iter() {
            let live_out = &live_outs[bb.usize()];

            let num_stmts = self.num_block_stmts(*bb);

            let block_begin = block_begins[bb.usize()];
            let block_end   = StmtIndex { value: block_begin.value + num_stmts as u32 };

            let mut live = live_out.iter().map(|live| {
                live.then(|| block_end)
            }).collect::<Vec<_>>();

            #[inline]
            fn gen(var: StmtId, stop: StmtIndex, live: &mut Vec<Option<StmtIndex>>) {
                let id = var.usize();
                if live[id].is_none() {
                    live[id] = Some(stop);
                }
            }

            fn kill(var: StmtId, start: StmtIndex, live: &mut Vec<Option<StmtIndex>>, intervals: &mut Vec<Vec<(StmtIndex, StmtIndex)>>) {
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
            let mut parallel_copy_pos = None;
            let mut phi_pos           = None;
            self.block_stmts_rev(*bb, |stmt| {
                let stmt_pos = stmt_indices[stmt.id().usize()];

                let stmt_pos =
                    if stmt.is_phi() {
                        if let Some(phi_pos) = phi_pos {
                            phi_pos
                        }
                        else {
                            phi_pos = Some(stmt_pos);
                            stmt_pos
                        }
                    }
                    else if let StmtData::ParallelCopy { src: _, copy_id: id } = stmt.data {
                        if let Some((current_id, current_pos)) = parallel_copy_pos {
                            if current_id == id {
                                current_pos
                            }
                            else {
                                parallel_copy_pos = Some((id, stmt_pos));
                                stmt_pos
                            }
                        }
                        else {
                            parallel_copy_pos = Some((id, stmt_pos));
                            stmt_pos
                        }
                    }
                    else {
                        stmt_pos
                    };

                if stmt.has_value() {
                    let start = stmt_pos;
                    if no_empty_intervals {
                        let mut stop = start;
                        if stmt.is_parallel_copy() {
                            // parallel copies have the same start position.
                            // if one is unused (start == stop), its register may be
                            // released and made available for other copies in the
                            // same parallel group, which is no good.
                            stop = StmtIndex { value: start.value + 1 };
                        }
                        gen(stmt.id(), stop, &mut live);
                    }
                    kill(stmt.id(), start, &mut live, &mut intervals)
                }

                if !stmt.is_phi() {
                    stmt.args(self, |arg| {
                        let stop = stmt_pos;
                        gen(arg, stop, &mut live);
                    });
                }
            });

            for id in self.stmt_ids() {
                let start = block_begin;
                kill(id, start, &mut live, &mut intervals);
            }
        }

        LiveIntervals { intervals }
    }

    pub fn live_intervals(&self, post_order: &PostOrder, block_order: &BlockOrder, block_begins: &BlockBegins, stmt_indices: &StmtIndices, no_empty_intervals: bool) -> LiveIntervals {
        let gen_kill = self.block_gen_kill();
        let live_sets = self.block_live_in_out(&post_order, &gen_kill);
        self.live_intervals_ex(block_order, block_begins, stmt_indices, &live_sets, no_empty_intervals)
    }
}

impl PostOrder {
    pub fn indices(&self) -> PostOrderIndices {
        let mut indices = vec![PostOrderIndex::NONE; self.blocks.len()];
        for (index, bb) in self.blocks.iter().enumerate() {
            indices[bb.usize()] = PostOrderIndex { value: index as u32 };
        }
        PostOrderIndices { indices }
    }
}

impl PostOrderIndex {
    #[inline(always)]
    pub fn usize(self) -> usize { self.value as usize }
}


impl BlockOrder {
    pub fn block_begins_and_stmt_indices(&self, fun: &Function) -> (BlockBegins, StmtIndices) {
        let mut block_begins = vec![StmtIndex::NONE; fun.num_blocks()];
        let mut stmt_indices = vec![StmtIndex::NONE; fun.num_stmts()];

        let mut cursor = StmtIndex { value: 0 };
        for bb in &self.order {
            block_begins[bb.usize()] = cursor;

            fun.block_stmts(*bb, |stmt| {
                stmt_indices[stmt.id().usize()] = cursor;
                cursor.value += 1;
            });
        }
        block_begins.push(cursor);

        (BlockBegins { begins: block_begins }, StmtIndices { indices: stmt_indices })
    }
}

