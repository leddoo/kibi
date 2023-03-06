use derive_more::{Deref, Display};
use crate::index_vec::*;
use crate::macros::define_id;
use super::*;


#[derive(Deref)]
pub struct Predecessors {
    pub preds: IndexVec<BlockId, Vec<BlockId>>,
}


#[derive(Deref)]
pub struct PostOrder {
    pub blocks: Vec<BlockId>,
}

define_id!(PostOrderIndex, OptPostOrderIndex);

pub struct PostOrderIndices {
    pub indices: IndexVec<BlockId, OptPostOrderIndex>,
}


// ### dominance ###

pub struct ImmediateDominators {
    pub idom: IndexVec<BlockId, BlockId>,
}

#[derive(Deref)]
pub struct DomTree {
    pub tree: IndexVec<BlockId, Vec<BlockId>>,
}

#[derive(Deref)]
pub struct DominanceFrontiers {
    pub frontiers: IndexVec<BlockId, Vec<BlockId>>,
}


// ### block order ###

#[derive(Deref)]
pub struct BlockOrder {
    pub order: Vec<BlockId>,
}

#[derive(Clone, Copy, Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct InstrIndex {
    pub value: u32,
}

impl InstrIndex {
    pub const NONE: InstrIndex = InstrIndex { value: u32::MAX };
}

#[derive(Deref)]
pub struct BlockBegins {
    pub begins: IndexVec<BlockId, InstrIndex>,
}

#[derive(Deref)]
pub struct InstrIndices {
    pub indices: IndexVec<InstrId, InstrIndex>,
}


// ### liveness ###

pub struct BlockGenKill {
    pub gens:  IndexVec<BlockId, IndexVec<InstrId, bool>>,
    pub kills: IndexVec<BlockId, IndexVec<InstrId, bool>>,
}

pub struct BlockLiveInOut {
    pub live_ins:  IndexVec<BlockId, IndexVec<InstrId, bool>>,
    pub live_outs: IndexVec<BlockId, IndexVec<InstrId, bool>>,
}

#[derive(Deref)]
pub struct LiveIntervals {
    pub intervals: IndexVec<InstrId, Vec<(InstrIndex, InstrIndex)>>,
}



impl PostOrderIndices {
    #[inline(always)]
    pub fn get_unck(&self, bb: BlockId) -> PostOrderIndex {
        self.indices[bb].unwrap_unck()
    }

    #[inline(always)]
    pub fn get(&self, bb: BlockId) -> Option<PostOrderIndex> {
        self.indices[bb].to_option()
    }
}

impl ImmediateDominators {
    #[inline]
    pub fn get_unck(&self, bb: BlockId) -> BlockId {
        self.idom[bb]
    }

    #[inline]
    pub fn get(&self, bb: BlockId) -> Option<BlockId> {
        let idom = self.idom[bb];
        (bb.is_entry() || idom != bb).then_some(idom)
    }

    #[inline]
    pub fn is_unreachable(&self, bb: BlockId) -> bool {
        self.get(bb).is_none()
    }

    pub fn is_dominated_by(&self, bb: BlockId, dom: BlockId) -> bool {
        let mut at = bb;
        loop {
            if at == dom {
                return true;
            }

            let idom = self.idom[at];
            if at == idom {
                return false;
            }
            at = idom;
        }
    }
}


impl Function {
    pub fn predecessors(&self) -> Predecessors {
        let mut preds = index_vec![vec![]; self.num_blocks()];

        for bb in self.block_ids() {
            self.block_successors(bb, |succ|
                preds[succ].push(bb));
        }

        Predecessors { preds }
    }

    pub fn post_order(&self) -> PostOrder {
        let mut post_order = vec![];
        let mut visited = index_vec![false; self.num_blocks()];

        fn visit(fun: &Function, bb: BlockId,
            post_order: &mut Vec<BlockId>,
            visited: &mut IndexVec<BlockId, bool>,
        ) {
            fun.block_successors(bb, |succ| {
                if !visited[succ] {
                    visited[succ] = true;
                    visit(fun, succ, post_order, visited);
                }
            });

            post_order.push(bb);
        }
        visit(self, BlockId::ENTRY, &mut post_order, &mut visited);

        PostOrder { blocks: post_order }
    }

    pub fn post_order_indices(&self, post_order: &PostOrder) -> PostOrderIndices {
        let mut indices = index_vec![OptPostOrderIndex::NONE; self.num_blocks()];
        for (index, bb) in post_order.blocks.iter().enumerate() {
            indices[*bb] = PostOrderIndex::new_unck(index as u32).some();
        }
        PostOrderIndices { indices }
    }

    pub fn immediate_dominators(&self, preds: &Predecessors, post_order: &PostOrder, post_indices: &PostOrderIndices) -> ImmediateDominators {
        let mut doms = index_vec![None; self.num_blocks()];

        let bb0 = post_indices.get_unck(BlockId::ENTRY);
        doms[bb0] = Some(bb0);

        let mut changed = true;
        while changed {
            changed = false;

            for bb_id in post_order.iter().rev().copied() {
                if bb_id.is_entry() { continue }

                let preds = &preds[bb_id];
                let bb = post_indices.get_unck(bb_id);

                let mut new_dom = post_indices.get_unck(preds[0]);

                for pred_id in preds.iter().skip(1).copied() {
                    let Some(pred) = post_indices.get(pred_id) else { continue };

                    // intersect.
                    if doms[pred].is_some() {
                        let mut x = new_dom;
                        let mut y = pred;

                        while x != y {
                            while x < y {
                                x = doms[x].unwrap();
                            }
                            while y < x {
                                y = doms[y].unwrap();
                            }
                        }

                        new_dom = x;
                    }
                }

                if doms[bb] != Some(new_dom) {
                    doms[bb] = Some(new_dom);
                    changed = true;
                }
            }
        }

        let idom = self.block_ids()
            .map(|bb| {
                if let Some(post_index) = post_indices.get(bb) {
                    let idom_post_index = doms[post_index].unwrap();
                    let idom            = post_order[idom_post_index.usize()];
                    idom
                }
                else { bb } // unreachable.
            }).collect();
        ImmediateDominators { idom }
    }

    pub fn dominator_tree(&self, idoms: &ImmediateDominators) -> DomTree {
        let mut tree = index_vec![vec![]; self.num_blocks()];

        for bb in self.block_ids().skip(1) {
            if let Some(idom) = idoms.get(bb) {
                tree[idom].push(bb);
            }
        }

        DomTree { tree }
    }

    pub fn dominance_frontiers(&self, preds: &Predecessors, idoms: &ImmediateDominators) -> DominanceFrontiers {
        let mut frontiers = index_vec![vec![]; self.num_blocks()];

        for bb in self.block_ids() {
            let preds = &preds[bb];
            if preds.len() < 2 { continue }

            let Some(idom) = idoms.get(bb) else { continue };

            for pred in preds.iter().copied() {
                if idoms.is_unreachable(pred) { continue }

                let mut at = pred;
                while at != idom {
                    let df = &mut frontiers[at];
                    if !df.contains(&bb) {
                        df.push(bb);
                    }
                    at = idoms.get_unck(at);
                }
            }
        }

        DominanceFrontiers { frontiers }
    }


    pub fn block_order_dominators_first(&self, idoms: &ImmediateDominators, dom_tree: &DomTree) -> BlockOrder {
        fn visit(bb: BlockId, order: &mut Vec<BlockId>, visited: &mut IndexVec<BlockId, bool>,
            fun: &Function, idom: &ImmediateDominators, dom_tree: &DomTree,
        ) {
            assert!(!visited[bb]);
            visited[bb] = true;
            order.push(bb);

            fun.block_successors(bb, |succ| {
                if !visited[succ] && idom.get_unck(succ) == bb {
                    visit(succ, order, visited, fun, idom, dom_tree);
                }
            });

            for child in &dom_tree[bb] {
                if !visited[*child] {
                    visit(*child, order, visited, fun, idom, dom_tree);
                }
            }
        }

        let mut order   = vec![];
        let mut visited = index_vec![false; self.num_blocks()];
        visit(BlockId::ENTRY, &mut order, &mut visited, self, idoms, dom_tree);
        BlockOrder { order }
    }


    pub fn block_gen_kill(&self) -> BlockGenKill {
        let mut gens  = IndexVec::with_capacity(self.num_blocks());
        let mut kills = IndexVec::with_capacity(self.num_blocks());

        for bb in self.block_ids() {
            let mut gen  = index_vec![false; self.num_instrs()];
            let mut kill = index_vec![false; self.num_instrs()];

            // instructions in reverse.
            self.block_instr_rev(bb, |instr| {
                if instr.has_value() {
                    kill[instr.id()] = true;
                    gen [instr.id()] = false;
                }

                if !instr.is_phi() {
                    instr.args(self, |arg| {
                        gen[arg] = true;
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

        let mut live_ins  = index_vec![index_vec![false; self.num_instrs()]; self.num_blocks()];
        let mut live_outs = index_vec![index_vec![false; self.num_instrs()]; self.num_blocks()];
        let mut changed = true;
        while changed {
            changed = false;

            for bb in post_order.iter().copied() {
                let gen   = &gens[bb];
                let kill  = &kills[bb];

                let mut new_live_out = index_vec![false; self.num_instrs()];
                self.block_successors(bb, |succ| {
                    // live_in.
                    for (i, live) in live_ins[succ].iter().enumerate() {
                        if *live {
                            new_live_out[InstrId::from_usize(i)] = true;
                        }
                    }

                    // phis: gen bb's args.
                    self.block_instrs_ex(succ, |instr| {
                        // @todo: try_phi Instr variant?
                        if let Some(map) = self.try_phi(instr.id()) {
                            let src = map.get(bb).unwrap();
                            new_live_out[src] = true;
                            return true;
                        }
                        false
                    });
                });

                let mut new_live_in = new_live_out.clone();
                for (i, kill) in kill.iter().enumerate() {
                    if *kill {
                        new_live_in[InstrId::from_usize(i)] = false;
                    }
                }
                for (i, gen) in gen.iter().enumerate() {
                    if *gen {
                        new_live_in[InstrId::from_usize(i)] = true;
                    }
                }

                if new_live_in != live_ins[bb] {
                    changed = true;
                    live_ins[bb] = new_live_in;
                }
                if new_live_out != live_outs[bb] {
                    changed = true;
                    live_outs[bb] = new_live_out;
                }
            }
        }

        BlockLiveInOut { live_ins, live_outs }
    }

    pub fn live_intervals_ex(&self,
        block_order: &BlockOrder, block_begins: &BlockBegins,
        instr_indices: &InstrIndices,
        live_sets: &BlockLiveInOut,
        no_empty_intervals: bool,
    ) -> LiveIntervals {
        let BlockLiveInOut { live_ins: _, live_outs } = live_sets;

        let mut intervals = index_vec![vec![]; self.num_instrs()];
        for bb in block_order.iter().copied() {
            let live_out = &live_outs[bb];

            let num_instrs = self.num_block_instrs(bb);

            let block_begin = block_begins[bb];
            let block_end   = InstrIndex { value: block_begin.value + num_instrs as u32 };

            let mut live = live_out.iter().map(|live| {
                live.then(|| block_end)
            }).collect::<IndexVec<_,_>>();

            #[inline]
            fn gen(var: InstrId, stop: InstrIndex, live: &mut IndexVec<InstrId, Option<InstrIndex>>) {
                if live[var].is_none() {
                    live[var] = Some(stop);
                }
            }

            fn kill(var: InstrId, start: InstrIndex, live: &mut IndexVec<InstrId, Option<InstrIndex>>, intervals: &mut IndexVec<InstrId, Vec<(InstrIndex, InstrIndex)>>) {
                if let Some(stop) = live[var] {
                    live[var] = None;

                    let interval = &mut intervals[var];
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

            // instructions.
            let mut parallel_copy_pos = None;
            let mut phi_pos           = None;
            self.block_instr_rev(bb, |instr| {
                let instr_pos = instr_indices[instr.id()];

                let instr_pos =
                    if instr.is_phi() {
                        if let Some(phi_pos) = phi_pos {
                            phi_pos
                        }
                        else {
                            phi_pos = Some(instr_pos);
                            instr_pos
                        }
                    }
                    else if let InstrData::ParallelCopy { src: _, copy_id: id } = instr.data {
                        if let Some((current_id, current_pos)) = parallel_copy_pos {
                            if current_id == id {
                                current_pos
                            }
                            else {
                                parallel_copy_pos = Some((id, instr_pos));
                                instr_pos
                            }
                        }
                        else {
                            parallel_copy_pos = Some((id, instr_pos));
                            instr_pos
                        }
                    }
                    else {
                        instr_pos
                    };

                if instr.has_value() {
                    let start = instr_pos;
                    if no_empty_intervals {
                        let mut stop = start;
                        if instr.is_parallel_copy() {
                            // parallel copies have the same start position.
                            // if one is unused (start == stop), its register may be
                            // released and made available for other copies in the
                            // same parallel group, which is no good.
                            stop = InstrIndex { value: start.value + 1 };
                        }
                        gen(instr.id(), stop, &mut live);
                    }
                    kill(instr.id(), start, &mut live, &mut intervals)
                }

                if !instr.is_phi() {
                    instr.args(self, |arg| {
                        let stop = instr_pos;
                        gen(arg, stop, &mut live);
                    });
                }
            });

            for id in self.instr_ids() {
                let start = block_begin;
                kill(id, start, &mut live, &mut intervals);
            }
        }

        LiveIntervals { intervals }
    }

    pub fn live_intervals(&self, post_order: &PostOrder, block_order: &BlockOrder, block_begins: &BlockBegins, instr_indices: &InstrIndices, no_empty_intervals: bool) -> LiveIntervals {
        let gen_kill = self.block_gen_kill();
        let live_sets = self.block_live_in_out(&post_order, &gen_kill);
        self.live_intervals_ex(block_order, block_begins, instr_indices, &live_sets, no_empty_intervals)
    }
}


impl BlockOrder {
    pub fn block_begins_and_instr_indices(&self, fun: &Function) -> (BlockBegins, InstrIndices) {
        let mut block_begins  = index_vec![InstrIndex::NONE; fun.num_blocks()];
        let mut instr_indices = index_vec![InstrIndex::NONE; fun.num_instrs()];

        let mut cursor = InstrIndex { value: 0 };
        for bb in self.order.iter().copied() {
            block_begins[bb] = cursor;

            fun.block_instrs(bb, |instr| {
                instr_indices[instr.id()] = cursor;
                cursor.value += 1;
            });
        }
        block_begins.push(cursor);

        (BlockBegins { begins: block_begins }, InstrIndices { indices: instr_indices })
    }
}

