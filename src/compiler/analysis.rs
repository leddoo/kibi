use derive_more::Deref;
use super::*;

#[derive(Deref)]
pub struct Predecessors {
    preds: Vec<Vec<BlockId>>,
}


#[derive(Deref)]
pub struct PostOrder {
    blocks: Vec<BlockId>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PostOrderIndex {
    value: u32,
}

impl PostOrderIndex {
    pub const NONE: PostOrderIndex = PostOrderIndex { value: u32::MAX };
}

#[derive(Deref)]
pub struct PostOrderIndices {
    indices: Vec<PostOrderIndex>,
}


#[derive(Deref)]
pub struct ImmediateDominators {
    idom: Vec<BlockId>,
}

#[derive(Deref)]
pub struct DomTree {
    tree: Vec<Vec<BlockId>>,
}

#[derive(Deref)]
pub struct DominanceFrontiers {
    frontiers: Vec<Vec<BlockId>>,
}



impl<'a> Function<'a> {
    pub fn preds_and_post_order(&self) -> (Predecessors, PostOrder) {
        let mut preds = vec![vec![]; self.blocks.len()];
        let mut post_order = vec![];
        let mut visited = vec![false; self.blocks.len()];

        fn visit(fun: &Function, bb: BlockId,
            preds: &mut Vec<Vec<BlockId>>,
            post_order: &mut Vec<BlockId>,
            visited: &mut Vec<bool>,
        ) {
            let block = &fun.blocks[bb.usize()];

            block.successors(|succ| {
                preds[succ.usize()].push(bb);

                if !visited[succ.usize()] {
                    visited[succ.usize()] = true;
                    visit(fun, succ, preds, post_order, visited);
                }
            });

            post_order.push(bb);
        }
        visit(self, BlockId::ENTRY, &mut preds, &mut post_order, &mut visited);

        for bb in &post_order {
            if !bb.is_entry() {
                assert!(preds[bb.usize()].len() > 0);
            }
        }

        (Predecessors { preds }, PostOrder { blocks: post_order })
    }

    pub fn immediate_dominators(&self, preds: &Predecessors, post_order: &PostOrder, post_indices: &PostOrderIndices) -> ImmediateDominators {
        let mut doms = vec![None; self.blocks.len()];

        let bb0 = post_indices[BlockId::ENTRY.usize()];
        doms[bb0.usize()] = Some(bb0);

        let mut changed = true;
        while changed {
            changed = false;

            for bb_id in post_order.iter().rev() {
                if bb_id.is_entry() { continue }

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

        let idom = self.blocks.iter()
            .map(|block| {
                let post_index      = post_indices[block.id.usize()];
                let idom_post_index = doms[post_index.usize()].unwrap();
                let idom            = post_order[idom_post_index.usize()];
                idom
            })
            .collect::<Vec<BlockId>>();
        ImmediateDominators { idom }
    }

    pub fn dominator_tree(&self, idoms: &ImmediateDominators) -> DomTree {
        let mut tree = vec![vec![]; self.blocks.len()];

        for block in self.blocks.iter().skip(1) {
            let bb = block.id;
            let idom = idoms[bb.usize()];
            tree[idom.usize()].push(bb);
        }

        DomTree { tree }
    }

    pub fn dominance_frontiers(&self, preds: &Predecessors, idoms: &ImmediateDominators) -> DominanceFrontiers {
        let mut frontiers = vec![vec![]; self.blocks.len()];

        for block in self.blocks.iter() {
            let bb = block.id;

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

