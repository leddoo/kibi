use crate::index_vec::*;
use super::*;


pub fn local2reg_ex(fun: &mut Function, preds: &Predecessors, dom_tree: &DomTree, dom_frontiers: &DominanceFrontiers) {
    // find phis
    let mut phis = {
        let mut visited = index_vec![index_vec![false; fun.num_locals()]; fun.num_blocks()];

        // collect defs.
        let mut stack = vec![];
        for bb in fun.block_ids() {
            fun.block_instrs(bb, |instr| {
                let InstrData::SetLocal { dst: lid, src: _ } = instr.data else { return };

                let key = (bb, lid);
                if !visited[bb][lid] {
                    visited[bb][lid] = true;
                    stack.push(key);
                }
            });
        }

        // phis for each bb.
        let mut phis: IndexVec<BlockId, Vec<(LocalId, Vec<(BlockId, OptInstrId)>, InstrId)>>
            = index_vec![vec![]; fun.num_blocks()];

        // for each def, create phis in dom frontier.
        while let Some((from_bb, lid)) = stack.pop() {
            for to_bb in dom_frontiers[from_bb].iter().copied() {
                let to_phis = &mut phis[to_bb];

                let local_was_new = to_phis.iter().find(|(l, _, _)| *l == lid).is_none();
                if local_was_new {
                    let preds = &preds[to_bb];

                    // init phi.
                    let map = preds.iter().map(|p| (*p, None.into())).collect();
                    let instr = fun.new_phi((SourceRange::null(), None.into()), &[]);
                    to_phis.push((lid, map, instr));

                    // to_bb now defines the local.
                    let key = (to_bb, lid);
                    if !visited[to_bb][lid] {
                        visited[to_bb][lid] = true;
                        stack.push(key);
                    }
                }
            }
        }

        phis
    };

    // rename vars.
    {
        fn visit(bb: BlockId, mut new_names: IndexVec<LocalId, OptInstrId>,
            phis: &mut IndexVec<BlockId, Vec<(LocalId, Vec<(BlockId, OptInstrId)>, InstrId)>>,
            fun: &mut Function, idom_tree: &DomTree,
        ) {
            // update var names.
            for (lid, _map, instr) in &phis[bb] {
                new_names[*lid] = instr.some();
            }
            fun.block_instr_mut(bb, |instr| { match instr.data {
                InstrData::Param { id } |
                InstrData::Local { id } => {
                    new_names[id] = instr.id().some();
                }

                InstrData::GetLocal { src } => {
                    let new_name = new_names[src].unwrap();
                    instr.data = InstrData::Copy { src: new_name };
                    new_names[src] = instr.id().some();
                }

                InstrData::SetLocal { dst, src } => {
                    instr.data = InstrData::Copy { src };
                    new_names[dst] = instr.id().some();
                }

                _ => (),
            }});

            // propagate to successors.
            fun.block_successors(bb, |succ| {
                for (l, map, _) in &mut phis[succ] {
                    let entry = map.iter_mut().find(|(from, _)| *from == bb).unwrap();
                    assert!(entry.1.is_none());

                    entry.1 = new_names[*l].unwrap().some();
                }
            });

            // propagate to dominated blocks.
            for d in idom_tree[bb].iter() {
                visit(*d, new_names.clone(), phis, fun, idom_tree);
            }
        }

        let new_names = index_vec![None.into(); fun.num_locals()];
        visit(BlockId::ENTRY, new_names, &mut phis, fun, &dom_tree);
    }

    // insert phis.
    {
        for (bb_index, phis) in phis.into_iter().enumerate() {
            let block = BlockId::from_usize(bb_index);
            let mut at = None.into();

            for (_, map, instr_id) in phis {
                let map: Vec<PhiEntry> = map.into_iter().map(|(bb, src)| { (bb, src.unwrap()) }).collect();
                fun.set_phi(instr_id, &map);

                fun.insert_after(block, at, instr_id);
                at = instr_id.some();
            }
        }
    }
    fun.slow_integrity_check();
}


pub fn copy_propagation_ex(fun: &mut Function, dom_tree: &DomTree) {
    fn visit(bb: BlockId, fun: &mut Function, dom_tree: &DomTree) {
        // inline copies.
        fun.block_replace_args(bb, |fun, arg| {
            if let InstrData::Copy { src } = arg.get(fun).data {
                let mut new_arg = src;
                while let InstrData::Copy { src } = new_arg.get(fun).data {
                    new_arg = src;
                }
                *arg = new_arg;
            }
        });

        // propagate to dominated blocks.
        for d in dom_tree[bb].iter() {
            visit(*d, fun, dom_tree);
        }
    }

    visit(BlockId::ENTRY, fun, &dom_tree);
    fun.slow_integrity_check();
}


pub fn dead_copy_elim(fun: &mut Function) {
    let mut visited = index_vec![false; fun.num_instrs()];
    fun.all_args(|arg| visited[arg] = true);

    for bb in fun.block_ids() {
        let mut current = bb.get(fun).first();

        while let Some(at) = current.to_option() {
            let instr = at.get_mut(fun);
            let next = instr.next();
            if !visited[at] {
                if let InstrData::Copy { src } = instr.data {
                    let source_values = core::mem::take(&mut instr.source.values);

                    // put value info on copy src.
                    let src = src.get_mut(fun);
                    src.source.values.extend(source_values);

                    // remove.
                    fun.remove_instr(at);
                }
            }

            current = next;
        }
    }

    fun.slow_integrity_check();
}

