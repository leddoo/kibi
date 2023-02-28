use super::*;


pub fn local2reg_ex(fun: &mut Function, preds: &Predecessors, dom_tree: &DomTree, dom_frontiers: &DominanceFrontiers) {
    // find phis
    let mut phis = {
        // @temp
        use std::collections::HashSet;

        let mut visited: HashSet<(BlockId, LocalId)> = HashSet::new();

        // collect defs.
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

        // phis for each bb.
        let mut phis: Vec<Vec<(LocalId, Vec<(BlockId, Option<StmtId>)>, StmtId)>>
            = vec![vec![]; fun.num_blocks()];

        // for each def, create phis in dom frontier.
        while let Some((from_bb, lid)) = stack.pop() {
            for to_bb in dom_frontiers[from_bb.usize()].iter().copied() {
                let to_phis = &mut phis[to_bb.usize()];

                let local_was_new = to_phis.iter().find(|(l, _, _)| *l == lid).is_none();
                if local_was_new {
                    let preds = &preds[to_bb.usize()];

                    // init phi.
                    let map = preds.iter().map(|p| (*p, None)).collect();
                    let stmt = fun.new_phi(SourceRange::null(), &[]);
                    to_phis.push((lid, map, stmt));

                    // to_bb now defines the local.
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
            fun.block_stmts_mut(bb, |stmt| { match stmt.data {
                StmtData::Param { id } |
                StmtData::Local { id } => {
                    new_names[id.usize()] = Some(stmt.id());
                }

                StmtData::GetLocal { src } => {
                    let new_name = new_names[src.usize()].unwrap();
                    stmt.data = StmtData::Copy { src: new_name };
                    new_names[src.usize()] = Some(stmt.id());
                }

                StmtData::SetLocal { dst, src } => {
                    stmt.data = StmtData::Copy { src };
                    new_names[dst.usize()] = Some(stmt.id());
                }

                _ => (),
            }});

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
        visit(BlockId::ENTRY, new_names, &mut phis, fun, &dom_tree);
    }

    // insert phis.
    {
        for (bb_index, phis) in phis.into_iter().enumerate() {
            let block = BlockId::from_usize(bb_index);
            let mut at = None.into();

            for (_, map, stmt_id) in phis {
                let map: Vec<PhiEntry> = map.into_iter().map(|(bb, src)| { (bb, src.unwrap()) }).collect();
                fun.set_phi(stmt_id, &map);

                fun.insert_after(block, at, stmt_id);
                at = stmt_id.some();
            }
        }
    }
    fun.slow_integrity_check();
}


pub fn copy_propagation_ex(fun: &mut Function, dom_tree: &DomTree) {
    fn visit(bb: BlockId, fun: &mut Function, dom_tree: &Vec<Vec<BlockId>>) {
        // inline copies.
        fun.block_replace_args(bb, |fun, arg| {
            if let StmtData::Copy { src } = arg.get(fun).data {
                let mut new_arg = src;
                while let StmtData::Copy { src } = new_arg.get(fun).data {
                    new_arg = src;
                }
                *arg = new_arg;
            }
        });

        // propagate to dominated blocks.
        for d in dom_tree[bb.usize()].iter() {
            visit(*d, fun, dom_tree);
        }
    }

    visit(BlockId::ENTRY, fun, &dom_tree);
    fun.slow_integrity_check();
}


pub fn dead_copy_elim(fun: &mut Function) {
    let mut visited = vec![false; fun.num_stmts()];
    fun.all_args(|arg| visited[arg.usize()] = true);

    fun.retain_stmts(|stmt| {
        visited[stmt.id().usize()] || !stmt.is_copy()
    });
    fun.slow_integrity_check();
}

