use crate::index_vec::*;
use super::*;


// - conventional ssa: phis & all their arguments don't interfere (live intervals don't overlap & can be joined).
// - assumes there are no critical edges.
// - inserts parallel copies for phi arguments in predecessor blocks.
// - inserts parallel copies for phi outputs after phis.
// - obviously not idempotent.
pub fn convert_to_cssa_naive(fun: &mut Function, preds: &Predecessors) {
    // reused across iterations. cleared at end of iter.
    let mut pred_copy_ids = index_vec![None; fun.num_blocks()];

    for bb in fun.block_ids() {
        if let Some(first_phi) = fun.block_first_phi(bb).to_option() {
            let phis_copy_id = fun.new_parallel_copy_id();

            for pred in preds[bb].iter() {
                pred_copy_ids[*pred] = Some(fun.new_parallel_copy_id());
            }

            let mut new_phi_cursor = OptStmtId::NONE;
            let mut old_phi_cursor = first_phi.some();
            while let Some(at) = old_phi_cursor.to_option() {
                let Some(phi_map) = fun.try_phi(at) else { break };

                // parallel copies for predecessors.
                // update phi map.
                let mut phi_map = phi_map.to_vec();
                for (pred, src) in &mut phi_map {
                    let source = src.get(fun).source;
                    let copy_id = pred_copy_ids[*pred].unwrap();
                    let copy = fun.new_stmt(source,
                        StmtData::ParallelCopy { src: *src, copy_id });

                    fun.insert_before_terminator(*pred, copy);
                    *src = copy;
                }
                fun.set_phi(at, &phi_map);

                // make parallel copies for own phis.
                // the phis themselves become the parallel copies,
                // so uses don't have to be updated.
                // new phis are inserted at the start of the block.
                let phi = at.get(fun);
                let new_phi = fun.new_stmt(phi.source, phi.data);

                let phi = at.get_mut(fun);
                phi.data = StmtData::ParallelCopy { src: new_phi, copy_id: phis_copy_id };
                old_phi_cursor = phi.next();

                fun.insert_after(bb, new_phi_cursor, new_phi);
                new_phi_cursor = new_phi.some();
            }

            // clear copy ids.
            for copy_id in &mut pred_copy_ids {
                *copy_id = None;
            }
        }
    }
}
