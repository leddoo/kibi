use crate::bytecode::{InstrWord, ByteCodeBuilder};
use crate::Constant;
use crate::index_vec::*;
use super::*;


pub struct CompileResult {
    pub code:       Vec<InstrWord>,
    pub constants:  Vec<Constant>,
    pub stack_size: u32,
    pub reg_mapping: IndexVec<Reg, Vec<ValueMapping>>,
    pub pc_to_node:  Vec<OptNodeId>,
}

#[derive(Clone, Debug)]
pub struct ValueMapping {
    pub pc_begin: u32,
    pub pc_end:   u32,
    pub values:   Vec<NodeId>,
}


impl Function {
    pub fn compile_ex(&self, post_order: &PostOrder, idoms: &ImmediateDominators, dom_tree: &DomTree) -> CompileResult {
        let block_order = self.block_order_dominators_first(&idoms, &dom_tree);

        let (block_begins, instr_indices) = block_order.block_begins_and_instr_indices(self);

        // println!("block order:");
        // for bb in block_order.iter() {
        //     println!("{}", bb);
        //     self.block_instrs(*bb, |instr| {
        //         println!("  ({}) {}", instr_indices[instr.id()], instr.fmt(self));
        //     });
        // }

        let live_intervals = self.live_intervals(&post_order, &block_order, &block_begins, &instr_indices, true);

        // println!("live:");
        // for (i, interval) in live_intervals.iter().enumerate() {
        //     println!("s{i}: {interval:?}");
        // }

        let regs = alloc_regs_linear_scan(self, &live_intervals, &instr_indices);

        let GenBytecodeResult { code, constants, stack_size, instr_index_to_pc, pc_to_node }
            = generate_bytecode(self, &block_order, &regs);

        let reg_mapping = {
            let mut mapping = index_vec![vec![]; stack_size as usize];

            for bb in self.block_ids() {
                self.block_instrs(bb, |instr| {
                    let Some(reg) = regs.mapping[instr.id()].to_option() else { return };
                    for (begin, end) in &live_intervals[instr.id()] {
                        let pc_begin = instr_index_to_pc[*begin];
                        let pc_end   = instr_index_to_pc[*end];
                        if pc_begin != pc_end {
                            let values = instr.source.values.clone();
                            mapping[reg].push(ValueMapping { pc_begin, pc_end, values });
                        }
                    }
                });
            }

            mapping
        };

        CompileResult { code, constants, stack_size, reg_mapping, pc_to_node }
    }
}


crate::macros::define_id!(Reg, OptReg, "r{}");

pub struct RegisterAllocation {
    pub mapping:  IndexVec<InstrId, OptReg>,
    pub num_regs: usize,
}

pub fn alloc_regs_linear_scan(fun: &Function, intervals: &LiveIntervals, instr_indices: &InstrIndices) -> RegisterAllocation {
    let mut intervals = intervals.intervals.clone();
    let mut joins     = fun.instr_ids().collect::<IndexVec<InstrId, InstrId>>();

    // NOTE: hints are currently disabled.
    //  they cause unintuitive behavior with loops that swap variables:
    //  the swap is done in the loop header, instead of being done at the
    //  end of the loop body, as it should be. this happens because the 
    //  parallel copies in the bb before the loop header are joined with
    //  the parallel copies at the end of the loop body. meaning they're
    //  already assigned a register when processing the loop header.
    //  and the parallel copies in the loop header get "copy src" hints
    //  from the parallel copies at the end of the loop body (these hints are
    //  currently disabled). so the parallel copies in the loop header choose
    //  the registers that the variables should end up in. meaning those parallel copies
    //  becomes the swap, if that makes sense :D
    //  also, the hints don't actually do anything for regular copies,
    //  as their arguments are always processed before them.
    //  disabling hints does sometimes result in an extra copy with cancelling
    //  boolean operators (and/or). but the code generated for those looks
    //  kinda sus anyway & should be investigated.
    let mut hints     = fun.instr_ids().collect::<IndexVec<InstrId, InstrId>>();

    fn rep(instr: InstrId, joins: &IndexVec<InstrId, InstrId>) -> InstrId {
        let mut at = instr;
        loop {
            let join = joins[at];
            if join == at {
                return at;
            }
            else {
                at = join;
            }
        }
    }

    fn join(a: InstrId, b: InstrId, joins: &mut IndexVec<InstrId, InstrId>, intervals: &mut IndexVec<InstrId, Vec<(InstrIndex, InstrIndex)>>) -> bool {
        let rep_a = rep(a, joins);
        let rep_b = rep(b, joins);
        if rep_a == rep_b {
            return true;
        }

        let int_a = &intervals[rep_a];
        let int_b = &intervals[rep_b];

        // merge intervals, checking for overlap.
        let mut new_int = Vec::with_capacity(int_a.len() + int_b.len());
        let mut at_a = 0;
        let mut at_b = 0;
        while at_a < int_a.len() || at_b < int_b.len() {
            if at_a >= int_a.len() {
                new_int.push(int_b[at_b]);
                at_b += 1;
            }
            else if at_b >= int_b.len() {
                new_int.push(int_a[at_a]);
                at_a += 1;
            }
            else {
                let (begin_a, end_a) = int_a[at_a];
                let (begin_b, end_b) = int_b[at_b];
                // a starts before b?
                if begin_a < begin_b {
                    // a ends before b?
                    if end_a < begin_b {
                        new_int.push((begin_a, end_a));
                        at_a += 1;
                    }
                    // a ends at b?
                    else if end_a == begin_b {
                        // can merge intervals.
                        new_int.push((begin_a, end_b));
                        at_a += 1;
                        at_b += 1;
                    }
                    // overlap.
                    else {
                        println!("overlap of {},{} with {},{}", begin_a,end_a, begin_b,end_b);
                        return false;
                    }
                }
                // b starts before a.
                else if begin_b < begin_a {
                    // b ends before a?
                    if end_b < begin_a {
                        new_int.push((begin_b, end_b));
                        at_b += 1;
                    }
                    // b ends at a?
                    else if end_b == begin_a {
                        // can merge intervals.
                        new_int.push((begin_b, end_a));
                        at_a += 1;
                        at_b += 1;
                    }
                    // overlap.
                    else {
                        println!("overlap of {},{} with {},{}", begin_a,end_a, begin_b,end_b);
                        return false;
                    }
                }
                // overlap.
                else {
                    println!("overlap of {},{} with {},{}", begin_a,end_a, begin_b,end_b);
                    return false;
                }
            }
        }

        intervals[rep_b].clear();
        intervals[rep_a] = new_int;
        joins[rep_b] = rep_a;

        return true;
    }


    // phi joins & copy hints.
    for bb in fun.block_ids() {
        fun.block_instrs(bb, |instr| {
            if let Some(map) = fun.try_phi(instr.id()) {
                let mut join_into       = instr.id();
                let mut join_into_index = instr_indices[join_into];

                // join phi with args.
                for (_, arg) in map.iter().copied() {
                    let arg_index = instr_indices[arg];
                    let other =
                        if arg_index < join_into_index {
                            let other = join_into;
                            join_into       = arg;
                            join_into_index = arg_index;
                            other
                        }
                        else { arg };

                    let joined = join(join_into, other, &mut joins, &mut intervals);
                    if !joined {
                        println!("failed to join {} with {}", join_into, other);
                    }
                    assert!(joined);
                }
            }
            else if let Some(src) = instr.try_any_copy() {
                if hints[src] == src {
                    hints[src] = instr.id();
                }
            }
        });
    }


    #[derive(Debug)]
    struct Interval<'a> {
        instr: InstrId,
        start: InstrIndex,
        stop:  InstrIndex,
        ranges: &'a [(InstrIndex, InstrIndex)],
    }

    let mut intervals =
        intervals.iter().enumerate()
        .filter_map(|(i, ranges)| {
            if ranges.len() == 0 { return None }
            Some(Interval {
                instr:  InstrId::from_usize(i),
                start: ranges[0].0,
                stop:  ranges[ranges.len()-1].1,
                ranges,
            })
        }).collect::<Vec<_>>();
    intervals.sort_unstable_by(|a, b| a.start.cmp(&b.start));


    struct ActiveInterval<'a> {
        ranges: &'a [(InstrIndex, InstrIndex)],
        stop:   InstrIndex,
        reg:    Reg,
        live:      bool,
        allocated: bool,
        // @temp
        _instr: InstrId,
        _start: InstrIndex,
    }

    let mut actives = vec![];
    let mut regs    = index_vec![false; fun.num_params()];

    let mut mapping = index_vec![OptReg::NONE; fun.num_instrs()];

    // assign params.
    {
        let mut i = 0;
        fun.block_instrs_ex(BlockId::ENTRY, |instr| {
            if instr.is_param() {
                mapping[instr.id()] = Reg(i).some();
                i += 1;
                return true;
            }
            false
        });
        assert_eq!(i, fun.num_params() as u32);
    }

    for new_int in &intervals {
        //println!("new: {:?} {}..{}", new_int.instr, new_int.start, new_int.stop);

        // update live intervals.
        //println!("update live intervals");
        actives.retain_mut(|active: &mut ActiveInterval| {
            if !active.live {
                return true;
            }
            debug_assert!(active.allocated);
            debug_assert!(regs[active.reg]);

            //println!("  {:?}({}) {}({}) {}..{}", active._instr, active.live, active.reg, active.allocated, active._start, active.stop);

            // expire interval.
            if active.stop <= new_int.start {
                //println!("    expired");
                regs[active.reg] = false;
                return false;
            }

            // no longer live.
            let rng_stop = active.ranges[0].1;
            if rng_stop <= new_int.start {
                //println!("    now inactive");
                // free register if new interval fits in hole.
                let next_start = active.ranges[1].0;
                if next_start >= new_int.stop {
                    //println!("    new interval fits in hole; freeing register.");
                    active.allocated = false;
                    regs[active.reg] = false;
                }

                active.ranges = &active.ranges[1..];
                active.live   = false;
            }

            return true;
        });

        //println!("update non-live intervals");
        actives.retain_mut(|active: &mut ActiveInterval| {
            if active.live {
                return true;
            }
            //println!("  {:?}({}) {}({}) {}..{}", active._instr, active.live, active.reg, active.allocated, active._start, active.stop);

            debug_assert!(!active.allocated || regs[active.reg]);

            // expire interval.
            if active.stop <= new_int.start {
                //println!("    expired");
                if active.allocated {
                    regs[active.reg] = false;
                }
                return false;
            }

            // skipped range?
            let rng_end = active.ranges[0].1;
            if rng_end <= new_int.start {
                //println!("    skipped range");
                // need to have another range.
                // otherwise would have expired.
                active.ranges = &active.ranges[1..];
                // @todo: should this be a loop?
                //  does the "otherwise would have expired" argument still hold then?
            }

            // live again?
            let rng_start = active.ranges[0].0;
            if rng_start <= new_int.start {
                //println!("    reactivating");
                debug_assert!(active.allocated == regs[active.reg]);
                active.live      = true;
                active.allocated = true;
                regs[active.reg] = true;
            }
            // remains non-live.
            else {
                // check interval overlap.
                let mut no_overlap = new_int.stop <= rng_start;

                // todo: how much does this help?
                // check range overlap.
                if !no_overlap {
                    let int_a = new_int.ranges;
                    let int_b = active.ranges;

                    no_overlap = true;

                    let mut at_a = 0;
                    let mut at_b = 0;
                    while at_a < int_a.len() && at_b < int_b.len() {
                        let (begin_a, end_a) = int_a[at_a];
                        let (begin_b, end_b) = int_b[at_b];

                        if end_a <= begin_b {
                            at_a += 1;
                        }
                        else if end_b <= begin_a {
                            at_b += 1;
                        }
                        else {
                            //println!("intersecion: {},{} {},{}", begin_a, end_a, begin_b, end_b);
                            no_overlap = false;
                            break;
                        }
                    }
                }

                // new interval fits in hole?
                if no_overlap {
                    // try to free register.
                    if active.allocated {
                        //println!("    new interval fits in hole; freeing register.");
                        active.allocated = false;
                        regs[active.reg] = false;
                    }
                }
                // new interval intersects next range.
                else {
                    // @todo: this is broken.
                    // may be allocated by other non-live active & freed later, if that active expires.
                    // validation below will detect this, so it's not super urgent.
                    // consider ref count for registers.
                    // or a "blocked_regs" set.
                    if !active.allocated && regs[active.reg] == false {
                        //println!("    new interval intersects next range; reclaiming register.");
                        active.allocated = true;
                        regs[active.reg] = true;
                    }
                }
            }

            return true;
        });


        let reg = 'find_reg: {
            // pre-assigned.
            if let Some(reg) = mapping[new_int.instr].to_option() {
                break 'find_reg reg;
            }

            // regular hint.
            if 0==1 {
                // @todo-opt: do rep thing after hint construction.
                let reg_hint = hints[new_int.instr];
                if reg_hint != new_int.instr {
                    let reg_hint = rep(reg_hint, &joins);
                    if let Some(reg) = mapping[reg_hint].to_option() {
                        if regs[reg] == false {
                            break 'find_reg reg;
                        }
                    }
                }
            }

            // first arg hint.
            'first_arg: {
                let first_arg = match new_int.instr.get(fun).data {
                    InstrData::Copy  { src }                 => src,
                    InstrData::ParallelCopy { src, copy_id: _ } => src,
                    InstrData::Op1 { op: _, src }            => src,
                    InstrData::Op2 { op: _,  src1, src2: _ } => src1,
                    InstrData::WritePath { path_id, value: _, is_def: _ } => {
                        match path_id.get(fun).base {
                            PathBase::Instr(base) => base,
                            PathBase::Items | PathBase::Env => break 'first_arg,
                        }
                    }
                    _ => break 'first_arg,
                };

                let first_arg = rep(first_arg, &joins);

                if let Some(reg) = mapping[first_arg].to_option() {
                    if regs[reg] == false {
                        break 'find_reg reg;
                    }
                }
            }

            // reuse some register.
            if let Some(reg) = regs.iter().position(|used| *used == false) {
                break 'find_reg Reg(reg as u32);
            }

            // alloc new register.
            let reg = regs.len() as u32;
            regs.push(false);
            Reg(reg)
        };

        assert!(regs[reg] == false);
        regs[reg] = true;

        //println!("{} -> {}", new_int.instr, reg);

        actives.push(ActiveInterval {
            ranges: new_int.ranges,
            stop:   new_int.stop,
            reg,
            live:      true,
            allocated: true,

            _instr: new_int.instr,
            _start: new_int.start,
        });

        mapping[new_int.instr] = reg.some();


        // @temp
        let mut allocated_by = index_vec![None; regs.len()];
        for active in &actives {
            if active.allocated {
                let reg = active.reg;
                assert!(allocated_by[reg].is_none());
                allocated_by[reg] = Some(active._instr);
            }
        }
        for (i, used) in regs.iter().enumerate() {
            let reg = Reg::from_usize(i);
            assert!(!*used || allocated_by[reg].is_some());
        }
    }

    for instr in fun.instr_ids() {
        let rep = rep(instr, &joins);
        if instr != rep {
            mapping[instr] = mapping[rep];
        }
    }

    //println!("register allocation done. used {} registers.", regs.len());
    RegisterAllocation { mapping, num_regs: regs.len() }
}


pub struct GenBytecodeResult {
    pub code:              Vec<InstrWord>,
    pub constants:         Vec<Constant>,
    pub stack_size:        u32,
    pub instr_index_to_pc: IndexVec<InstrIndex, u32>,
    pub pc_to_node:        Vec<OptNodeId>,
}

pub fn generate_bytecode(fun: &Function, block_order: &BlockOrder, regs: &RegisterAllocation) -> GenBytecodeResult {
    assert_eq!(block_order[0], BlockId::ENTRY);

    // for instr in fun.instr_ids() {
    //     println!("{}: {:?}", instr, regs.mapping[instr]);
    // }

    // @temp
    const NO_REG: u8 = 127;
    assert!(regs.num_regs < NO_REG as usize);
    assert!(block_order.len() < u16::MAX as usize / 2);

    let num_regs = regs.num_regs as u32;

    // returns `NO_REG`, if no register was assigned.
    // if `NO_REG` ends up in the bytecode (which would be a bug),
    // the validator will detect this.
    let reg = |instr: InstrId| {
        regs.mapping[instr].to_option()
        .unwrap_or(Reg(NO_REG as u32)).value() as u8
    };

    let mut block_offsets = vec![u16::MAX; fun.num_blocks()];

    let mut bcb = ByteCodeBuilder::new();

    // @temp: constants builder (dedup).
    // @temp: @strings-first.
    let mut constants = vec![];
    for i in 0..fun.num_strings() {
        constants.push(Constant::String { value: StringId::from_usize(i).get(fun).into() });
    }

    let mut instr_index_to_pc = index_vec![];
    let mut pc_to_node = vec![];

    #[inline(always)]
    fn map_pcs_to_node<F: FnOnce(&mut ByteCodeBuilder)>(node: OptNodeId, bcb: &mut ByteCodeBuilder, pc_to_node: &mut Vec<OptNodeId>, f: F) {
        let old_offset = bcb.current_offset();
        f(bcb);
        let new_offset = bcb.current_offset();
        for _ in old_offset..new_offset {
            pc_to_node.push(node);
        }
    }

    for (block_index, bb) in block_order.iter().enumerate() {
        block_offsets[bb.usize()] = bcb.current_offset() as u16;

        let next_bb = block_order.get(block_index + 1).cloned();

        let mut instr_cursor = bb.get(fun).first();

        while let Some(instr_id) = instr_cursor.to_option() {
            let instr = instr_id.get(fun);
            instr_cursor = instr.next();

            if let InstrData::ParallelCopy { src, copy_id } = instr.data {
                let mut copied_to = vec![vec![]; regs.num_regs];
                copied_to[reg(src) as usize].push(reg(instr_id));

                while let Some(at) = instr_cursor.to_option() {
                    instr_index_to_pc.push(bcb.current_offset() as u32);

                    let copy_instr = at.get(fun);
                    let InstrData::ParallelCopy { src, copy_id: cid } = copy_instr.data else { break };
                    if cid != copy_id { break }

                    copied_to[reg(src) as usize].push(reg(at));

                    instr_cursor = copy_instr.next();
                }

                map_pcs_to_node(None.into(), &mut bcb, &mut pc_to_node, |bcb| {
                    impl_parallel_copy(regs.num_regs, &copied_to, bcb);
                });

                continue;
            }
            // else (no parallel copy):

            instr_index_to_pc.push(bcb.current_offset() as u32);

            let dst = reg(instr.id());

            // @temp
            if dst == NO_REG && instr.has_value() {
                continue;
            }

            map_pcs_to_node(instr.source.node, &mut bcb, &mut pc_to_node, |bcb| {
                use InstrData::*;
                match instr.data {
                    Copy { src } => {
                        let src = reg(src);
                        if dst != src { bcb.copy(dst, src) }
                    }

                    Phi { map_id: _ } => (),

                    ParallelCopy { src: _, copy_id: _ } => unreachable!(),

                    Param { id: _ } |
                    Local { id: _ } => (),

                    GetLocal { src: _ } |
                    SetLocal { dst: _, src: _ } => unimplemented!(),

                    LoadEnv => bcb.load_env(dst),

                    LoadNil             => bcb.load_nil(dst),
                    LoadBool  { value } => bcb.load_bool(dst, value),

                    LoadInt { value } => {
                        if let Ok(v) = value.try_into() {
                            bcb.load_int(dst, v);
                        }
                        else {
                            // @temp: integers.
                            let c = constants.len();
                            constants.push(Constant::Number { value: value as f64 });
                            bcb.load_const(dst, c as u16);
                        }
                    }

                    LoadFloat { value } => {
                        let c = constants.len();
                        constants.push(Constant::Number { value });
                        bcb.load_const(dst, c as u16);
                    }

                    LoadString { id } => {
                        // @strings-first.
                        bcb.load_const(dst, id.usize() as u16);
                    }

                    ListNew { values } => {
                        let values: Vec<u8> = values.get(fun).iter().map(|arg| reg(*arg)).collect();
                        bcb.list_new(dst, &values);
                    }

                    TupleNew { values } => {
                        let values: Vec<u8> = values.get(fun).iter().map(|arg| reg(*arg)).collect();
                        bcb.tuple_new(dst, &values);
                    }

                    TupleNew0 => {
                        bcb.load_unit(dst);
                    }

                    ReadPath { path_id } => {
                        let path = path_id.get(fun);

                        let base = match path.base {
                            PathBase::Items        => crate::bytecode::PathBase::ITEMS,
                            PathBase::Env          => crate::bytecode::PathBase::ENV,
                            PathBase::Instr(instr) => crate::bytecode::PathBase::reg(reg(instr)),
                        };

                        let keys = path.keys.iter().map(|key| match key {
                            // @strings-first.
                            PathKey::Field(field) => crate::bytecode::PathKey::Field { string: field.usize() as u16 },
                            PathKey::Index(index) => crate::bytecode::PathKey::Index { reg: reg(*index) },
                        }).collect::<Vec<_>>();

                        bcb.read_path(dst, base, &keys);
                    }

                    WritePath { path_id, value, is_def } => {
                        let path = path_id.get(fun);

                        let base = match path.base {
                            PathBase::Items => crate::bytecode::PathBase::ITEMS,
                            PathBase::Env   => crate::bytecode::PathBase::ENV,
                            PathBase::Instr(instr) => {
                                let base = reg(instr);
                                assert_eq!(dst, base);
                                crate::bytecode::PathBase::reg(base)
                            }
                        };

                        let keys = path.keys.iter().map(|key| match key {
                            // @strings-first.
                            PathKey::Field(field) => crate::bytecode::PathKey::Field { string: field.usize() as u16 },
                            PathKey::Index(index) => crate::bytecode::PathKey::Index { reg: reg(*index) },
                        }).collect::<Vec<_>>();

                        bcb.write_path(base, &keys, reg(value), is_def);
                    }

                    Call { func, args_id } => {
                        let args: Vec<u8> = args_id.get(fun).iter().map(|arg| reg(*arg)).collect();
                        bcb.call(dst, reg(func), &args);
                    }

                    Op1 { op, src } => {
                        let src = reg(src);
                        use self::Op1::*;
                        match op {
                            Not    => bcb.not(dst, src),
                            Negate => bcb.negate(dst, src),
                        }
                    }

                    Op2 { op, src1, src2 } => {
                        let src1 = reg(src1);
                        let src2 = reg(src2);
                        use self::Op2::*;
                        match op {
                            Add         => bcb.add(dst, src1, src2),
                            Sub         => bcb.sub(dst, src1, src2),
                            Mul         => bcb.mul(dst, src1, src2),
                            Div         => bcb.div(dst, src1, src2),
                            FloorDiv    => bcb.floor_div(dst, src1, src2),
                            Rem         => bcb.rem(dst, src1, src2),
                            And         => unimplemented!(),
                            Or          => unimplemented!(),
                            CmpEq       => bcb.cmp_eq(dst, src1, src2),
                            CmpNe       => bcb.cmp_ne(dst, src1, src2),
                            CmpLe       => bcb.cmp_le(dst, src1, src2),
                            CmpLt       => bcb.cmp_lt(dst, src1, src2),
                            CmpGe       => bcb.cmp_ge(dst, src1, src2),
                            CmpGt       => bcb.cmp_gt(dst, src1, src2),
                            OrElse      => unimplemented!(),
                        }
                    }

                    Jump { target } => {
                        if Some(target) != next_bb {
                            bcb.jump(target.usize() as u16);
                        }
                    }

                    // @todo-opt: special case if neither branch is next_bb.
                    SwitchBool { src, on_true, on_false } => {
                        if Some(on_true) != next_bb {
                            bcb.jump_true(reg(src), on_true.usize() as u16);
                        }
                        if Some(on_false) != next_bb {
                            bcb.jump_false(reg(src), on_false.usize() as u16);
                        }
                    }

                    // @todo-opt: special case if neither branch is next_bb.
                    SwitchNil { src, on_nil, on_non_nil } => {
                        if Some(on_nil) != next_bb {
                            bcb.jump_nil(reg(src), on_nil.usize() as u16);
                        }
                        if Some(on_non_nil) != next_bb {
                            bcb.jump_non_nil(reg(src), on_non_nil.usize() as u16);
                        }
                    }

                    Return { src } => {
                        bcb.ret(reg(src));
                    }
                }
            });
        }
    }

    let mut code = bcb.build();

    assert_eq!(pc_to_node.len(), code.len());

    let mut i = 0;
    while i < code.len() {
        let instr = &mut code[i];
        i += 1;

        use crate::bytecode::opcode::*;
        match instr.opcode() as u8 {
            JUMP | JUMP_TRUE | JUMP_FALSE | JUMP_NIL | JUMP_NOT_NIL => {
                let block = instr.u16() as usize;
                instr.patch_u16(block_offsets[block]);
            }

            NOP | UNREACHABLE |
            COPY | SWAP |
            LOAD_NIL | LOAD_BOOL | LOAD_INT | LOAD_CONST | LOAD_ENV |
            LIST_NEW |
            TUPLE_NEW | LOAD_UNIT |
            MAP_NEW |
            READ_PATH | WRITE_PATH | WRITE_PATH_DEF |
            ADD | SUB | MUL | DIV | FLOOR_DIV | REM |
            ADD_INT | NEGATE |
            NOT |
            CMP_EQ | CMP_NE | CMP_LE | CMP_LT | CMP_GE | CMP_GT |
            CALL | RET |
            EXTRA
            => (),

            0 | END ..= 254 => unreachable!(),
        }
    }

    GenBytecodeResult { code, constants, stack_size: num_regs, instr_index_to_pc, pc_to_node }
}

fn impl_parallel_copy(num_regs: usize, copied_to: &[Vec<u8>], bcb: &mut ByteCodeBuilder) {
    #[derive(Clone, Copy, Debug, PartialEq)]
    enum Status {
        None,
        Visited, // but not written to.
        Path,
        Cycle      { prev: u8 },
        CycleStart { last: u8 },
    }

    let mut status = vec![Status::None; num_regs];


    // returns whether `src` is in a cycle starting at `src0`.
    fn copy_paths(src0: usize, src: usize, copied_to: &[Vec<u8>], status: &mut [Status], bcb: &mut ByteCodeBuilder) -> bool {
        debug_assert_eq!(status[src], Status::None);
        status[src] = Status::Visited;

        let mut cycle = false;
        for dst in copied_to[src].iter().copied() {
            let dst = dst as usize;

            if dst == src0 {
                assert!(cycle == false);
                cycle = true;

                assert_eq!(status[src0], Status::Visited);
                status[src0] = Status::CycleStart { last: src as u8 };
            }
            else if status[dst] == Status::Visited {
                status[dst] = Status::Path;
                bcb.copy(dst as u8, src as u8);
            }
            else {
                assert_eq!(status[dst], Status::None);

                let new_cycle = copy_paths(src0, dst, copied_to, status, bcb);
                if new_cycle {
                    assert!(cycle == false);
                    cycle = true;

                    status[dst] = Status::Cycle { prev: src as u8 };
                }
                else {
                    status[dst] = Status::Path;
                    bcb.copy(dst as u8, src as u8);
                }
            }
            debug_assert!(status[dst] != Status::None && status[dst] != Status::Visited);
        }

        cycle
    }
    for src in 0..num_regs {
        if status[src] == Status::None {
            copy_paths(src, src, copied_to, &mut status, bcb);
        }
    }
    
    // copy cycles.
    for src0 in 0..num_regs {
        if let Status::CycleStart { last } = status[src0] {
            // self-cycle, don't need any swaps.
            if last as usize == src0 {
                continue;
            }

            bcb.swap(src0 as u8, last);

            let mut at = last as usize;
            loop {
                let Status::Cycle { prev } = status[at] else { unreachable!() };
                if prev as usize == src0 {
                    break
                }
                bcb.swap(at as u8, prev);

                at = prev as usize;
            }
        }
    }
}

