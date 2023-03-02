use crate::bytecode::Instruction;
use crate::Constant;
use super::*;


impl Function {
    pub fn compile_ex(&self, post_order: &PostOrder, idoms: &ImmediateDominators, dom_tree: &DomTree, fun_protos: &[u32]) -> (Vec<Instruction>, Vec<Constant>, u32) {
        let block_order = self.block_order_dominators_first(&idoms, &dom_tree);

        let (block_begins, stmt_indices) = block_order.block_begins_and_stmt_indices(self);

        // println!("block order:");
        // for bb in block_order.iter() {
        //     println!("{}", bb);
        //     self.block_stmts(*bb, |stmt| {
        //         println!("  ({}) {}", stmt_indices[stmt.id().usize()], stmt.fmt(self));
        //     });
        // }

        let live_intervals = self.live_intervals(&post_order, &block_order, &block_begins, &stmt_indices, true);

        // println!("live:");
        // for (i, interval) in live_intervals.iter().enumerate() {
        //     println!("s{i}: {interval:?}");
        // }

        let regs = alloc_regs_linear_scan(self, &live_intervals);

        let (code, constants) = generate_bytecode(self, &block_order, &regs, fun_protos);

        (code, constants, regs.num_regs as u32)
    }
}


crate::macros::define_id!(Reg, OptReg, "r{}");

pub struct RegisterAllocation {
    pub mapping:  Vec<OptReg>,
    pub num_regs: usize,
}

pub fn alloc_regs_linear_scan(fun: &Function, intervals: &LiveIntervals) -> RegisterAllocation {
    let mut intervals = intervals.intervals.clone();
    let mut joins     = fun.stmt_ids().collect::<Vec<_>>();
    let mut hints     = fun.stmt_ids().collect::<Vec<_>>();

    fn rep(stmt: StmtId, joins: &Vec<StmtId>) -> StmtId {
        let mut at = stmt;
        loop {
            let join = joins[at.usize()];
            if join == at {
                return at;
            }
            else {
                at = join;
            }
        }
    }

    fn join(a: StmtId, b: StmtId, joins: &mut Vec<StmtId>, intervals: &mut Vec<Vec<(StmtIndex, StmtIndex)>>) -> bool {
        let rep_a = rep(a, joins);
        let rep_b = rep(b, joins);
        if rep_a == rep_b {
            return true;
        }

        let int_a = &intervals[rep_a.usize()];
        let int_b = &intervals[rep_b.usize()];

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

        intervals[rep_b.usize()].clear();
        intervals[rep_a.usize()] = new_int;
        joins[rep_b.usize()] = rep_a;

        return true;
    }


    // phi joins & copy hints.
    for bb in fun.block_ids() {
        fun.block_stmts(bb, |stmt| {
            if let Some(map) = fun.try_phi(stmt.id()) {
                // join phi with args.
                for (_, arg) in map.iter() {
                    let joined = join(stmt.id(), *arg, &mut joins, &mut intervals);
                    if !joined {
                        println!("failed to join {} with {}", stmt.id(), arg);
                    }
                    assert!(joined);
                }
            }
            else if let Some(src) = stmt.try_any_copy() {
                if hints[src.usize()] == src {
                    hints[src.usize()] = stmt.id();
                }
            }
        });
    }


    #[derive(Debug)]
    struct Interval<'a> {
        stmt: StmtId,
        start: StmtIndex,
        stop:  StmtIndex,
        ranges: &'a [(StmtIndex, StmtIndex)],
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


    struct ActiveInterval<'a> {
        ranges: &'a [(StmtIndex, StmtIndex)],
        stop:   StmtIndex,
        reg:    Reg,
        live:      bool,
        allocated: bool,
        // @temp
        _stmt: StmtId,
        _start: StmtIndex,
    }

    let mut actives = vec![];
    let mut regs    = vec![false; fun.num_params()];

    let mut mapping = vec![OptReg::NONE; fun.num_stmts()];

    // assign params.
    {
        let mut i = 0;
        fun.block_stmts_ex(BlockId::ENTRY, |stmt| {
            if stmt.is_param() {
                mapping[stmt.id().usize()] = Reg(i).some();
                i += 1;
                return true;
            }
            false
        });
        assert_eq!(i, fun.num_params() as u32);
    }

    for new_int in &intervals {
        //println!("new: {:?} {}..{}", new_int.stmt, new_int.start, new_int.stop);

        // update live intervals.
        //println!("update live intervals");
        actives.retain_mut(|active: &mut ActiveInterval| {
            if !active.live {
                return true;
            }
            debug_assert!(active.allocated);
            debug_assert!(regs[active.reg.usize()]);

            //println!("  {:?}({}) {}({}) {}..{}", active._stmt, active.live, active.reg, active.allocated, active._start, active.stop);

            // expire interval.
            if active.stop <= new_int.start {
                //println!("    expired");
                regs[active.reg.usize()] = false;
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
                    regs[active.reg.usize()] = false;
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
            //println!("  {:?}({}) {}({}) {}..{}", active._stmt, active.live, active.reg, active.allocated, active._start, active.stop);

            debug_assert!(!active.allocated || regs[active.reg.usize()]);

            // expire interval.
            if active.stop <= new_int.start {
                //println!("    expired");
                if active.allocated {
                    regs[active.reg.usize()] = false;
                }
                return false;
            }

            // live again?
            let rng_start = active.ranges[0].0;
            if rng_start <= new_int.start {
                //println!("    reactivating");
                debug_assert!(active.allocated == regs[active.reg.usize()]);
                active.live      = true;
                active.allocated = true;
                regs[active.reg.usize()] = true;
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
                        regs[active.reg.usize()] = false;
                    }
                }
                // new interval intersects next range.
                else {
                    // @todo: this is broken.
                    // may be allocated by other non-live active & freed later, if that active expires.
                    // validation below will detect this, so it's not super urgent.
                    // consider ref count for registers.
                    // or a "blocked_regs" set.
                    if !active.allocated && regs[active.reg.usize()] == false {
                        //println!("    new interval intersects next range; reclaiming register.");
                        active.allocated = true;
                        regs[active.reg.usize()] = true;
                    }
                }
            }

            return true;
        });


        let reg = 'find_reg: {
            // pre-assigned.
            if let Some(reg) = mapping[new_int.stmt.usize()].to_option() {
                break 'find_reg reg;
            }

            // todo: how much does this help?
            if 1==1
            {

            // regular hint.
            {
                // @todo-opt: do rep thing after hint construction.
                let reg_hint = hints[new_int.stmt.usize()];
                if reg_hint != new_int.stmt {
                    let reg_hint = rep(reg_hint, &joins);
                    if let Some(reg) = mapping[reg_hint.usize()].to_option() {
                        if regs[reg.usize()] == false {
                            break 'find_reg reg;
                        }
                    }
                }
            }

            // first arg hint.
            'first_arg: {

                let first_arg = match new_int.stmt.get(fun).data {
                    StmtData::Copy  { src }                 => src,
                    StmtData::ParallelCopy { src, copy_id: _ } => src,
                    StmtData::Op1 { op: _, src }            => src,
                    StmtData::Op2 { op: _,  src1, src2: _ } => src1,
                    _ => break 'first_arg,
                };

                if let Some(reg) = mapping[first_arg.usize()].to_option() {
                    if regs[reg.usize()] == false {
                        break 'find_reg reg;
                    }
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

        assert!(regs[reg.usize()] == false);
        regs[reg.usize()] = true;

        //println!("{} -> {}", new_int.stmt, reg);

        actives.push(ActiveInterval {
            ranges: new_int.ranges,
            stop:   new_int.stop,
            reg,
            live:      true,
            allocated: true,

            _stmt: new_int.stmt,
            _start: new_int.start,
        });

        mapping[new_int.stmt.usize()] = reg.some();


        // @temp
        let mut allocated_by = vec![None; regs.len()];
        for active in &actives {
            if active.allocated {
                let reg = active.reg.usize();
                assert!(allocated_by[reg].is_none());
                allocated_by[reg] = Some(active._stmt);
            }
        }
        for (i, used) in regs.iter().enumerate() {
            assert!(!*used || allocated_by[i].is_some());
        }
    }

    for stmt in fun.stmt_ids() {
        let rep = rep(stmt, &joins);
        if stmt != rep {
            mapping[stmt.usize()] = mapping[rep.usize()];
        }
    }

    //println!("register allocation done. used {} registers.", regs.len());
    RegisterAllocation { mapping, num_regs: regs.len() }
}


pub fn generate_bytecode(fun: &Function, block_order: &BlockOrder, regs: &RegisterAllocation, fun_protos: &[u32]) -> (Vec<Instruction>, Vec<Constant>) {
    assert_eq!(block_order[0], BlockId::ENTRY);

    // for stmt in fun.stmt_ids() {
    //     println!("{}: {}", stmt, regs.mapping[stmt.usize()]);
    // }

    // @temp
    const NO_REG: u8 = 127;
    assert!(regs.num_regs < NO_REG as usize);
    assert!(block_order.len() < u16::MAX as usize / 2);

    // returns `NO_REG`, if no register was assigned.
    // if `NO_REG` ends up in the bytecode (which would be a bug),
    // the validator will detect this.
    let reg = |stmt: StmtId| {
        regs.mapping[stmt.usize()].to_option()
        .unwrap_or(Reg(NO_REG as u32)).value() as u8
    };

    let mut block_offsets = vec![u16::MAX; fun.num_blocks()];

    let mut bcb = crate::bytecode::ByteCodeBuilder::new();

    // @temp: constants builder (dedup).
    // @temp: @strings-first.
    let mut constants = vec![];
    for i in 0..fun.num_strings() {
        constants.push(Constant::String { value: StringId::from_usize(i).get(fun).into() });
    }

    for (block_index, bb) in block_order.iter().enumerate() {
        block_offsets[bb.usize()] = bcb.current_offset() as u16;

        let next_bb = block_order.get(block_index + 1).cloned();

        let mut stmt_cursor = bb.get(fun).first();

        while let Some(stmt_id) = stmt_cursor.to_option() {
            let stmt = stmt_id.get(fun);
            stmt_cursor = stmt.next();

            if let StmtData::ParallelCopy { src, copy_id } = stmt.data {
                let mut copied_to = vec![vec![]; regs.num_regs];
                copied_to[reg(src) as usize].push(reg(stmt_id));

                while let Some(at) = stmt_cursor.to_option() {
                    let copy_stmt = at.get(fun);
                    let StmtData::ParallelCopy { src, copy_id: cid } = copy_stmt.data else { break };
                    if cid != copy_id { break }

                    copied_to[reg(src) as usize].push(reg(at));

                    stmt_cursor = copy_stmt.next();
                }

                impl_parallel_copy(regs.num_regs, &copied_to, &mut bcb);
                

                continue;
            }
            // else (no parallel copy):

            let dst = reg(stmt.id());

            // @temp
            if dst == NO_REG && stmt.has_value() {
                continue;
            }

            use StmtData::*;
            match stmt.data {
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

                ListNew => bcb.list_new(dst),
                ListAppend { list, value } => bcb.list_append(reg(list), reg(value)),

                TupleNew { values } => {
                    let values: Vec<u8> = values.get(fun).iter().map(|arg| reg(*arg)).collect();
                    bcb.tuple_new(dst, &values);
                }

                NewFunction { id } => bcb.new_function(dst, fun_protos[id.usize()].try_into().unwrap()),

                GetIndex { base, index } => bcb.get(dst, reg(base), reg(index)),

                SetIndex { base, index, value, is_define } => {
                    if is_define { bcb.def(reg(base), reg(index), reg(value)) }
                    else         { bcb.set(reg(base), reg(index), reg(value)) }
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
                    bcb.ret(reg(src));
                }
            }
        }
    }

    let mut code = bcb.build();

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
            LIST_NEW | LIST_APPEND |
            TUPLE_NEW |
            TABLE_NEW |
            NEW_FUNCTION |
            DEF | SET | GET | LEN |
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

    (code, constants)
}

fn impl_parallel_copy(num_regs: usize, copied_to: &[Vec<u8>], bcb: &mut crate::ByteCodeBuilder) {
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
    fn copy_paths(src0: usize, src: usize, copied_to: &[Vec<u8>], status: &mut [Status], bcb: &mut crate::ByteCodeBuilder) -> bool {
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

