use crate::bytecode::Instruction;
use crate::Constant;
use super::*;


impl Function {
    pub fn compile_ex(&self, post_order: &PostOrder, idoms: &ImmediateDominators, dom_tree: &DomTree) -> (Vec<Instruction>, Vec<Constant>, u32) {
        let block_order = self.block_order_dominators_first(&idoms, &dom_tree);

        let (block_begins, stmt_indices) = block_order.block_begins_and_stmt_indices(self);


        let live_intervals = self.live_intervals(&post_order, &block_order, &block_begins, &stmt_indices);

        let regs = alloc_regs_linear_scan(self, &live_intervals);

        let (code, constants) = generate_bytecode(self, &block_order, &regs);

        (code, constants, regs.num_regs)
    }
}


pub struct RegisterAllocation {
    pub mapping:  Vec<u32>,
    pub num_regs: u32,
}

pub fn alloc_regs_linear_scan(fun: &Function, live_intervals: &LiveIntervals) -> RegisterAllocation {
    let mut intervals = live_intervals.intervals.clone();
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


    for bb in fun.block_ids() {
        fun.block_stmts_ex(bb, |stmt| {
            if let Some(map) = fun.try_phi(stmt.id()) {
                // join phi with args.
                for (_, arg) in map.iter() {
                    let StmtData::PhiArg { src: arg_src } = arg.get(fun).data else { unreachable!() };
                    hints[arg_src.usize()] = *arg;

                    let joined = join(stmt.id(), *arg, &mut joins, &mut intervals);
                    assert!(joined);
                }
                return true;
            }
            false
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
        reg:    u32,
        live:      bool,
        allocated: bool,
        // @temp
        _stmt: StmtId,
        _start: StmtIndex,
    }

    let mut actives = vec![];
    let mut regs    = <Vec<bool>>::new();

    let mut mapping = vec![u32::MAX; fun.num_stmts()];

    for new_int in &intervals {
        //println!("new: {:?} {}..{}", new_int.stmt, new_int.start, new_int.stop);

        // update live intervals.
        //println!("update live intervals");
        actives.retain_mut(|active: &mut ActiveInterval| {
            if !active.live {
                return true;
            }
            debug_assert!(active.allocated);
            debug_assert!(regs[active.reg as usize]);

            //println!("  {:?}({}) r{}({}) {}..{}", active._stmt, active.live, active.reg, active.allocated, active._start, active.stop);

            // expire interval.
            if active.stop <= new_int.start {
                //println!("    expired");
                regs[active.reg as usize] = false;
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
                    regs[active.reg as usize] = false;
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
            //println!("  {:?}({}) r{}({}) {}..{}", active._stmt, active.live, active.reg, active.allocated, active._start, active.stop);

            debug_assert!(!active.allocated || regs[active.reg as usize]);

            // expire interval.
            if active.stop <= new_int.start {
                //println!("    expired");
                if active.allocated {
                    regs[active.reg as usize] = false;
                }
                return false;
            }

            // live again?
            let rng_start = active.ranges[0].0;
            if rng_start <= new_int.start {
                //println!("    reactivating");
                debug_assert!(active.allocated == regs[active.reg as usize]);
                active.live      = true;
                active.allocated = true;
                regs[active.reg as usize] = true;
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
                        regs[active.reg as usize] = false;
                    }
                }
                // new interval intersects next range.
                else {
                    // @todo: this is broken.
                    // may be allocated by other non-live active & freed later, if that active expires.
                    // validation below will detect this, so it's not super urgent.
                    // consider ref count for registers.
                    // or a "blocked_regs" set.
                    if !active.allocated && regs[active.reg as usize] == false {
                        //println!("    new interval intersects next range; reclaiming register.");
                        active.allocated = true;
                        regs[active.reg as usize] = true;
                    }
                }
            }

            return true;
        });


        let reg = 'find_reg: {
            // todo: how much does this help?
            if 1==1
            {

            // regular hint.
            {
                let reg_hint = hints[new_int.stmt.usize()];
                let reg = mapping[reg_hint.usize()];
                if reg != u32::MAX && regs[reg as usize] == false {
                    break 'find_reg reg;
                }
            }

            // first arg hint.
            'first_arg: {
                let first_arg = match new_int.stmt.get(fun).data {
                    StmtData::Copy  { src }                 => src,
                    StmtData::PhiArg { src }                => src,
                    StmtData::Op1 { op: _, src }            => src,
                    StmtData::Op2 { op: _,  src1, src2: _ } => src1,
                    _ => break 'first_arg,
                };

                let reg = mapping[first_arg.usize()];
                if reg != u32::MAX && regs[reg as usize] == false {
                    break 'find_reg reg;
                }
            }

            // phi hint.
            if let Some(map) = fun.try_phi(new_int.stmt) {
                for (_, arg) in map.iter() {
                    let StmtData::PhiArg { src } = arg.get(fun).data else { unreachable!() };

                    let reg = mapping[src.usize()];
                    if reg != u32::MAX && regs[reg as usize] == false {
                        break 'find_reg reg;
                    }
                }
            }

            }

            // reuse register.
            if let Some(reg) = regs.iter().position(|used| *used == false) {
                break 'find_reg reg as u32;
            }

            // alloc new register.
            let reg = regs.len() as u32;
            regs.push(false);
            reg
        };

        assert!(regs[reg as usize] == false);
        regs[reg as usize] = true;

        // println!("{} -> r{}", new_int.stmt, reg);

        actives.push(ActiveInterval {
            ranges: new_int.ranges,
            stop:   new_int.stop,
            reg,
            live:      true,
            allocated: true,

            _stmt: new_int.stmt,
            _start: new_int.start,
        });

        mapping[new_int.stmt.usize()] = reg;


        // @temp
        let mut allocated_by = vec![None; regs.len()];
        for active in &actives {
            if active.allocated {
                let reg = active.reg as usize;
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
    RegisterAllocation { mapping, num_regs: regs.len() as u32 }
}


pub fn generate_bytecode(fun: &Function, block_order: &BlockOrder, regs: &RegisterAllocation) -> (Vec<Instruction>, Vec<Constant>) {
    assert_eq!(block_order[0], BlockId::ROOT);
    assert_eq!(block_order[1], BlockId::REAL_ENTRY);

    // @temp
    assert!(regs.num_regs < 128);
    assert!(block_order.len() < u16::MAX as usize / 2);

    let reg = |stmt: StmtId| regs.mapping[stmt.usize()] as u8;

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

        // don't generate code for the @param-block.
        if block_index == 0 {
            continue;
        }

        fun.block_stmts(*bb, |stmt| {
            let dst = reg(stmt.id());

            // @temp
            if dst == 255 && stmt.has_value() {
                return
            }

            let next_bb = block_order.get(block_index + 1).cloned();

            use StmtData::*;
            match stmt.data {
                Copy { src } | PhiArg { src } => {
                    let src = reg(src);
                    if dst != src { bcb.copy(dst, src) }
                }

                Phi { map_id: _ } => (),

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

                GetIndex { base, index } => bcb.get(dst, reg(base), reg(index)),

                SetIndex { base, index, value, is_define } => {
                    if is_define { bcb.def(reg(base), reg(index), reg(value)) }
                    else         { bcb.set(reg(base), reg(index), reg(value)) }
                }

                Call { func, args_id } => {
                    let args: Vec<u8> = args_id.get(fun).iter().map(|arg| reg(*arg)).collect();
                    bcb.gather_call(reg(func), &args, dst, 1);
                }

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

    (code, constants)
}

