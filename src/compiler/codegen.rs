use crate::bytecode::Instruction;
use super::*;


impl Function {
    pub fn compile_mut_ex(&mut self, post_order: &PostOrder, idoms: &ImmediateDominators, dom_tree: &DomTree) -> Vec<Instruction> {
        // insert phi copies.
        {
            for bb in self.block_ids() {
                let mut at = bb.get(self).first();
                while let Some(current) = at.to_option() {
                    self.try_phi_mut(current, |fun, mut map| {
                        for (from_bb, stmt) in map.iter_mut() {
                            let copy = fun.new_stmt(SourceRange::null(), StmtData::Copy { src: *stmt });
                            fun.insert_before_terminator(*from_bb, copy);
                            *stmt = copy;
                        }
                    });

                    at = current.get(self).next();
                }
            }
        }
        self.slow_integrity_check();


        let block_order = self.block_order_dominators_first(&idoms, &dom_tree);

        let (block_begins, stmt_indices) = block_order.block_begins_and_stmt_indices(self);


        let live_intervals = self.live_intervals(&post_order, &block_order, &block_begins, &stmt_indices);

        let regs = alloc_regs_linear_scan(self, &live_intervals);

        let code = generate_bytecode(self, &block_order, &regs);

        code
    }
}


pub struct RegisterAllocation {
    pub mapping:  Vec<u32>,
    pub num_regs: u32,
}

pub fn alloc_regs_linear_scan(fun: &Function, live_intervals: &LiveIntervals) -> RegisterAllocation {
    #[derive(Debug)]
    struct Interval<'a> {
        stmt: StmtId,
        start: StmtIndex,
        stop:  StmtIndex,
        ranges: &'a [(StmtIndex, StmtIndex)],
    }

    let mut intervals =
        live_intervals.iter().enumerate()
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


    let mut constraints = vec![None; fun.num_stmts()];
    let mut next_constraint_reg = 0u32;

    for bb in fun.block_ids() {
        fun.block_stmts_ex(bb, |stmt| {
            if let Some(map) = fun.try_phi(stmt.id()) {
                let constraint_reg = next_constraint_reg;
                next_constraint_reg += 1;

                debug_assert!(constraints[stmt.id().usize()].is_none());
                constraints[stmt.id().usize()] = Some(constraint_reg);

                for (_, src) in map.iter() {
                    debug_assert!(constraints[src.usize()].is_none());
                    constraints[src.usize()] = Some(constraint_reg);
                }

                return true;
            }
            false
        });
    }


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

    let mut constraint_regs = vec![None; next_constraint_reg as usize];

    let mut mapping = vec![u32::MAX; fun.num_stmts()];

    for new_int in &intervals {
        //println!("new: {:?} {}..{}", new_int.stmt, new_int.start, new_int.stop);

        let constraint     = constraints[new_int.stmt.usize()];
        let constraint_reg = constraint.and_then(|c| constraint_regs[c as usize]);

        // update live intervals.
        //println!("update live intervals");
        actives.retain_mut(|active: &mut ActiveInterval| {
            if !active.live {
                return true;
            }
            debug_assert!(active.allocated);
            debug_assert!(regs[active.reg as usize]);

            //println!("  {:?}({}) r{}({}) {}..{}", active.stmt, active.live, active.reg, active.allocated, active.start, active.stop);

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
                // note: constraints make this a non-local check,
                // so assume new interval doesn't fit, if constrained.
                let next_start = active.ranges[1].0;
                if next_start >= new_int.stop && constraint.is_none() {
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
            //println!("  {:?}({}) r{}({}) {}..{}", active.stmt, active.live, active.reg, active.allocated, active.start, active.stop);

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
                // new interval fits in hole?
                if new_int.stop <= rng_start {
                    // try to free register.
                    // again, be conservative if there are constraints.
                    if active.allocated && constraint.is_none() {
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

        let reg =
            if let Some(reg) = constraint_reg {
                assert!(regs[reg as usize] == false);
                regs[reg as usize] = true;
                reg
            }
            else if let Some(reg) = regs.iter().position(|used| *used == false) {
                regs[reg] = true;
                reg as u32
            }
            else {
                let reg = regs.len();
                regs.push(true);
                reg as u32
            };

        if let (Some(constraint), None) = (constraint, constraint_reg) {
            constraint_regs[constraint as usize] = Some(reg);
        }

        //println!("-> r{}", reg);

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

    //println!("register allocation done. used {} registers.", regs.len());
    RegisterAllocation { mapping, num_regs: regs.len() as u32 }
}


pub fn generate_bytecode(fun: &Function, block_order: &BlockOrder, regs: &RegisterAllocation) -> Vec<Instruction> {
    let mut bcb = crate::bytecode::ByteCodeBuilder::new();

    // @temp
    assert!(regs.num_regs < 128);
    assert!(block_order.len() < u16::MAX as usize / 2);

    let reg = |stmt: StmtId| regs.mapping[stmt.usize()] as u8;

    let mut block_offsets = vec![u16::MAX; fun.num_blocks()];

    for (block_index, bb) in block_order.iter().enumerate() {
        block_offsets[bb.usize()] = bcb.current_offset() as u16;

        fun.block_stmts(*bb, |stmt| {
            let dst = reg(stmt.id());

            // @temp
            if dst == 255 && !stmt.is_terminator() {
                return
            }

            let next_bb = block_order.get(block_index + 1).cloned();

            use StmtData::*;
            match stmt.data {
                Copy { src } => {
                    let src = reg(src);
                    if dst != src { bcb.copy(dst, src) }
                }

                Phi { map_id: _ } => (),

                GetLocal { src: _ } |
                SetLocal { dst: _, src: _ } => unimplemented!(),

                LoadNil             => bcb.load_nil(dst),
                LoadBool  { value } => bcb.load_bool(dst, value),
                LoatInt   { value: _ } => unimplemented!(),
                LoadFloat { value: _ } => unimplemented!(),

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

    code
}

