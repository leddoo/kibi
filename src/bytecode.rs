pub mod opcode {
    pub const NOP:              u8 = 1;
    pub const UNREACHABLE:      u8 = 2;

    pub const COPY:             u8 = 3;

    pub const LOAD_NIL:         u8 = 4;
    pub const LOAD_BOOL:        u8 = 5;
    pub const LOAD_INT:         u8 = 6;
    pub const LOAD_CONST:       u8 = 7;
    pub const LOAD_ENV:         u8 = 8;

    pub const LIST_NEW:         u8 = 9;
    pub const LIST_APPEND:      u8 = 10;

    pub const TABLE_NEW:        u8 = 11;

    pub const DEF:              u8 = 12;
    pub const SET:              u8 = 13;
    pub const GET:              u8 = 14;
    pub const LEN:              u8 = 15;

    pub const ADD:              u8 = 16;
    pub const SUB:              u8 = 17;
    pub const MUL:              u8 = 18;
    pub const DIV:              u8 = 19;
    pub const INC:              u8 = 20;
    pub const DEC:              u8 = 21;

    pub const CMP_EQ:           u8 = 22;
    pub const CMP_LE:           u8 = 23;
    pub const CMP_LT:           u8 = 24;
    pub const CMP_GE:           u8 = 25;
    pub const CMP_GT:           u8 = 26;

    pub const JUMP:             u8 = 27;
    pub const JUMP_TRUE:        u8 = 28;
    pub const JUMP_FALSE:       u8 = 29;
    pub const JUMP_EQ:          u8 = 30;
    pub const JUMP_LE:          u8 = 31;
    pub const JUMP_LT:          u8 = 32;
    pub const JUMP_NEQ:         u8 = 33;
    pub const JUMP_NLE:         u8 = 34;
    pub const JUMP_NLT:         u8 = 35;

    pub const PACKED_CALL:      u8 = 36;
    pub const GATHER_CALL:      u8 = 37;
    pub const RET:              u8 = 38;
    pub const END:              u8 = 39;

    pub const EXTRA:            u8 = 255;
}


#[derive(Clone, Copy, PartialEq, Debug)]
#[repr(transparent)]
pub struct Instruction (u32);

impl Instruction {
    #[inline(always)]
    pub fn opcode(self) -> u32 {
        let opcode = self.0 & 0xff;
        debug_assert!(opcode < opcode::END as u32 || opcode == opcode::EXTRA as u32);
        opcode
    }

    #[inline(always)]
    pub fn patch_opcode(&mut self, new_op: u8) {
        self.0 &= !0xff;
        self.0 |= new_op as u32;
    }

    #[inline(always)]
    pub fn _b2(self) -> bool {
        unsafe { core::mem::transmute(((self.0 >> 16) & 1) as u8) }
    }

    #[inline(always)]
    pub fn _c1(self) -> u32 {
        (self.0 >> 8) & 0xff
    }

    #[inline(always)]
    pub fn _c2(self) -> u32 {
        (self.0 >> 16) & 0xff
    }

    #[inline(always)]
    pub fn _c3(self) -> u32 {
        (self.0 >> 24) & 0xff
    }

    #[inline(always)]
    pub fn _u16(self) -> u32 {
        (self.0 >> 16) & 0xffff
    }

    #[inline(always)]
    pub fn patch_u16(&mut self, new_u16: u16) {
        self.0 &= 0xffff;
        self.0 |= (new_u16 as u32) << 16;
    }


    #[inline(always)]
    pub fn encode_op(op: u8) -> Instruction {
        Instruction(op as u32)
    }

    #[inline(always)]
    pub fn encode_c1(op: u8, c1: u8) -> Instruction {
        Instruction(op as u32 | (c1 as u32) << 8)
    }

    #[inline(always)]
    pub fn c1(self) -> u32 {
        self._c1()
    }

    #[inline(always)]
    pub fn encode_c2(op: u8, c1: u8, c2: u8) -> Instruction {
        Instruction(op as u32 | (c1 as u32) << 8 | (c2 as u32) << 16)
    }

    #[inline(always)]
    pub fn c2(self) -> (u32, u32) {
        (self._c1(), self._c2())
    }

    #[inline(always)]
    pub fn c1b(self) -> (u32, bool) {
        (self._c1(), self._b2())
    }

    #[inline(always)]
    pub fn encode_c3(op: u8, c1: u8, c2: u8, c3: u8) -> Instruction {
        Instruction(op as u32 | (c1 as u32) << 8 | (c2 as u32) << 16 | (c3 as u32) << 24)
    }

    #[inline(always)]
    pub fn c3(self) -> (u32, u32, u32) {
        (self._c1(), self._c2(), self._c3())
    }

    #[inline(always)]
    pub fn encode_c1u16(op: u8, c1: u8, v: u16) -> Instruction {
        Instruction(op as u32 | (c1 as u32) << 8 | (v as u32) << 16)
    }

    #[inline(always)]
    pub fn c1u16(self) -> (u32, u32) {
        (self._c1(), self._u16())
    }

    #[inline(always)]
    pub fn encode_u16(op: u8, v: u16) -> Instruction {
        Instruction(op as u32 | (v as u32) << 16)
    }

    #[inline(always)]
    pub fn u16(self) -> u32 {
        self._u16()
    }
}


pub struct ByteCodeBuilder {
    buffer: Vec<Instruction>,

    block_stack: Vec<usize>,
    blocks:      Vec<(u16, u16)>,
}

impl ByteCodeBuilder {
    pub fn new() -> Self {
        ByteCodeBuilder {
            buffer: vec![],
            block_stack: vec![],
            blocks:      vec![],
        }
    }

    pub fn nop(&mut self) {
        self.buffer.push(Instruction::encode_op(opcode::NOP));
    }

    pub fn unreachable(&mut self) {
        self.buffer.push(Instruction::encode_op(opcode::UNREACHABLE));
    }

    pub fn copy(&mut self, dst: u8, src: u8) {
        self.buffer.push(Instruction::encode_c2(opcode::COPY, dst, src));
    }


    pub fn load_nil(&mut self, dst: u8) {
        self.buffer.push(Instruction::encode_c1(opcode::LOAD_NIL, dst));
    }

    pub fn load_bool(&mut self, dst: u8, value: bool) {
        self.buffer.push(Instruction::encode_c2(opcode::LOAD_BOOL, dst, value as u8));
    }

    pub fn load_int(&mut self, dst: u8, value: i16) {
        self.buffer.push(Instruction::encode_c1u16(opcode::LOAD_INT, dst, value as u16));
    }

    pub fn load_const(&mut self, dst: u8, index: u16) {
        self.buffer.push(Instruction::encode_c1u16(opcode::LOAD_CONST, dst, index));
    }

    pub fn load_env(&mut self, dst: u8) {
        self.buffer.push(Instruction::encode_c1(opcode::LOAD_ENV, dst));
    }


    pub fn list_new(&mut self, dst: u8) {
        self.buffer.push(Instruction::encode_c1(opcode::LIST_NEW, dst));
    }

    pub fn list_append(&mut self, list: u8, value: u8) {
        self.buffer.push(Instruction::encode_c2(opcode::LIST_APPEND, list, value));
    }


    pub fn table_new(&mut self, dst: u8) {
        self.buffer.push(Instruction::encode_c1(opcode::TABLE_NEW, dst));
    }


    pub fn def(&mut self, obj: u8, key: u8, value: u8) {
        self.buffer.push(Instruction::encode_c3(opcode::DEF, obj, key, value));
    }

    pub fn set(&mut self, obj: u8, key: u8, value: u8) {
        self.buffer.push(Instruction::encode_c3(opcode::SET, obj, key, value));
    }

    pub fn get(&mut self, dst: u8, obj: u8, key: u8) {
        self.buffer.push(Instruction::encode_c3(opcode::GET, dst, obj, key));
    }

    pub fn len(&mut self, dst: u8, obj: u8) {
        self.buffer.push(Instruction::encode_c2(opcode::LEN, dst, obj));
    }


    pub fn add(&mut self, dst: u8, src1: u8, src2: u8) {
        self.buffer.push(Instruction::encode_c3(opcode::ADD, dst, src1, src2));
    }

    pub fn sub(&mut self, dst: u8, src1: u8, src2: u8) {
        self.buffer.push(Instruction::encode_c3(opcode::SUB, dst, src1, src2));
    }

    pub fn mul(&mut self, dst: u8, src1: u8, src2: u8) {
        self.buffer.push(Instruction::encode_c3(opcode::MUL, dst, src1, src2));
    }

    pub fn div(&mut self, dst: u8, src1: u8, src2: u8) {
        self.buffer.push(Instruction::encode_c3(opcode::DIV, dst, src1, src2));
    }

    pub fn inc(&mut self, dst: u8) {
        self.buffer.push(Instruction::encode_c1(opcode::INC, dst));
    }

    pub fn dec(&mut self, dst: u8) {
        self.buffer.push(Instruction::encode_c1(opcode::DEC, dst));
    }


    pub fn cmp_eq(&mut self, dst: u8, src1: u8, src2: u8) {
        self.buffer.push(Instruction::encode_c3(opcode::CMP_EQ, dst, src1, src2));
    }

    pub fn cmp_le(&mut self, dst: u8, src1: u8, src2: u8) {
        self.buffer.push(Instruction::encode_c3(opcode::CMP_LE, dst, src1, src2));
    }

    pub fn cmp_lt(&mut self, dst: u8, src1: u8, src2: u8) {
        self.buffer.push(Instruction::encode_c3(opcode::CMP_LT, dst, src1, src2));
    }

    pub fn cmp_ge(&mut self, dst: u8, src1: u8, src2: u8) {
        self.buffer.push(Instruction::encode_c3(opcode::CMP_GE, dst, src1, src2));
    }

    pub fn cmp_gt(&mut self, dst: u8, src1: u8, src2: u8) {
        self.buffer.push(Instruction::encode_c3(opcode::CMP_GT, dst, src1, src2));
    }


    pub fn jump(&mut self, target: u16) {
        self.buffer.push(Instruction::encode_u16(opcode::JUMP, target));
    }

    pub fn jump_true(&mut self, src: u8, target: u16) {
        self.buffer.push(Instruction::encode_c1u16(opcode::JUMP_TRUE, src, target));
    }

    pub fn jump_false(&mut self, src: u8, target: u16) {
        self.buffer.push(Instruction::encode_c1u16(opcode::JUMP_FALSE, src, target));
    }

    pub fn jump_eq(&mut self, src1: u8, src2: u8, target: u16) {
        self.buffer.push(Instruction::encode_c2(opcode::JUMP_EQ, src1, src2));
        self.buffer.push(Instruction::encode_u16(opcode::EXTRA, target));
    }

    pub fn jump_le(&mut self, src1: u8, src2: u8, target: u16) {
        self.buffer.push(Instruction::encode_c2(opcode::JUMP_LE, src1, src2));
        self.buffer.push(Instruction::encode_u16(opcode::EXTRA, target));
    }

    pub fn jump_lt(&mut self, src1: u8, src2: u8, target: u16) {
        self.buffer.push(Instruction::encode_c2(opcode::JUMP_LT, src1, src2));
        self.buffer.push(Instruction::encode_u16(opcode::EXTRA, target));
    }

    pub fn jump_neq(&mut self, src1: u8, src2: u8, target: u16) {
        self.buffer.push(Instruction::encode_c2(opcode::JUMP_NEQ, src1, src2));
        self.buffer.push(Instruction::encode_u16(opcode::EXTRA, target));
    }

    pub fn jump_nle(&mut self, src1: u8, src2: u8, target: u16) {
        self.buffer.push(Instruction::encode_c2(opcode::JUMP_NLE, src1, src2));
        self.buffer.push(Instruction::encode_u16(opcode::EXTRA, target));
    }

    pub fn jump_nlt(&mut self, src1: u8, src2: u8, target: u16) {
        self.buffer.push(Instruction::encode_c2(opcode::JUMP_NLT, src1, src2));
        self.buffer.push(Instruction::encode_u16(opcode::EXTRA, target));
    }


    pub fn packed_call(&mut self, func: u8, args: u8, num_args: u8, rets: u8, num_rets: u8) {
        self.buffer.push(Instruction::encode_c3(opcode::PACKED_CALL, func, rets, num_rets));
        self.buffer.push(Instruction::encode_c2(opcode::EXTRA, args, num_args));
    }

    pub fn gather_call(&mut self, func: u8, args: &[u8], rets: u8, num_rets: u8) {
        assert!(args.len() < 128);
        self.buffer.push(Instruction::encode_c3(opcode::GATHER_CALL, func, rets, num_rets));
        self.buffer.push(Instruction::encode_u16(opcode::EXTRA, args.len() as u16));
        for arg in args {
            self.buffer.push(Instruction::encode_u16(opcode::EXTRA, *arg as u16));
        }
    }

    pub fn ret(&mut self, rets: u8, num_rets: u8) {
        self.buffer.push(Instruction::encode_c2(opcode::RET, rets, num_rets));
    }


    pub fn begin_block(&mut self) {
        let block = self.blocks.len();
        let begin = self.buffer.len() as u16;
        self.block_stack.push(block);
        self.blocks.push((begin, u16::MAX));
    }

    pub fn end_block(&mut self) {
        let block = self.block_stack.pop().unwrap();
        let end = self.buffer.len() as u16;
        self.blocks[block].1 = end;
    }

    pub fn block<F: FnOnce(&mut ByteCodeBuilder)>(&mut self, f: F) {
        self.begin_block();
        f(self);
        self.end_block();
    }

    pub fn _block_begin(&self, index: usize) -> u16 {
        assert!(index < self.block_stack.len());
        let block = self.block_stack[self.block_stack.len() - 1 - index];
        self.blocks[block].0
    }

    const JUMP_BLOCK_END_BIT: usize = 1 << 15;

    pub fn _block_end(&self, index: usize) -> u16 {
        assert!(index < self.block_stack.len());
        let block = self.block_stack[self.block_stack.len() - 1 - index];
        (block | Self::JUMP_BLOCK_END_BIT) as u16
    }


    pub fn exit_block(&mut self, index: usize) {
        self.jump(self._block_end(index));
    }

    pub fn exit_true(&mut self, src: u8, index: usize) {
        self.jump_true(src, self._block_end(index));
    }

    pub fn exit_false(&mut self, src: u8, index: usize) {
        self.jump_false(src, self._block_end(index));
    }

    pub fn exit_eq(&mut self, src1: u8, src2: u8, index: usize) {
        self.jump_eq(src1, src2, self._block_end(index));
    }

    pub fn exit_le(&mut self, src1: u8, src2: u8, index: usize) {
        self.jump_le(src1, src2, self._block_end(index));
    }

    pub fn exit_lt(&mut self, src1: u8, src2: u8, index: usize) {
        self.jump_lt(src1, src2, self._block_end(index));
    }

    pub fn exit_neq(&mut self, src1: u8, src2: u8, index: usize) {
        self.jump_neq(src1, src2, self._block_end(index));
    }

    pub fn exit_nle(&mut self, src1: u8, src2: u8, index: usize) {
        self.jump_nle(src1, src2, self._block_end(index));
    }

    pub fn exit_nlt(&mut self, src1: u8, src2: u8, index: usize) {
        self.jump_nlt(src1, src2, self._block_end(index));
    }

    pub fn repeat_block(&mut self, index: usize) {
        self.jump(self._block_begin(index));
    }

    pub fn repeat_true(&mut self, src: u8, index: usize) {
        self.jump_true(src, self._block_begin(index));
    }

    pub fn repeat_false(&mut self, src: u8, index: usize) {
        self.jump_false(src, self._block_begin(index));
    }

    pub fn repeat_eq(&mut self, src1: u8, src2: u8, index: usize) {
        self.jump_eq(src1, src2, self._block_begin(index));
    }

    pub fn repeat_le(&mut self, src1: u8, src2: u8, index: usize) {
        self.jump_le(src1, src2, self._block_begin(index));
    }

    pub fn repeat_lt(&mut self, src1: u8, src2: u8, index: usize) {
        self.jump_lt(src1, src2, self._block_begin(index));
    }

    pub fn repeat_neq(&mut self, src1: u8, src2: u8, index: usize) {
        self.jump_neq(src1, src2, self._block_begin(index));
    }

    pub fn repeat_nle(&mut self, src1: u8, src2: u8, index: usize) {
        self.jump_nle(src1, src2, self._block_begin(index));
    }

    pub fn repeat_nlt(&mut self, src1: u8, src2: u8, index: usize) {
        self.jump_nlt(src1, src2, self._block_begin(index));
    }


    pub fn build(mut self) -> Vec<Instruction> {
        assert!(self.buffer.len() < (1 << 16));
        assert!(self.blocks.len() < (1 << 12));

        assert!(self.block_stack.len() == 0);

        let mut i = 0;
        while i < self.buffer.len() {
            let instr = &mut self.buffer[i];
            i += 1;

            use opcode::*;
            match instr.opcode() as u8 {
                JUMP_EQ  | JUMP_LE  | JUMP_LT |
                JUMP_NEQ | JUMP_NLE | JUMP_NLT => {
                    let extra = &mut self.buffer[i];
                    i += 1;

                    assert_eq!(extra.opcode() as u8, EXTRA);

                    let target = extra.u16() as usize;
                    if target & Self::JUMP_BLOCK_END_BIT != 0 {
                        let block = target & !Self::JUMP_BLOCK_END_BIT;
                        let end = self.blocks[block].1;
                        extra.patch_u16(end);
                    }
                }

                JUMP | JUMP_TRUE | JUMP_FALSE => {
                    let target = instr.u16() as usize;
                    if target & Self::JUMP_BLOCK_END_BIT != 0 {
                        let block = target & !Self::JUMP_BLOCK_END_BIT;
                        let end = self.blocks[block].1;
                        instr.patch_u16(end);
                    }
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

        self.buffer
    }
}


