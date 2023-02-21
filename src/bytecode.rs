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

    pub const NEW_FUNCTION:     u8 = 39;
    pub const SWAP:             u8 = 40;
    pub const END:              u8 = 41;

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
        (self._c1(), self.u16())
    }

    #[inline(always)]
    pub fn encode_u16(op: u8, v: u16) -> Instruction {
        Instruction(op as u32 | (v as u32) << 16)
    }

    #[inline(always)]
    pub fn u16(self) -> u32 {
        (self.0 >> 16) & 0xffff
    }
}


pub struct ByteCodeBuilder {
    buffer: Vec<Instruction>,
}

impl ByteCodeBuilder {
    pub fn new() -> Self {
        ByteCodeBuilder {
            buffer: vec![],
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

    pub fn swap(&mut self, dst: u8, src: u8) {
        self.buffer.push(Instruction::encode_c2(opcode::SWAP, dst, src));
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


    pub fn new_function(&mut self, dst: u8, proto: u16) {
        self.buffer.push(Instruction::encode_c1u16(opcode::NEW_FUNCTION, dst, proto));
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



    #[inline(always)]
    pub fn current_offset(&self) -> usize {
        self.buffer.len()
    }


    pub fn build(self) -> Vec<Instruction> {
        assert!(self.buffer.len() < (1 << 16));
        self.buffer
    }
}


pub fn dump(code: &[Instruction]) {
    let mut pc = 0;

    macro_rules! next_instr {
        () => {{
            let instr = code[pc];
            pc += 1;
            instr
        }};
    }

    macro_rules! next_instr_extra {
        () => {{
            let extra = next_instr!();
            assert_eq!(extra.opcode() as u8, crate::bytecode::opcode::EXTRA);
            extra
        }};
    }

    while pc < code.len() {
        print!("{:02}: ", pc);

        let instr = next_instr!();

        use crate::bytecode::opcode::*;
        match instr.opcode() as u8 {
            NOP => (),

            UNREACHABLE => {
                println!("  unreachable");
                break;
            }


            COPY => {
                let (dst, src) = instr.c2();
                println!("  copy r{}, r{}", dst, src);
            }

            SWAP => {
                let (dst, src) = instr.c2();
                println!("  swap r{}, r{}", dst, src);
            }


            LOAD_NIL => {
                let dst = instr.c1();
                println!("  load_nil r{}", dst);
            }

            LOAD_BOOL => {
                let (dst, value) = instr.c1b();
                println!("  load_bool r{}, {}", dst, value);
            }

            LOAD_INT => {
                let (dst, value) = instr.c1u16();
                let value = value as u16 as i16 as f64;
                println!("  load_int r{}, {}", dst, value);
            }

            LOAD_CONST => {
                let (dst, index) = instr.c1u16();
                println!("  load_const r{}, c{}", dst, index);
            }

            LOAD_ENV => {
                let dst = instr.c1();
                println!("  load_env r{}", dst);
            }


            LIST_NEW => {
                let dst = instr.c1();
                println!("  list_new r{}", dst);
            }

            LIST_APPEND => {
                let (list, value) = instr.c2();
                println!("  list_append r{}, r{}", list, value);
            }


            TABLE_NEW => {
                let dst = instr.c1();
                println!("  table_new r{}", dst);
            }


            DEF => {
                // @todo-speed: remove checks.
                let (obj, key, value) = instr.c3();
                println!("  def r{}, r{}, r{}", obj, key, value);
            }

            SET => {
                let (obj, key, value) = instr.c3();
                println!("  set r{}, r{}, r{}", obj, key, value);
            }

            GET => {
                let (dst, obj, key) = instr.c3();
                println!("  get r{}, r{}, r{}", dst, obj, key);
            }

            LEN => {
                let (dst, obj) = instr.c2();
                println!("  len r{}, r{}", dst, obj);
            }


            ADD => {
                let (dst, src1, src2) = instr.c3();
                println!("  add r{}, r{}, r{}", dst, src1, src2);
            }

            SUB => {
                let (dst, src1, src2) = instr.c3();
                println!("  sub r{}, r{}, r{}", dst, src1, src2);
            }

            MUL => {
                let (dst, src1, src2) = instr.c3();
                println!("  mul r{}, r{}, r{}", dst, src1, src2);
            }

            DIV => {
                let (dst, src1, src2) = instr.c3();
                println!("  div r{}, r{}, r{}", dst, src1, src2);
            }

            INC => {
                let dst = instr.c1();
                println!("  inc r{}", dst);
            }

            DEC => {
                let dst = instr.c1();
                println!("  dec r{}", dst);
            }


            CMP_EQ => {
                let (dst, src1, src2) = instr.c3();
                println!("  cmp_eq r{}, r{}, r{}", dst, src1, src2);
            }

            CMP_LE => {
                let (dst, src1, src2) = instr.c3();
                println!("  cmp_le r{}, r{}, r{}", dst, src1, src2);
            }

            CMP_LT => {
                let (dst, src1, src2) = instr.c3();
                println!("  cmp_lt r{}, r{}, r{}", dst, src1, src2);
            }

            CMP_GE => {
                let (dst, src1, src2) = instr.c3();
                println!("  cmp_ge r{}, r{}, r{}", dst, src1, src2);
            }

            CMP_GT => {
                let (dst, src1, src2) = instr.c3();
                println!("  cmp_gt r{}, r{}, r{}", dst, src1, src2);
            }


            JUMP => {
                let target = instr.u16();
                println!("  jump {}", target);
            }

            JUMP_TRUE => {
                let (src, target) = instr.c1u16();
                println!("  jump_true r{}, {}", src, target);
            }

            JUMP_FALSE => {
                let (src, target) = instr.c1u16();
                println!("  jump_false r{}, {}", src, target);
            }

            JUMP_EQ => {
                let (src1, src2) = instr.c2();
                let target = next_instr_extra!().u16();
                println!("  jump_eq r{}, r{}, {}", src1, src2, target);
            }

            JUMP_LE => {
                let (src1, src2) = instr.c2();
                let target = next_instr_extra!().u16();
                println!("  jump_le r{}, r{}, {}", src1, src2, target);
            }

            JUMP_LT => {
                let (src1, src2) = instr.c2();
                let target = next_instr_extra!().u16();
                println!("  jump_le r{}, r{}, {}", src1, src2, target);
            }

            JUMP_NEQ => {
                let (src1, src2) = instr.c2();
                let target = next_instr_extra!().u16();
                println!("  jump_le r{}, r{}, {}", src1, src2, target);
            }

            JUMP_NLE => {
                let (src1, src2) = instr.c2();
                let target = next_instr_extra!().u16();
                println!("  jump_nle r{}, r{}, {}", src1, src2, target);
            }

            JUMP_NLT => {
                let (src1, src2) = instr.c2();
                let target = next_instr_extra!().u16();
                println!("  jump_nlt r{}, r{}, {}", src1, src2, target);
            }


            PACKED_CALL => {
                unimplemented!()
            }

            GATHER_CALL => {
                let (func, rets, num_rets) = instr.c3();

                let num_args = next_instr_extra!();
                let num_args = num_args.u16();

                print!("  call r{}, [", func);

                for i in 0..num_args {
                    let arg = next_instr_extra!();
                    print!("r{}", arg.u16());
                    if i < num_args - 1 {
                        print!(", ");
                    }
                }

                println!("], r{}, {}", rets, num_rets);
            }

            RET => {
                let (rets, num_rets) = instr.c2();
                println!("  ret r{}, {}", rets, num_rets);
            }

            NEW_FUNCTION => {
                let (dst, proto) = instr.c1u16();
                println!("  new_function r{}, f{}", dst, proto);
            }

            // @todo-speed: this inserts a check to reduce dispatch table size.
            //  may want an unreachable_unchecked() in release.
            0 | END ..= 255 => unreachable!()
        }
    }
}


