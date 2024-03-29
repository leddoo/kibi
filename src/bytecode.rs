// @todo-robust: this file should be generated from a table.

pub mod opcode {
    pub const NOP:              u8 = 1;
    pub const UNREACHABLE:      u8 = 2;

    pub const COPY:             u8 = 3;
    pub const SWAP:             u8 = 4;

    pub const LOAD_NIL:         u8 = 5;
    pub const LOAD_BOOL:        u8 = 6;
    pub const LOAD_INT:         u8 = 7;
    pub const LOAD_CONST:       u8 = 8;
    pub const LOAD_ENV:         u8 = 9;

    pub const LIST_NEW:         u8 = 10;

    pub const TUPLE_NEW:        u8 = 11;
    pub const LOAD_UNIT:        u8 = 12;

    pub const MAP_NEW:          u8 = 13;

    pub const READ_PATH:        u8 = 14;
    pub const WRITE_PATH:       u8 = 15;
    pub const WRITE_PATH_DEF:   u8 = 16;

    pub const ADD:              u8 = 17;
    pub const SUB:              u8 = 18;
    pub const MUL:              u8 = 19;
    pub const DIV:              u8 = 20;
    pub const FLOOR_DIV:        u8 = 21;
    pub const REM:              u8 = 22;
    pub const ADD_INT:          u8 = 23;
    pub const NEGATE:           u8 = 24;

    pub const NOT:              u8 = 25;

    pub const CMP_EQ:           u8 = 26;
    pub const CMP_NE:           u8 = 27;
    pub const CMP_LE:           u8 = 28;
    pub const CMP_LT:           u8 = 29;
    pub const CMP_GE:           u8 = 30;
    pub const CMP_GT:           u8 = 31;

    pub const JUMP:             u8 = 32;
    pub const JUMP_TRUE:        u8 = 33;
    pub const JUMP_FALSE:       u8 = 34;
    pub const JUMP_NIL:         u8 = 35;
    pub const JUMP_NOT_NIL:     u8 = 36;

    pub const CALL:             u8 = 37;
    pub const RET:              u8 = 38;

    pub const END:              u8 = 39;

    pub const EXTRA:            u8 = 255;


    pub const fn name(opcode: u8) -> &'static str {
        match opcode {
            NOP                 => "nop",
            UNREACHABLE         => "unreachable",
            COPY                => "copy",
            SWAP                => "swap",
            LOAD_NIL            => "load_nil",
            LOAD_BOOL           => "load_bool",
            LOAD_INT            => "load_int",
            LOAD_CONST          => "load_const",
            LOAD_ENV            => "load_env",
            LIST_NEW            => "list_new",
            TUPLE_NEW           => "tuple_new",
            LOAD_UNIT           => "load_unit",
            MAP_NEW             => "map_new",
            READ_PATH           => "read_path",
            WRITE_PATH          => "write_path",
            WRITE_PATH_DEF      => "write_path_def",
            ADD                 => "add",
            SUB                 => "sub",
            MUL                 => "mul",
            DIV                 => "div",
            FLOOR_DIV           => "floor_div",
            REM                 => "rem",
            ADD_INT             => "add_int",
            NEGATE              => "negate",
            NOT                 => "not",
            CMP_EQ              => "cmp_eq",
            CMP_NE              => "cmp_ne",
            CMP_LE              => "cmp_le",
            CMP_LT              => "cmp_lt",
            CMP_GE              => "cmp_ge",
            CMP_GT              => "cmp_gt",
            JUMP                => "jump",
            JUMP_TRUE           => "jump_true",
            JUMP_FALSE          => "jump_false",
            JUMP_NIL            => "jump_nil",
            JUMP_NOT_NIL        => "jump_not_nil",
            CALL                => "call",
            RET                 => "ret",
            0 | 39..=255 => unreachable!()
        }
    }
}


#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct InstrWord(u32);

impl InstrWord {
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
    pub fn _bool2(self) -> bool {
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
    pub fn encode_op(op: u8) -> InstrWord {
        InstrWord(op as u32)
    }

    #[inline(always)]
    pub fn encode_c1(op: u8, c1: u8) -> InstrWord {
        InstrWord(op as u32 | (c1 as u32) << 8)
    }

    #[inline(always)]
    pub fn c1(self) -> u32 {
        self._c1()
    }

    #[inline(always)]
    pub fn encode_c2(op: u8, c1: u8, c2: u8) -> InstrWord {
        InstrWord(op as u32 | (c1 as u32) << 8 | (c2 as u32) << 16)
    }

    #[inline(always)]
    pub fn c2(self) -> (u32, u32) {
        (self._c1(), self._c2())
    }

    #[inline(always)]
    pub fn c1_bool(self) -> (u32, bool) {
        (self._c1(), self._bool2())
    }

    #[inline(always)]
    pub fn encode_c3(op: u8, c1: u8, c2: u8, c3: u8) -> InstrWord {
        InstrWord(op as u32 | (c1 as u32) << 8 | (c2 as u32) << 16 | (c3 as u32) << 24)
    }

    #[inline(always)]
    pub fn c3(self) -> (u32, u32, u32) {
        (self._c1(), self._c2(), self._c3())
    }

    #[inline(always)]
    pub fn encode_c1u16(op: u8, c1: u8, v: u16) -> InstrWord {
        InstrWord(op as u32 | (c1 as u32) << 8 | (v as u32) << 16)
    }

    #[inline(always)]
    pub fn c1u16(self) -> (u32, u32) {
        (self._c1(), self.u16())
    }

    #[inline(always)]
    pub fn encode_u16(op: u8, v: u16) -> InstrWord {
        InstrWord(op as u32 | (v as u32) << 16)
    }

    #[inline(always)]
    pub fn u16(self) -> u32 {
        (self.0 >> 16) & 0xffff
    }
}



#[derive(Clone, Copy, PartialEq, Debug)]
pub struct PathBase(u8);

impl PathBase {
    pub const ITEMS: PathBase = PathBase(254);
    pub const ENV:   PathBase = PathBase(255);

    #[inline(always)]
    pub const fn value(self) -> u8 { self.0 }

    #[inline(always)]
    pub fn reg(reg: u8) -> PathBase {
        assert!(reg < 254);
        PathBase(reg)
    }
}


#[derive(Clone, Copy, PartialEq, Debug)]
pub enum PathKey {
    Field { string: u16 },
    Index { reg:    u8  },
}

impl PathKey {
    pub const TYPE_FIELD: u8 = 1;
    pub const TYPE_INDEX: u8 = 2;

    pub fn encode(self) -> (u8, u16) {
        match self {
            PathKey::Field { string } => (PathKey::TYPE_FIELD, string),
            PathKey::Index { reg    } => (PathKey::TYPE_INDEX, reg as u16),
        }
    }

    pub fn decode(instr: InstrWord) -> PathKey {
        let (kind, value) = instr.c1u16();
        if kind == Self::TYPE_FIELD as u32 {
            PathKey::Field { string: value as u16 }
        }
        else if kind == Self::TYPE_INDEX as u32 {
            PathKey::Index { reg: value.try_into().unwrap() }
        }
        else {
            unimplemented!()
        }
    }
}

impl core::fmt::Display for PathKey {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            PathKey::Field { string } => write!(f, "f:{}", string),
            PathKey::Index { reg }    => write!(f, "i:r{}", reg),
        }
    }
}


pub struct ByteCodeBuilder {
    buffer: Vec<InstrWord>,
}

impl ByteCodeBuilder {
    pub fn new() -> Self {
        ByteCodeBuilder {
            buffer: vec![],
        }
    }

    pub fn nop(&mut self) {
        self.buffer.push(InstrWord::encode_op(opcode::NOP));
    }

    pub fn unreachable(&mut self) {
        self.buffer.push(InstrWord::encode_op(opcode::UNREACHABLE));
    }

    pub fn copy(&mut self, dst: u8, src: u8) {
        self.buffer.push(InstrWord::encode_c2(opcode::COPY, dst, src));
    }

    pub fn swap(&mut self, dst: u8, src: u8) {
        self.buffer.push(InstrWord::encode_c2(opcode::SWAP, dst, src));
    }


    pub fn load_nil(&mut self, dst: u8) {
        self.buffer.push(InstrWord::encode_c1(opcode::LOAD_NIL, dst));
    }

    pub fn load_bool(&mut self, dst: u8, value: bool) {
        self.buffer.push(InstrWord::encode_c2(opcode::LOAD_BOOL, dst, value as u8));
    }

    pub fn load_int(&mut self, dst: u8, value: i16) {
        self.buffer.push(InstrWord::encode_c1u16(opcode::LOAD_INT, dst, value as u16));
    }

    pub fn load_const(&mut self, dst: u8, index: u16) {
        self.buffer.push(InstrWord::encode_c1u16(opcode::LOAD_CONST, dst, index));
    }

    pub fn load_env(&mut self, dst: u8) {
        self.buffer.push(InstrWord::encode_c1(opcode::LOAD_ENV, dst));
    }


    pub fn list_new(&mut self, dst: u8, values: &[u8]) {
        assert!(values.len() < 128);
        self.buffer.push(InstrWord::encode_c1u16(opcode::LIST_NEW, dst, values.len() as u16));
        for v in values {
            self.buffer.push(InstrWord::encode_u16(opcode::EXTRA, *v as u16));
        }
    }


    pub fn tuple_new(&mut self, dst: u8, values: &[u8]) {
        assert!(values.len() < 128);
        self.buffer.push(InstrWord::encode_c1u16(opcode::TUPLE_NEW, dst, values.len() as u16));
        for v in values {
            self.buffer.push(InstrWord::encode_u16(opcode::EXTRA, *v as u16));
        }
    }

    pub fn load_unit(&mut self, dst: u8) {
        self.buffer.push(InstrWord::encode_c1(opcode::LOAD_UNIT, dst));
    }


    pub fn map_new(&mut self, dst: u8) {
        self.buffer.push(InstrWord::encode_c1(opcode::MAP_NEW, dst));
    }


    pub fn read_path(&mut self, dst: u8, base: PathBase, keys: &[PathKey]) {
        assert!(keys.len() < 128);
        self.buffer.push(InstrWord::encode_c3(opcode::READ_PATH, dst, base.0, keys.len() as u8));
        for key in keys {
            let (kind, value) = key.encode();
            self.buffer.push(InstrWord::encode_c1u16(opcode::EXTRA, kind, value));
        }
    }

    pub fn write_path(&mut self, base: PathBase, keys: &[PathKey], value: u8, is_define: bool) {
        assert!(keys.len() < 128);
        let op = if is_define { opcode::WRITE_PATH_DEF } else { opcode::WRITE_PATH };
        self.buffer.push(InstrWord::encode_c3(op, base.0, keys.len() as u8, value));
        for key in keys {
            let (kind, value) = key.encode();
            self.buffer.push(InstrWord::encode_c1u16(opcode::EXTRA, kind, value));
        }
    }


    pub fn add(&mut self, dst: u8, src1: u8, src2: u8) {
        self.buffer.push(InstrWord::encode_c3(opcode::ADD, dst, src1, src2));
    }

    pub fn sub(&mut self, dst: u8, src1: u8, src2: u8) {
        self.buffer.push(InstrWord::encode_c3(opcode::SUB, dst, src1, src2));
    }

    pub fn mul(&mut self, dst: u8, src1: u8, src2: u8) {
        self.buffer.push(InstrWord::encode_c3(opcode::MUL, dst, src1, src2));
    }

    pub fn div(&mut self, dst: u8, src1: u8, src2: u8) {
        self.buffer.push(InstrWord::encode_c3(opcode::DIV, dst, src1, src2));
    }

    pub fn floor_div(&mut self, dst: u8, src1: u8, src2: u8) {
        self.buffer.push(InstrWord::encode_c3(opcode::FLOOR_DIV, dst, src1, src2));
    }

    pub fn rem(&mut self, dst: u8, src1: u8, src2: u8) {
        self.buffer.push(InstrWord::encode_c3(opcode::REM, dst, src1, src2));
    }

    pub fn add_int(&mut self, dst: u8, value: i16) {
        self.buffer.push(InstrWord::encode_c1u16(opcode::ADD_INT, dst, value as u16));
    }

    pub fn negate(&mut self, dst: u8, src: u8) {
        self.buffer.push(InstrWord::encode_c2(opcode::NEGATE, dst, src));
    }


    pub fn not(&mut self, dst: u8, src: u8) {
        self.buffer.push(InstrWord::encode_c2(opcode::NOT, dst, src));
    }



    pub fn cmp_eq(&mut self, dst: u8, src1: u8, src2: u8) {
        self.buffer.push(InstrWord::encode_c3(opcode::CMP_EQ, dst, src1, src2));
    }

    pub fn cmp_ne(&mut self, dst: u8, src1: u8, src2: u8) {
        self.buffer.push(InstrWord::encode_c3(opcode::CMP_NE, dst, src1, src2));
    }

    pub fn cmp_le(&mut self, dst: u8, src1: u8, src2: u8) {
        self.buffer.push(InstrWord::encode_c3(opcode::CMP_LE, dst, src1, src2));
    }

    pub fn cmp_lt(&mut self, dst: u8, src1: u8, src2: u8) {
        self.buffer.push(InstrWord::encode_c3(opcode::CMP_LT, dst, src1, src2));
    }

    pub fn cmp_ge(&mut self, dst: u8, src1: u8, src2: u8) {
        self.buffer.push(InstrWord::encode_c3(opcode::CMP_GE, dst, src1, src2));
    }

    pub fn cmp_gt(&mut self, dst: u8, src1: u8, src2: u8) {
        self.buffer.push(InstrWord::encode_c3(opcode::CMP_GT, dst, src1, src2));
    }


    pub fn jump(&mut self, target: u16) {
        self.buffer.push(InstrWord::encode_u16(opcode::JUMP, target));
    }

    pub fn jump_true(&mut self, src: u8, target: u16) {
        self.buffer.push(InstrWord::encode_c1u16(opcode::JUMP_TRUE, src, target));
    }

    pub fn jump_false(&mut self, src: u8, target: u16) {
        self.buffer.push(InstrWord::encode_c1u16(opcode::JUMP_FALSE, src, target));
    }

    pub fn jump_nil(&mut self, src: u8, target: u16) {
        self.buffer.push(InstrWord::encode_c1u16(opcode::JUMP_NIL, src, target));
    }

    pub fn jump_non_nil(&mut self, src: u8, target: u16) {
        self.buffer.push(InstrWord::encode_c1u16(opcode::JUMP_NOT_NIL, src, target));
    }


    pub fn call(&mut self, dst: u8, func: u8, args: &[u8]) {
        assert!(args.len() < 128);
        self.buffer.push(InstrWord::encode_c2(opcode::CALL, dst, func));
        self.buffer.push(InstrWord::encode_u16(opcode::EXTRA, args.len() as u16));
        for arg in args {
            self.buffer.push(InstrWord::encode_u16(opcode::EXTRA, *arg as u16));
        }
    }

    pub fn ret(&mut self, src: u8) {
        self.buffer.push(InstrWord::encode_c1(opcode::RET, src));
    }



    #[inline(always)]
    pub fn current_offset(&self) -> usize {
        self.buffer.len()
    }


    pub fn build(self) -> Vec<InstrWord> {
        assert!(self.buffer.len() < (1 << 16));
        self.buffer
    }
}



#[derive(Debug)]
pub struct Instr {
    pub pc:     u16,
    pub opcode: u8,
    pub data:   InstrData,
}

#[derive(Debug)]
pub enum InstrData {
    Nop,
    Unreachable,

    Copy                { dst: u8, src: u8 },
    Swap                { dst: u8, src: u8 },

    LoadNil             { dst: u8 },
    LoadBool            { dst: u8, value: bool },
    LoadInt             { dst: u8, value: i16 },
    LoadConst           { dst: u8, index: u16 },
    LoadEnv             { dst: u8 },

    ListNew             { dst: u8, values: Vec<u8>, },

    TupleNew            { dst: u8, values: Vec<u8> },
    LoadUnit            { dst: u8 },

    MapNew              { dst: u8 }, 

    ReadPath            { dst: u8, base: PathBase, keys: Vec<PathKey> },
    WritePath           { base: PathBase, keys: Vec<PathKey>, value: u8 },

    Op1                 { dst: u8, src: u8 },
    Op2                 { dst: u8, src1: u8, src2: u8 },

    AddInt              { dst: u8, value: i16 },

    Jump                { target: u16 },
    JumpC1              { target: u16, src: u8 },

    Call                { dst: u8, func: u8, args: Vec<u8> },
    Ret                 { src: u8 },
}

impl Instr {
    #[inline(always)]
    pub fn name(&self) -> &'static str {
        opcode::name(self.opcode)
    }
}


pub struct ByteCodeDecoder<'a> {
    code: &'a [InstrWord],
    pc:   usize,
}

impl<'a> ByteCodeDecoder<'a> {
    pub fn new(code: &'a [InstrWord]) -> Self {
        ByteCodeDecoder { code, pc: 0 }
    }

    pub fn done(&self) -> bool {
        self.pc >= self.code.len()
    }

    fn next_instr(&mut self) -> Option<(InstrWord, u16)> {
        let instr = *self.code.get(self.pc)?;
        let pc    = self.pc as u16;
        self.pc += 1;
        Some((instr, pc))
    }

    fn next_instr_extra(&mut self) -> Option<InstrWord> {
        let (extra, _) = self.next_instr()?;
        assert_eq!(extra.opcode() as u8, crate::bytecode::opcode::EXTRA);
        Some(extra)
    }

    pub fn next(&mut self) -> Option<Instr> {
        let (instr, pc) = self.next_instr()?;
        let opcode = instr.opcode() as u8;

        use crate::bytecode::opcode::*;
        let data = match opcode {
            NOP => {
                InstrData::Nop
            }

            UNREACHABLE => {
                InstrData::Unreachable
            }


            COPY => {
                let (dst, src) = instr.c2();
                InstrData::Copy { dst: dst as u8, src: src as u8 }
            }

            SWAP => {
                let (dst, src) = instr.c2();
                InstrData::Swap { dst: dst as u8, src: src as u8 }
            }


            LOAD_NIL => {
                let dst = instr.c1();
                InstrData::LoadNil { dst: dst as u8 }
            }

            LOAD_BOOL => {
                let (dst, value) = instr.c1_bool();
                InstrData::LoadBool { dst: dst as u8, value }
            }

            LOAD_INT => {
                let (dst, value) = instr.c1u16();
                let value = value as u16 as i16;
                InstrData::LoadInt { dst: dst as u8, value }
            }

            LOAD_CONST => {
                let (dst, index) = instr.c1u16();
                InstrData::LoadConst { dst: dst as u8, index: index as u16 }
            }

            LOAD_ENV => {
                let dst = instr.c1();
                InstrData::LoadEnv { dst: dst as u8 }
            }


            LIST_NEW => {
                let (dst, len) = instr.c1u16();

                let mut values = Vec::with_capacity(len as usize);
                for _ in 0..len {
                    let v = self.next_instr_extra()?;
                    values.push(v.u16() as u8);
                }

                InstrData::ListNew { dst: dst as u8, values }
            }
            

            TUPLE_NEW => {
                let (dst, len) = instr.c1u16();

                let mut values = Vec::with_capacity(len as usize);
                for _ in 0..len {
                    let v = self.next_instr_extra()?;
                    values.push(v.u16() as u8);
                }

                InstrData::TupleNew { dst: dst as u8, values }
            }

            LOAD_UNIT => {
                let dst = instr.c1();
                InstrData::LoadUnit { dst: dst as u8 }
            }


            MAP_NEW => {
                let dst = instr.c1();
                InstrData::MapNew { dst: dst as u8 }
            }


            READ_PATH => {
                let (dst, base, num_keys) = instr.c3();
                let mut keys = Vec::with_capacity(num_keys as usize);
                for _ in 0..num_keys {
                    keys.push(PathKey::decode(self.next_instr_extra()?));
                }
                InstrData::ReadPath { dst: dst as u8, base: PathBase(base as u8), keys }
            }

            WRITE_PATH | WRITE_PATH_DEF => {
                let (base, num_keys, value) = instr.c3();
                let mut keys = Vec::with_capacity(num_keys as usize);
                for _ in 0..num_keys {
                    keys.push(PathKey::decode(self.next_instr_extra()?));
                }
                InstrData::WritePath { base: PathBase(base as u8), keys, value: value as u8 }
            }


            NEGATE | NOT => {
                let (dst, src) = instr.c2();
                InstrData::Op1 { dst: dst as u8, src: src as u8 }
            }

            ADD | SUB | MUL | DIV | FLOOR_DIV | REM |
            CMP_EQ | CMP_NE | CMP_LE | CMP_LT | CMP_GE | CMP_GT => {
                let (dst, src1, src2) = instr.c3();
                InstrData::Op2 { dst: dst as u8, src1: src1 as u8, src2: src2 as u8 }
            }

            ADD_INT => {
                let (dst, value) = instr.c1u16();
                let value = value as u16 as i16;
                InstrData::AddInt { dst: dst as u8, value }
            }


            JUMP => {
                let target = instr.u16();
                InstrData::Jump { target: target as u16 }
            }

            JUMP_TRUE | JUMP_FALSE | JUMP_NIL | JUMP_NOT_NIL => {
                let (src, target) = instr.c1u16();
                InstrData::JumpC1 { target: target as u16, src: src as u8 }
            }


            CALL => {
                let (dst, func) = instr.c2();
                let num_args = self.next_instr_extra()?.u16();

                let mut args = Vec::with_capacity(num_args as usize);
                for _ in 0..num_args {
                    let arg = self.next_instr_extra()?;
                    args.push(arg.u16() as u8);
                }

                InstrData::Call { dst: dst as u8, func: func as u8, args }
            }

            RET => {
                let src = instr.c1();
                InstrData::Ret { src: src as u8 }
            }

            // @todo-speed: this inserts a check to reduce dispatch table size.
            //  may want an unreachable_unchecked() in release.
            0 | END ..= 255 => unreachable!()
        };
        Some(Instr { pc, opcode, data })
    }

    pub fn decode(code: &[InstrWord]) -> Option<Vec<Instr>> {
        let mut decoder = ByteCodeDecoder::new(code);
        let mut instrs = vec![];
        while let Some(instr) = decoder.next() {
            instrs.push(instr);
        }
        decoder.done().then_some(instrs)
    }
}


pub fn dump(code: &[InstrWord]) {
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

        let instr  = next_instr!();
        let opcode = instr.opcode() as u8;

        use crate::bytecode::opcode::*;
        match opcode {
            NOP => {
                println!("  nop");
            }

            UNREACHABLE => {
                println!("  unreachable");
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
                let (dst, value) = instr.c1_bool();
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
                let (dst, len) = instr.c1u16();
                print!("  list_new r{}, [", dst);

                for i in 0..len {
                    let v = next_instr_extra!();
                    print!("r{}", v.u16());
                    if i < len - 1 {
                        print!(", ");
                    }
                }

                println!("]");
            }
            

            TUPLE_NEW => {
                let (dst, len) = instr.c1u16();
                print!("  tuple_new r{}, [", dst);

                for i in 0..len {
                    let v = next_instr_extra!();
                    print!("r{}", v.u16());
                    if i < len - 1 {
                        print!(", ");
                    }
                }

                println!("]");
            }

            LOAD_UNIT => {
                let dst = instr.c1();
                println!("  tuple_new r{}, []", dst);
            }


            MAP_NEW => {
                let dst = instr.c1();
                println!("  map_new r{}", dst);
            }


            READ_PATH => {
                let (dst, base, num_keys) = instr.c3();
                print!("  read_path r{}, ", dst);
                if      base == 254 { print!("ITEMS[") }
                else if base == 255 { print!("ENV[") }
                else                { print!("r{}[", base) };
                for i in 0..num_keys {
                    print!("{}", PathKey::decode(next_instr_extra!()));
                    if i < num_keys-1 { print!(", "); }
                }
                println!("]");
            }

            WRITE_PATH | WRITE_PATH_DEF => {
                let is_def = opcode == WRITE_PATH_DEF;
                let (base, num_keys, value) = instr.c3();
                print!("  write_path");
                if is_def { print!("(d)") }
                print!(" ");
                if      base == 254 { print!("ITEMS[") }
                else if base == 255 { print!("ENV[") }
                else                { print!("r{}[", base) };
                for i in 0..num_keys {
                    print!("{}", PathKey::decode(next_instr_extra!()));
                    if i < num_keys-1 { print!(", "); }
                }
                println!("], r{}", value);
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

            FLOOR_DIV => {
                let (dst, src1, src2) = instr.c3();
                println!("  floor_div r{}, r{}, r{}", dst, src1, src2);
            }

            REM => {
                let (dst, src1, src2) = instr.c3();
                println!("  rem r{}, r{}, r{}", dst, src1, src2);
            }

            ADD_INT => {
                let (dst, value) = instr.c1u16();
                println!("  add_int r{}, {}", dst, value);
            }

            NEGATE => {
                let (dst, src) = instr.c2();
                println!("  negate r{}, r{}", dst, src);
            }


            NOT => {
                let (dst, src) = instr.c2();
                println!("  or r{}, r{}", dst, src);
            }


            CMP_EQ => {
                let (dst, src1, src2) = instr.c3();
                println!("  cmp_eq r{}, r{}, r{}", dst, src1, src2);
            }

            CMP_NE => {
                let (dst, src1, src2) = instr.c3();
                println!("  cmp_ne r{}, r{}, r{}", dst, src1, src2);
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

            JUMP_NIL => {
                let (src, target) = instr.c1u16();
                println!("  jump_nil r{}, {}", src, target);
            }

            JUMP_NOT_NIL => {
                let (src, target) = instr.c1u16();
                println!("  jump_not_nil r{}, {}", src, target);
            }


            CALL => {
                let (dst, func) = instr.c2();

                let num_args = next_instr_extra!();
                let num_args = num_args.u16();

                print!("  call r{}, r{}, [", dst, func);

                for i in 0..num_args {
                    let arg = next_instr_extra!();
                    print!("r{}", arg.u16());
                    if i < num_args - 1 {
                        print!(", ");
                    }
                }

                println!("]");
            }

            RET => {
                let src = instr.c1();
                println!("  ret r{}", src);
            }

            // @todo-speed: this inserts a check to reduce dispatch table size.
            //  may want an unreachable_unchecked() in release.
            0 | END ..= 255 => unreachable!()
        }
    }
}


