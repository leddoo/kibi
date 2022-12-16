#![allow(dead_code)]


#[derive(Clone, Copy, Debug)]
enum Value {
    Nil,
    Bool   { value: bool   },
    Number { value: f64    },
    String { index: usize  },
    List   { index: usize  },
    Table  { index: usize  },
    Func   { index: usize  },
    // Fiber
}

impl Value {
}


#[derive(Debug)]
struct GcObject {
    marked: bool,
    data: GcObjectData,
}

#[derive(Debug)]
enum GcObjectData {
    Nil,
    Free  { next:  Option<usize> },
    List  { values: Vec<Value> },
    Table { values: Vec<(Value, Value)> },
    String { value: String },
    Func   { proto: u32 },
}



#[derive(Debug)]
struct FuncProto {
    code: Vec<Instruction>,
    num_params: u32,
    num_regs:   u32,
    //is_varargs: bool,
}



///
/// encoding stuff:
/// - the opcode is always in the low byte.
/// - `extra` always has the low byte 0xff, which is an invalid opcode.
/// - jumps with `extra` store their target in `extra`.
///
#[derive(Clone, Copy, PartialEq, Debug)]
#[repr(u32)]
enum Opcode {
    Invalid0 = 0,
    Nop,
    Unreachable,

    Copy,

    SetNil,
    SetBool,
    SetInt,
    // TODO: constants.
    //SetNumber,
    //SetString,

    ListNew,
    ListAppend,
    ListDef,
    ListSet,
    ListGet,
    ListLen,

    //Def,
    //Set,
    //Get,

    Add,
    Sub,
    Mul,
    Div,
    //IDiv,
    //IMod,
    //Inc,

    CmpEq,
    CmpLe,
    CmpLt,
    CmpGe,
    CmpGt,

    Jump,
    JumpTrue,
    JumpFalse,
    JumpEq,
    JumpLe,
    JumpLt,
    JumpNEq,
    JumpNLe,
    JumpNLt,


    Call,
    Ret,

    Print,

    Gc,

    Invalid255 = 255,
}

impl Opcode {
    #[inline]
    fn is_jump(self) -> bool {
        use Opcode::*;
        match self {
            Jump    | JumpTrue | JumpFalse |
            JumpEq  | JumpLe   | JumpLt    |
            JumpNEq | JumpNLe  | JumpNLt   => true,
            _ => false
        }
    }

    #[inline]
    fn has_extra(self) -> bool {
        use Opcode::*;
        match self {
            JumpEq  | JumpLe   | JumpLt    |
            JumpNEq | JumpNLe  | JumpNLt   => true,
            _ => false
        }
    }
}


// TODO: u8. & Reg32 for decode.
type Reg = u32;


#[derive(Clone, Copy, PartialEq, Debug)]
#[repr(transparent)]
struct Instruction (u32);

impl Instruction {
    #[inline(always)]
    unsafe fn opcode(self) -> Opcode {
        let opcode = self.0 & 0xff;
        debug_assert!(opcode <= Opcode::Gc as u32);
        core::mem::transmute(opcode)
    }

    #[inline]
    fn patch_opcode(&mut self, new_op: Opcode) {
        self.0 &= !0xff;
        self.0 |= new_op as u32;
    }

    #[inline(always)]
    fn _r1(self) -> Reg {
        (self.0 >> 8) & 0xff
    }

    #[inline(always)]
    fn _r2(self) -> Reg {
        (self.0 >> 16) & 0xff
    }

    #[inline(always)]
    fn _r3(self) -> Reg {
        (self.0 >> 24) & 0xff
    }

    #[inline(always)]
    fn _b2(self) -> bool {
        unsafe { core::mem::transmute(((self.0 >> 16) & 1) as u8) }
    }

    #[inline(always)]
    fn _u8_1(self) -> u32 {
        (self.0 >> 8) & 0xff
    }

    #[inline(always)]
    fn _u8_2(self) -> u32 {
        (self.0 >> 16) & 0xff
    }

    #[inline(always)]
    fn _u8_3(self) -> u32 {
        (self.0 >> 24) & 0xff
    }

    #[inline(always)]
    fn _u16(self) -> u32 {
        (self.0 >> 16) & 0xffff
    }

    #[inline(always)]
    fn patch_u16(&mut self, new_u16: u16) {
        self.0 &= 0xffff;
        self.0 |= (new_u16 as u32) << 16;
    }


    #[inline(always)]
    fn encode_op(op: Opcode) -> Instruction {
        Instruction(op as u32)
    }

    #[inline(always)]
    fn encode_r1(op: Opcode, r1: Reg) -> Instruction {
        debug_assert!(r1 & 0xff == r1);
        Instruction(op as u32 | r1 << 8)
    }

    #[inline]
    fn r1(self) -> Reg {
        self._r1()
    }

    #[inline(always)]
    fn encode_r2(op: Opcode, r1: Reg, r2: Reg) -> Instruction {
        debug_assert!(r1 & 0xff == r1);
        debug_assert!(r2 & 0xff == r2);
        Instruction(op as u32 | r1 << 8 | r2 << 16)
    }

    #[inline]
    fn r2(self) -> (Reg, Reg) {
        (self._r1(), self._r2())
    }

    #[inline(always)]
    fn encode_r3(op: Opcode, r1: Reg, r2: Reg, r3: Reg) -> Instruction {
        debug_assert!(r1 & 0xff == r1);
        debug_assert!(r2 & 0xff == r2);
        debug_assert!(r3 & 0xff == r3);
        Instruction(op as u32 | r1 << 8 | r2 << 16 | r3 << 24)
    }

    #[inline]
    fn r3(self) -> (Reg, Reg, Reg) {
        (self._r1(), self._r2(), self._r3())
    }

    #[inline(always)]
    fn encode_r1b(op: Opcode, r1: Reg, v: bool) -> Instruction {
        debug_assert!(r1 & 0xff == r1);
        Instruction(op as u32 | r1 << 8 | (v as u32) << 16)
    }

    #[inline]
    fn r1b(self) -> (Reg, bool) {
        (self._r1(), self._b2())
    }

    #[inline(always)]
    fn encode_r1c1(op: Opcode, r1: Reg, c1: u8) -> Instruction {
        debug_assert!(r1 & 0xff == r1);
        Instruction(op as u32 | r1 << 8 | (c1 as u32) << 16)
    }

    #[inline]
    fn r1c1(self) -> (Reg, u32) {
        (self._r1(), self._u8_2())
    }

    #[inline(always)]
    fn encode_r1c2(op: Opcode, r1: Reg, c1: u8, c2: u8) -> Instruction {
        debug_assert!(r1 & 0xff == r1);
        Instruction(op as u32 | r1 << 8 | (c1 as u32) << 16 | (c2 as u32) << 24)
    }

    #[inline]
    fn r1c2(self) -> (Reg, u32, u32) {
        (self._r1(), self._u8_2(), self._u8_3())
    }

    #[inline(always)]
    fn encode_r1u16(op: Opcode, r1: Reg, v: u16) -> Instruction {
        debug_assert!(r1 & 0xff == r1);
        Instruction(op as u32 | r1 << 8 | (v as u32) << 16)
    }

    #[inline]
    fn r1u16(self) -> (Reg, u32) {
        (self._r1(), self._u16())
    }

    #[inline(always)]
    fn encode_u16(op: Opcode, v: u16) -> Instruction {
        Instruction(op as u32 | (v as u32) << 16)
    }

    #[inline]
    fn u16(self) -> u32 {
        self._u16()
    }

    #[inline(always)]
    fn encode_extra(v: u32) -> Instruction {
        assert!(v < (1 << 24));
        Instruction(v << 8 | 0xff)
    }

    #[inline]
    fn extra(self) -> u32 {
        self.0 >> 8
    }
}



struct ByteCodeBuilder {
    buffer: Vec<Instruction>,

    block_stack: Vec<usize>,
    blocks:      Vec<(u16, u16)>,
}

impl ByteCodeBuilder {
    fn new() -> Self {
        ByteCodeBuilder {
            buffer: vec![],
            block_stack: vec![],
            blocks:      vec![],
        }
    }

    fn nop(&mut self) {
        self.buffer.push(Instruction::encode_op(Opcode::Nop));
    }

    fn unreachable(&mut self) {
        self.buffer.push(Instruction::encode_op(Opcode::Unreachable));
    }

    fn copy(&mut self, dst: Reg, src: Reg) {
        self.buffer.push(Instruction::encode_r2(Opcode::Copy, dst, src));
    }

    fn set_nil(&mut self, dst: Reg) {
        self.buffer.push(Instruction::encode_r1(Opcode::SetNil, dst));
    }

    fn set_bool(&mut self, dst: Reg, value: bool) {
        self.buffer.push(Instruction::encode_r1b(Opcode::SetBool, dst, value));
    }

    fn set_int(&mut self, dst: Reg, value: i16) {
        self.buffer.push(Instruction::encode_r1u16(Opcode::SetInt, dst, value as u16));
    }

    fn list_new(&mut self, dst: Reg) {
        self.buffer.push(Instruction::encode_r1(Opcode::ListNew, dst));
    }

    fn list_append(&mut self, list: Reg, value: Reg) {
        self.buffer.push(Instruction::encode_r2(Opcode::ListAppend, list, value));
    }

    fn list_def(&mut self, list: Reg, index: Reg, value: Reg) {
        self.buffer.push(Instruction::encode_r3(Opcode::ListDef, list, index, value));
    }

    fn list_set(&mut self, list: Reg, index: Reg, value: Reg) {
        self.buffer.push(Instruction::encode_r3(Opcode::ListSet, list, index, value));
    }

    fn list_get(&mut self, dst: Reg, list: Reg, index: Reg) {
        self.buffer.push(Instruction::encode_r3(Opcode::ListGet, dst, list, index));
    }

    fn list_len(&mut self, dst: Reg, list: Reg) {
        self.buffer.push(Instruction::encode_r2(Opcode::ListLen, dst, list));
    }

    /*
    fn def(&mut self, obj: Reg, index: Reg, value: Reg) {
        self.buffer.push(Instruction::encode_r3(Opcode::Def, obj, index, value));
    }

    fn set(&mut self, obj: Reg, index: Reg, value: Reg) {
        self.buffer.push(Instruction::encode_r3(Opcode::Set, obj, index, value));
    }

    fn get(&mut self, obj: Reg, list: Reg, index: Reg) {
        self.buffer.push(Instruction::encode_r3(Opcode::Get, obj, list, index));
    }
    */

    fn add(&mut self, dst: Reg, src1: Reg, src2: Reg) {
        self.buffer.push(Instruction::encode_r3(Opcode::Add, dst, src1, src2));
    }

    fn sub(&mut self, dst: Reg, src1: Reg, src2: Reg) {
        self.buffer.push(Instruction::encode_r3(Opcode::Sub, dst, src1, src2));
    }

    fn mul(&mut self, dst: Reg, src1: Reg, src2: Reg) {
        self.buffer.push(Instruction::encode_r3(Opcode::Mul, dst, src1, src2));
    }

    fn div(&mut self, dst: Reg, src1: Reg, src2: Reg) {
        self.buffer.push(Instruction::encode_r3(Opcode::Div, dst, src1, src2));
    }

    fn cmp_eq(&mut self, dst: Reg, src1: Reg, src2: Reg) {
        self.buffer.push(Instruction::encode_r3(Opcode::CmpEq, dst, src1, src2));
    }

    fn cmp_le(&mut self, dst: Reg, src1: Reg, src2: Reg) {
        self.buffer.push(Instruction::encode_r3(Opcode::CmpLe, dst, src1, src2));
    }

    fn cmp_lt(&mut self, dst: Reg, src1: Reg, src2: Reg) {
        self.buffer.push(Instruction::encode_r3(Opcode::CmpLt, dst, src1, src2));
    }

    fn cmp_ge(&mut self, dst: Reg, src1: Reg, src2: Reg) {
        self.buffer.push(Instruction::encode_r3(Opcode::CmpGe, dst, src1, src2));
    }

    fn cmp_gt(&mut self, dst: Reg, src1: Reg, src2: Reg) {
        self.buffer.push(Instruction::encode_r3(Opcode::CmpGt, dst, src1, src2));
    }

    fn jump(&mut self, target: u16) {
        self.buffer.push(Instruction::encode_u16(Opcode::Jump, target));
    }

    fn jump_true(&mut self, src: Reg, target: u16) {
        self.buffer.push(Instruction::encode_r1u16(Opcode::JumpTrue, src, target));
    }

    fn jump_false(&mut self, src: Reg, target: u16) {
        self.buffer.push(Instruction::encode_r1u16(Opcode::JumpFalse, src, target));
    }

    fn jump_eq(&mut self, src1: Reg, src2: Reg, target: u16) {
        self.buffer.push(Instruction::encode_r2(Opcode::JumpEq, src1, src2));
        self.buffer.push(Instruction::encode_extra(target as u32));
    }

    fn jump_le(&mut self, src1: Reg, src2: Reg, target: u16) {
        self.buffer.push(Instruction::encode_r2(Opcode::JumpLe, src1, src2));
        self.buffer.push(Instruction::encode_extra(target as u32));
    }

    fn jump_lt(&mut self, src1: Reg, src2: Reg, target: u16) {
        self.buffer.push(Instruction::encode_r2(Opcode::JumpLt, src1, src2));
        self.buffer.push(Instruction::encode_extra(target as u32));
    }

    fn jump_neq(&mut self, src1: Reg, src2: Reg, target: u16) {
        self.buffer.push(Instruction::encode_r2(Opcode::JumpNEq, src1, src2));
        self.buffer.push(Instruction::encode_extra(target as u32));
    }

    fn jump_nle(&mut self, src1: Reg, src2: Reg, target: u16) {
        self.buffer.push(Instruction::encode_r2(Opcode::JumpNLe, src1, src2));
        self.buffer.push(Instruction::encode_extra(target as u32));
    }

    fn jump_nlt(&mut self, src1: Reg, src2: Reg, target: u16) {
        self.buffer.push(Instruction::encode_r2(Opcode::JumpNLt, src1, src2));
        self.buffer.push(Instruction::encode_extra(target as u32));
    }

    fn call(&mut self, dst: Reg, num_args: u8, num_rets: u8) {
        self.buffer.push(Instruction::encode_r1c2(Opcode::Call, dst, num_args, num_rets));
    }

    fn ret(&mut self, rets: Reg, num_rets: u8) {
        self.buffer.push(Instruction::encode_r1c1(Opcode::Ret, rets, num_rets));
    }

    fn print(&mut self, reg: Reg) {
        self.buffer.push(Instruction::encode_r1(Opcode::Print, reg));
    }

    fn gc(&mut self) {
        self.buffer.push(Instruction::encode_op(Opcode::Gc));
    }


    fn begin_block(&mut self) {
        let block = self.blocks.len();
        let begin = self.buffer.len() as u16;
        self.block_stack.push(block);
        self.blocks.push((begin, u16::MAX));
    }

    fn end_block(&mut self) {
        let block = self.block_stack.pop().unwrap();
        let end = self.buffer.len() as u16;
        self.blocks[block].1 = end;
    }

    fn block<F: FnOnce(&mut ByteCodeBuilder)>(&mut self, f: F) {
        self.begin_block();
        f(self);
        self.end_block();
    }

    #[inline]
    fn _block_begin(&self, index: usize) -> u16 {
        assert!(index < self.block_stack.len());
        let block = self.block_stack[self.block_stack.len() - 1 - index];
        self.blocks[block].0
    }

    const JUMP_BLOCK_END_BIT: usize = 1 << 15;

    #[inline]
    fn _block_end(&self, index: usize) -> u16 {
        assert!(index < self.block_stack.len());
        let block = self.block_stack[self.block_stack.len() - 1 - index];
        (block | Self::JUMP_BLOCK_END_BIT) as u16
    }


    fn exit_block(&mut self, index: usize) {
        self.jump(self._block_end(index));
    }

    fn exit_eq(&mut self, src1: Reg, src2: Reg, index: usize) {
        self.jump_eq(src1, src2, self._block_end(index));
    }

    fn exit_le(&mut self, src1: Reg, src2: Reg, index: usize) {
        self.jump_le(src1, src2, self._block_end(index));
    }

    fn exit_lt(&mut self, src1: Reg, src2: Reg, index: usize) {
        self.jump_lt(src1, src2, self._block_end(index));
    }

    fn exit_neq(&mut self, src1: Reg, src2: Reg, index: usize) {
        self.jump_neq(src1, src2, self._block_end(index));
    }

    fn exit_nle(&mut self, src1: Reg, src2: Reg, index: usize) {
        self.jump_nle(src1, src2, self._block_end(index));
    }

    fn exit_nlt(&mut self, src1: Reg, src2: Reg, index: usize) {
        self.jump_nlt(src1, src2, self._block_end(index));
    }

    fn repeat_block(&mut self, index: usize) {
        self.jump(self._block_begin(index));
    }

    fn repeat_eq(&mut self, src1: Reg, src2: Reg, index: usize) {
        self.jump_eq(src1, src2, self._block_begin(index));
    }

    fn repeat_le(&mut self, src1: Reg, src2: Reg, index: usize) {
        self.jump_le(src1, src2, self._block_begin(index));
    }

    fn repeat_lt(&mut self, src1: Reg, src2: Reg, index: usize) {
        self.jump_lt(src1, src2, self._block_begin(index));
    }

    fn repeat_neq(&mut self, src1: Reg, src2: Reg, index: usize) {
        self.jump_neq(src1, src2, self._block_begin(index));
    }

    fn repeat_nle(&mut self, src1: Reg, src2: Reg, index: usize) {
        self.jump_nle(src1, src2, self._block_begin(index));
    }

    fn repeat_nlt(&mut self, src1: Reg, src2: Reg, index: usize) {
        self.jump_nlt(src1, src2, self._block_begin(index));
    }


    fn build(mut self) -> Vec<Instruction> {
        assert!(self.buffer.len() < (1 << 16));
        assert!(self.blocks.len() < (1 << 12));

        assert!(self.block_stack.len() == 0);

        let mut i = 0;
        while i < self.buffer.len() {
            let instr = &mut self.buffer[i];
            i += 1;

            let op = unsafe { instr.opcode() };

            if op.has_extra() {
                let extra = &mut self.buffer[i];
                i += 1;

                if op.is_jump() {
                    let target = extra.extra() as usize;
                    if target & Self::JUMP_BLOCK_END_BIT != 0 {
                        let block = target & !Self::JUMP_BLOCK_END_BIT;
                        let end = self.blocks[block].1;
                        *extra = Instruction::encode_extra(end as u32);
                    }
                }
            }
            else if op.is_jump() {
                let target = instr.u16() as usize;
                if target & Self::JUMP_BLOCK_END_BIT != 0 {
                    let block = target & !Self::JUMP_BLOCK_END_BIT;
                    let end = self.blocks[block].1;
                    instr.patch_u16(end);
                }
            }
        }

        self.buffer
    }
}



#[derive(Debug)]
struct StackFrame {
    func_proto: u32,

    dest_reg:   u32,
    num_rets:   u32,
    //num_varags: u32,

    pc:   u32,
    func: u32,
    base: u32,
    top:  u32,
}

impl StackFrame {
    const ROOT: StackFrame = StackFrame {
        func_proto: u32::MAX,
        dest_reg: 0, num_rets: 0, //num_varags: 0,
        pc: 0, func: 0, base: 0, top: 0,
    };
}


#[derive(Debug)]
struct Vm {
    func_protos: Vec<FuncProto>,

    pc:     usize,
    frames: Vec<StackFrame>,
    stack:  Vec<Value>, // @todo-speed: don't use a vec.
    heap:   Vec<GcObject>,

    first_free: Option<usize>,
    gc_timer:   u32,
}

impl Vm {
    fn new() -> Self {
        Vm {
            func_protos: vec![],

            pc:     usize::MAX,
            frames: vec![StackFrame::ROOT],
            stack:  vec![],
            heap:   vec![],

            first_free: None,
            gc_timer:   0,
        }
    }

    fn heap_alloc(&mut self) -> usize {
        self.gc_timer += 1;
        if self.gc_timer >= 1000 {
            self.gc_timer = 0;
            self.gc();
        }

        if let Some(first_free) = self.first_free {
            let object = &mut self.heap[first_free];
            let GcObjectData::Free { next } = object.data else { unreachable!() };
            object.data = GcObjectData::Nil;

            self.first_free = next;
            first_free
        }
        else {
            let index = self.heap.len();
            self.heap.push(GcObject { marked: false, data: GcObjectData::Nil });
            index
        }
    }

    fn heap_free(&mut self, index: usize) {
        println!("free {} ({:?})", index, self.heap[index].data);
        self.heap[index].data = GcObjectData::Free { next: self.first_free };
        self.first_free = Some(index);
    }

    fn gc(&mut self) {
        fn mark_value(heap: &mut Vec<GcObject>, value: &Value) {
            match value {
                Value::String { index } |
                Value::List { index } |
                Value::Table { index } => {
                    mark_object(heap, *index);
                }

                _ => (),
            }
        }

        fn mark_object(heap: &mut Vec<GcObject>, index: usize) {
            let object = &mut heap[index];
            if object.marked {
                return;
            }
            object.marked = true;

            // @safety: recursive calls won't access this object, as it's `marked`.
            // @todo-safety: but there are two simultaneous mut refs, so this is ub.
            let object = unsafe { &mut *(object as *mut GcObject) };

            match &object.data {
                GcObjectData::List { values: value } => {
                    for v in value {
                        mark_value(heap, v);
                    }
                }

                GcObjectData::Table { values: value } => {
                    for (k, v) in value {
                        mark_value(heap, k);
                        mark_value(heap, v);
                    }
                }

                GcObjectData::String { value: _ } => {}

                _ => unreachable!()
            }
        }

        println!("gc");

        // mark.
        for value in &self.stack {
            mark_value(&mut self.heap, value);
        }

        // sweep.
        for i in 0..self.heap.len() {
            let object = &mut self.heap[i];
            if object.marked {
                object.marked = false;
            }
            else {
                self.heap_free(i);
            }
        }
    }

    #[inline]
    fn string_value(&self, object: usize) -> &str {
        if let GcObjectData::String { value } = &self.heap[object].data {
            value
        }
        else { unreachable!() }
    }

    #[inline]
    fn value_eq(&mut self, v1: Value, v2: Value) -> bool {
        use Value::*;
        match (v1, v2) {
            (Nil, Nil) => true,

            (Bool { value: v1 }, Bool { value: v2 }) =>
                v1 == v2,

            (Number { value: v1 }, Number { value: v2 }) =>
                v1 == v2,

            (String { index: i1 }, String { index: i2 }) => {
                self.string_value(i1) == self.string_value(i2)
            }

            (List { index: i1 }, List { index: i2 }) =>
                i1 == i2,

            (Table { index: _i1 }, Table { index: _i2 }) =>
                unimplemented!(),

            _ => false,
        }
    }

    #[inline]
    fn value_le(&mut self, v1: Value, v2: Value) -> bool {
        use Value::*;
        match (v1, v2) {
            (Number { value: v1 }, Number { value: v2 }) =>
                v1 <= v2,

            _ => unimplemented!(),
        }
    }

    #[inline]
    fn value_lt(&mut self, v1: Value, v2: Value) -> bool {
        use Value::*;
        match (v1, v2) {
            (Number { value: v1 }, Number { value: v2 }) =>
                v1 < v2,

            _ => unimplemented!(),
        }
    }

    #[inline]
    fn value_ge(&mut self, v1: Value, v2: Value) -> bool {
        use Value::*;
        match (v1, v2) {
            (Number { value: v1 }, Number { value: v2 }) =>
                v1 >= v2,

            _ => unimplemented!(),
        }
    }

    #[inline]
    fn value_gt(&mut self, v1: Value, v2: Value) -> bool {
        use Value::*;
        match (v1, v2) {
            (Number { value: v1 }, Number { value: v2 }) =>
                v1 > v2,

            _ => unimplemented!(),
        }
    }

    #[inline]
    fn value_add(&mut self, v1: Value, v2: Value) -> Value {
        use Value::*;
        match (v1, v2) {
            (Number { value: v1 }, Number { value: v2 }) =>
                Number { value: v1 + v2 },

            _ => unimplemented!(),
        }
    }

    #[inline]
    fn value_sub(&mut self, v1: Value, v2: Value) -> Value {
        use Value::*;
        match (v1, v2) {
            (Number { value: v1 }, Number { value: v2 }) =>
                Number { value: v1 - v2 },

            _ => unimplemented!(),
        }
    }

    #[inline]
    fn value_mul(&mut self, v1: Value, v2: Value) -> Value {
        use Value::*;
        match (v1, v2) {
            (Number { value: v1 }, Number { value: v2 }) =>
                Number { value: v1 * v2 },

            _ => unimplemented!(),
        }
    }

    #[inline]
    fn value_div(&mut self, v1: Value, v2: Value) -> Value {
        use Value::*;
        match (v1, v2) {
            (Number { value: v1 }, Number { value: v2 }) =>
                Number { value: v1 / v2 },

            _ => unimplemented!(),
        }
    }

    #[inline]
    fn value_print(&self, value: Value) {
        match value {
            Value::Nil              => print!("nil"),
            Value::Bool   { value } => print!("{}", value),
            Value::Number { value } => print!("{}", value),
            Value::String { index } => {
                let GcObjectData::String { value } = &self.heap[index].data else { unreachable!() };
                print!("{}", value);
            }
            Value::List   { index } => print!("<List {}>", index),
            Value::Table  { index } => print!("<Table {}>", index),
            Value::Func   { index } => print!("<Func {}>", index),
        }
    }

    #[inline(always)]
    fn reg(&mut self, reg: Reg) -> &mut Value {
        // @todo-speed: obviously don't do this.
        let frame = self.frames.last().unwrap();
        debug_assert!(frame.base + reg < frame.top);
        &mut self.stack[(frame.base + reg) as usize]
    }

    #[inline(always)]
    fn next_instr(&mut self) -> Instruction {
        // @todo-speed: obviously don't do this.
        let frame = self.frames.last().unwrap();
        let proto = &self.func_protos[frame.func_proto as usize];

        let result = proto.code[self.pc];
        self.pc += 1;
        result
    }

    #[inline(never)]
    fn run(&mut self) {
        if self.frames.len() == 1 {
            return;
        }

        loop {
            let instr = self.next_instr();

            let op = unsafe { instr.opcode() };
            match op {
                Opcode::Invalid0 | Opcode::Invalid255 => unreachable!(),

                Opcode::Nop => (),

                Opcode::Unreachable => unimplemented!(),


                Opcode::Copy => {
                    let (dst, src) = instr.r2();
                    // @todo-speed: remove checks.
                    *self.reg(dst) = *self.reg(src);
                }


                Opcode::SetNil => {
                    let dst = instr.r1();
                    // @todo-speed: remove checks.
                    *self.reg(dst) = Value::Nil;
                }

                Opcode::SetBool => {
                    let (dst, value) = instr.r1b();
                    // @todo-speed: remove checks.
                    *self.reg(dst) = Value::Bool { value };
                }

                Opcode::SetInt => {
                    let (dst, value) = instr.r1u16();
                    let value = value as u16 as i16 as f64;
                    // @todo-speed: remove checks.
                    *self.reg(dst) = Value::Number { value };
                }

                /*
                Opcode::SetNumber { dst, value } => {
                    // @todo-speed: remove checks.
                    self.stack[dst as usize] = Value::Number { value };
                }

                Opcode::SetString { dst, value } => {
                    let index = self.heap_alloc();
                    // @todo-speed: constant table.
                    self.heap[index].data = GcObjectData::String { value: value.into() };

                    // @todo-speed: remove checks.
                    self.stack[dst as usize] = Value::String { index };
                }
                */


                Opcode::ListNew => {
                    let dst = instr.r1();

                    let index = self.heap_alloc();
                    self.heap[index].data = GcObjectData::List { values: vec![] };

                    // @todo-speed: remove checks.
                    *self.reg(dst) = Value::List { index };
                }

                Opcode::ListAppend => {
                    let (list, value) = instr.r2();

                    // @todo-speed: remove checks.
                    let list  = *self.reg(list);
                    let value = *self.reg(value);

                    // @todo-robust: error.
                    let Value::List { index: list_index } = list else { unimplemented!() };

                    let object = &mut self.heap[list_index];
                    let GcObjectData::List { values } = &mut object.data else { unreachable!() };

                    values.push(value);
                }

                Opcode::ListDef => {
                    let (list, index, value) = instr.r3();

                    // @todo-speed: remove checks.
                    let list  = *self.reg(list);
                    let index = *self.reg(index);
                    let value = *self.reg(value);

                    // @todo-robust: error.
                    let Value::List { index: list_index } = list else { unimplemented!() };

                    // @todo-cleanup: value utils.
                    let object = &mut self.heap[list_index];
                    let GcObjectData::List { values } = &mut object.data else { unreachable!() };

                    // @todo-robust: error.
                    let Value::Number { value: index } = index else { unimplemented!() };
                    let index = index as usize;

                    if index >= values.len() {
                        values.resize(index + 1, Value::Nil);
                    }
                    values[index] = value;
                }

                Opcode::ListSet => {
                    let (list, index, value) = instr.r3();

                    // @todo-speed: remove checks.
                    let list  = *self.reg(list);
                    let index = *self.reg(index);
                    let value = *self.reg(value);

                    // @todo-robust: error.
                    let Value::List { index: list_index } = list else { unimplemented!() };

                    // @todo-cleanup: value utils.
                    let object = &mut self.heap[list_index];
                    let GcObjectData::List { values } = &mut object.data else { unreachable!() };

                    // @todo-robust: error.
                    let Value::Number { value: index } = index else { unimplemented!() };

                    // @todo-robust: error.
                    let slot = &mut values[index as usize];
                    *slot = value;
                }

                Opcode::ListGet => {
                    let (dst, list, index) = instr.r3();

                    // @todo-speed: remove checks.
                    let list  = *self.reg(list);
                    let index = *self.reg(index);

                    // @todo-robust: error.
                    let Value::List { index: list_index } = list else { unimplemented!() };

                    // @todo-cleanup: value utils.
                    let object = &mut self.heap[list_index];
                    let GcObjectData::List { values } = &mut object.data else { unreachable!() };

                    // @todo-robust: error.
                    let Value::Number { value: index } = index else { unimplemented!() };

                    // @todo-robust: error.
                    let value = values[index as usize];

                    *self.reg(dst) = value;
                }

                Opcode::ListLen => {
                    let (dst, list) = instr.r2();

                    // @todo-speed: remove checks.
                    let list = *self.reg(list);

                    // @todo-robust: error.
                    let Value::List { index: list_index } = list else { unimplemented!() };

                    // @todo-cleanup: value utils.
                    let object = &mut self.heap[list_index];
                    let GcObjectData::List { values } = &mut object.data else { unreachable!() };

                    let len = Value::Number { value: values.len() as f64 };
                    *self.reg(dst) = len;
                }


                Opcode::Add => {
                    let (dst, src1, src2) = instr.r3();
                    // @todo-speed: remove checks.
                    let src1 = *self.reg(src1);
                    let src2 = *self.reg(src2);
                    let result = self.value_add(src1, src2);
                    *self.reg(dst) = result;
                }

                Opcode::Sub => {
                    let (dst, src1, src2) = instr.r3();
                    // @todo-speed: remove checks.
                    let src1 = *self.reg(src1);
                    let src2 = *self.reg(src2);
                    let result = self.value_sub(src1, src2);
                    *self.reg(dst) = result;
                }

                Opcode::Mul => {
                    let (dst, src1, src2) = instr.r3();
                    // @todo-speed: remove checks.
                    let src1 = *self.reg(src1);
                    let src2 = *self.reg(src2);
                    let result = self.value_mul(src1, src2);
                    *self.reg(dst) = result;
                }

                Opcode::Div => {
                    let (dst, src1, src2) = instr.r3();
                    // @todo-speed: remove checks.
                    let src1 = *self.reg(src1);
                    let src2 = *self.reg(src2);
                    let result = self.value_div(src1, src2);
                    *self.reg(dst) = result;
                }


                Opcode::CmpEq => {
                    let (dst, src1, src2) = instr.r3();
                    // @todo-speed: remove checks.
                    let src1 = *self.reg(src1);
                    let src2 = *self.reg(src2);
                    let result = self.value_eq(src1, src2);
                    *self.reg(dst) = Value::Bool { value: result };
                }

                Opcode::CmpLe => {
                    let (dst, src1, src2) = instr.r3();
                    // @todo-speed: remove checks.
                    let src1 = *self.reg(src1);
                    let src2 = *self.reg(src2);
                    let result = self.value_le(src1, src2);
                    *self.reg(dst) = Value::Bool { value: result };
                }

                Opcode::CmpLt => {
                    let (dst, src1, src2) = instr.r3();
                    // @todo-speed: remove checks.
                    let src1 = *self.reg(src1);
                    let src2 = *self.reg(src2);
                    let result = self.value_lt(src1, src2);
                    *self.reg(dst) = Value::Bool { value: result };
                }

                Opcode::CmpGe => {
                    let (dst, src1, src2) = instr.r3();
                    // @todo-speed: remove checks.
                    let src1 = *self.reg(src1);
                    let src2 = *self.reg(src2);
                    let result = self.value_ge(src1, src2);
                    *self.reg(dst) = Value::Bool { value: result };
                }

                Opcode::CmpGt => {
                    let (dst, src1, src2) = instr.r3();
                    // @todo-speed: remove checks.
                    let src1 = *self.reg(src1);
                    let src2 = *self.reg(src2);
                    let result = self.value_gt(src1, src2);
                    *self.reg(dst) = Value::Bool { value: result };
                }


                Opcode::Jump => {
                    let target = instr.u16();
                    self.pc = target as usize;
                }

                Opcode::JumpTrue => {
                    let (src, target) = instr.r1u16();

                    // @todo-speed: remove checks.
                    let condition = *self.reg(src);

                    // @todo-robust: error.
                    // @todo-cleanup: value utils.
                    let Value::Bool { value } = condition else { unimplemented!() };

                    if value {
                        self.pc = target as usize;
                    }
                }

                Opcode::JumpFalse => {
                    let (src, target) = instr.r1u16();

                    // @todo-speed: remove checks.
                    let condition = *self.reg(src);

                    // @todo-robust: error.
                    // @todo-cleanup: value utils.
                    let Value::Bool { value } = condition else { unimplemented!() };

                    if !value {
                        self.pc = target as usize;
                    }
                }

                Opcode::JumpEq => {
                    let (src1, src2) = instr.r2();
                    let target = self.next_instr().extra();

                    // @todo-speed: remove checks.
                    let src1 = *self.reg(src1);
                    let src2 = *self.reg(src2);
                    if self.value_eq(src1, src2) {
                        self.pc = target as usize;
                    }
                }

                Opcode::JumpLe => {
                    let (src1, src2) = instr.r2();
                    let target = self.next_instr().extra();

                    // @todo-speed: remove checks.
                    let src1 = *self.reg(src1);
                    let src2 = *self.reg(src2);
                    if self.value_le(src1, src2) {
                        self.pc = target as usize;
                    }
                }

                Opcode::JumpLt => {
                    let (src1, src2) = instr.r2();
                    let target = self.next_instr().extra();

                    // @todo-speed: remove checks.
                    let src1 = *self.reg(src1);
                    let src2 = *self.reg(src2);
                    if self.value_lt(src1, src2) {
                        self.pc = target as usize;
                    }
                }

                Opcode::JumpNEq => {
                    let (src1, src2) = instr.r2();
                    let target = self.next_instr().extra();

                    // @todo-speed: remove checks.
                    let src1 = *self.reg(src1);
                    let src2 = *self.reg(src2);
                    if !self.value_eq(src1, src2) {
                        self.pc = target as usize;
                    }
                }

                Opcode::JumpNLe => {
                    let (src1, src2) = instr.r2();
                    let target = self.next_instr().extra();

                    // @todo-speed: remove checks.
                    let src1 = *self.reg(src1);
                    let src2 = *self.reg(src2);
                    if !self.value_le(src1, src2) {
                        self.pc = target as usize;
                    }
                }

                Opcode::JumpNLt => {
                    let (src1, src2) = instr.r2();
                    let target = self.next_instr().extra();

                    // @todo-speed: remove checks.
                    let src1 = *self.reg(src1);
                    let src2 = *self.reg(src2);
                    if !self.value_lt(src1, src2) {
                        self.pc = target as usize;
                    }
                }


                Opcode::Call => {
                    let (dst, num_args, num_rets) = instr.r1c2();
                    self.prep_call(dst, num_args, num_rets);
                }

                Opcode::Ret => {
                    let (rets, num_rets) = instr.r1c1();

                    let frame = self.frames.pop().unwrap();
                    debug_assert!(frame.base + rets + num_rets <= frame.top);

                    // @todo-robust: raise error.
                    assert!(frame.num_rets <= num_rets);

                    let prev_frame = self.frames.last_mut().unwrap();

                    // copy rets to their destination.
                    let dst_base = prev_frame.base + frame.dest_reg;
                    debug_assert!(dst_base + frame.num_rets <= prev_frame.top);
                    let src_base = frame.base + rets;
                    // @todo-correctness: copy ltr vs copy rtl?
                    debug_assert!(dst_base + frame.num_rets <= src_base);
                    // @todo-speed: special cases for n < 4.
                    for i in 0..frame.num_rets {
                        self.stack[(dst_base + i) as usize] = self.stack[(src_base + i) as usize];
                    }

                    // reset vm state.
                    self.pc = prev_frame.pc as usize;
                    self.stack.truncate(prev_frame.top as usize);

                    // @todo-speed: debug only.
                    prev_frame.pc = u32::MAX;

                    if self.frames.len() == 1 {
                        return;
                    }
                }


                Opcode::Print => {
                    let reg = instr.r1();
                    // @todo-speed: remove checks.
                    let value = *self.reg(reg);
                    self.value_print(value);
                    println!();
                }


                Opcode::Gc => {
                    self.gc();
                }
            }
        }
    }

    fn _push(&mut self, value: Value) {
        self.stack.push(value);
        self.frames.last_mut().unwrap().top += 1;
    }

    fn _pop(&mut self) -> Value {
        let frame = self.frames.last_mut().unwrap();
        assert!(frame.top > frame.base);
        frame.top -= 1;
        self.stack.pop().unwrap()
    }

    fn pop_n(&mut self, n: u32) {
        let frame = self.frames.last_mut().unwrap();
        assert!(frame.top >= frame.base + n);
        frame.top -= n as u32;
        self.stack.truncate(frame.top as usize);
    }

    // TODO: maybe put these on some "Guard"
    // that wraps `&mut Vm`.
    // cause calling them while execution is suspended is ub.
    // TEMP: don't expose protos.
    fn push_func(&mut self, proto: u32) {
        let index = self.heap_alloc();
        self.heap[index].data = GcObjectData::Func { proto };
        self._push(Value::Func { index });
    }

    fn push_number(&mut self, value: f64) {
        self._push(Value::Number { value });
    }

    // @todo-speed: maybe parameters should be immutable.
    //  that would enable compilers to optimize repeated function calls.
    //  but not sure that's really all that common.
    // @todo-speed: inline(always).
    #[inline]
    fn prep_call(&mut self, dst: u32, num_args: u32, num_rets: u32) {
        assert!(num_args < 128);
        assert!(num_rets < 128);

        let frame = self.frames.last_mut().unwrap();
        frame.pc = self.pc as u32;

        let func = frame.top - num_args - 1;
        debug_assert!(func >= frame.base);

        let func_value = self.stack[func as usize];
        // @todo-robust: error.
        let Value::Func { index: func_index } = func_value else { unimplemented!() };
        // @todo-cleanup: value utils.
        let GcObjectData::Func { proto: func_proto } = self.heap[func_index].data else { unreachable!() };
        let proto = &self.func_protos[func_proto as usize];

        // @todo-robust: error.
        assert!(num_args == proto.num_params);

        let base = func + 1;
        let top  = base + proto.num_regs;

        self.frames.push(StackFrame {
            func_proto,
            dest_reg: dst,
            num_rets,
            //num_varags: 0,
            pc: u32::MAX,
            func,
            base,
            top,
        });
        self.pc = 0;
        self.stack.resize(top as usize, Value::Nil);
    }

    fn call(&mut self, dst: u32, num_args: u8, num_rets: u8) {
        self.prep_call(dst, num_args as u32, num_rets as u32);
        self.run();
    }
}


fn main() {
    let mut vm = Vm::new();

    // fib(n, f) = if n < 2 then n else f(n-2) + f(n-1) end
    vm.func_protos.push(FuncProto {
        code: {
            let mut b = ByteCodeBuilder::new();
            b.block(|b| {
                // if
                b.block(|b| {
                    b.set_int(2, 2);
                    b.exit_nlt(0, 2, 0);
                    b.ret(0, 1);
                });
                // else
                b.copy(4, 1);
                b.sub(5, 0, 2);
                b.copy(6, 1);
                b.call(2, 2, 1);

                b.copy(4, 1);
                b.set_int(3, 1);
                b.sub(5, 0, 3);
                b.copy(6, 1);
                b.call(3, 2, 1);

                b.add(2, 2, 3);
                b.ret(2, 1);
            });
            b.build()
        },
        num_params: 2,
        num_regs:   7,
        //is_varargs: false,
    });

    // run(f, n): for i in 0..n do print(f(i)) end
    vm.func_protos.push(FuncProto {
        code: {
            let mut b = ByteCodeBuilder::new();
            b.set_int(2, 0);
            b.block(|b| {
                b.exit_nlt(2, 1, 0);
                b.copy(3, 0);
                b.copy(4, 2);
                b.copy(5, 0);
                b.call(3, 2, 1);
                b.print(3);
                b.set_int(3, 1);
                b.add(2, 2, 3);
                b.repeat_block(0);
            });
            b.ret(0, 0);
            b.build()
        },
        num_params: 2,
        num_regs:   6,
        //is_varargs: false,
    });

    let t0 = std::time::Instant::now();
    vm.push_func(1);
    vm.push_func(0);
    vm.push_number(25.0);
    vm.call(0, 2, 0);
    println!("{:?}", t0.elapsed());
}

