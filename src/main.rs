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

impl From<bool> for Value { #[inline(always)] fn from(value: bool) -> Self { Value::Bool   { value } } }
impl From<f64>  for Value { #[inline(always)] fn from(value: f64)  -> Self { Value::Number { value } } }


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
    Table  (TableData),
    String { value: String },
    Func   { proto: u32 },
}


#[derive(Debug)]
struct TableData {
    values: Vec<(Value, Value)>,
}

impl TableData {
    fn insert(&mut self, key: Value, value: Value, vm: &mut Vm) {
        if let Some(v) = self.index(key, vm) {
            *v = value;
        }
        else {
            self.values.push((key, value));
        }
    }

    fn index(&mut self, key: Value, vm: &mut Vm) -> Option<&mut Value> {
        for (k, v) in &mut self.values {
            // @todo-decide: should this use `raw_eq`?
            if vm.generic_eq(*k, key) {
                return Some(v);
            }
        }
        None
    }

    fn len(&self) -> usize {
        self.values.len()
    }
}



#[derive(Debug)]
struct FuncProto {
    code: Vec<Instruction>,
    constants: Vec<Value>,
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

    LoadNil,
    LoadBool,
    LoadInt,
    LoadConst,
    LoadEnv,

    ListNew,
    ListAppend,
    ListDef,
    ListSet,
    ListGet,
    ListLen,

    TableNew,
    TableDef,
    TableSet,
    TableGet,
    TableLen,

    Def,
    Set,
    Get,
    Len,

    Add,
    Sub,
    Mul,
    Div,
    //IDiv,
    //IMod,
    Inc,
    Dec,

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

    #[inline(always)]
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

    #[inline(always)]
    fn r1(self) -> Reg {
        self._r1()
    }

    #[inline(always)]
    fn encode_r2(op: Opcode, r1: Reg, r2: Reg) -> Instruction {
        debug_assert!(r1 & 0xff == r1);
        debug_assert!(r2 & 0xff == r2);
        Instruction(op as u32 | r1 << 8 | r2 << 16)
    }

    #[inline(always)]
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

    #[inline(always)]
    fn r3(self) -> (Reg, Reg, Reg) {
        (self._r1(), self._r2(), self._r3())
    }

    #[inline(always)]
    fn encode_r1b(op: Opcode, r1: Reg, v: bool) -> Instruction {
        debug_assert!(r1 & 0xff == r1);
        Instruction(op as u32 | r1 << 8 | (v as u32) << 16)
    }

    #[inline(always)]
    fn r1b(self) -> (Reg, bool) {
        (self._r1(), self._b2())
    }

    #[inline(always)]
    fn encode_r1c1(op: Opcode, r1: Reg, c1: u8) -> Instruction {
        debug_assert!(r1 & 0xff == r1);
        Instruction(op as u32 | r1 << 8 | (c1 as u32) << 16)
    }

    #[inline(always)]
    fn r1c1(self) -> (Reg, u32) {
        (self._r1(), self._u8_2())
    }

    #[inline(always)]
    fn encode_r1c2(op: Opcode, r1: Reg, c1: u8, c2: u8) -> Instruction {
        debug_assert!(r1 & 0xff == r1);
        Instruction(op as u32 | r1 << 8 | (c1 as u32) << 16 | (c2 as u32) << 24)
    }

    #[inline(always)]
    fn r1c2(self) -> (Reg, u32, u32) {
        (self._r1(), self._u8_2(), self._u8_3())
    }

    #[inline(always)]
    fn encode_r1u16(op: Opcode, r1: Reg, v: u16) -> Instruction {
        debug_assert!(r1 & 0xff == r1);
        Instruction(op as u32 | r1 << 8 | (v as u32) << 16)
    }

    #[inline(always)]
    fn r1u16(self) -> (Reg, u32) {
        (self._r1(), self._u16())
    }

    #[inline(always)]
    fn encode_u16(op: Opcode, v: u16) -> Instruction {
        Instruction(op as u32 | (v as u32) << 16)
    }

    #[inline(always)]
    fn u16(self) -> u32 {
        self._u16()
    }

    #[inline(always)]
    fn encode_extra(v: u32) -> Instruction {
        assert!(v < (1 << 24));
        Instruction(v << 8 | 0xff)
    }

    #[inline(always)]
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


    fn load_nil(&mut self, dst: Reg) {
        self.buffer.push(Instruction::encode_r1(Opcode::LoadNil, dst));
    }

    fn load_bool(&mut self, dst: Reg, value: bool) {
        self.buffer.push(Instruction::encode_r1b(Opcode::LoadBool, dst, value));
    }

    fn load_int(&mut self, dst: Reg, value: i16) {
        self.buffer.push(Instruction::encode_r1u16(Opcode::LoadInt, dst, value as u16));
    }

    fn load_const(&mut self, dst: Reg, index: u16) {
        self.buffer.push(Instruction::encode_r1u16(Opcode::LoadConst, dst, index));
    }

    fn load_env(&mut self, dst: Reg) {
        self.buffer.push(Instruction::encode_r1(Opcode::LoadEnv, dst));
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


    fn table_new(&mut self, dst: Reg) {
        self.buffer.push(Instruction::encode_r1(Opcode::TableNew, dst));
    }

    fn table_def(&mut self, table: Reg, key: Reg, value: Reg) {
        self.buffer.push(Instruction::encode_r3(Opcode::TableDef, table, key, value));
    }

    fn table_set(&mut self, table: Reg, key: Reg, value: Reg) {
        self.buffer.push(Instruction::encode_r3(Opcode::TableSet, table, key, value));
    }

    fn table_get(&mut self, dst: Reg, table: Reg, key: Reg) {
        self.buffer.push(Instruction::encode_r3(Opcode::TableGet, dst, table, key));
    }

    fn table_len(&mut self, dst: Reg, table: Reg) {
        self.buffer.push(Instruction::encode_r2(Opcode::TableLen, dst, table));
    }


    fn def(&mut self, obj: Reg, key: Reg, value: Reg) {
        self.buffer.push(Instruction::encode_r3(Opcode::Def, obj, key, value));
    }

    fn set(&mut self, obj: Reg, key: Reg, value: Reg) {
        self.buffer.push(Instruction::encode_r3(Opcode::Set, obj, key, value));
    }

    fn get(&mut self, dst: Reg, obj: Reg, key: Reg) {
        self.buffer.push(Instruction::encode_r3(Opcode::Get, dst, obj, key));
    }

    fn len(&mut self, dst: Reg, obj: Reg) {
        self.buffer.push(Instruction::encode_r2(Opcode::Len, dst, obj));
    }


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

    fn inc(&mut self, dst: Reg) {
        self.buffer.push(Instruction::encode_r1(Opcode::Inc, dst));
    }

    fn dec(&mut self, dst: Reg) {
        self.buffer.push(Instruction::encode_r1(Opcode::Dec, dst));
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

    fn _block_begin(&self, index: usize) -> u16 {
        assert!(index < self.block_stack.len());
        let block = self.block_stack[self.block_stack.len() - 1 - index];
        self.blocks[block].0
    }

    const JUMP_BLOCK_END_BIT: usize = 1 << 15;

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

    env: Value,

    first_free: Option<usize>,
    gc_timer:   u32,
}

impl Vm {
    fn new() -> Self {
        let mut vm = Vm {
            func_protos: vec![],

            pc:     usize::MAX,
            frames: vec![StackFrame::ROOT],
            stack:  vec![],
            heap:   vec![],

            env: Value::Nil,

            first_free: None,
            gc_timer:   0,
        };

        vm.env = vm.table_new();

        vm
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

                GcObjectData::Table (table) => {
                    for (k, v) in &table.values {
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

    fn string_value(&self, object: usize) -> &str {
        if let GcObjectData::String { value } = &self.heap[object].data {
            value
        }
        else { unreachable!() }
    }


    fn raw_eq(&self, v1: Value, v2: Value) -> bool {
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

            (Table { index: i1 }, Table { index: i2 }) =>
                i1 == i2,

            _ => false,
        }
    }

    fn generic_eq(&mut self, v1: Value, v2: Value) -> bool {
        // @todo-feature: meta tables & userdata.
        self.raw_eq(v1, v2)
    }

    fn generic_le(&mut self, v1: Value, v2: Value) -> bool {
        use Value::*;
        match (v1, v2) {
            (Number { value: v1 }, Number { value: v2 }) =>
                v1 <= v2,

            _ => unimplemented!(),
        }
    }

    fn generic_lt(&mut self, v1: Value, v2: Value) -> bool {
        use Value::*;
        match (v1, v2) {
            (Number { value: v1 }, Number { value: v2 }) =>
                v1 < v2,

            _ => unimplemented!(),
        }
    }

    fn generic_ge(&mut self, v1: Value, v2: Value) -> bool {
        use Value::*;
        match (v1, v2) {
            (Number { value: v1 }, Number { value: v2 }) =>
                v1 >= v2,

            _ => unimplemented!(),
        }
    }

    fn generic_gt(&mut self, v1: Value, v2: Value) -> bool {
        use Value::*;
        match (v1, v2) {
            (Number { value: v1 }, Number { value: v2 }) =>
                v1 > v2,

            _ => unimplemented!(),
        }
    }

    fn generic_add(&mut self, v1: Value, v2: Value) -> Value {
        use Value::*;
        match (v1, v2) {
            (Number { value: v1 }, Number { value: v2 }) =>
                Number { value: v1 + v2 },

            _ => unimplemented!(),
        }
    }

    fn generic_sub(&mut self, v1: Value, v2: Value) -> Value {
        use Value::*;
        match (v1, v2) {
            (Number { value: v1 }, Number { value: v2 }) =>
                Number { value: v1 - v2 },

            _ => unimplemented!(),
        }
    }

    fn generic_mul(&mut self, v1: Value, v2: Value) -> Value {
        use Value::*;
        match (v1, v2) {
            (Number { value: v1 }, Number { value: v2 }) =>
                Number { value: v1 * v2 },

            _ => unimplemented!(),
        }
    }

    fn generic_div(&mut self, v1: Value, v2: Value) -> Value {
        use Value::*;
        match (v1, v2) {
            (Number { value: v1 }, Number { value: v2 }) =>
                Number { value: v1 / v2 },

            _ => unimplemented!(),
        }
    }

    fn generic_print(&self, value: Value) {
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


    fn string_new(&mut self, value: &str) -> Value {
        // @todo-cleanup: alloc utils.
        let index = self.heap_alloc();
        self.heap[index].data = GcObjectData::String { value: value.into() };
        Value::String { index }
    }


    fn list_new(&mut self) -> Value {
        // @todo-cleanup: alloc utils.
        let index = self.heap_alloc();
        self.heap[index].data = GcObjectData::List { values: vec![] };
        Value::List { index }
    }

    fn list_append(&mut self, list: Value, value: Value) {
        // @todo-robust: error.
        let Value::List { index: list_index } = list else { unimplemented!() };

        let object = &mut self.heap[list_index];
        let GcObjectData::List { values } = &mut object.data else { unreachable!() };

        values.push(value);
    }

    fn list_def(&mut self, list: Value, index: Value, value: Value) {
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

    fn list_set(&mut self, list: Value, index: Value, value: Value) {
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

    fn list_get(&mut self, list: Value, index: Value) -> Value {
        // @todo-robust: error.
        let Value::List { index: list_index } = list else { unimplemented!() };

        // @todo-cleanup: value utils.
        let object = &mut self.heap[list_index];
        let GcObjectData::List { values } = &mut object.data else { unreachable!() };

        // @todo-robust: error.
        let Value::Number { value: index } = index else { unimplemented!() };

        // @todo-robust: error.
        let value = values[index as usize];

        value
    }

    fn list_len(&mut self, list: Value) -> Value {
        // @todo-robust: error.
        let Value::List { index: list_index } = list else { unimplemented!() };

        // @todo-cleanup: value utils.
        let object = &mut self.heap[list_index];
        let GcObjectData::List { values } = &mut object.data else { unreachable!() };

        (values.len() as f64).into()
    }


    fn table_new(&mut self) -> Value {
        // @todo-cleanup: alloc utils.
        let index = self.heap_alloc();
        self.heap[index].data = GcObjectData::Table(TableData { values: vec![] });
        Value::Table { index }
    }

    #[inline]
    unsafe fn to_table_data<'vm, 'tbl>(&'vm mut self, table: Value) -> &'tbl mut TableData {
        // @todo-robust: error.
        let Value::Table { index: table_index } = table else { unimplemented!() };

        // @todo-cleanup: value utils.
        let object = &mut self.heap[table_index];
        let GcObjectData::Table(table_data) = &mut object.data else { unreachable!() };

        // @todo-critical-safety: memory allocation rework (stable allocations).
        //  and figure out how to ensure exclusive access.
        &mut *(table_data as *mut TableData)
    }

    fn table_def(&mut self, table: Value, key: Value, value: Value) {
        unsafe { self.to_table_data(table) }.insert(key, value, self)
    }

    fn table_set(&mut self, table: Value, key: Value, value: Value) {
        // @todo-robust: error.
        *unsafe { self.to_table_data(table) }.index(key, self).unwrap() = value;
    }

    fn table_get(&mut self, table: Value, key: Value) -> Value {
        // @todo-robust: error.
        *unsafe { self.to_table_data(table) }.index(key, self).unwrap()
    }

    fn table_len(&mut self, table: Value) -> Value {
        let len = unsafe { self.to_table_data(table) }.len();
        (len as f64).into()
    }


    fn generic_def(&mut self, obj: Value, key: Value, value: Value) {
        // @todo-speed: avoid double type check.
        // @todo-cleanup: value utils.
        if let Value::List { index: _ } = obj {
            self.list_def(obj, key, value);
        }
        // @todo-cleanup: value utils.
        else if let Value::Table { index: _ } = obj {
            self.table_def(obj, key, value);
        }
        else {
            unimplemented!()
        }
    }

    fn generic_set(&mut self, obj: Value, key: Value, value: Value) {
        // @todo-speed: avoid double type check.
        // @todo-cleanup: value utils.
        if let Value::List { index: _ } = obj {
            self.list_set(obj, key, value);
        }
        // @todo-cleanup: value utils.
        else if let Value::Table { index: _ } = obj {
            self.table_set(obj, key, value);
        }
        else {
            unimplemented!()
        }
    }

    fn generic_get(&mut self, obj: Value, key: Value) -> Value {
        // @todo-speed: avoid double type check.
        // @todo-cleanup: value utils.
        if let Value::List { index: _ } = obj {
            self.list_get(obj, key)
        }
        // @todo-cleanup: value utils.
        else if let Value::Table { index: _ } = obj {
            self.table_get(obj, key)
        }
        else {
            unimplemented!()
        }
    }

    fn generic_len(&mut self, obj: Value) -> Value {
        // @todo-speed: avoid double type check.
        // @todo-cleanup: value utils.
        if let Value::List { index: _ } = obj {
            self.list_len(obj)
        }
        // @todo-cleanup: value utils.
        else if let Value::Table { index: _ } = obj {
            self.table_len(obj)
        }
        else {
            unimplemented!()
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
    fn reg2(&mut self, regs: (Reg, Reg)) -> (Value, Value) {
        (*self.reg(regs.0), *self.reg(regs.1))
    }

    #[inline(always)]
    fn reg2_dest(&mut self, regs: (Reg, Reg)) -> (Reg, Value) {
        (regs.0, *self.reg(regs.1))
    }

    #[inline(always)]
    fn reg3(&mut self, regs: (Reg, Reg, Reg)) -> (Value, Value, Value) {
        (*self.reg(regs.0), *self.reg(regs.1), *self.reg(regs.2))
    }

    #[inline(always)]
    fn reg3_dst(&mut self, regs: (Reg, Reg, Reg)) -> (Reg, Value, Value) {
        (regs.0, *self.reg(regs.1), *self.reg(regs.2))
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

    #[inline(always)]
    fn load_const(&mut self, index: usize) -> Value {
        // @todo-speed: obviously don't do this.
        let frame = self.frames.last().unwrap();
        let proto = &self.func_protos[frame.func_proto as usize];
        proto.constants[index]
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


                Opcode::LoadNil => {
                    let dst = instr.r1();
                    // @todo-speed: remove checks.
                    *self.reg(dst) = Value::Nil;
                }

                Opcode::LoadBool => {
                    let (dst, value) = instr.r1b();
                    // @todo-speed: remove checks.
                    *self.reg(dst) = value.into();
                }

                Opcode::LoadInt => {
                    let (dst, value) = instr.r1u16();
                    let value = value as u16 as i16 as f64;
                    // @todo-speed: remove checks.
                    *self.reg(dst) = value.into();
                }

                Opcode::LoadConst => {
                    let (dst, index) = instr.r1u16();
                    // @todo-speed: remove checks.
                    *self.reg(dst) = self.load_const(index as usize);
                }

                Opcode::LoadEnv => {
                    let dst = instr.r1();
                    // @todo-speed: remove checks.
                    *self.reg(dst) = self.env;
                }


                Opcode::ListNew => {
                    let dst = instr.r1();
                    // @todo-speed: remove checks.
                    *self.reg(dst) = self.list_new();
                }

                Opcode::ListAppend => {
                    // @todo-speed: remove checks.
                    let (list, value) = self.reg2(instr.r2());
                    self.list_append(list, value);
                }

                Opcode::ListDef => {
                    // @todo-speed: remove checks.
                    let (list, index, value) = self.reg3(instr.r3());
                    self.list_def(list, index, value);
                }

                Opcode::ListSet => {
                    // @todo-speed: remove checks.
                    let (list, index, value) = self.reg3(instr.r3());
                    self.list_set(list, index, value);
                }

                Opcode::ListGet => {
                    // @todo-speed: remove checks.
                    let (dst, list, index) = self.reg3_dst(instr.r3());
                    *self.reg(dst) = self.list_get(list, index);
                }

                Opcode::ListLen => {
                    // @todo-speed: remove checks.
                    let (dst, list) = self.reg2_dest(instr.r2());
                    *self.reg(dst) = self.list_len(list);
                }


                Opcode::TableNew => {
                    let dst = instr.r1();
                    // @todo-speed: remove checks.
                    *self.reg(dst) = self.table_new();
                }

                Opcode::TableDef => {
                    // @todo-speed: remove checks.
                    let (table, key, value) = self.reg3(instr.r3());
                    self.table_def(table, key, value);
                }

                Opcode::TableSet => {
                    // @todo-speed: remove checks.
                    let (table, key, value) = self.reg3(instr.r3());
                    self.table_set(table, key, value);
                }

                Opcode::TableGet => {
                    // @todo-speed: remove checks.
                    let (dst, table, key) = self.reg3_dst(instr.r3());
                    *self.reg(dst) = self.table_get(table, key);
                }

                Opcode::TableLen => {
                    // @todo-speed: remove checks.
                    let (dst, table) = self.reg2_dest(instr.r2());
                    *self.reg(dst) = self.table_len(table);
                }


                Opcode::Def => {
                    // @todo-speed: remove checks.
                    let (obj, key, value) = self.reg3(instr.r3());
                    self.generic_def(obj, key, value);
                }

                Opcode::Set => {
                    // @todo-speed: remove checks.
                    let (obj, key, value) = self.reg3(instr.r3());
                    self.generic_set(obj, key, value);
                }

                Opcode::Get => {
                    // @todo-speed: remove checks.
                    let (dst, obj, key) = self.reg3_dst(instr.r3());
                    *self.reg(dst) = self.generic_get(obj, key);
                }

                Opcode::Len => {
                    // @todo-speed: remove checks.
                    let (dst, obj) = self.reg2_dest(instr.r2());
                    *self.reg(dst) = self.generic_len(obj);
                }


                Opcode::Add => {
                    // @todo-speed: remove checks.
                    let (dst, src1, src2) = self.reg3_dst(instr.r3());
                    *self.reg(dst) = self.generic_add(src1, src2);
                }

                Opcode::Sub => {
                    // @todo-speed: remove checks.
                    let (dst, src1, src2) = self.reg3_dst(instr.r3());
                    *self.reg(dst) = self.generic_sub(src1, src2);
                }

                Opcode::Mul => {
                    // @todo-speed: remove checks.
                    let (dst, src1, src2) = self.reg3_dst(instr.r3());
                    *self.reg(dst) = self.generic_mul(src1, src2);
                }

                Opcode::Div => {
                    // @todo-speed: remove checks.
                    let (dst, src1, src2) = self.reg3_dst(instr.r3());
                    *self.reg(dst) = self.generic_div(src1, src2);
                }

                Opcode::Inc => {
                    let dst = instr.r1();
                    let Value::Number { value } = self.reg(dst) else { unimplemented!() };
                    *value += 1.0;
                }

                Opcode::Dec => {
                    let dst = instr.r1();
                    let Value::Number { value } = self.reg(dst) else { unimplemented!() };
                    *value -= 1.0;
                }


                Opcode::CmpEq => {
                    // @todo-speed: remove checks.
                    let (dst, src1, src2) = self.reg3_dst(instr.r3());
                    *self.reg(dst) = self.generic_eq(src1, src2).into();
                }

                Opcode::CmpLe => {
                    // @todo-speed: remove checks.
                    let (dst, src1, src2) = self.reg3_dst(instr.r3());
                    *self.reg(dst) = self.generic_le(src1, src2).into();
                }

                Opcode::CmpLt => {
                    // @todo-speed: remove checks.
                    let (dst, src1, src2) = self.reg3_dst(instr.r3());
                    *self.reg(dst) = self.generic_lt(src1, src2).into();
                }

                Opcode::CmpGe => {
                    // @todo-speed: remove checks.
                    let (dst, src1, src2) = self.reg3_dst(instr.r3());
                    *self.reg(dst) = self.generic_ge(src1, src2).into();
                }

                Opcode::CmpGt => {
                    // @todo-speed: remove checks.
                    let (dst, src1, src2) = self.reg3_dst(instr.r3());
                    *self.reg(dst) = self.generic_gt(src1, src2).into();
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
                    // @todo-speed: remove checks.
                    let (src1, src2) = self.reg2(instr.r2());
                    let target = self.next_instr().extra();

                    if self.generic_eq(src1, src2) {
                        self.pc = target as usize;
                    }
                }

                Opcode::JumpLe => {
                    // @todo-speed: remove checks.
                    let (src1, src2) = self.reg2(instr.r2());
                    let target = self.next_instr().extra();

                    if self.generic_le(src1, src2) {
                        self.pc = target as usize;
                    }
                }

                Opcode::JumpLt => {
                    // @todo-speed: remove checks.
                    let (src1, src2) = self.reg2(instr.r2());
                    let target = self.next_instr().extra();

                    if self.generic_lt(src1, src2) {
                        self.pc = target as usize;
                    }
                }

                Opcode::JumpNEq => {
                    // @todo-speed: remove checks.
                    let (src1, src2) = self.reg2(instr.r2());
                    let target = self.next_instr().extra();

                    if !self.generic_eq(src1, src2) {
                        self.pc = target as usize;
                    }
                }

                Opcode::JumpNLe => {
                    // @todo-speed: remove checks.
                    let (src1, src2) = self.reg2(instr.r2());
                    let target = self.next_instr().extra();

                    if !self.generic_le(src1, src2) {
                        self.pc = target as usize;
                    }
                }

                Opcode::JumpNLt => {
                    // @todo-speed: remove checks.
                    let (src1, src2) = self.reg2(instr.r2());
                    let target = self.next_instr().extra();

                    if !self.generic_lt(src1, src2) {
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
                    // @todo-decide: allow writing results into args?
                    //  if not, could make also args immutable. might help with repeated calls.
                    //  also depends on how the rust api will work.
                    debug_assert!(dst_base + frame.num_rets <= frame.func);
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
                    self.generic_print(value);
                    println!();
                }


                Opcode::Gc => {
                    self.gc();
                }
            }
        }
    }


    fn push(&mut self, value: Value) {
        self.stack.push(value);
        self.frames.last_mut().unwrap().top += 1;
    }

    fn pop(&mut self) -> Value {
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
        self.push(Value::Func { index });
    }

    fn push_number(&mut self, value: f64) {
        self.push(value.into());
    }

    // @todo-#api: unsafe version that doesn't copy the string.
    //  for stuff like looking up constants in native functions.
    //  needs to be unsafe; can't guarantee the user won't insert it into a table.
    fn push_str(&mut self, value: &str) {
        let v = self.string_new(value);
        self.push(v);
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

        debug_assert!(frame.top >= frame.base + num_args + 1);
        let func = frame.top - num_args - 1;

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

    fn call_perserve_args(&mut self, dst: u32, num_args: u8, num_rets: u8) {
        self.prep_call(dst, num_args as u32, num_rets as u32);
        self.run();
    }

    fn call(&mut self, dst: u32, num_args: u8, num_rets: u8) {
        self.call_perserve_args(dst, num_args, num_rets);
        self.pop_n(num_args as u32 + 1);
    }
}



fn mk_fib() -> FuncProto {
    // fib(n, f) = if n < 2 then n else f(n-2) + f(n-1) end
    FuncProto {
        code: {
            let mut b = ByteCodeBuilder::new();
            b.block(|b| {
                // if
                b.block(|b| {
                    b.load_int(2, 2);
                    b.exit_nlt(0, 2, 0);
                    b.ret(0, 1);
                });
                // else
                b.copy(4, 1);
                b.sub(5, 0, 2);
                b.copy(6, 1);
                b.call(2, 2, 1);

                b.copy(4, 1);
                b.load_int(3, 1);
                b.sub(5, 0, 3);
                b.copy(6, 1);
                b.call(3, 2, 1);

                b.add(2, 2, 3);
                b.ret(2, 1);
            });
            b.build()
        },
        constants: vec![],
        num_params: 2,
        num_regs:   7,
        //is_varargs: false,
    }
}



#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fib() {
        let mut vm = Vm::new();

        vm.func_protos.push(mk_fib());

        fn fib_rs(i: f64) -> f64 {
            if i < 2.0 { i }
            else       { fib_rs(i - 2.0) + fib_rs(i - 1.0) }
        }

        for i in 0..15 {
            vm.push(Value::Nil);
            vm.push_func(0);
            vm.push_number(i as f64);
            vm.push_func(0);
            vm.call(0, 2, 1);
            let Value::Number { value } = vm.pop() else { panic!() };
            assert_eq!(value, fib_rs(i as f64));
        }
    }


    #[test]
    fn list_to_table() {
        let mut vm = Vm::new();

        vm.func_protos.push(FuncProto {
            code: {
                let mut b = ByteCodeBuilder::new();
                b.table_new(1);
                b.len(2, 0);
                b.load_int(3, 0);
                b.block(|b| {
                    b.exit_nlt(3, 2, 0);
                    b.get(4, 0, 3);
                    b.inc(3);
                    b.get(5, 0, 3);
                    b.inc(3);
                    b.def(1, 4, 5);
                    b.repeat_block(0);
                });
                b.ret(1, 1);
                b.build()
            },
            constants: vec![],
            num_params: 1, 
            num_regs: 6,
        });

        vm.push(Value::Nil);
        vm.push_func(0);

        let entries: &[(Value, Value)] = &[
            (false.into(), 0.5.into()),
            (2.0.into(), 4.0.into()),
            (5.0.into(), 10.0.into()),
        ];

        let list = vm.list_new();
        vm.push(list);
        for (k, v) in entries {
            vm.list_append(list, *k);
            vm.list_append(list, *v);
        }

        vm.call(0, 1, 1);

        let table = vm.stack[0];
        for e in entries {
            let (k, v) = *e;
            let tv = vm.table_get(table, k);
            assert!(vm.raw_eq(tv, v));
        }
    }

    #[test]
    fn env() {
        let mut vm = Vm::new();

        let foo = vm.string_new("foo");
        let bar = vm.string_new("bar");

        // `_ENV.foo := "bar"`
        vm.func_protos.push(FuncProto {
            code: {
                let mut b = ByteCodeBuilder::new();
                b.load_env(0);
                b.load_const(1, 0);
                b.load_const(2, 1);
                b.def(0, 1, 2);
                b.ret(0, 0);
                b.build()
            },
            constants: vec![foo, bar],
            num_params: 0, 
            num_regs: 3,
        });

        // `return _ENV.foo`
        vm.func_protos.push(FuncProto {
            code: {
                let mut b = ByteCodeBuilder::new();
                b.load_env(0);
                b.load_const(1, 0);
                b.get(0, 0, 1);
                b.ret(0, 1);
                b.build()
            },
            constants: vec![foo],
            num_params: 0, 
            num_regs: 2,
        });

        vm.push_func(0);
        vm.call(0, 0, 0);

        vm.push(Value::Nil);
        vm.push_func(1);
        vm.call(0, 0, 1);
        assert_eq!(vm.stack.len(), 1);

        let result = vm.stack[0];
        assert!(vm.generic_eq(result, bar));
    }
}


fn main() {
    let mut vm = Vm::new();

    vm.func_protos.push(mk_fib());

    // run(f, n): for i in 0..n do print(f(i)) end
    vm.func_protos.push(FuncProto {
        code: {
            let mut b = ByteCodeBuilder::new();
            b.load_int(2, 0);
            b.block(|b| {
                b.exit_nlt(2, 1, 0);
                b.copy(4, 0);
                b.copy(5, 2);
                b.copy(6, 0);
                b.call(3, 2, 1);
                b.print(3);
                b.load_int(3, 1);
                b.add(2, 2, 3);
                b.repeat_block(0);
            });
            b.ret(0, 0);
            b.build()
        },
        constants: vec![],
        num_params: 2,
        num_regs:   7,
        //is_varargs: false,
    });

    let t0 = std::time::Instant::now();
    vm.push_func(1);
    vm.push_func(0);
    vm.push_number(25.0);
    vm.call(0, 2, 0);
    println!("{:?}", t0.elapsed());
}

