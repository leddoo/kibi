#![allow(dead_code)]


#[derive(Clone, Copy, Debug)]
enum Value {
    Nil,
    Bool   { value: bool   },
    Number { value: f64    },
    String { index: usize  },
    List   { index: usize  },
    Table  { index: usize  },
    // Function
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
}



#[derive(Clone, Copy, PartialEq, Debug)]
#[repr(u32)]
enum Opcode {
    Invalid = 0,
    Halt,
    Nop,

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

    Print,

    Gc,
}


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
    fn _bool(self) -> bool {
        unsafe { core::mem::transmute(((self.0 >> 16) & 1) as u8) }
    }

    #[inline(always)]
    fn _u16(self) -> u32 {
        (self.0 >> 16) & 0xffff
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
        (self._r1(), self._bool())
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
}



struct ByteCodeBuilder {
    buffer: Vec<Instruction>,
}

impl ByteCodeBuilder {
    fn new() -> Self {
        ByteCodeBuilder {
            buffer: vec![],
        }
    }

    fn halt(&mut self) {
        self.buffer.push(Instruction::encode_op(Opcode::Halt));
    }

    fn nop(&mut self) {
        self.buffer.push(Instruction::encode_op(Opcode::Nop));
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
        self.buffer.push(Instruction(target as u32));
    }

    fn jump_le(&mut self, src1: Reg, src2: Reg, target: u16) {
        self.buffer.push(Instruction::encode_r2(Opcode::JumpLe, src1, src2));
        self.buffer.push(Instruction(target as u32));
    }

    fn jump_lt(&mut self, src1: Reg, src2: Reg, target: u16) {
        self.buffer.push(Instruction::encode_r2(Opcode::JumpLt, src1, src2));
        self.buffer.push(Instruction(target as u32));
    }

    fn jump_neq(&mut self, src1: Reg, src2: Reg, target: u16) {
        self.buffer.push(Instruction::encode_r2(Opcode::JumpNEq, src1, src2));
        self.buffer.push(Instruction(target as u32));
    }

    fn jump_nle(&mut self, src1: Reg, src2: Reg, target: u16) {
        self.buffer.push(Instruction::encode_r2(Opcode::JumpNLe, src1, src2));
        self.buffer.push(Instruction(target as u32));
    }

    fn jump_nlt(&mut self, src1: Reg, src2: Reg, target: u16) {
        self.buffer.push(Instruction::encode_r2(Opcode::JumpNLt, src1, src2));
        self.buffer.push(Instruction(target as u32));
    }

    fn print(&mut self, reg: Reg) {
        self.buffer.push(Instruction::encode_r1(Opcode::Print, reg));
    }

    fn gc(&mut self) {
        self.buffer.push(Instruction::encode_op(Opcode::Gc));
    }

    // TODO: blocks.

    fn build(self) -> Vec<Instruction> {
        self.buffer
    }
}



#[derive(Debug)]
struct Vm {
    code: Vec<Instruction>,
    pc:   usize,

    stack: Vec<Value>,
    heap:  Vec<GcObject>,

    first_free: Option<usize>,
    gc_timer:   u32,
}

impl Vm {
    fn new(code: Vec<Instruction>, stack_size: usize) -> Self {
        Vm {
            code,
            pc: 0,
            stack: vec![Value::Nil; stack_size],
            heap:  vec![],

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
        }
    }

    #[inline(always)]
    fn next_instr(&mut self) -> Instruction {
        debug_assert!(self.pc < self.code.len());
        let result = unsafe { *self.code.get_unchecked(self.pc) };
        self.pc += 1;
        result
    }

    #[inline(never)]
    fn run(&mut self) {
        loop {
            //println!("{} {:?} {:?}", self.pc, self.code[self.pc], self);

            let instr = self.next_instr();

            let op = unsafe { instr.opcode() };
            match op {
                Opcode::Invalid => unreachable!(),

                Opcode::Nop => (),

                Opcode::Halt => {
                    self.pc -= 1;
                    return;
                },


                Opcode::Copy => {
                    let (dst, src) = instr.r2();
                    // @todo-speed: remove checks.
                    self.stack[dst as usize] = self.stack[src as usize];
                }


                Opcode::SetNil => {
                    let dst = instr.r1();
                    // @todo-speed: remove checks.
                    self.stack[dst as usize] = Value::Nil;
                }

                Opcode::SetBool => {
                    let (dst, value) = instr.r1b();
                    // @todo-speed: remove checks.
                    self.stack[dst as usize] = Value::Bool { value };
                }

                Opcode::SetInt => {
                    let (dst, value) = instr.r1u16();
                    let value = value as u16 as i16 as f64;
                    // @todo-speed: remove checks.
                    self.stack[dst as usize] = Value::Number { value };
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
                    self.stack[dst as usize] = Value::List { index };
                }

                Opcode::ListAppend => {
                    let (list, value) = instr.r2();

                    // @todo-speed: remove checks.
                    let list  = self.stack[list  as usize];
                    let value = self.stack[value as usize];

                    // @todo-robust: error.
                    let Value::List { index: list_index } = list else { unimplemented!() };

                    let object = &mut self.heap[list_index];
                    let GcObjectData::List { values } = &mut object.data else { unreachable!() };

                    values.push(value);
                }

                Opcode::ListDef => {
                    let (list, index, value) = instr.r3();

                    // @todo-speed: remove checks.
                    let list  = self.stack[list  as usize];
                    let index = self.stack[index as usize];
                    let value = self.stack[value as usize];

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
                    let list  = self.stack[list  as usize];
                    let index = self.stack[index as usize];
                    let value = self.stack[value as usize];

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
                    let list  = self.stack[list  as usize];
                    let index = self.stack[index as usize];

                    // @todo-robust: error.
                    let Value::List { index: list_index } = list else { unimplemented!() };

                    // @todo-cleanup: value utils.
                    let object = &mut self.heap[list_index];
                    let GcObjectData::List { values } = &mut object.data else { unreachable!() };

                    // @todo-robust: error.
                    let Value::Number { value: index } = index else { unimplemented!() };

                    // @todo-robust: error.
                    let value = values[index as usize];

                    self.stack[dst as usize] = value;
                }

                Opcode::ListLen => {
                    let (dst, list) = instr.r2();

                    // @todo-speed: remove checks.
                    let list = self.stack[list  as usize];

                    // @todo-robust: error.
                    let Value::List { index: list_index } = list else { unimplemented!() };

                    // @todo-cleanup: value utils.
                    let object = &mut self.heap[list_index];
                    let GcObjectData::List { values } = &mut object.data else { unreachable!() };

                    let len = Value::Number { value: values.len() as f64 };
                    self.stack[dst as usize] = len;
                }


                Opcode::Add => {
                    let (dst, src1, src2) = instr.r3();
                    // @todo-speed: remove checks.
                    let src1 = self.stack[src1 as usize];
                    let src2 = self.stack[src2 as usize];
                    let result = self.value_add(src1, src2);
                    self.stack[dst as usize] = result;
                }

                Opcode::Sub => {
                    let (dst, src1, src2) = instr.r3();
                    // @todo-speed: remove checks.
                    let src1 = self.stack[src1 as usize];
                    let src2 = self.stack[src2 as usize];
                    let result = self.value_sub(src1, src2);
                    self.stack[dst as usize] = result;
                }

                Opcode::Mul => {
                    let (dst, src1, src2) = instr.r3();
                    // @todo-speed: remove checks.
                    let src1 = self.stack[src1 as usize];
                    let src2 = self.stack[src2 as usize];
                    let result = self.value_mul(src1, src2);
                    self.stack[dst as usize] = result;
                }

                Opcode::Div => {
                    let (dst, src1, src2) = instr.r3();
                    // @todo-speed: remove checks.
                    let src1 = self.stack[src1 as usize];
                    let src2 = self.stack[src2 as usize];
                    let result = self.value_div(src1, src2);
                    self.stack[dst as usize] = result;
                }


                Opcode::CmpEq => {
                    let (dst, src1, src2) = instr.r3();
                    // @todo-speed: remove checks.
                    let src1 = self.stack[src1 as usize];
                    let src2 = self.stack[src2 as usize];
                    let result = self.value_eq(src1, src2);
                    self.stack[dst as usize] = Value::Bool { value: result };
                }

                Opcode::CmpLe => {
                    let (dst, src1, src2) = instr.r3();
                    // @todo-speed: remove checks.
                    let src1 = self.stack[src1 as usize];
                    let src2 = self.stack[src2 as usize];
                    let result = self.value_le(src1, src2);
                    self.stack[dst as usize] = Value::Bool { value: result };
                }

                Opcode::CmpLt => {
                    let (dst, src1, src2) = instr.r3();
                    // @todo-speed: remove checks.
                    let src1 = self.stack[src1 as usize];
                    let src2 = self.stack[src2 as usize];
                    let result = self.value_lt(src1, src2);
                    self.stack[dst as usize] = Value::Bool { value: result };
                }

                Opcode::CmpGe => {
                    let (dst, src1, src2) = instr.r3();
                    // @todo-speed: remove checks.
                    let src1 = self.stack[src1 as usize];
                    let src2 = self.stack[src2 as usize];
                    let result = self.value_ge(src1, src2);
                    self.stack[dst as usize] = Value::Bool { value: result };
                }

                Opcode::CmpGt => {
                    let (dst, src1, src2) = instr.r3();
                    // @todo-speed: remove checks.
                    let src1 = self.stack[src1 as usize];
                    let src2 = self.stack[src2 as usize];
                    let result = self.value_gt(src1, src2);
                    self.stack[dst as usize] = Value::Bool { value: result };
                }


                Opcode::Jump => {
                    let target = instr.u16();
                    self.pc = target as usize;
                }

                Opcode::JumpTrue => {
                    let (src, target) = instr.r1u16();

                    // @todo-speed: remove checks.
                    let condition = self.stack[src as usize];

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
                    let condition = self.stack[src as usize];

                    // @todo-robust: error.
                    // @todo-cleanup: value utils.
                    let Value::Bool { value } = condition else { unimplemented!() };

                    if !value {
                        self.pc = target as usize;
                    }
                }

                Opcode::JumpEq => {
                    let (src1, src2) = instr.r2();
                    let target = self.next_instr().0;

                    // @todo-speed: remove checks.
                    let src1 = self.stack[src1 as usize];
                    let src2 = self.stack[src2 as usize];
                    if self.value_eq(src1, src2) {
                        self.pc = target as usize;
                    }
                }

                Opcode::JumpLe => {
                    let (src1, src2) = instr.r2();
                    let target = self.next_instr().0;

                    // @todo-speed: remove checks.
                    let src1 = self.stack[src1 as usize];
                    let src2 = self.stack[src2 as usize];
                    if self.value_le(src1, src2) {
                        self.pc = target as usize;
                    }
                }

                Opcode::JumpLt => {
                    let (src1, src2) = instr.r2();
                    let target = self.next_instr().0;

                    // @todo-speed: remove checks.
                    let src1 = self.stack[src1 as usize];
                    let src2 = self.stack[src2 as usize];
                    if self.value_lt(src1, src2) {
                        self.pc = target as usize;
                    }
                }

                Opcode::JumpNEq => {
                    let (src1, src2) = instr.r2();
                    let target = self.next_instr().0;

                    // @todo-speed: remove checks.
                    let src1 = self.stack[src1 as usize];
                    let src2 = self.stack[src2 as usize];
                    if !self.value_eq(src1, src2) {
                        self.pc = target as usize;
                    }
                }

                Opcode::JumpNLe => {
                    let (src1, src2) = instr.r2();
                    let target = self.next_instr().0;

                    // @todo-speed: remove checks.
                    let src1 = self.stack[src1 as usize];
                    let src2 = self.stack[src2 as usize];
                    if !self.value_le(src1, src2) {
                        self.pc = target as usize;
                    }
                }

                Opcode::JumpNLt => {
                    let (src1, src2) = instr.r2();
                    let target = self.next_instr().0;

                    // @todo-speed: remove checks.
                    let src1 = self.stack[src1 as usize];
                    let src2 = self.stack[src2 as usize];
                    if !self.value_lt(src1, src2) {
                        self.pc = target as usize;
                    }
                }


                Opcode::Print => {
                    let reg = instr.r1();
                    // @todo-speed: remove checks.
                    let value = self.stack[reg as usize];
                    self.value_print(value);
                    println!();
                }


                Opcode::Gc => {
                    self.gc();
                }
            }
        }
    }
}


fn main() {
    let mut b = ByteCodeBuilder::new();
    b.list_new(0);
    b.set_nil(2); //Opcode::SetString   { dst: 2, value: "hi" },
    b.list_append(0, 2);
    b.set_int(2, 69);
    b.list_append(0, 2);
    b.set_bool(2, false);
    b.list_append(0, 2);

    b.set_nil(2); //Opcode::SetString   { dst: 2, value: "list contents:" },
    b.print(2); //Opcode::Print       { value: 2 },

    // i = 0
    b.set_int(1, 0);

    // 10, loop:
    b.list_len(2, 0);
    b.jump_nlt(1, 2, 18);
    b.list_get(2, 0, 1);
    b.print(2);
    b.set_int(2, 1);
    b.add(1, 1, 2);
    b.jump(10);

    // 18, done:
    b.halt();


    let mut vm = Vm::new(b.build(), 3);

    let t0 = std::time::Instant::now();
    vm.run();
    println!("{:?}", t0.elapsed());

    /*
        var l := [ "hi", 69, false ]
        var i := 0
        while i < l:len() do
            print l[i]
            i = i + 1
        end

        constants:
            0: "hi"

        registers:
            0: l
            1: i
            2: t0

        instructions:
            list_new        l
            load_const      t0, "hi"(0)
            list_append     l, t0
            load_int        t0, 69
            list_append     l, t0
            load_bool       t0, false
            list_append     l, t0

            load_int        i, 0
            block $loop
                list_len        t0, l
                exit_nlt        i, t0, $loop(0)
                list_get        t0, l, i
                print           t0
                load_int        t0, 1
                add             i, i, temp0
                repeat          $loop(0)
            end
            return

    */
}

