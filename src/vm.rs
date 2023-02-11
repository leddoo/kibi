use crate::bytecode::*;
use crate::value::*;

use core::cell::UnsafeCell;


// @safety-#vm-transparent
#[repr(transparent)]
pub struct Vm {
    pub(crate) inner: VmImpl,
}

impl Vm {
    pub fn new() -> Vm {
        Vm { inner: VmImpl::new() }
    }


    #[inline]
    pub fn add_func(&mut self, name: &str, desc: FuncDesc) {
        let constants = desc.constants.into_iter().map(|c| { match c {
            Constant::Nil              => Value::Nil,
            Constant::Bool   { value } => Value::Bool { value },
            Constant::Number { value } => Value::Number { value },
            Constant::String { value } => self.inner.string_new(value),
        }}).collect();

        self.inner.add_func(name, FuncProto {
            code: desc.code,
            constants,
            num_params: desc.num_params,
            stack_size: desc.stack_size,
        });
    }

    #[inline]
    pub fn call(&mut self) -> VmResult<()> {
        self.inner.call(0, 0, 0)
    }

    #[inline]
    pub fn generic_print(&mut self, reg: u32) {
        let value = *self.inner.reg(reg);
        self.inner.generic_print(value);
    }


    #[inline]
    pub fn instruction_counter(&self) -> u64 {
        let extra = self.inner.counter_target - self.inner.counter;
        self.inner.instruction_counter + extra as u64
    }


    #[inline]
    pub fn interrupt_ptr(&self) -> *mut bool {
        self.inner.interrupt.get()
    }

    #[inline(always)]
    pub fn check_interrupt(&mut self) -> VmResult<()> {
        self.inner.check_interrupt()
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum VmError {
    Counter,
    Interrupt,
    InvalidOperation,
}

pub type VmResult<T> = Result<T, VmError>;


#[derive(Debug)]
struct StackFrame {
    func_proto: usize,
    is_native: bool,

    dest_reg: u32,
    num_rets: u32,

    pc:   u32,
    base: u32,
    top:  u32,
}

impl StackFrame {
    const ROOT: StackFrame = StackFrame {
        func_proto: usize::MAX,
        is_native: true,
        dest_reg: 0, num_rets: 0,
        pc: 0, base: 0, top: 0,
    };
}


#[derive(Debug)]
pub(crate) struct VmImpl {
    pub func_protos: Vec<FuncProto>,

    pc:     usize,
    frames: Vec<StackFrame>,
    stack:  Vec<Value>, // @todo-speed: don't use a vec.
    heap:   Vec<GcObject>,

    env: Value,

    first_free: Option<usize>,
    gc_timer:   u32,

    counter:        u32,
    counter_target: u32,
    instruction_counter: u64,

    interrupt: UnsafeCell<bool>,
}

impl VmImpl {
    pub fn new() -> Self {
        let mut vm = VmImpl {
            func_protos: vec![],

            pc:     usize::MAX,
            frames: vec![StackFrame::ROOT],
            stack:  vec![],
            heap:   vec![],

            env: Value::Nil,

            first_free: None,
            gc_timer:   0,

            counter: 0,
            counter_target: 10_000,
            instruction_counter: 0,

            interrupt: UnsafeCell::new(false),
        };

        vm.env = vm.table_new();

        vm
    }

    pub fn add_func(&mut self, name: &str, proto: FuncProto) {
        let proto_index = self.func_protos.len();
        self.func_protos.push(proto);

        let name = self.string_new(name);
        let env = self.env;
        // @todo-robust: error.
        self.table_def(env, name, Value::Func { proto: proto_index }).unwrap();
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
        if 1==1 {
            if 1==1 { return }
            // @todo-correct: also walk func protos, _ENV, etc.
            unimplemented!();
        }

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


    pub fn raw_eq(&self, v1: Value, v2: Value) -> bool {
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

    pub fn generic_eq(&mut self, v1: Value, v2: Value) -> VmResult<bool> {
        // @todo-feature: meta tables & userdata.
        Ok(self.raw_eq(v1, v2))
    }

    fn generic_le(&mut self, v1: Value, v2: Value) -> VmResult<bool> {
        use Value::*;
        match (v1, v2) {
            (Number { value: v1 }, Number { value: v2 }) =>
                Ok(v1 <= v2),

            _ => Err(VmError::InvalidOperation),
        }
    }

    fn generic_lt(&mut self, v1: Value, v2: Value) -> VmResult<bool> {
        use Value::*;
        match (v1, v2) {
            (Number { value: v1 }, Number { value: v2 }) =>
                Ok(v1 < v2),

            _ => Err(VmError::InvalidOperation),
        }
    }

    fn generic_ge(&mut self, v1: Value, v2: Value) -> VmResult<bool> {
        use Value::*;
        match (v1, v2) {
            (Number { value: v1 }, Number { value: v2 }) =>
                Ok(v1 >= v2),

            _ => Err(VmError::InvalidOperation),
        }
    }

    fn generic_gt(&mut self, v1: Value, v2: Value) -> VmResult<bool> {
        use Value::*;
        match (v1, v2) {
            (Number { value: v1 }, Number { value: v2 }) =>
                Ok(v1 > v2),

            _ => Err(VmError::InvalidOperation),
        }
    }

    fn generic_add(&mut self, v1: Value, v2: Value) -> VmResult<Value> {
        use Value::*;
        match (v1, v2) {
            (Number { value: v1 }, Number { value: v2 }) =>
                Ok(Number { value: v1 + v2 }),

            _ => Err(VmError::InvalidOperation),
        }
    }

    fn generic_sub(&mut self, v1: Value, v2: Value) -> VmResult<Value> {
        use Value::*;
        match (v1, v2) {
            (Number { value: v1 }, Number { value: v2 }) =>
                Ok(Number { value: v1 - v2 }),

            _ => Err(VmError::InvalidOperation),
        }
    }

    fn generic_mul(&mut self, v1: Value, v2: Value) -> VmResult<Value> {
        use Value::*;
        match (v1, v2) {
            (Number { value: v1 }, Number { value: v2 }) =>
                Ok(Number { value: v1 * v2 }),

            _ => Err(VmError::InvalidOperation),
        }
    }

    fn generic_div(&mut self, v1: Value, v2: Value) -> VmResult<Value> {
        use Value::*;
        match (v1, v2) {
            (Number { value: v1 }, Number { value: v2 }) =>
                Ok(Number { value: v1 / v2 }),

            _ => Err(VmError::InvalidOperation),
        }
    }

    pub fn generic_print(&self, value: Value) {
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
            Value::Func   { proto } => print!("<Func {}>", proto),
        }
    }


    pub fn string_new(&mut self, value: &str) -> Value {
        // @todo-cleanup: alloc utils.
        let index = self.heap_alloc();
        self.heap[index].data = GcObjectData::String { value: value.into() };
        Value::String { index }
    }


    pub fn list_new(&mut self) -> Value {
        // @todo-cleanup: alloc utils.
        let index = self.heap_alloc();
        self.heap[index].data = GcObjectData::List { values: vec![] };
        Value::List { index }
    }

    pub fn list_append(&mut self, list: Value, value: Value) -> VmResult<()> {
        let Value::List { index: list_index } = list else { return Err(VmError::InvalidOperation) };

        let object = &mut self.heap[list_index];
        let GcObjectData::List { values } = &mut object.data else { unreachable!() };

        values.push(value);
        Ok(())
    }

    fn list_def(&mut self, list: Value, index: Value, value: Value) -> VmResult<()> {
        let Value::List { index: list_index } = list else { return Err(VmError::InvalidOperation) };

        // @todo-cleanup: value utils.
        let object = &mut self.heap[list_index];
        let GcObjectData::List { values } = &mut object.data else { unreachable!() };

        let Value::Number { value: index } = index else { return Err(VmError::InvalidOperation) };
        let index = index as usize;

        if index >= values.len() {
            values.resize(index + 1, Value::Nil);
        }
        values[index] = value;
        Ok(())
    }

    fn list_set(&mut self, list: Value, index: Value, value: Value) -> VmResult<()> {
        let Value::List { index: list_index } = list else { return Err(VmError::InvalidOperation) };

        // @todo-cleanup: value utils.
        let object = &mut self.heap[list_index];
        let GcObjectData::List { values } = &mut object.data else { unreachable!() };

        let Value::Number { value: index } = index else { return Err(VmError::InvalidOperation) };

        let slot = values.get_mut(index as usize).ok_or(VmError::InvalidOperation)?;
        *slot = value;
        Ok(())
    }

    fn list_get(&mut self, list: Value, index: Value) -> VmResult<Value> {
        let Value::List { index: list_index } = list else { return Err(VmError::InvalidOperation) };

        // @todo-cleanup: value utils.
        let object = &mut self.heap[list_index];
        let GcObjectData::List { values } = &mut object.data else { unreachable!() };

        let Value::Number { value: index } = index else { return Err(VmError::InvalidOperation) };

        let value = *values.get(index as usize).ok_or(VmError::InvalidOperation)?;
        Ok(value)
    }

    fn list_len(&mut self, list: Value) -> VmResult<Value> {
        let Value::List { index: list_index } = list else { return Err(VmError::InvalidOperation) };

        // @todo-cleanup: value utils.
        let object = &mut self.heap[list_index];
        let GcObjectData::List { values } = &mut object.data else { unreachable!() };

        Ok((values.len() as f64).into())
    }


    fn table_new(&mut self) -> Value {
        // @todo-cleanup: alloc utils.
        let index = self.heap_alloc();
        self.heap[index].data = GcObjectData::Table(TableData { values: vec![] });
        Value::Table { index }
    }

    #[inline]
    unsafe fn to_table_data<'vm, 'tbl>(&'vm mut self, table: Value) -> VmResult<&'tbl mut TableData> {
        let Value::Table { index: table_index } = table else { return Err(VmError::InvalidOperation) };

        // @todo-cleanup: value utils.
        let object = &mut self.heap[table_index];
        let GcObjectData::Table(table_data) = &mut object.data else { unreachable!() };

        // @todo-critical-safety: memory allocation rework (stable allocations).
        //  and figure out how to ensure exclusive access.
        Ok(&mut *(table_data as *mut TableData))
    }

    fn table_def(&mut self, table: Value, key: Value, value: Value) -> VmResult<()> {
        let td = unsafe { self.to_table_data(table)? };
        td.insert(key, value, self);
        Ok(())
    }

    fn table_set(&mut self, table: Value, key: Value, value: Value) -> VmResult<()> {
        let td = unsafe { self.to_table_data(table)? };
        let slot = td.index(key, self).ok_or(VmError::InvalidOperation)?;
        *slot = value;
        Ok(())
    }

    pub fn table_get(&mut self, table: Value, key: Value) -> VmResult<Value> {
        let td = unsafe { self.to_table_data(table)? };
        let value = *td.index(key, self).ok_or(VmError::InvalidOperation)?;
        Ok(value)
    }

    fn table_len(&mut self, table: Value) -> VmResult<Value> {
        let td = unsafe { self.to_table_data(table)? };
        let len = td.len();
        Ok((len as f64).into())
    }


    fn generic_def(&mut self, obj: Value, key: Value, value: Value) -> VmResult<()> {
        // @todo-speed: avoid double type check.
        // @todo-cleanup: value utils.
        if let Value::List { index: _ } = obj {
            self.list_def(obj, key, value)
        }
        // @todo-cleanup: value utils.
        else if let Value::Table { index: _ } = obj {
            self.table_def(obj, key, value)
        }
        else {
            Err(VmError::InvalidOperation)
        }
    }

    fn generic_set(&mut self, obj: Value, key: Value, value: Value) -> VmResult<()> {
        // @todo-speed: avoid double type check.
        // @todo-cleanup: value utils.
        if let Value::List { index: _ } = obj {
            self.list_set(obj, key, value)
        }
        // @todo-cleanup: value utils.
        else if let Value::Table { index: _ } = obj {
            self.table_set(obj, key, value)
        }
        else {
            Err(VmError::InvalidOperation)
        }
    }

    fn generic_get(&mut self, obj: Value, key: Value) -> VmResult<Value> {
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
            Err(VmError::InvalidOperation)
        }
    }

    fn generic_len(&mut self, obj: Value) -> VmResult<Value> {
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
            Err(VmError::InvalidOperation)
        }
    }


    #[inline(always)]
    pub fn check_interrupt(&mut self) -> VmResult<()> {
        let interrupt = unsafe { self.interrupt.get().read_volatile() };
        if interrupt {
            unsafe { self.interrupt.get().write_volatile(false) };
            return Err(VmError::Interrupt);
        }
        Ok(())
    }

    fn unwind_until_native(&mut self) {
        loop {
            let frame = self.frames.last().unwrap();
            if frame.is_native {
                // reset vm state.
                self.pc = usize::MAX;
                self.stack.truncate(frame.top as usize);
                break;
            }
            self.frames.pop();
        }
    }


    #[inline(always)]
    pub fn reg(&mut self, reg: u32) -> &mut Value {
        // @todo-speed: obviously don't do this.
        let frame = self.frames.last().unwrap();
        debug_assert!(frame.base + reg < frame.top);
        &mut self.stack[(frame.base + reg) as usize]
    }

    #[inline(always)]
    pub fn reg2(&mut self, regs: (u32, u32)) -> (Value, Value) {
        (*self.reg(regs.0), *self.reg(regs.1))
    }

    #[inline(always)]
    pub fn reg2_dst(&mut self, regs: (u32, u32)) -> (u32, Value) {
        (regs.0, *self.reg(regs.1))
    }

    #[inline(always)]
    pub fn reg3(&mut self, regs: (u32, u32, u32)) -> (Value, Value, Value) {
        (*self.reg(regs.0), *self.reg(regs.1), *self.reg(regs.2))
    }

    #[inline(always)]
    pub fn reg3_dst(&mut self, regs: (u32, u32, u32)) -> (u32, Value, Value) {
        (regs.0, *self.reg(regs.1), *self.reg(regs.2))
    }

    #[inline(always)]
    fn next_instr(&mut self) -> Instruction {
        // @todo-speed: obviously don't do this.
        let frame = self.frames.last().unwrap();
        let proto = &self.func_protos[frame.func_proto];

        let FuncCode::ByteCode(code) = &proto.code else { unreachable!() };

        let result = code[self.pc];
        self.pc += 1;
        result
    }

    #[inline(always)]
    fn next_instr_extra(&mut self) -> Instruction {
        let result = self.next_instr();
        debug_assert_eq!(result.opcode() as u8, opcode::EXTRA);
        result
    }

    #[inline(always)]
    fn load_const(&mut self, index: usize) -> Value {
        // @todo-speed: obviously don't do this.
        let frame = self.frames.last().unwrap();
        let proto = &self.func_protos[frame.func_proto];
        proto.constants[index]
    }

    #[inline(never)]
    fn run(&mut self) -> (VmResult<()>,) { // wrap in tuple to prevent accidental `?` usage.
        if self.frames.len() == 1 {
            // @todo-decide: should this be an error?
            return (Ok(()),);
        }

        loop {
            let mut result = Err(VmError::Counter);

            macro_rules! vm_try {
                ($e: expr) => {
                    match $e {
                        Ok(v) => v,
                        Err(e) => {
                            result = Err(e);
                            break;
                        }
                    }
                };
            }

            macro_rules! vm_jump {
                ($target: expr) => {
                    self.pc = $target as usize;
                };
            }

            if self.counter != 0 { loop {
                self.counter = self.counter.wrapping_sub(1);
                if self.counter == 0 {
                    break;
                }

                let instr = self.next_instr();

                use opcode::*;
                match instr.opcode() as u8 {
                    NOP => (),

                    UNREACHABLE => {
                        result = Err(VmError::InvalidOperation);
                        break;
                    }


                    COPY => {
                        let (dst, src) = instr.c2();
                        // @todo-speed: remove checks.
                        *self.reg(dst) = *self.reg(src);
                    }


                    LOAD_NIL => {
                        let dst = instr.c1();
                        // @todo-speed: remove checks.
                        *self.reg(dst) = Value::Nil;
                    }

                    LOAD_BOOL => {
                        let (dst, value) = instr.c1b();
                        // @todo-speed: remove checks.
                        *self.reg(dst) = value.into();
                    }

                    LOAD_INT => {
                        let (dst, value) = instr.c1u16();
                        let value = value as u16 as i16 as f64;
                        // @todo-speed: remove checks.
                        *self.reg(dst) = value.into();
                    }

                    LOAD_CONST => {
                        let (dst, index) = instr.c1u16();
                        // @todo-speed: remove checks.
                        *self.reg(dst) = self.load_const(index as usize);
                    }

                    LOAD_ENV => {
                        let dst = instr.c1();
                        // @todo-speed: remove checks.
                        *self.reg(dst) = self.env;
                    }


                    LIST_NEW => {
                        let dst = instr.c1();
                        // @todo-speed: remove checks.
                        *self.reg(dst) = self.list_new();
                    }

                    LIST_APPEND => {
                        // @todo-speed: remove checks.
                        let (list, value) = self.reg2(instr.c2());
                        vm_try!(self.list_append(list, value));
                    }


                    TABLE_NEW => {
                        let dst = instr.c1();
                        // @todo-speed: remove checks.
                        *self.reg(dst) = self.table_new();
                    }


                    DEF => {
                        // @todo-speed: remove checks.
                        let (obj, key, value) = self.reg3(instr.c3());
                        vm_try!(self.generic_def(obj, key, value));
                    }

                    SET => {
                        // @todo-speed: remove checks.
                        let (obj, key, value) = self.reg3(instr.c3());
                        vm_try!(self.generic_set(obj, key, value));
                    }

                    GET => {
                        // @todo-speed: remove checks.
                        let (dst, obj, key) = self.reg3_dst(instr.c3());
                        *self.reg(dst) = vm_try!(self.generic_get(obj, key));
                    }

                    LEN => {
                        // @todo-speed: remove checks.
                        let (dst, obj) = self.reg2_dst(instr.c2());
                        *self.reg(dst) = vm_try!(self.generic_len(obj));
                    }


                    ADD => {
                        // @todo-speed: remove checks.
                        let (dst, src1, src2) = self.reg3_dst(instr.c3());
                        *self.reg(dst) = vm_try!(self.generic_add(src1, src2));
                    }

                    SUB => {
                        // @todo-speed: remove checks.
                        let (dst, src1, src2) = self.reg3_dst(instr.c3());
                        *self.reg(dst) = vm_try!(self.generic_sub(src1, src2));
                    }

                    MUL => {
                        // @todo-speed: remove checks.
                        let (dst, src1, src2) = self.reg3_dst(instr.c3());
                        *self.reg(dst) = vm_try!(self.generic_mul(src1, src2));
                    }

                    DIV => {
                        // @todo-speed: remove checks.
                        let (dst, src1, src2) = self.reg3_dst(instr.c3());
                        *self.reg(dst) = vm_try!(self.generic_div(src1, src2));
                    }

                    INC => {
                        let dst = instr.c1();
                        let Value::Number { value } = self.reg(dst) else {
                            result = Err(VmError::InvalidOperation);
                            break;
                        };
                        *value += 1.0;
                    }

                    DEC => {
                        let dst = instr.c1();
                        let Value::Number { value } = self.reg(dst) else {
                            result = Err(VmError::InvalidOperation);
                            break;
                        };
                        *value -= 1.0;
                    }


                    CMP_EQ => {
                        // @todo-speed: remove checks.
                        let (dst, src1, src2) = self.reg3_dst(instr.c3());
                        *self.reg(dst) = vm_try!(self.generic_eq(src1, src2)).into();
                    }

                    CMP_LE => {
                        // @todo-speed: remove checks.
                        let (dst, src1, src2) = self.reg3_dst(instr.c3());
                        *self.reg(dst) = vm_try!(self.generic_le(src1, src2)).into();
                    }

                    CMP_LT => {
                        // @todo-speed: remove checks.
                        let (dst, src1, src2) = self.reg3_dst(instr.c3());
                        *self.reg(dst) = vm_try!(self.generic_lt(src1, src2)).into();
                    }

                    CMP_GE => {
                        // @todo-speed: remove checks.
                        let (dst, src1, src2) = self.reg3_dst(instr.c3());
                        *self.reg(dst) = vm_try!(self.generic_ge(src1, src2)).into();
                    }

                    CMP_GT => {
                        // @todo-speed: remove checks.
                        let (dst, src1, src2) = self.reg3_dst(instr.c3());
                        *self.reg(dst) = vm_try!(self.generic_gt(src1, src2)).into();
                    }


                    JUMP => {
                        let target = instr.u16();
                        vm_jump!(target);
                    }

                    JUMP_TRUE => {
                        let (src, target) = instr.c1u16();

                        // @todo-speed: remove checks.
                        let condition = *self.reg(src);

                        // @todo-cleanup: value utils.
                        let Value::Bool { value } = condition else {
                            result = Err(VmError::InvalidOperation);
                            break;
                        };

                        if value {
                            vm_jump!(target);
                        }
                    }

                    JUMP_FALSE => {
                        let (src, target) = instr.c1u16();

                        // @todo-speed: remove checks.
                        let condition = *self.reg(src);

                        // @todo-cleanup: value utils.
                        let Value::Bool { value } = condition else {
                            result = Err(VmError::InvalidOperation);
                            break;
                        };

                        if !value {
                            vm_jump!(target);
                        }
                    }

                    JUMP_EQ => {
                        // @todo-speed: remove checks.
                        let (src1, src2) = self.reg2(instr.c2());
                        let target = self.next_instr_extra().u16();

                        if vm_try!(self.generic_eq(src1, src2)) {
                            vm_jump!(target);
                        }
                    }

                    JUMP_LE => {
                        // @todo-speed: remove checks.
                        let (src1, src2) = self.reg2(instr.c2());
                        let target = self.next_instr_extra().u16();

                        if vm_try!(self.generic_le(src1, src2)) {
                            vm_jump!(target);
                        }
                    }

                    JUMP_LT => {
                        // @todo-speed: remove checks.
                        let (src1, src2) = self.reg2(instr.c2());
                        let target = self.next_instr_extra().u16();

                        if vm_try!(self.generic_lt(src1, src2)) {
                            vm_jump!(target);
                        }
                    }

                    JUMP_NEQ => {
                        // @todo-speed: remove checks.
                        let (src1, src2) = self.reg2(instr.c2());
                        let target = self.next_instr_extra().u16();

                        if !vm_try!(self.generic_eq(src1, src2)) {
                            vm_jump!(target);
                        }
                    }

                    JUMP_NLE => {
                        // @todo-speed: remove checks.
                        let (src1, src2) = self.reg2(instr.c2());
                        let target = self.next_instr_extra().u16();

                        if !vm_try!(self.generic_le(src1, src2)) {
                            vm_jump!(target);
                        }
                    }

                    JUMP_NLT => {
                        // @todo-speed: remove checks.
                        let (src1, src2) = self.reg2(instr.c2());
                        let target = self.next_instr_extra().u16();

                        if !vm_try!(self.generic_lt(src1, src2)) {
                            vm_jump!(target);
                        }
                    }


                    PACKED_CALL => {
                        let (func, rets, num_rets) = instr.c3();
                        let (args, num_args) = self.next_instr().c2();
                        vm_try!(self.pre_packed_call(func, args, num_args, rets, num_rets));
                    }

                    GATHER_CALL => {
                        let (func, rets, num_rets) = instr.c3();
                        let num_args = self.next_instr();
                        debug_assert_eq!(num_args.opcode() as u8, EXTRA);
                        let num_args = num_args.u16();

                        let args = {
                            // @todo-speed: obviously don't do this.
                            let frame = self.frames.last().unwrap();
                            let proto = &self.func_protos[frame.func_proto];

                            let FuncCode::ByteCode(code) = &proto.code else { unreachable!() };

                            // TEMP: this is safe, as code is (currently) immutable.
                            // and doesn't get collected, as the function is on the stack.
                            let code = unsafe { &*(code as *const Vec<Instruction>) };

                            let result = &code[self.pc .. self.pc + num_args as usize];
                            self.pc += num_args as usize;
                            result
                        };

                        let frame = self.frames.last().unwrap();
                        let abs_func = frame.base + func;
                        let src_base = frame.base as usize;

                        vm_try!(self.pre_call(abs_func, num_args, rets, num_rets, |vm, dst_base| {
                            for (i, arg) in args.iter().enumerate() {
                                debug_assert_eq!(arg.opcode() as u8, EXTRA);

                                let arg = arg.u16() as usize;
                                vm.stack[dst_base + i] = vm.stack[src_base + arg];
                            }
                        }));
                    }

                    RET => {
                        let (rets, actual_rets) = instr.c2();

                        if vm_try!(self.post_call(rets, actual_rets)) {
                            result = Ok(());
                            break;
                        }
                    }

                    // @todo-speed: this inserts a check to reduce dispatch table size.
                    //  may want an unreachable_unchecked() in release.
                    0 | END ..= 255 => unreachable!()
                }
            }}

            match result {
                Ok(v) => {
                    return (Ok(v),);
                }

                Err(VmError::Counter) => {
                    debug_assert_eq!(self.counter, 0);
                    self.instruction_counter += self.counter_target as u64;
                    self.counter = self.counter_target;

                    if self.check_interrupt().is_err() {
                        self.unwind_until_native();
                        return (Err(VmError::Interrupt),);
                    }
                }

                Err(e) => {
                    self.unwind_until_native();
                    return (Err(e),);
                }
            }
        }
    }


    pub fn push(&mut self, value: Value) {
        self.stack.push(value);
        self.frames.last_mut().unwrap().top += 1;
    }

    #[allow(dead_code)] // @temp: used in tests.
    pub fn pop(&mut self) -> Value {
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
    #[allow(dead_code)] // @temp: used in tests.
    pub fn func_new(&mut self, proto: usize) -> Value {
        Value::Func { proto }
    }
    #[allow(dead_code)] // @temp: used in tests.
    pub fn push_func(&mut self, proto: usize) {
        let f = self.func_new(proto);
        self.push(f);
    }

    #[allow(dead_code)] // @temp: used in tests.
    pub fn push_number(&mut self, value: f64) {
        self.push(value.into());
    }

    #[allow(dead_code)] // @temp: used in tests.
    pub fn push_global(&mut self, name: &str) -> VmResult<()> {
        // @todo-safety: keep alive.
        let n = self.string_new(name);
        let env = self.env;
        let v = self.generic_get(env, n)?;
        self.push(v);
        Ok(())
    }

    fn pre_call<CopyArgs: FnOnce(&mut VmImpl, usize)>(&mut self,
        abs_func: u32, num_args: u32,
        dst: u32, num_rets: u32,
        copy_args: CopyArgs) -> VmResult<bool>
    {
        assert!(num_args < 128);
        assert!(num_rets < 128);
        
        let func_value = self.stack[abs_func as usize];

        let Value::Func { proto: func_proto } = func_value else {
            return Err(VmError::InvalidOperation);
        };
        let proto = &self.func_protos[func_proto];

        // check args.
        if num_args != proto.num_params {
            return Err(VmError::InvalidOperation);
        }

        // save vm state.
        let frame = self.frames.last_mut().unwrap();
        frame.pc = self.pc as u32;

        // push frame.
        let base = frame.top;
        let top  = base + proto.stack_size;
        self.frames.push(StackFrame {
            func_proto,
            is_native: proto.code.is_native(),
            dest_reg: dst, num_rets,
            pc: u32::MAX,
            base, top,
        });
        self.pc = 0;
        self.stack.resize(top as usize, Value::Nil);

        // copy args.
        copy_args(self, base as usize);

        // execute (if native)
        let proto = &self.func_protos[func_proto];
        match &proto.code {
            FuncCode::ByteCode(_code) => {
                Ok(true)
            }

            FuncCode::Native(code) => {
                self.pc = usize::MAX;

                // call host function.
                // @safety-#vm-transparent
                // @todo-cleanup: can this be removed somehow?
                let actual_rets = code.0(unsafe { core::mem::transmute_copy(&self) })?;

                let frame = self.frames.last().unwrap();
                assert!(frame.base + actual_rets <= frame.top);

                self.post_call(frame.top - frame.base - actual_rets, actual_rets)?;

                Ok(false)
            }
        }
    }

    fn post_call(&mut self, rets: u32, actual_rets: u32) -> VmResult<bool> {
        let frame = self.frames.last().unwrap();
        // @todo-speed: validate in host api & compiler.
        assert!(frame.base + rets + actual_rets <= frame.top);

        // check num_rets.
        let num_rets = frame.num_rets;
        if actual_rets < frame.num_rets {
            return Err(VmError::InvalidOperation);
        }

        // pop frame.
        let frame = self.frames.pop().unwrap();

        // copy rets.
        let prev_frame = self.frames.last_mut().unwrap();
        debug_assert!(prev_frame.base + frame.dest_reg + num_rets <= prev_frame.top);
        let dst_base = (prev_frame.base + frame.dest_reg) as usize;
        let src_base = (frame.base + rets) as usize;
        for i in 0..num_rets as usize {
            self.stack[dst_base + i] = self.stack[src_base + i];
        }

        // reset vm state.
        self.pc = prev_frame.pc as usize;
        self.stack.truncate(prev_frame.top as usize);

        // @todo-speed: debug only.
        prev_frame.pc = u32::MAX;

        Ok(prev_frame.is_native)
    }

    fn pre_packed_call(&mut self, func: u32, args: u32, num_args: u32, dst: u32, num_rets: u32) -> VmResult<bool> {
        let frame = self.frames.last().unwrap();
        let abs_func = frame.base + func;
        let abs_args = frame.base + args;

        self.pre_call(abs_func, num_args, dst, num_rets, |vm, dst_base| {
            let src_base = abs_args as usize;
            for i in 0..num_args as usize {
                vm.stack[dst_base + i] = vm.stack[src_base + i];
            }
        })
    }

    // @todo-#host_api: what's the function call api?
    fn call_perserve_args(&mut self, rets: u32, num_args: u32, num_rets: u32) -> VmResult<()> {
        let frame = self.frames.last().unwrap();
        let args = frame.top - num_args - frame.base;
        let func = args - 1;
        if self.pre_packed_call(func, args, num_args, rets, num_rets)? {
            self.run().0?;
        }
        Ok(())
    }

    // @todo-#host_api: what's the function call api?
    pub fn call(&mut self, rets: u32, num_args: u32, num_rets: u32) -> VmResult<()> {
        self.call_perserve_args(rets, num_args, num_rets)?;
        self.pop_n(num_args as u32 + 1);
        Ok(())
    }
}



#[cfg(test)]
mod tests {
    use super::*;

    fn mk_fib() -> FuncProto {
        // fib(n, f) = if n < 2 then n else f(n-2) + f(n-1) end
        FuncProto {
            code: FuncCode::ByteCode({
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
                    b.packed_call(4, 5, 2, 2, 1);

                    b.copy(4, 1);
                    b.load_int(3, 1);
                    b.sub(5, 0, 3);
                    b.copy(6, 1);
                    b.packed_call(4, 5, 2, 3, 1);

                    b.add(2, 2, 3);
                    b.ret(2, 1);
                });
                b.build()
            }),
            constants: vec![],
            num_params: 2,
            stack_size: 7,
        }
    }


    #[test]
    fn fib() {
        let mut vm = Vm::new();

        vm.inner.func_protos.push(mk_fib());

        fn fib_rs(i: f64) -> f64 {
            if i < 2.0 { i }
            else       { fib_rs(i - 2.0) + fib_rs(i - 1.0) }
        }

        for i in 0..15 {
            vm.inner.push(Value::Nil);
            vm.inner.push_func(0);
            vm.inner.push_number(i as f64);
            vm.inner.push_func(0);
            vm.inner.call(0, 2, 1).unwrap();
            let Value::Number { value } = vm.inner.pop() else { panic!() };
            assert_eq!(value, fib_rs(i as f64));
        }
    }


    #[test]
    fn list_to_table() {
        let mut vm = Vm::new();

        vm.inner.func_protos.push(FuncProto {
            code: FuncCode::ByteCode({
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
            }),
            constants: vec![],
            num_params: 1,
            stack_size: 6,
        });

        vm.inner.push(Value::Nil);
        vm.inner.push_func(0);

        let entries: &[(Value, Value)] = &[
            (false.into(), 0.5.into()),
            (2.0.into(), 4.0.into()),
            (5.0.into(), 10.0.into()),
        ];

        let list = vm.inner.list_new();
        vm.inner.push(list);
        for (k, v) in entries {
            vm.inner.list_append(list, *k).unwrap();
            vm.inner.list_append(list, *v).unwrap();
        }

        vm.inner.call(0, 1, 1).unwrap();

        let table = *vm.inner.reg(0);
        for e in entries {
            let (k, v) = *e;
            let tv = vm.inner.table_get(table, k).unwrap();
            assert!(vm.inner.raw_eq(tv, v));
        }
    }

    #[test]
    fn env() {
        let mut vm = Vm::new();

        let foo = vm.inner.string_new("foo");
        let bar = vm.inner.string_new("bar");

        // `_ENV.foo := "bar"`
        vm.inner.func_protos.push(FuncProto {
            code: FuncCode::ByteCode({
                let mut b = ByteCodeBuilder::new();
                b.load_env(0);
                b.load_const(1, 0);
                b.load_const(2, 1);
                b.def(0, 1, 2);
                b.ret(0, 0);
                b.build()
            }),
            constants: vec![foo, bar],
            num_params: 0,
            stack_size: 3,
        });

        // `return _ENV.foo`
        vm.inner.func_protos.push(FuncProto {
            code: FuncCode::ByteCode({
                let mut b = ByteCodeBuilder::new();
                b.load_env(0);
                b.load_const(1, 0);
                b.get(0, 0, 1);
                b.ret(0, 1);
                b.build()
            }),
            constants: vec![foo],
            num_params: 0,
            stack_size: 2,
        });

        vm.inner.push_func(0);
        vm.inner.call(0, 0, 0).unwrap();

        vm.inner.push(Value::Nil);
        vm.inner.push_func(1);
        vm.inner.call(0, 0, 1).unwrap();
        assert_eq!(vm.inner.stack.len(), 1);

        let result = vm.inner.stack[0];
        assert!(vm.inner.generic_eq(result, bar).unwrap());
    }

    #[test]
    fn host_func() {
        let mut vm = Vm::new();

        let lua_branch = vm.inner.string_new("lua_branch");
        let host_fib   = vm.inner.string_new("host_fib");
        let host_base  = vm.inner.string_new("host_base");
        let host_rec   = vm.inner.string_new("host_rec");

        // (if n <= 2 { host_base } else { host_rec })(n)
        vm.inner.func_protos.push(FuncProto {
            code: FuncCode::ByteCode({
                let mut b = ByteCodeBuilder::new();
                b.block(|b| {
                    b.block(|b|{
                        b.load_int(1, 2);
                        b.exit_nlt(0, 1, 0);
                        b.load_const(2, 0);
                        b.exit_block(1);
                    });
                    b.load_const(2, 1);
                });
                b.load_env(1);
                b.get(1, 1, 2);
                b.copy(2, 0);
                b.packed_call(1, 2, 1, 0, 1);
                b.ret(0, 1);
                b.build()
            }),
            constants: vec![host_base, host_rec],
            num_params: 1,
            stack_size: 3,
        });

        fn host_fib_fn(vm: &mut Vm) -> VmResult<u32> {
            let n = *vm.inner.reg(0);
            vm.inner.push_global("lua_branch")?;
            vm.inner.push(n);
            vm.inner.call(0, 1, 1)?;
            return Ok(1);
        }
        vm.inner.func_protos.push(FuncProto {
            code: FuncCode::Native(NativeFuncPtrEx(host_fib_fn)),
            constants: vec![],
            num_params: 1,
            stack_size: 1,
        });

        fn host_base_fn(_vm: &mut Vm) -> VmResult<u32> {
            return Ok(1);
        }
        vm.inner.func_protos.push(FuncProto {
            code: FuncCode::Native(NativeFuncPtrEx(host_base_fn)),
            constants: vec![],
            num_params: 1,
            stack_size: 1,
        });

        fn host_rec_fn(vm: &mut Vm) -> VmResult<u32> {
            let n = *vm.inner.reg(0);
            vm.inner.push(Value::Nil);
            vm.inner.push(Value::Nil);
            let Value::Number { value: n } = n else { return Err(VmError::InvalidOperation) };
            vm.inner.push_global("host_fib")?;
            vm.inner.push_number(n - 2.0);
            vm.inner.call(1, 1, 1)?;
            vm.inner.push_global("host_fib")?;
            vm.inner.push_number(n - 1.0);
            vm.inner.call(2, 1, 1)?;
            let b = vm.inner.pop();
            let a = vm.inner.pop();
            let r = vm.inner.generic_add(a, b)?;
            vm.inner.push(r);
            return Ok(1);
        }
        vm.inner.func_protos.push(FuncProto {
            code: FuncCode::Native(NativeFuncPtrEx(host_rec_fn)),
            constants: vec![],
            num_params: 1,
            stack_size: 1,
        });

        let env = vm.inner.env;
        vm.inner.generic_def(env, lua_branch, Value::Func { proto: 0 }).unwrap();
        vm.inner.generic_def(env, host_fib,   Value::Func { proto: 1 }).unwrap();
        vm.inner.generic_def(env, host_base,  Value::Func { proto: 2 }).unwrap();
        vm.inner.generic_def(env, host_rec,   Value::Func { proto: 3 }).unwrap();

        fn fib_rs(i: f64) -> f64 {
            if i < 2.0 { i }
            else       { fib_rs(i - 2.0) + fib_rs(i - 1.0) }
        }

        for i in 0..10 {
            vm.inner.push(Value::Nil);
            vm.inner.push_global("host_fib").unwrap();
            vm.inner.push_number(i as f64);
            vm.inner.call(0, 1, 1).unwrap();
            let Value::Number { value } = vm.inner.pop() else { panic!() };
            assert_eq!(value, fib_rs(i as f64));
        }
    }

    /*
    #[test]
    fn lexical_scoping() {
        let mut vm = Vm::new();

        use core::sync::atomic::{AtomicUsize, Ordering};

        const RESULTS: &[f64] = &[ 42.0, 12.0, 69.0, 70.0, 8.0, 70.0, 71.0, 12.0, 24.0 ];

        static INDEX: AtomicUsize = AtomicUsize::new(0);
        INDEX.store(0, Ordering::Relaxed);

        vm.inner.add_func("yield", FuncProto {
            code: FuncCode::Native(NativeFuncPtrEx(|vm| {
                let i = INDEX.fetch_add(1, Ordering::Relaxed);

                let expected = RESULTS[i];

                let v = *vm.inner.reg(0);
                print!("yield: ");
                vm.inner.generic_print(v);
                println!();

                assert!(vm.inner.raw_eq(v, expected.into()));

                return Ok(0);
            })),
            constants: vec![],
            num_params: 1,
            stack_size: 1,
        });

        let chunk = r#"
            (var foo 42) (yield foo)
            (do
                (set foo 12) (yield foo)
                (var foo 69) (yield foo)
                (do
                    (set foo 70) (yield foo)
                    (var foo  8) (yield foo))
                (yield foo)
                (set foo 71) (yield foo))
            (yield foo)
            (set foo (* foo 2)) (yield foo)
        "#;

        use crate::parser::*;
        use crate::compiler::*;

        let ast = parse_many(chunk).unwrap();
        compile_chunk(&ast, &mut vm).unwrap();
        vm.inner.call(0, 0, 0).unwrap();
        assert_eq!(vm.inner.stack.len(), 0);
    }

    #[test]
    fn control_flow() {
        let mut vm = Vm::new();

        let code = r#"
            (var i 0)
            (var j 0)
            (var k 1)
            (while (< i 100) (do
                (set j (+ j (if (> k 0) 1 2)))
                (set k (- 0 k))
                (set i (+ i 1))))
        "#;

        use crate::parser::*;
        use crate::compiler::*;

        let ast = parse_many(code).unwrap();
        compile_chunk(&ast, &mut vm).unwrap();
        vm.inner.call(0, 0, 0).unwrap();
        assert_eq!(vm.inner.stack.len(), 0);

        let env = vm.inner.env;
        let i = vm.inner.string_new("i");
        let i = vm.inner.generic_get(env, i).unwrap();
        println!("i: {:?}", i);
        let j = vm.inner.string_new("j");
        let j = vm.inner.generic_get(env, j).unwrap();
        println!("j: {:?}", j);

        assert!(vm.inner.raw_eq(i, 100.0.into()));
        assert!(vm.inner.raw_eq(j, 150.0.into()));
    }
    */
}



