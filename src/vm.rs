use std::rc::Rc;
use core::sync::atomic::{AtomicBool, Ordering as MemOrder};

use crate::bytecode::*;
use crate::value::*;


pub trait DebugHook: 'static {
    fn on_instruction_limit(&mut self, vm: &mut Vm) -> VmResult<DebugHookResult>;
}

pub enum DebugHookResult {
    Continue,
    Pause,
}

impl<T> DebugHook for T where T: 'static + FnMut(&mut Vm) -> VmResult<DebugHookResult> {
    #[inline(always)]
    fn on_instruction_limit(&mut self, vm: &mut Vm) -> VmResult<DebugHookResult> { (self)(vm) }
}


// @safety-#vm-transparent
#[repr(transparent)]
pub struct Vm {
    pub(crate) inner: VmImpl,
}

impl Vm {
    pub fn new() -> Vm {
        Vm { inner: VmImpl::new() }
    }


    pub fn add_func(&mut self, name: &str, desc: FuncDesc) {
        let constants = desc.constants.into_iter().map(|c| { match c {
            Constant::Nil              => Value::Nil,
            Constant::Bool   { value } => Value::Bool { value },
            Constant::Number { value } => Value::Number { value },
            Constant::String { value } => VmImpl::string_new(&value),
        }}).collect();

        self.inner.add_func(name, FuncProto {
            krate: None.into(),
            func_idx: 0,
            code: desc.code,
            constants,
            num_params: desc.num_params,
            stack_size: desc.stack_size,
        });
    }

    pub fn load_crate(&mut self, dst: u32, funcs: &[FuncDesc], items: &[crate::bbir::Item]) {
        let krate = CrateId::from_usize(self.inner.krates.len());

        let func_base = self.inner.func_protos.len();
        for (index, desc) in funcs.iter().enumerate() {
            let constants = desc.constants.iter().map(|c| { match c {
                Constant::Nil              => Value::Nil,
                Constant::Bool   { value } => (*value).into(),
                Constant::Number { value } => (*value).into(),
                Constant::String { value } => VmImpl::string_new(value),
            }}).collect();

            self.inner.func_protos.push(FuncProto {
                krate:    krate.some(),
                func_idx: index as u32,
                code: desc.code.clone(),
                constants,
                num_params: desc.num_params,
                stack_size: desc.stack_size,
            });
        }

        let crate_items = items.iter().map(|item| {
            let mut value = Value::Nil;
            let read_only = true;
            let mut uninitialized = true;
            match item.data {
                crate::bbir::ItemData::None => (),

                crate::bbir::ItemData::Func(id) => {
                    value = Value::Func { proto: func_base + id.usize() };
                    uninitialized = false;
                }
            }

            Item { value, read_only, uninitialized }
        }).collect();
        self.inner.krates.push(Crate { items: crate_items });

        *self.inner.reg_mut(dst) = Value::Func { proto: func_base };
    }

    pub fn call(&mut self, dst: u32, func: u32, args: &[u32]) -> VmResult<()> {
        let this = &mut self.inner;

        let run = this.pre_call(dst, func, args.len() as u32, |vm, dst_base| {
            let src_base = vm.frames.last().unwrap().base as usize;
            for (i, arg) in args.iter().copied().enumerate() {
                vm.stack[dst_base + i] = vm.stack[src_base + arg as usize].clone();
            }
        })?;

        if run {
            this.run().0?;
        }

        Ok(())
    }

    #[inline]
    pub fn run(&mut self) -> VmResult<bool> {
        self.inner.run().0
    }


    #[inline]
    pub fn generic_print(&mut self, reg: u32) {
        let value = self.inner.reg(reg);
        self.inner.generic_print(value);
    }


    #[inline(always)]
    pub fn set_instr_limit(&mut self, limit: u32) {
        self.inner.set_instr_limit(limit);
    }

    #[inline(always)]
    pub fn reset_instr_limit(&mut self) {
        self.inner.set_instr_limit(DEFAULT_INSTR_LIMIT);
    }

    #[inline]
    pub fn instruction_counter(&self) -> u64 {
        self.inner.instruction_counter()
    }


    #[inline(always)]
    pub fn interrupt_ptr(&self) -> &AtomicBool {
        &self.inner.interrupt
    }

    #[inline(always)]
    pub fn check_interrupt(&mut self) -> VmResult<()> {
        self.inner.check_interrupt()
    }


    pub fn set_debug_hook<Hook: DebugHook>(&mut self, hook: Hook) {
        self.inner.debug_hook = DebugHookWrapper::Some(Box::new(hook));
    }

    pub fn clear_debug_hook(&mut self) {
        self.inner.debug_hook = DebugHookWrapper::None;
    }

    pub fn can_pause(&self) -> bool {
        self.inner.can_pause()
    }
}

#[derive(Clone, Copy, Debug)]
pub struct DebugFrame {
    pub krate:    OptCrateId,
    pub func_idx: u32,

    pub pc:   u16,
    pub base: u32,
    pub top:  u32,
}

impl DebugFrame {
    fn from_stack_frame(vm: &VmImpl, frame: &StackFrame, pc: u16) -> DebugFrame {
        let proto = &vm.func_protos[frame.func_proto];
        DebugFrame {
            krate: proto.krate,
            func_idx: proto.func_idx,
            pc,
            base: frame.base,
            top:  frame.top,
        }
    }
}

impl Vm {
    pub fn call_stack<F: FnMut(DebugFrame)>(&self, mut f: F) {
        let this = &self.inner;
        for i in 1 .. this.frames.len() - 1 {
            let frame = &this.frames[i];
            f(DebugFrame::from_stack_frame(this, frame, frame.pc as u16));
        }
        if this.frames.len() > 1 {
            let frame = this.frames.last().unwrap();
            f(DebugFrame::from_stack_frame(this, frame, this.pc as u16));
        }
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

    dst_abs: u32,

    pc:   u32,
    base: u32,
    top:  u32,
}

impl StackFrame {
    const ROOT: StackFrame = StackFrame {
        func_proto: usize::MAX,
        is_native: true,
        dst_abs: 0,
        pc: 0, base: 0, top: 0,
    };
}

struct Item {
    value:          Value,
    read_only:      bool,
    uninitialized:  bool,
}

struct Crate {
    items: Vec<Item>,
}


pub(crate) struct VmImpl {
    func_protos: Vec<FuncProto>,
    krates:      Vec<Crate>,

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

    interrupt: AtomicBool,

    debug_hook: DebugHookWrapper,
}

enum DebugHookWrapper {
    None,
    Taken,
    Some(Box<dyn DebugHook>),
}

impl DebugHookWrapper {
    #[inline(always)]
    fn take(&mut self) -> Option<Box<dyn DebugHook>> {
        if let DebugHookWrapper::None = self {
            return None;
        }

        let this = core::mem::replace(self, DebugHookWrapper::Taken);
        match this {
            DebugHookWrapper::None  => unreachable!(),
            DebugHookWrapper::Taken => unreachable!(),
            DebugHookWrapper::Some(hook) => Some(hook)
        }
    }
}


const DEFAULT_INSTR_LIMIT: u32 = 10_000;

impl VmImpl {
    fn new() -> Self {
        let root_stack_size = 16;

        let mut vm = VmImpl {
            func_protos: vec![],
            krates:      vec![],

            pc:     usize::MAX,
            frames: vec![StackFrame::ROOT],
            stack:  vec![Value::Nil; root_stack_size],
            heap:   vec![],

            env: Value::Nil,

            first_free: None,
            gc_timer:   0,

            counter:        DEFAULT_INSTR_LIMIT,
            counter_target: DEFAULT_INSTR_LIMIT,
            instruction_counter: 0,

            interrupt: AtomicBool::new(false),
            debug_hook: DebugHookWrapper::None,
        };

        vm.frames.last_mut().unwrap().top = root_stack_size as u32;

        vm.env = Self::map_new();

        vm
    }

    fn set_instr_limit(&mut self, limit: u32) {
        self.instruction_counter = self.instruction_counter();
        self.counter        = limit;
        self.counter_target = limit;
    }

    #[inline(always)]
    fn instruction_counter(&self) -> u64 {
        self.instruction_counter + (self.counter_target - self.counter) as u64
    }


    #[inline]
    fn can_pause(&self) -> bool {
        self.frames[1..].iter().all(|frame| frame.is_native == false)
    }


    fn add_func(&mut self, name: &str, proto: FuncProto) {
        let proto_index = self.func_protos.len();
        self.func_protos.push(proto);

        let name = Self::string_new(name);
        // @todo-robust: error.
        let Value::Map { values: env } = &mut self.env else { unimplemented!() };
        Self::map_def(Rc::make_mut(env), &name, Value::Func { proto: proto_index }).unwrap();
    }

    // @TEMP
    #[allow(dead_code)]
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

    // @TEMP
    fn heap_free(&mut self, index: usize) {
        println!("free {} ({:?})", index, self.heap[index].data);
        self.heap[index].data = GcObjectData::Free { next: self.first_free };
        self.first_free = Some(index);
    }

    // @TEMP
    fn gc(&mut self) {
        if 1==1 {
            if 1==1 { return }
            // @todo-correct: also walk func protos, _ENV, etc.
            unimplemented!();
        }

        fn mark_value(heap: &mut Vec<GcObject>, value: &Value) {
            match value {
                Value::Tuple { values } |
                Value::List { values } => {
                    for v in values.iter() {
                        mark_value(heap, v);
                    }
                }

                Value::Map { values } => {
                    for (k, v) in values.iter() {
                        mark_value(heap, k);
                        mark_value(heap, v);
                    }
                }

                _ => (),
            }
        }

        // @TEMP
        #[allow(dead_code)]
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


    fn raw_eq(v1: &Value, v2: &Value) -> bool {
        use Value::*;
        match (v1, v2) {
            (Nil, Nil) => true,

            (Bool { value: v1 }, Bool { value: v2 }) =>
                v1 == v2,

            (Number { value: v1 }, Number { value: v2 }) =>
                v1 == v2,

            (String { value: v1 }, String { value: v2 }) =>
                v1 == v2,

            (Unit, Unit) => true,

            (Tuple { values: v1 }, Tuple { values: v2 }) =>
                Self::raw_eq_list(v1, v2),

            (List { values: v1 }, List { values: v2 }) =>
                Self::raw_eq_list(v1, v2),

            (Map { values: v1 }, Map { values: v2 }) =>
                Self::raw_eq_map(v1, v2),

            _ => false,
        }
    }

    fn raw_eq_list(v1: &Rc<Vec<Value>>, v2: &Rc<Vec<Value>>) -> bool {
        if Rc::ptr_eq(v1, v2) {
            return true;
        }

        if v1.len() != v2.len() {
            return false;
        }
        for i in 0..v1.len() {
            if !Self::raw_eq(&v1[i], &v2[i]) {
                return false;
            }
        }
        true
    }

    fn raw_eq_map(v1: &Rc<Vec<(Value, Value)>>, v2: &Rc<Vec<(Value, Value)>>) -> bool {
        if Rc::ptr_eq(v1, v2) {
            return true;
        }

        if v1.len() != v2.len() {
            return false;
        }
        for (key, value) in v1.iter() {
            if let Some(other) = Self::map_index(v2, key) {
                if !Self::raw_eq(value, other) {
                    return false;
                }
            }
            else {
                return false;
            }
        }
        true
    }

    fn generic_eq(&self, v1: &Value, v2: &Value) -> VmResult<bool> {
        Ok(Self::raw_eq(v1, v2))
    }

    fn generic_ne(&self, v1: &Value, v2: &Value) -> VmResult<bool> {
        Ok(!Self::raw_eq(v1, v2))
    }

    fn generic_le(&self, v1: &Value, v2: &Value) -> VmResult<bool> {
        use Value::*;
        match (v1, v2) {
            (Number { value: v1 }, Number { value: v2 }) =>
                Ok(v1 <= v2),

            _ => Err(VmError::InvalidOperation),
        }
    }

    fn generic_lt(&self, v1: &Value, v2: &Value) -> VmResult<bool> {
        use Value::*;
        match (v1, v2) {
            (Number { value: v1 }, Number { value: v2 }) =>
                Ok(v1 < v2),

            _ => Err(VmError::InvalidOperation),
        }
    }

    fn generic_ge(&self, v1: &Value, v2: &Value) -> VmResult<bool> {
        use Value::*;
        match (v1, v2) {
            (Number { value: v1 }, Number { value: v2 }) =>
                Ok(v1 >= v2),

            _ => Err(VmError::InvalidOperation),
        }
    }

    fn generic_gt(&self, v1: &Value, v2: &Value) -> VmResult<bool> {
        use Value::*;
        match (v1, v2) {
            (Number { value: v1 }, Number { value: v2 }) =>
                Ok(v1 > v2),

            _ => Err(VmError::InvalidOperation),
        }
    }

    fn generic_add(&self, v1: &Value, v2: &Value) -> VmResult<Value> {
        use Value::*;
        match (v1, v2) {
            (Number { value: v1 }, Number { value: v2 }) =>
                Ok(Number { value: v1 + v2 }),

            _ => Err(VmError::InvalidOperation),
        }
    }

    fn generic_sub(&self, v1: &Value, v2: &Value) -> VmResult<Value> {
        use Value::*;
        match (v1, v2) {
            (Number { value: v1 }, Number { value: v2 }) =>
                Ok(Number { value: v1 - v2 }),

            _ => Err(VmError::InvalidOperation),
        }
    }

    fn generic_mul(&self, v1: &Value, v2: &Value) -> VmResult<Value> {
        use Value::*;
        match (v1, v2) {
            (Number { value: v1 }, Number { value: v2 }) =>
                Ok(Number { value: v1 * v2 }),

            _ => Err(VmError::InvalidOperation),
        }
    }

    fn generic_div(&self, v1: &Value, v2: &Value) -> VmResult<Value> {
        use Value::*;
        match (v1, v2) {
            (Number { value: v1 }, Number { value: v2 }) => {
                if *v2 == 0.0 {
                    return Err(VmError::InvalidOperation);
                }
                Ok(Number { value: v1 / v2 })
            }

            _ => Err(VmError::InvalidOperation),
        }
    }

    fn generic_floor_div(&self, v1: &Value, v2: &Value) -> VmResult<Value> {
        use Value::*;
        match (v1, v2) {
            (Number { value: v1 }, Number { value: v2 }) => {
                if *v2 == 0.0 {
                    return Err(VmError::InvalidOperation);
                }
                Ok(Number { value: (v1 / v2).floor() })
            }

            _ => Err(VmError::InvalidOperation),
        }
    }

    fn generic_rem(&self, v1: &Value, v2: &Value) -> VmResult<Value> {
        use Value::*;
        match (v1, v2) {
            (Number { value: v1 }, Number { value: v2 }) => {
                if *v2 == 0.0 {
                    return Err(VmError::InvalidOperation);
                }
                Ok(Number { value: v1 % v2 })
            }

            _ => Err(VmError::InvalidOperation),
        }
    }

    fn generic_negate(&self, value: &Value) -> VmResult<Value> {
        use Value::*;
        match value {
            Number { value } => {
                Ok(Number { value: -value })
            }

            _ => Err(VmError::InvalidOperation),
        }
    }

    fn generic_print(&self, value: &Value) {
        match value {
            Value::Nil              => print!("nil"),
            Value::Bool   { value } => print!("{}", value),
            Value::Number { value } => print!("{}", value),
            Value::String { value } => print!("{}", value),
            Value::Unit => print!("()"),
            Value::Tuple  { values } => {
                print!("(");
                if values.len() == 1 {
                    self.generic_print(&values[0]);
                    print!(",)");
                }
                else {
                    for (i, v) in values.iter().enumerate() {
                        self.generic_print(v);
                        if i < values.len() - 1 { print!(", ") }
                    }
                    print!(")");
                }
            }
            Value::List { values } => {
                print!("[");
                for (i, v) in values.iter().enumerate() {
                    self.generic_print(v);
                    if i < values.len() - 1 { print!(", ") }
                }
                print!("]");
            }
            Value::Map { values } => {
                print!("{{");
                for (i, (k, v)) in values.iter().enumerate() {
                    self.generic_print(k);
                    print!(": ");
                    self.generic_print(v);
                    if i < values.len() - 1 { print!(", ") }
                }
                print!("}}");
            }
            Value::Func { proto } => print!("<Func {}>", proto),
        }
    }


    fn string_new(value: &str) -> Value {
        Value::String { value: Rc::new(value.into()) }
    }


    fn list_new(values: Vec<Value>) -> Value {
        Value::List { values: Rc::new(values) }
    }


    fn tuple_new(values: Vec<Value>) -> Value {
        if values.len() != 0 {
            Value::Tuple { values: Rc::new(values) }
        }
        else {
            Value::Unit
        }
    }


    fn map_new() -> Value {
        Value::Map { values: Rc::new(vec![]) }
    }

    fn map_index<'m>(map: &'m Vec<(Value, Value)>, key: &Value) -> Option<&'m Value> {
        for (k, v) in map.iter() {
            if Self::raw_eq(k, key) {
                return Some(v);
            }
        }
        None
    }

    fn map_index_mut<'m>(map: &'m mut Vec<(Value, Value)>, key: &Value) -> Option<&'m mut Value> {
        for (k, v) in map.iter_mut() {
            if Self::raw_eq(k, key) {
                return Some(v);
            }
        }
        None
    }

    fn map_def(map: &mut Vec<(Value, Value)>, key: &Value, value: Value) -> VmResult<()> {
        if let Some(slot) = Self::map_index_mut(map, key) {
            *slot = value;
        }
        else {
            map.push((key.clone(), value));
        }
        Ok(())
    }

    fn read_path(&self, base: &Value, keys: &[InstrWord]) -> VmResult<Value> {
        let key = PathKey::decode(keys[0]);
        let rem_keys = &keys[1..];

        match base {
            Value::Unit => {
                // @todo: same error as for tuple out of bounds.
                Err(VmError::InvalidOperation)
            }

            Value::Tuple { values } |
            Value::List { values } => {
                let PathKey::Index { reg } = key else { return Err(VmError::InvalidOperation) };
                let key = self.reg(reg as u32);

                let Value::Number { value: index } = key else { return Err(VmError::InvalidOperation) };
                let index = *index as usize;

                let value = values.get(index).ok_or(VmError::InvalidOperation)?;
                if rem_keys.len() == 0 {
                    Ok(value.clone())
                }
                else {
                    self.read_path(value, rem_keys)
                }
            }

            Value::Map { values } => {
                let key = match key {
                    // @temp: maps are still like "tables/objects".
                    //  cause env is still a map, which we should change.
                    PathKey::Field { string } => self.load_const(string as usize),
                    PathKey::Index { reg }    => self.reg(reg as u32),
                };

                let value = Self::map_index(values, key).ok_or(VmError::InvalidOperation)?;
                if rem_keys.len() == 0 {
                    Ok(value.clone())
                }
                else {
                    self.read_path(value, rem_keys)
                }
            }

            _ => Err(VmError::InvalidOperation)
        }
    }

    fn write_path(&self, base: &mut Value, keys: &[InstrWord], value: Value, is_def: bool) -> VmResult<()> {
        let key = PathKey::decode(keys[0]);
        let rem_keys = &keys[1..];

        match base {
            Value::Unit => {
                Err(VmError::InvalidOperation)
            }

            Value::Tuple { values } => {
                let PathKey::Index { reg } = key else { return Err(VmError::InvalidOperation) };
                let key = self.reg(reg as u32);

                let Value::Number { value: index } = key else { return Err(VmError::InvalidOperation) };
                let index = *index as usize;

                let values = Rc::make_mut(values);

                let slot = values.get_mut(index).ok_or(VmError::InvalidOperation)?;
                if rem_keys.len() == 0 {
                    *slot = value;
                    Ok(())
                }
                else {
                    self.write_path(slot, rem_keys, value, is_def)
                }
            }

            Value::List { values } => {
                let PathKey::Index { reg } = key else { return Err(VmError::InvalidOperation) };
                let key = self.reg(reg as u32);

                let Value::Number { value: index } = key else { return Err(VmError::InvalidOperation) };
                let index = *index as usize;

                let values = Rc::make_mut(values);

                if rem_keys.len() == 0 {
                    if is_def {
                        if index >= values.len() {
                            values.resize(index + 1, Value::Nil);
                        }
                        values[index] = value;
                        Ok(())
                    }
                    else {
                        let slot = values.get_mut(index).ok_or(VmError::InvalidOperation)?;
                        *slot = value;
                        Ok(())
                    }
                }
                else {
                    let slot = values.get_mut(index).ok_or(VmError::InvalidOperation)?;
                    self.write_path(slot, rem_keys, value, is_def)
                }
            }

            Value::Map { values } => {
                let key = match key {
                    // @temp: maps are still like "tables/objects".
                    //  cause env is still a map, which we should change.
                    PathKey::Field { string } => self.load_const(string as usize),
                    PathKey::Index { reg }    => self.reg(reg as u32),
                };

                let values = Rc::make_mut(values);
                let slot = Self::map_index_mut(values, key);

                if rem_keys.len() == 0 {
                    if let Some(slot) = slot {
                        *slot = value;
                        Ok(())
                    }
                    else {
                        if is_def {
                            values.push((key.clone(), value));
                            Ok(())
                        }
                        else { Err(VmError::InvalidOperation) }
                    }
                }
                else {
                    if let Some(slot) = slot {
                        self.write_path(slot, rem_keys, value, is_def)
                    }
                    else { Err(VmError::InvalidOperation) }
                }
            }

            _ => Err(VmError::InvalidOperation)
        }
    }


    #[inline(always)]
    fn check_interrupt(&mut self) -> VmResult<()> {
        let interrupt = self.interrupt.load(MemOrder::SeqCst);
        if interrupt {
            self.interrupt.store(false, MemOrder::SeqCst);
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
    fn reg(&self, reg: u32) -> &Value {
        // @todo-speed: obviously don't do this.
        let frame = self.frames.last().unwrap();
        debug_assert!(frame.base + reg < frame.top);
        &self.stack[(frame.base + reg) as usize]
    }

    #[inline(always)]
    fn reg_mut(&mut self, reg: u32) -> &mut Value {
        // @todo-speed: obviously don't do this.
        let frame = self.frames.last().unwrap();
        debug_assert!(frame.base + reg < frame.top);
        &mut self.stack[(frame.base + reg) as usize]
    }

    #[inline(always)]
    fn reg2_dst(&self, regs: (u32, u32)) -> (u32, &Value) {
        (regs.0, self.reg(regs.1))
    }

    #[inline(always)]
    fn reg3_dst(&self, regs: (u32, u32, u32)) -> (u32, &Value, &Value) {
        (regs.0, self.reg(regs.1), self.reg(regs.2))
    }

    #[inline(always)]
    unsafe fn get_current_function_bytecode<'c>(&self) -> &'c Vec<InstrWord> {
        // @todo-speed: obviously don't do this.
        let frame = self.frames.last().unwrap();
        let proto = &self.func_protos[frame.func_proto];

        let FuncCode::ByteCode(code) = &proto.code else { unreachable!() };
        &*(code as *const Vec<InstrWord>)
    }

    #[inline(always)]
    fn next_instr(&mut self) -> InstrWord {
        // @todo-speed: obviously don't do this.
        let frame = self.frames.last().unwrap();
        let proto = &self.func_protos[frame.func_proto];

        let FuncCode::ByteCode(code) = &proto.code else { unreachable!() };

        let result = code[self.pc];
        self.pc += 1;
        result
    }

    #[inline(always)]
    fn next_instr_extra(&mut self) -> InstrWord {
        let result = self.next_instr();
        debug_assert_eq!(result.opcode() as u8, opcode::EXTRA);
        result
    }

    #[inline(always)]
    fn load_const(&self, index: usize) -> &Value {
        // @todo-speed: obviously don't do this.
        let frame = self.frames.last().unwrap();
        let proto = &self.func_protos[frame.func_proto];
        &proto.constants[index]
    }

    #[inline(never)]
    fn run(&mut self) -> (VmResult<bool>,) { // wrap in tuple to prevent accidental usage of the `?` operator. (that would mess up the counter)
        if self.frames.len() == 1 {
            return (Ok(false),);
        }

        if self.counter_target == 0 {
            debug_assert_eq!(self.counter, 0);
            return (Ok(true),);
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

            macro_rules! vm_err {
                ($err: expr) => {{
                    result = Err($err);
                    break;
                }};
            }

            macro_rules! vm_jump {
                ($target: expr) => {
                    self.pc = $target as usize;
                };
            }

            debug_assert!(self.counter <= self.counter_target);

            if self.counter > 0 { loop {
                let instr  = self.next_instr();
                let opcode = instr.opcode() as u8;

                use opcode::*;
                match opcode {
                    NOP => (),

                    UNREACHABLE => {
                        vm_err!(VmError::InvalidOperation);
                    }


                    COPY => {
                        let (dst, src) = instr.c2();
                        // @todo-speed: remove checks.
                        *self.reg_mut(dst) = self.reg(src).clone();
                    }

                    SWAP => {
                        let (dst, src) = instr.c2();
                        // @todo-speed: remove checks.
                        // @todo-speed: remove clones.
                        let dst_val = self.reg(dst).clone();
                        let src_val = self.reg(src).clone();
                        *self.reg_mut(dst) = src_val;
                        *self.reg_mut(src) = dst_val;
                    }


                    LOAD_NIL => {
                        let dst = instr.c1();
                        // @todo-speed: remove checks.
                        *self.reg_mut(dst) = Value::Nil;
                    }

                    LOAD_BOOL => {
                        let (dst, value) = instr.c1_bool();
                        // @todo-speed: remove checks.
                        *self.reg_mut(dst) = value.into();
                    }

                    LOAD_INT => {
                        let (dst, value) = instr.c1u16();
                        let value = value as u16 as i16 as f64;
                        // @todo-speed: remove checks.
                        *self.reg_mut(dst) = value.into();
                    }

                    LOAD_CONST => {
                        let (dst, index) = instr.c1u16();
                        // @todo-speed: remove checks.
                        *self.reg_mut(dst) = self.load_const(index as usize).clone();
                    }


                    LOAD_ENV => {
                        //let dst = instr.c1();
                        //*self.reg_mut(dst) = self.env.clone();
                        // @temp-no-env-access.
                        unimplemented!()
                    }


                    LIST_NEW => {
                        let (dst, len) = instr.c1u16();

                        let mut values = Vec::with_capacity(len as usize);
                        for _ in 0..len {
                            let v = self.next_instr_extra();
                            values.push(self.reg(v.u16()).clone());
                        }

                        *self.reg_mut(dst) = Self::list_new(values);
                    }


                    TUPLE_NEW => {
                        let (dst, len) = instr.c1u16();

                        let mut values = Vec::with_capacity(len as usize);
                        for _ in 0..len {
                            let v = self.next_instr_extra();
                            values.push(self.reg(v.u16()).clone());
                        }

                        *self.reg_mut(dst) = Self::tuple_new(values);
                    }

                    LOAD_UNIT => {
                        let dst = instr.c1();
                        *self.reg_mut(dst) = Value::Unit;
                    }


                    MAP_NEW => {
                        let dst = instr.c1();
                        *self.reg_mut(dst) = Self::map_new();
                    }


                    READ_PATH => {
                        let (dst, base, num_keys) = instr.c3();

                        let code = unsafe { self.get_current_function_bytecode() };
                        let keys = &code[self.pc .. self.pc + num_keys as usize];
                        self.pc += num_keys as usize;

                        let value = match base as u8 {
                            // Items
                            254 => {
                                let key = PathKey::decode(keys[0]);
                                let rem_keys = &keys[1..];

                                // this is waaay too nasty!!!
                                let PathKey::Index { reg: index } = key else { unreachable!()};
                                let index = self.reg(index as u32);
                                let Value::Number { value: index } = index else { unreachable!()};
                                let index = *index as usize;

                                let frame = self.frames.last().unwrap();
                                let proto = &self.func_protos[frame.func_proto];
                                let krate = &self.krates[proto.krate.unwrap().usize()];

                                let item = &krate.items[index];
                                if item.uninitialized { vm_err!(VmError::InvalidOperation) }

                                if rem_keys.len() > 0 {
                                    vm_try!(self.read_path(&item.value, rem_keys))
                                }
                                else {
                                    item.value.clone()
                                }
                            }

                            // Env
                            255 => vm_try!(self.read_path(&self.env, keys)),

                            // Reg
                            0..=253 => vm_try!(self.read_path(self.reg(base), keys)),
                        };

                        *self.reg_mut(dst) = value;
                    }

                    WRITE_PATH | WRITE_PATH_DEF => {
                        let is_def = opcode == WRITE_PATH_DEF;
                        let (base, num_keys, value) = instr.c3();

                        let value = self.reg(value).clone();

                        let code = unsafe { self.get_current_function_bytecode() };
                        let keys = &code[self.pc .. self.pc + num_keys as usize];
                        self.pc += num_keys as usize;

                        // @todo-safety: this is UB, if base is in the keys.
                        let this = unsafe { &mut *(self as *mut VmImpl)  };

                        match base as u8 {
                            // Items
                            254 => {
                                let key = PathKey::decode(keys[0]);
                                let rem_keys = &keys[1..];

                                // this is waaay too nasty!!!
                                let PathKey::Index { reg: index } = key else { unreachable!()};
                                let index = self.reg(index as u32);
                                let Value::Number { value: index } = index else { unreachable!()};
                                let index = *index as usize;

                                let frame = self.frames.last().unwrap();
                                let proto = &self.func_protos[frame.func_proto];
                                let krate = &mut this.krates[proto.krate.unwrap().usize()];

                                let item = &mut krate.items[index];
                                if item.uninitialized { vm_err!(VmError::InvalidOperation) }
                                if item.read_only     { vm_err!(VmError::InvalidOperation) }

                                if rem_keys.len() > 0 {
                                    // unsafe
                                    vm_try!(self.write_path(&mut item.value, rem_keys, value, is_def));
                                }
                                else {
                                    item.value = value;
                                }
                            }

                            // Env
                            // unsafe
                            255 => vm_try!(self.write_path(&mut this.env, keys, value, is_def)),

                            // Reg
                            // unsafe
                            0..=253 => vm_try!(self.write_path(this.reg_mut(base), keys, value, is_def)),
                        }
                    }


                    ADD => {
                        // @todo-speed: remove checks.
                        let (dst, src1, src2) = self.reg3_dst(instr.c3());
                        *self.reg_mut(dst) = vm_try!(self.generic_add(src1, src2));
                    }

                    SUB => {
                        // @todo-speed: remove checks.
                        let (dst, src1, src2) = self.reg3_dst(instr.c3());
                        *self.reg_mut(dst) = vm_try!(self.generic_sub(src1, src2));
                    }

                    MUL => {
                        // @todo-speed: remove checks.
                        let (dst, src1, src2) = self.reg3_dst(instr.c3());
                        *self.reg_mut(dst) = vm_try!(self.generic_mul(src1, src2));
                    }

                    DIV => {
                        // @todo-speed: remove checks.
                        let (dst, src1, src2) = self.reg3_dst(instr.c3());
                        *self.reg_mut(dst) = vm_try!(self.generic_div(src1, src2));
                    }

                    FLOOR_DIV => {
                        let (dst, src1, src2) = self.reg3_dst(instr.c3());
                        *self.reg_mut(dst) = vm_try!(self.generic_floor_div(src1, src2));
                    }

                    REM => {
                        let (dst, src1, src2) = self.reg3_dst(instr.c3());
                        *self.reg_mut(dst) = vm_try!(self.generic_rem(src1, src2));
                    }

                    ADD_INT => {
                        let (dst, imm) = instr.c1u16();
                        let Value::Number { value } = self.reg_mut(dst) else {
                            vm_err!(VmError::InvalidOperation);
                        };
                        *value += imm as u16 as i16 as f64;
                    }

                    NEGATE => {
                        // @todo-speed: remove checks.
                        let (dst, src) = self.reg2_dst(instr.c2());
                        *self.reg_mut(dst) = vm_try!(self.generic_negate(src));
                    }


                    NOT => {
                        // @todo-speed: remove checks.
                        let (dst, src) = self.reg2_dst(instr.c2());

                        // @todo-cleanup: value utils.
                        let Value::Bool { value } = src else {
                            vm_err!(VmError::InvalidOperation);
                        };
                        *self.reg_mut(dst) = Value::Bool { value: !value };
                    }


                    CMP_EQ => {
                        // @todo-speed: remove checks.
                        let (dst, src1, src2) = self.reg3_dst(instr.c3());
                        *self.reg_mut(dst) = vm_try!(self.generic_eq(src1, src2)).into();
                    }

                    CMP_NE => {
                        // @todo-speed: remove checks.
                        let (dst, src1, src2) = self.reg3_dst(instr.c3());
                        *self.reg_mut(dst) = vm_try!(self.generic_ne(src1, src2)).into();
                    }

                    CMP_LE => {
                        // @todo-speed: remove checks.
                        let (dst, src1, src2) = self.reg3_dst(instr.c3());
                        *self.reg_mut(dst) = vm_try!(self.generic_le(src1, src2)).into();
                    }

                    CMP_LT => {
                        // @todo-speed: remove checks.
                        let (dst, src1, src2) = self.reg3_dst(instr.c3());
                        *self.reg_mut(dst) = vm_try!(self.generic_lt(src1, src2)).into();
                    }

                    CMP_GE => {
                        // @todo-speed: remove checks.
                        let (dst, src1, src2) = self.reg3_dst(instr.c3());
                        *self.reg_mut(dst) = vm_try!(self.generic_ge(src1, src2)).into();
                    }

                    CMP_GT => {
                        // @todo-speed: remove checks.
                        let (dst, src1, src2) = self.reg3_dst(instr.c3());
                        *self.reg_mut(dst) = vm_try!(self.generic_gt(src1, src2)).into();
                    }


                    JUMP => {
                        let target = instr.u16();
                        vm_jump!(target);
                    }

                    JUMP_TRUE => {
                        let (src, target) = instr.c1u16();

                        // @todo-speed: remove checks.
                        let condition = self.reg(src);

                        // @todo-cleanup: value utils.
                        let Value::Bool { value } = condition else {
                            vm_err!(VmError::InvalidOperation);
                        };

                        if *value {
                            vm_jump!(target);
                        }
                    }

                    JUMP_FALSE => {
                        let (src, target) = instr.c1u16();

                        // @todo-speed: remove checks.
                        let condition = self.reg(src);

                        // @todo-cleanup: value utils.
                        let Value::Bool { value } = condition else {
                            vm_err!(VmError::InvalidOperation);
                        };

                        if !value {
                            vm_jump!(target);
                        }
                    }

                    JUMP_NIL => {
                        let (src, target) = instr.c1u16();

                        if self.reg(src).is_nil() {
                            vm_jump!(target);
                        }
                    }

                    JUMP_NOT_NIL => {
                        let (src, target) = instr.c1u16();

                        if !self.reg(src).is_nil() {
                            vm_jump!(target);
                        }
                    }


                    CALL => {
                        let (dst, func) = instr.c2();
                        let num_args = self.next_instr_extra().u16();

                        let args = {
                            let code = unsafe { self.get_current_function_bytecode() };

                            let result = &code[self.pc .. self.pc + num_args as usize];
                            self.pc += num_args as usize;
                            result
                        };

                        let frame = self.frames.last().unwrap();
                        let src_base = frame.base as usize;

                        vm_try!(self.pre_call(dst, func, num_args, |vm, dst_base| {
                            for (i, arg) in args.iter().enumerate() {
                                debug_assert_eq!(arg.opcode() as u8, EXTRA);

                                let arg = arg.u16() as usize;
                                vm.stack[dst_base + i] = vm.stack[src_base + arg].clone();
                            }
                        }));
                    }

                    RET => {
                        let src = instr.c1();

                        let value = self.reg(src).clone();

                        let dst_abs = self.frames.last().unwrap().dst_abs;
                        self.stack[dst_abs as usize] = value;

                        if vm_try!(self.post_call()) {
                            self.counter = self.counter.wrapping_sub(1);
                            result = Ok(());
                            break;
                        }
                    }

                    // @todo-speed: this inserts a check to reduce dispatch table size.
                    //  may want an unreachable_unchecked() in release.
                    0 | END ..= 255 => unreachable!()
                }

                self.counter = self.counter.wrapping_sub(1);
                if self.counter == 0 {
                    break;
                }
            }}

            match result {
                Ok(_v) => {
                    debug_assert_eq!(_v, ());
                    return (Ok(true),);
                }

                Err(VmError::Counter) => {
                    debug_assert_eq!(self.counter, 0);
                    self.instruction_counter += self.counter_target as u64;
                    self.counter = self.counter_target;

                    if let Some(mut hook) = self.debug_hook.take() {
                        // @safety-#vm-transparent
                        let result = hook.on_instruction_limit(unsafe { core::mem::transmute_copy(&self) });

                        if let DebugHookWrapper::Taken = self.debug_hook {
                            self.debug_hook = DebugHookWrapper::Some(hook);
                        }

                        let Ok(result) = result else {
                            self.unwind_until_native();
                            return (result.map(|_| true),);
                        };

                        match result {
                            DebugHookResult::Continue => (),

                            DebugHookResult::Pause => {
                                assert!(self.can_pause());
                                return (Ok(true),);
                            }
                        }
                    }

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


    fn pre_call<CopyArgs: FnOnce(&mut VmImpl, usize)>(&mut self,
        dst: u32, func: u32, num_args: u32, copy_args: CopyArgs
    ) -> VmResult<bool> {
        assert!(num_args < 128);

        let frame = self.frames.last_mut().unwrap();
        let caller_base = frame.base;

        let func_value = &self.stack[(caller_base + func) as usize];

        let Value::Func { proto: func_proto } = func_value else {
            return Err(VmError::InvalidOperation);
        };
        let func_proto = *func_proto;
        let proto = &self.func_protos[func_proto];

        // check args.
        if num_args != proto.num_params {
            return Err(VmError::InvalidOperation);
        }

        // save vm state.
        frame.pc = self.pc as u32;

        // push frame.
        let base = frame.top;
        let top  = base + proto.stack_size;
        self.frames.push(StackFrame {
            func_proto,
            is_native: proto.code.is_native(),
            dst_abs: caller_base + dst,
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
                let ret = code.0(unsafe { core::mem::transmute_copy(&self) })?;

                let frame = self.frames.last().unwrap();
                let dst_abs = frame.dst_abs;

                match ret {
                    NativeFuncReturn::Unit => {
                        self.stack[dst_abs as usize] = Value::Unit;
                    }
                    NativeFuncReturn::Reg(src) => {
                        self.stack[dst_abs as usize] = self.reg(src).clone();
                    }
                }

                self.post_call()?;

                Ok(false)
            }
        }
    }

    // caller is responsible for returning the value.
    fn post_call(&mut self) -> VmResult<bool> {
        // pop frame.
        self.frames.pop().unwrap();

        // reset vm state.
        let prev_frame = self.frames.last_mut().unwrap();
        self.pc = prev_frame.pc as usize;
        self.stack.truncate(prev_frame.top as usize);

        // @todo-speed: debug only.
        prev_frame.pc = u32::MAX;

        Ok(prev_frame.is_native)
    }
}



#[cfg(test)]
mod tests {
    /*
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



