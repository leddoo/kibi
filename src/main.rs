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
enum Op {
    Nop,
    Halt,

    Copy        { to: u32, from: u32 },

    Jump        { target: u32 },
    JumpTrue    { src: u32, target: u32 },
    JumpFalse   { src: u32, target: u32 },
    JumpEq      { src1: u32, src2: u32, target: u32 },
    JumpLe      { src1: u32, src2: u32, target: u32 },
    JumpLt      { src1: u32, src2: u32, target: u32 },
    JumpNEq     { src1: u32, src2: u32, target: u32 },
    JumpNLe     { src1: u32, src2: u32, target: u32 },
    JumpNLt     { src1: u32, src2: u32, target: u32 },

    SetNil      { dst: u32 },
    SetBool     { dst: u32, value: bool },
    SetNumber   { dst: u32, value: f64 },
    SetString   { dst: u32, value: &'static str },

    ListNew     { dst: u32 },
    ListAppend  { list: u32, value: u32 },
    ListDef     { list: u32, index: u32, value: u32 },
    ListSet     { list: u32, index: u32, value: u32 },
    ListGet     { dst: u32, list: u32, index: u32 },
    ListLen     { dst: u32, list: u32 },

    Add         { dst: u32, src1: u32, src2: u32 },
    Sub         { dst: u32, src1: u32, src2: u32 },
    Mul         { dst: u32, src1: u32, src2: u32 },
    Div         { dst: u32, src1: u32, src2: u32 },
    IDiv        { dst: u32, src1: u32, src2: u32 },
    IMod        { dst: u32, src1: u32, src2: u32 },
    Inc         { reg: u32 },

    CmpEq       { dst: u32, src1: u32, src2: u32 },
    CmpLe       { dst: u32, src1: u32, src2: u32 },
    CmpLt       { dst: u32, src1: u32, src2: u32 },
    CmpGe       { dst: u32, src1: u32, src2: u32 },
    CmpGt       { dst: u32, src1: u32, src2: u32 },

    Print       { value: u32 },

    Gc,
}


#[derive(Debug)]
struct Vm {
    code: Vec<Op>,
    pc:   usize,

    stack: Vec<Value>,
    heap:  Vec<GcObject>,

    first_free: Option<usize>,
    gc_timer:   u32,
}

impl Vm {
    fn new(code: Vec<Op>, stack_size: usize) -> Self {
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


    fn step(&mut self) -> bool {
        //println!("{} {:?} {:?}", self.pc, self.code[self.pc], self);

        let op = self.code[self.pc];
        self.pc += 1;

        match op {
            Op::Nop => (),

            Op::Halt => {
                self.pc -= 1;
                return false
            },


            Op::Copy { to, from } => {
                // @todo-speed: remove checks.
                self.stack[to as usize] = self.stack[from as usize];
            }


            Op::Jump { target } => {
                self.pc = target as usize;
            }

            Op::JumpTrue { src, target } => {
                // @todo-speed: remove checks.
                let condition = self.stack[src as usize];

                // @todo-robust: error.
                // @todo-cleanup: value utils.
                let Value::Bool { value } = condition else { unimplemented!() };

                if value {
                    self.pc = target as usize;
                }
            }

            Op::JumpFalse { src, target } => {
                // @todo-speed: remove checks.
                let condition = self.stack[src as usize];

                // @todo-robust: error.
                // @todo-cleanup: value utils.
                let Value::Bool { value } = condition else { unimplemented!() };

                if !value {
                    self.pc = target as usize;
                }
            }

            Op::JumpEq { src1, src2, target } => {
                // @todo-speed: remove checks.
                let src1 = self.stack[src1 as usize];
                let src2 = self.stack[src2 as usize];
                if self.value_eq(src1, src2) {
                    self.pc = target as usize;
                }
            }

            Op::JumpLe { src1, src2, target } => {
                // @todo-speed: remove checks.
                let src1 = self.stack[src1 as usize];
                let src2 = self.stack[src2 as usize];
                if self.value_le(src1, src2) {
                    self.pc = target as usize;
                }
            }

            Op::JumpLt { src1, src2, target } => {
                // @todo-speed: remove checks.
                let src1 = self.stack[src1 as usize];
                let src2 = self.stack[src2 as usize];
                if self.value_lt(src1, src2) {
                    self.pc = target as usize;
                }
            }

            Op::JumpNEq { src1, src2, target } => {
                // @todo-speed: remove checks.
                let src1 = self.stack[src1 as usize];
                let src2 = self.stack[src2 as usize];
                if !self.value_eq(src1, src2) {
                    self.pc = target as usize;
                }
            }

            Op::JumpNLe { src1, src2, target } => {
                // @todo-speed: remove checks.
                let src1 = self.stack[src1 as usize];
                let src2 = self.stack[src2 as usize];
                if !self.value_le(src1, src2) {
                    self.pc = target as usize;
                }
            }

            Op::JumpNLt { src1, src2, target } => {
                // @todo-speed: remove checks.
                let src1 = self.stack[src1 as usize];
                let src2 = self.stack[src2 as usize];
                if !self.value_lt(src1, src2) {
                    self.pc = target as usize;
                }
            }


            Op::SetNil { dst } => {
                // @todo-speed: remove checks.
                self.stack[dst as usize] = Value::Nil;
            }

            Op::SetBool { dst, value } => {
                // @todo-speed: remove checks.
                self.stack[dst as usize] = Value::Bool { value };
            }

            Op::SetNumber { dst, value } => {
                // @todo-speed: remove checks.
                self.stack[dst as usize] = Value::Number { value };
            }

            Op::SetString { dst, value } => {
                let index = self.heap_alloc();
                // @todo-speed: constant table.
                self.heap[index].data = GcObjectData::String { value: value.into() };

                // @todo-speed: remove checks.
                self.stack[dst as usize] = Value::String { index };
            }


            Op::ListNew { dst } => {
                let index = self.heap_alloc();
                self.heap[index].data = GcObjectData::List { values: vec![] };

                // @todo-speed: remove checks.
                self.stack[dst as usize] = Value::List { index };
            }

            Op::ListAppend { list, value } => {
                // @todo-speed: remove checks.
                let list  = self.stack[list  as usize];
                let value = self.stack[value as usize];

                // @todo-robust: error.
                let Value::List { index: list_index } = list else { unimplemented!() };

                let object = &mut self.heap[list_index];
                let GcObjectData::List { values } = &mut object.data else { unreachable!() };

                values.push(value);
            }

            Op::ListDef { list, index, value } => {
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

            Op::ListSet { list, index, value } => {
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

            Op::ListGet { dst, list, index } => {
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

            Op::ListLen { dst, list } => {
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


            Op::Add { dst, src1, src2 } => {
                // @todo-speed: remove checks.
                let src1 = self.stack[src1 as usize];
                let src2 = self.stack[src2 as usize];
                let result = self.value_add(src1, src2);
                self.stack[dst as usize] = result;
            }

            Op::Sub { dst, src1, src2 } => {
                // @todo-speed: remove checks.
                let src1 = self.stack[src1 as usize];
                let src2 = self.stack[src2 as usize];
                let result = self.value_sub(src1, src2);
                self.stack[dst as usize] = result;
            }

            Op::Mul { dst, src1, src2 } => {
                // @todo-speed: remove checks.
                let src1 = self.stack[src1 as usize];
                let src2 = self.stack[src2 as usize];
                let result = self.value_mul(src1, src2);
                self.stack[dst as usize] = result;
            }

            Op::Div { dst, src1, src2 } => {
                // @todo-speed: remove checks.
                let src1 = self.stack[src1 as usize];
                let src2 = self.stack[src2 as usize];
                let result = self.value_div(src1, src2);
                self.stack[dst as usize] = result;
            }

            Op::IDiv { dst: _, src1: _, src2: _ } => {
                unimplemented!()
            }

            Op::IMod { dst: _, src1: _, src2: _ } => {
                unimplemented!()
            }

            Op::Inc { reg: dst } => {
                // @todo-speed: remove checks.
                let value = &mut self.stack[dst as usize];

                // @todo-robust: error.
                let Value::Number { value } = value else { unimplemented!() };

                *value += 1.0;
            }


            Op::CmpEq { dst, src1, src2 } => {
                // @todo-speed: remove checks.
                let src1 = self.stack[src1 as usize];
                let src2 = self.stack[src2 as usize];
                let result = self.value_eq(src1, src2);
                self.stack[dst as usize] = Value::Bool { value: result };
            }

            Op::CmpLe { dst, src1, src2 } => {
                // @todo-speed: remove checks.
                let src1 = self.stack[src1 as usize];
                let src2 = self.stack[src2 as usize];
                let result = self.value_le(src1, src2);
                self.stack[dst as usize] = Value::Bool { value: result };
            }

            Op::CmpLt { dst, src1, src2 } => {
                // @todo-speed: remove checks.
                let src1 = self.stack[src1 as usize];
                let src2 = self.stack[src2 as usize];
                let result = self.value_lt(src1, src2);
                self.stack[dst as usize] = Value::Bool { value: result };
            }

            Op::CmpGe { dst, src1, src2 } => {
                // @todo-speed: remove checks.
                let src1 = self.stack[src1 as usize];
                let src2 = self.stack[src2 as usize];
                let result = self.value_ge(src1, src2);
                self.stack[dst as usize] = Value::Bool { value: result };
            }

            Op::CmpGt { dst, src1, src2 } => {
                // @todo-speed: remove checks.
                let src1 = self.stack[src1 as usize];
                let src2 = self.stack[src2 as usize];
                let result = self.value_gt(src1, src2);
                self.stack[dst as usize] = Value::Bool { value: result };
            }


            Op::Print { value } => {
                // @todo-speed: remove checks.
                let value = self.stack[value as usize];
                self.value_print(value);
                println!();
            }


            Op::Gc => {
                self.gc();
            }
        }

        true
    }

    fn run(&mut self) {
        while self.step() {}
    }
}


fn main() {
    let mut vm = Vm::new(vec![
        Op::ListNew     { dst: 0 },

        Op::SetString   { dst: 2, value: "hi" },
        Op::ListAppend  { list: 0, value: 2 },

        Op::SetNumber   { dst: 2, value: 69.0 },
        Op::ListAppend  { list: 0, value: 2 },

        Op::SetBool     { dst: 2, value: false },
        Op::ListAppend  { list: 0, value: 2 },

        Op::SetString   { dst: 2, value: "list contents:" },
        Op::Print       { value: 2 },

        // i = 0
        Op::SetNumber   { dst: 1, value: 0.0 },

        // 10, loop:
        Op::ListLen     { dst: 2, list: 0 },
        Op::JumpNLt     { src1: 1, src2: 2, target: 16 },
        Op::ListGet     { dst: 2, list: 0, index: 1 },
        Op::Print       { value: 2 },
        Op::Inc         { reg: 1 },
        Op::Jump        { target: 10 },

        // 16, done:

        Op::Halt,
    ], 3);

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

