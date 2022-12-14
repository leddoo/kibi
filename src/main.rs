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
    fn print(&self, vm: &Vm) {
        match self {
            Value::Nil              => print!("nil"),
            Value::Bool   { value } => print!("{}", value),
            Value::Number { value } => print!("{}", value),
            Value::String { index } => {
                let GcObjectData::String { value } = &vm.heap[*index].data else { unreachable!() };
                print!("{}", value);
            }
            Value::List   { index } => print!("<List {}>", index),
            Value::Table  { index } => print!("<Table {}>", index),
        }
    }
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
    Halt,

    Copy (i32),

    Jump      (u32),
    JumpFalse (u32),

    PushNil,
    PushBool   (bool),
    PushNumber (f64),
    PushString (&'static str),
    PushList,
    PushTable,

    ListPush,
    ListRead,
    ListWrite,
    ListLen,

    TableInsert,
    TableRead,
    TableWrite,

    Add,
    Sub,
    Mul,
    Div,
    IDiv,
    IMod,
    Inc,

    CmpEq,
    CmpLe,
    CmpLt,
    CmpGe,
    CmpGt,

    Print,

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
    fn new(code: Vec<Op>) -> Self {
        Vm {
            code,
            pc: 0,
            stack: vec![],
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

    fn step(&mut self) -> bool {
        //println!("{} {:?} {:?}", self.pc, self.code[self.pc], self);

        let op = self.code[self.pc];
        self.pc += 1;

        match op {
            Op::Halt => {
                self.pc -= 1;
                return false
            },


            Op::Copy (index) => {
                // @todo-robust: error.
                let index =
                    if index < 0 { -index as usize }
                    else         { self.stack.len() - 1 - index as usize };
                let value = self.stack[index];
                self.stack.push(value);
            }


            Op::Jump (target) => {
                self.pc = target as usize;
            }

            Op::JumpFalse (target) => {
                // @todo-robust: error.
                let condition = self.stack.pop().unwrap();

                // @todo-robust: error.
                let Value::Bool { value } = condition else { unimplemented!() };

                if !value {
                    self.pc = target as usize;
                }
            }


            Op::PushNil => {
                self.stack.push(Value::Nil);
            }

            Op::PushBool (value) => {
                self.stack.push(Value::Bool { value });
            }

            Op::PushNumber (value) => {
                self.stack.push(Value::Number { value });
            }

            Op::PushString (value) => {
                let index = self.heap_alloc();
                self.heap[index].data = GcObjectData::String { value: value.into() };
                self.stack.push(Value::String { index })
            }

            Op::PushList => {
                let index = self.heap_alloc();
                self.heap[index].data = GcObjectData::List { values: vec![] };
                self.stack.push(Value::List { index });
            }

            Op::PushTable => {
                let index = self.heap_alloc();
                self.heap[index].data = GcObjectData::Table { values: vec![] };
                self.stack.push(Value::List { index });
            }


            Op::ListPush => {
                // @todo-robust: error.
                let value = self.stack.pop().unwrap();

                // @todo-robust: error.
                let list = self.stack.pop().unwrap();

                // @todo-robust: error.
                let Value::List { index: list_index } = list else { unimplemented!() };

                let object = &mut self.heap[list_index];
                let GcObjectData::List { values } = &mut object.data else { unreachable!() };

                values.push(value);
            }

            Op::ListRead => {
                // @todo-robust: error.
                let index = self.stack.pop().unwrap();

                // @todo-robust: error.
                let list = self.stack.pop().unwrap();

                // @todo-robust: error.
                let Value::List { index: list_index } = list else { unimplemented!() };

                let object = &mut self.heap[list_index];
                let GcObjectData::List { values } = &mut object.data else { unreachable!() };

                // @todo-robust: error.
                let Value::Number { value: index } = index else { unimplemented!() };

                // @todo-robust: error.
                let value = values[index as usize];

                self.stack.push(value);
            }

            Op::ListWrite => {
                // @todo-robust: error.
                let value = self.stack.pop().unwrap();

                // @todo-robust: error.
                let index = self.stack.pop().unwrap();

                // @todo-robust: error.
                let list = self.stack.pop().unwrap();

                // @todo-robust: error.
                let Value::List { index: list_index } = list else { unimplemented!() };

                let object = &mut self.heap[list_index];
                let GcObjectData::List { values } = &mut object.data else { unreachable!() };

                // @todo-robust: error.
                let Value::Number { value: index } = index else { unimplemented!() };

                // @todo-robust: error.
                let slot = &mut values[index as usize];

                *slot = value;
            }

            Op::ListLen => {
                // @todo-robust: error.
                let list = self.stack.pop().unwrap();

                // @todo-robust: error.
                let Value::List { index: list_index } = list else { unimplemented!() };

                let object = &mut self.heap[list_index];
                let GcObjectData::List { values } = &mut object.data else { unreachable!() };

                let result = Value::Number { value: values.len() as f64 };
                self.stack.push(result);
            }


            Op::TableInsert => {
                unimplemented!()
            }

            Op::TableRead => {
                unimplemented!()
            }

            Op::TableWrite => {
                unimplemented!()
            }


            Op::Add => {
                // @todo-robust: error.
                let b = self.stack.pop().unwrap();

                // @todo-robust: error.
                let a = self.stack.pop().unwrap();

                // @todo-robust: error.
                let Value::Number { value: a } = a else { unimplemented!() };

                // @todo-robust: error.
                let Value::Number { value: b } = b else { unimplemented!() };

                let result = Value::Number { value: a + b };
                self.stack.push(result);
            }

            Op::Sub => {
                // @todo-robust: error.
                let b = self.stack.pop().unwrap();

                // @todo-robust: error.
                let a = self.stack.pop().unwrap();

                // @todo-robust: error.
                let Value::Number { value: a } = a else { unimplemented!() };

                // @todo-robust: error.
                let Value::Number { value: b } = b else { unimplemented!() };

                let result = Value::Number { value: a - b };
                self.stack.push(result);
            }

            Op::Mul => {
                // @todo-robust: error.
                let b = self.stack.pop().unwrap();

                // @todo-robust: error.
                let a = self.stack.pop().unwrap();

                // @todo-robust: error.
                let Value::Number { value: a } = a else { unimplemented!() };

                // @todo-robust: error.
                let Value::Number { value: b } = b else { unimplemented!() };

                let result = Value::Number { value: a * b };
                self.stack.push(result);
            }

            Op::Div => {
                // @todo-robust: error.
                let b = self.stack.pop().unwrap();

                // @todo-robust: error.
                let a = self.stack.pop().unwrap();

                // @todo-robust: error.
                let Value::Number { value: a } = a else { unimplemented!() };

                // @todo-robust: error.
                let Value::Number { value: b } = b else { unimplemented!() };

                let result = Value::Number { value: a / b };
                self.stack.push(result);
            }

            Op::IDiv => {
                // @todo-robust: error.
                let b = self.stack.pop().unwrap();

                // @todo-robust: error.
                let a = self.stack.pop().unwrap();

                // @todo-robust: error.
                let Value::Number { value: a } = a else { unimplemented!() };
                let a = a as i64;

                // @todo-robust: error.
                let Value::Number { value: b } = b else { unimplemented!() };
                let b = b as i64;

                let result = Value::Number { value: (a / b) as f64 };
                self.stack.push(result);
            }

            Op::IMod => {
                // @todo-robust: error.
                let b = self.stack.pop().unwrap();

                // @todo-robust: error.
                let a = self.stack.pop().unwrap();

                // @todo-robust: error.
                let Value::Number { value: a } = a else { unimplemented!() };
                let a = a as i64;

                // @todo-robust: error.
                let Value::Number { value: b } = b else { unimplemented!() };
                let b = b as i64;

                let result = Value::Number { value: (a % b) as f64 };
                self.stack.push(result);
            }

            Op::Inc => {
                // @todo-robust: error.
                let a = self.stack.last_mut().unwrap();

                // @todo-robust: error.
                let Value::Number { value: a } = a else { unimplemented!() };

                *a += 1.0;
            }


            Op::CmpEq => {
                // @todo-robust: error.
                let b = self.stack.pop().unwrap();

                // @todo-robust: error.
                let a = self.stack.pop().unwrap();

                // @todo-feature: polymorphic.

                // @todo-robust: error.
                let Value::Number { value: a } = a else { unimplemented!() };

                // @todo-robust: error.
                let Value::Number { value: b } = b else { unimplemented!() };

                let result = Value::Bool { value: a == b };
                self.stack.push(result);
            }

            Op::CmpLe => {
                // @todo-robust: error.
                let b = self.stack.pop().unwrap();

                // @todo-robust: error.
                let a = self.stack.pop().unwrap();

                // @todo-feature: polymorphic.

                // @todo-robust: error.
                let Value::Number { value: a } = a else { unimplemented!() };

                // @todo-robust: error.
                let Value::Number { value: b } = b else { unimplemented!() };

                let result = Value::Bool { value: a <= b };
                self.stack.push(result);
            }

            Op::CmpLt => {
                // @todo-robust: error.
                let b = self.stack.pop().unwrap();

                // @todo-robust: error.
                let a = self.stack.pop().unwrap();

                // @todo-feature: polymorphic.

                // @todo-robust: error.
                let Value::Number { value: a } = a else { unimplemented!() };

                // @todo-robust: error.
                let Value::Number { value: b } = b else { unimplemented!() };

                let result = Value::Bool { value: a < b };
                self.stack.push(result);
            }

            Op::CmpGe => {
                // @todo-robust: error.
                let b = self.stack.pop().unwrap();

                // @todo-robust: error.
                let a = self.stack.pop().unwrap();

                // @todo-feature: polymorphic.

                // @todo-robust: error.
                let Value::Number { value: a } = a else { unimplemented!() };

                // @todo-robust: error.
                let Value::Number { value: b } = b else { unimplemented!() };

                let result = Value::Bool { value: a >= b };
                self.stack.push(result);
            }

            Op::CmpGt => {
                // @todo-robust: error.
                let b = self.stack.pop().unwrap();

                // @todo-robust: error.
                let a = self.stack.pop().unwrap();

                // @todo-feature: polymorphic.

                // @todo-robust: error.
                let Value::Number { value: a } = a else { unimplemented!() };

                // @todo-robust: error.
                let Value::Number { value: b } = b else { unimplemented!() };

                let result = Value::Bool { value: a > b };
                self.stack.push(result);
            }


            Op::Print => {
                // @todo-robust: error.
                let top = self.stack.pop().unwrap();
                top.print(self);
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
        Op::PushList,

        Op::Copy(0),
        Op::PushString("hi"),
        Op::ListPush,

        Op::Copy(0),
        Op::PushNumber(69.0),
        Op::ListPush,

        Op::Copy(0),
        Op::PushBool(false),
        Op::ListPush,

        Op::PushString("list contents:"),
        Op::Print,

        // i = 0
        Op::PushNumber(0.0),

        // 13, loop:
        Op::Copy(0), // push i
        Op::Copy(2), // push list
        Op::ListLen,
        Op::CmpLt,
        Op::JumpFalse(24),
        Op::Copy(1), // push list
        Op::Copy(1), // push i
        Op::ListRead,
        Op::Print,
        Op::Inc,
        Op::Jump(13),

        // 24, done:

        Op::Halt,
    ]);

    let t0 = std::time::Instant::now();
    vm.run();
    println!("{:?}", t0.elapsed());

    //println!("{:?}", vm);
}

