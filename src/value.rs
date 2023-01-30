use crate::vm::Vm;
use crate::bytecode::Instruction;


#[derive(Clone, Copy, Debug)]
pub enum Value {
    Nil,
    Bool   { value: bool   },
    Number { value: f64    },
    String { index: usize  },
    List   { index: usize  },
    Table  { index: usize  },
    Func   { proto: usize  },
    // Fiber
}

impl From<bool> for Value { #[inline(always)] fn from(value: bool) -> Self { Value::Bool   { value } } }
impl From<f64>  for Value { #[inline(always)] fn from(value: f64)  -> Self { Value::Number { value } } }



#[derive(Debug)]
pub struct GcObject {
    pub marked: bool,
    pub data: GcObjectData,
}

#[derive(Debug)]
pub enum GcObjectData {
    Nil,
    Free  { next:  Option<usize> },
    List  { values: Vec<Value> },
    Table  (TableData),
    String { value: String },
}


#[derive(Debug)]
pub struct TableData {
    pub values: Vec<(Value, Value)>,
}

impl TableData {
    pub fn insert(&mut self, key: Value, value: Value, vm: &mut Vm) {
        if let Some(v) = self.index(key, vm) {
            *v = value;
        }
        else {
            self.values.push((key, value));
        }
    }

    pub fn index(&mut self, key: Value, vm: &mut Vm) -> Option<&mut Value> {
        for (k, v) in &mut self.values {
            // @todo-decide: should this use `raw_eq`?
            if vm.generic_eq(*k, key) {
                return Some(v);
            }
        }
        None
    }

    pub fn len(&self) -> usize {
        self.values.len()
    }
}



pub type NativeFuncPtr = fn(&mut Vm) -> Result<u32, ()>;

pub struct NativeFuncPtrEx(pub NativeFuncPtr);
impl core::fmt::Debug for NativeFuncPtrEx { fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { (self.0 as *const u8).fmt(f) } }


#[derive(Debug)]
pub struct FuncProto {
    pub code:       FuncCode,
    pub constants:  Vec<Value>,
    pub num_params: u32,
    pub stack_size: u32,
}

#[derive(Debug)]
pub enum FuncCode {
    ByteCode (Vec<Instruction>),
    Native   (NativeFuncPtrEx),
}

impl FuncCode {
    #[inline(always)]
    pub fn is_native(&self) -> bool {
        match self {
            FuncCode::ByteCode(_) => false,
            FuncCode::Native(_)   => true,
        }
    }
}


