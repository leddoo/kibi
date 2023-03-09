use std::rc::Rc;
use crate::vm::*;
use crate::bytecode::*;


#[derive(Clone, Debug)]
pub(crate) enum Value {
    Nil,
    Bool   { value: bool   },
    Number { value: f64    },
    String { value: Rc<String>, },
    Unit,
    Tuple  { values: Rc<Vec<Value>>, },
    List   { values: Rc<Vec<Value>>, },
    Map    { values: Rc<Vec<(Value, Value)>> },
    Func   { proto: usize  },
}

impl From<bool> for Value { #[inline(always)] fn from(value: bool) -> Self { Value::Bool   { value } } }
impl From<f64>  for Value { #[inline(always)] fn from(value: f64)  -> Self { Value::Number { value } } }

impl Value {
    #[inline(always)]
    pub fn is_nil(&self) -> bool {
        if let Value::Nil = self { true } else { false }
    }
}



#[derive(Debug)]
pub(crate) struct GcObject {
    pub marked: bool,
    pub data: GcObjectData,
}

#[derive(Debug)]
pub(crate) enum GcObjectData {
    Nil,
    Free  { next:  Option<usize> },
}



pub enum NativeFuncReturn {
    Unit,
    Reg (u32),
}

pub type NativeFuncPtr = fn(&mut Vm) -> VmResult<NativeFuncReturn>;

#[derive(Clone)]
pub struct NativeFuncPtrEx(pub NativeFuncPtr);
impl core::fmt::Debug for NativeFuncPtrEx { fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { (self.0 as *const u8).fmt(f) } }


crate::macros::define_id!(CrateId, OptCrateId);


#[derive(Debug)]
pub(crate) struct FuncProto {
    pub krate:      OptCrateId,
    pub code:       FuncCode,
    pub constants:  Vec<Value>,
    pub num_params: u32,
    pub stack_size: u32,
}

#[derive(Clone, Debug)]
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



// @temp: move to kbtf.

#[derive(Clone, Debug)]
pub enum Constant {
    Nil,
    Bool   { value: bool    },
    Number { value: f64     },
    String { value: String },
}

#[derive(Clone, Debug)]
pub struct FuncDesc {
    pub code:       FuncCode,
    pub constants:  Vec<Constant>,
    pub num_params: u32,
    pub stack_size: u32,
}

