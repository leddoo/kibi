use sti::arena::Arena;
use sti::keyed::KVec;

use crate::env::SymbolId;
use crate::tt::{Term, LocalVarId};


sti::define_key!(pub, u32, BlockId);

impl BlockId {
    pub const ENTRY: BlockId = BlockId(0);
}


#[derive(Clone, Copy, Debug)]
pub struct Path<'a> {
    pub base: LocalVarId,
    pub projs: &'a [Proj],
}

#[derive(Clone, Copy, Debug)]
pub enum Proj {
    Deref,
}


#[derive(Clone, Copy, Debug)]
pub enum Stmt<'a> {
    Error,
    Axiom, // @temp
    Pop,
    Const(Term<'a>),
    ConstUnit,
    ConstBool(bool),
    ConstNat(u32),
    Ref(Path<'a>),
    Read(Path<'a>),
    Write(Path<'a>),
    Call { func: SymbolId, num_args: usize },
}


#[derive(Clone, Copy, Debug)]
pub enum Terminator {
    Jump { target: BlockId },
    Ite { on_true: BlockId, on_false: BlockId },
    Return,
}


#[derive(Clone, Copy, Debug)]
pub struct Block<'a> {
    pub stmts: &'a [Stmt<'a>],
    pub terminator: Terminator,
}


pub struct Function<'a> {
    pub blocks: KVec<BlockId, Block<'a>>,
}


mod builder;
pub use builder::build_def;

