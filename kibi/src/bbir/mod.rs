use sti::arena::Arena;
use sti::keyed::KVec;

use crate::env::SymbolId;
use crate::tt::{Term, LocalVarId};


sti::define_key!(pub, u32, BlockId, dsp: "bb{}");

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
    Dead(LocalVarId),
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



impl<'a> core::fmt::Display for Path<'a> {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        write!(f, "${}", self.base.inner())?;
        for proj in self.projs {
            match proj {
                Proj::Deref => write!(f, ".*")?,
            }
        }
        Ok(())
    }
}

impl<'a> core::fmt::Display for Stmt<'a> {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        match self {
            Stmt::Error => write!(f, "error"),
            Stmt::Axiom => write!(f, "axiom"),
            Stmt::Pop => write!(f, "pop"),
            Stmt::Dead(it) => write!(f, "dead ${}", it.inner()),
            Stmt::Const(_) => write!(f, "const ?"),
            Stmt::ConstUnit => write!(f, "const ()"),
            Stmt::ConstBool(it) => write!(f, "const {it}"),
            Stmt::ConstNat(it) => write!(f, "const {it}"),
            Stmt::Ref(it) => write!(f, "ref {it}"),
            Stmt::Read(it) => write!(f, "read {it}"),
            Stmt::Write(it) => write!(f, "write {it}"),
            Stmt::Call { func, num_args } => write!(f, "call {func:?}({num_args})"),
        }
    }
}

impl core::fmt::Display for Terminator {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        match self {
            Terminator::Jump { target } =>
                write!(f, "jump {}", target),

            Terminator::Ite { on_true, on_false } =>
                write!(f, "ite {} {}", on_true, on_false),

            Terminator::Return =>
                write!(f, "ret"),
        }
    }
}

impl<'a> core::fmt::Display for Block<'a> {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        for stmt in self.stmts {
            writeln!(f, "  {}", stmt)?;
        }
        writeln!(f, "  {}", self.terminator)?;
        Ok(())
    }
}

