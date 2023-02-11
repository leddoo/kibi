use core::cell::Cell;
use derive_more::{Deref, DerefMut};
use super::*;



// ### Statement ###

#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct StmtId(pub u32); // @temp

#[derive(Clone, Copy, Deref)]
#[repr(transparent)]
pub struct StmtRef<'a>(&'a Cell<Stmt<'a>>);


#[derive(Clone, Copy, Debug, Deref, DerefMut)]
pub struct Stmt<'a> {
    #[deref]
    #[deref_mut]
    pub data:   StmtData<'a>,
    pub id:     StmtId,
    pub source: SourceRange,
}

#[derive(Clone, Copy, Debug)]
pub enum StmtData<'a> {
    Copy        { src: StmtRef<'a> },

    Phi         { map: &'a [Cell<(BlockId, StmtRef<'a>)>] },

    GetLocal    { src: LocalId },
    SetLocal    { dst: LocalId, src: StmtRef<'a> },

    LoadNil,
    LoadBool    { value: bool },
    LoatInt     { value: i64 },
    LoadFloat   { value: f64 },

    Op1         { op: Op1, src: StmtRef<'a> },
    Op2         { op: Op2, src1: StmtRef<'a>, src2: StmtRef<'a> },

    Jump        { target: BlockId },
    SwitchBool  { src: StmtRef<'a>, on_true: BlockId, on_false: BlockId },
    Return      { src: StmtRef<'a> },
}



// ### Block ###

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BlockId(pub u32); // @temp

#[derive(Clone, Debug)]
pub struct Block<'a> {
    pub id: BlockId,
    pub statements: Vec<StmtRef<'a>>,
}



// ### Local ###

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LocalId(u32);



// ### Function ###

pub struct Function<'a> {
    // @temp
    pub blocks:     Vec<Block<'a>>,
    pub stmts:      Vec<StmtRef<'a>>,
    pub next_local: LocalId,
}



// --- StmtId ---

impl StmtId {
    #[inline(always)]
    pub fn usize(self) -> usize { self.0 as usize }
}



// --- StmtRef ---

impl<'a> StmtRef<'a> {
    #[inline(always)]
    pub fn id(self) -> StmtId { self.get().id }
}

impl<'a> core::fmt::Debug for StmtRef<'a> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.get().fmt(f)
    }
}

impl<'a> PartialEq for StmtRef<'a> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        core::ptr::eq(self.0, other.0)
    }
}

impl<'a> Eq for StmtRef<'a> {}

impl<'a> core::hash::Hash for StmtRef<'a> {
    #[inline]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        core::ptr::hash(self.0, state)
    }
}

impl<'a> core::fmt::Display for StmtRef<'a> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.get().fmt(f)
    }
}



// --- Stmt ---

impl<'a> core::fmt::Display for Stmt<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "r{} := ", self.id.0)?;

        use StmtData::*;
        match &self.data {
            Copy { src } => { write!(f, "copy r{}", src.get().id.0) }

            Phi { map } => {
                write!(f, "phi {{")?;
                for (i, (bb, src)) in map.iter().map(|e| e.get()).enumerate() {
                    write!(f, "{}: r{}", bb, src.get().id.0)?;

                    if i < map.len() - 1 { write!(f, ", ")?; }
                }
                write!(f, "}}")
            }

            GetLocal { src }      => { write!(f, "get_local {}", src) }
            SetLocal { dst, src } => { write!(f, "set_local {}, r{}", dst, src.get().id.0) }

            LoadNil             => { write!(f, "load_nil") }
            LoadBool  { value } => { write!(f, "load_bool {}", value) }
            LoatInt   { value } => { write!(f, "load_int {}", value) }
            LoadFloat { value } => { write!(f, "load_float {}", value) }

            Op1 { op, src }        => { write!(f, "{} r{}",      op.str(), src.get().id.0) }
            Op2 { op, src1, src2 } => { write!(f, "{} r{}, r{}", op.str(), src1.get().id.0, src2.get().id.0) }

            Jump       { target }                 => { write!(f, "jump {}", target) }
            SwitchBool { src, on_true, on_false } => { write!(f, "switch_bool r{}, {}, {}", src.get().id.0, on_true, on_false) }
            Return     { src }                    => { write!(f, "return r{}", src.get().id.0) }
        }
    }
}



// --- StmtData ---

impl<'a> StmtData<'a> {
    #[inline(always)]
    pub fn is_copy(&self) -> bool {
        if let StmtData::Copy { src: _ } = self { true } else { false }
    }

    #[inline(always)]
    pub fn is_phi(&self) -> bool {
        if let StmtData::Phi { map: _ } = self { true } else { false }
    }

    #[inline(always)]
    pub fn is_terminator(&self) -> bool {
        use StmtData::*;
        match self {
            Jump { target: _ } |
            SwitchBool { src: _, on_true: _, on_false: _ } |
            Return { src: _ } => true,

            Copy { src: _ } |
            Phi { map: _ } |
            GetLocal { src: _ } |
            LoadNil |
            LoadBool { value: _ } |
            LoatInt { value: _ } |
            LoadFloat { value: _ } |
            Op1 { op: _, src: _ } |
            Op2 { op: _, src1: _, src2: _ } |
            SetLocal { dst: _, src: _ } => false,
        }
    }

    #[inline(always)]
    pub fn has_value(&self) -> bool {
        use StmtData::*;
        match self {
            Copy { src: _ } |
            Phi { map: _ } |
            GetLocal { src: _ } |
            LoadNil |
            LoadBool { value: _ } |
            LoatInt { value: _ } |
            LoadFloat { value: _ } |
            Op1 { op: _, src: _ } |
            Op2 { op: _, src1: _, src2: _ } => true,

            SetLocal { dst: _, src: _ } |
            Jump { target: _ } |
            SwitchBool { src: _, on_true: _, on_false: _ } |
            Return { src: _ } => false,
        }
    }

    #[inline]
    pub fn args<F: FnMut(StmtRef<'a>)>(&self, mut f: F) {
        use StmtData::*;
        match self {
            Copy { src } => { f(*src) }

            Phi { map } => { for entry in *map { f(entry.get().1) } }

            GetLocal { src: _ } => (),
            SetLocal { dst: _, src } => { f(*src) }

            LoadNil |
            LoadBool  { value: _ } |
            LoatInt   { value: _ } |
            LoadFloat { value: _ } => (),

            Op1 { op: _, src }        => { f(*src) }
            Op2 { op: _, src1, src2 } => { f(*src1); f(*src2) }

            Jump       { target: _ } => (),
            SwitchBool { src, on_true: _, on_false: _ } => { f(*src) }
            Return     { src }                          => { f(*src) },
        }
    }

    #[inline]
    pub fn replace_args<F: FnMut(&mut StmtRef<'a>)>(&mut self, mut f: F) {
        use StmtData::*;
        match self {
            Copy { src } => { f(src) }

            Phi { map } => {
                for entry in *map {
                    let (bb, mut arg) = entry.get();
                    f(&mut arg);
                    entry.set((bb, arg));
                }
            }

            GetLocal { src: _ } => (),
            SetLocal { dst: _, src } => { f(src) }

            LoadNil |
            LoadBool  { value: _ } |
            LoatInt   { value: _ } |
            LoadFloat { value: _ } => (),


            Op1 { op: _, src }        => { f(src) }
            Op2 { op: _, src1, src2 } => { f(src1); f(src2) }

            Jump       { target: _ } => (),
            SwitchBool { src, on_true: _, on_false: _ } => { f(src) }
            Return     { src }                          => { f(src) },
        }
    }
}



// --- BlockId ---

impl BlockId {
    pub const ENTRY: BlockId = BlockId(0);

    #[inline(always)]
    pub fn is_entry(self) -> bool { self == BlockId::ENTRY }

    #[inline(always)]
    pub fn usize(self) -> usize { self.0 as usize }
}

impl core::fmt::Display for BlockId {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "bb{}", self.0)
    }
}



// --- Block ---

impl<'a> Block<'a> {
    pub fn new(id: BlockId) -> Self {
        Block {
            id,
            statements: vec![],
        }
    }

    #[inline]
    pub fn terminated(&self) -> bool {
        if let Some(last) = self.statements.last() {
            last.get().is_terminator()
        }
        else { false }
    }

    #[inline]
    pub fn successors<F: FnMut(BlockId)>(&self, mut f: F) {
        let Some(last) = self.statements.last() else { return };

        use StmtData::*;
        match last.get().data {
            Jump { target } => { f(target); }
            SwitchBool { src: _, on_true, on_false } => { f(on_true); f(on_false); }
            Return { src: _ } => {}

            _ => { unreachable!("called successors on unterminated block") }
        }
    }

    #[inline]
    pub fn args<F: FnMut(StmtRef<'a>)>(&self, mut f: F) {
        for stmt in &self.statements {
            stmt.get().args(&mut f);
        }
    }

    #[inline]
    pub fn replace_args<F: FnMut(&mut StmtRef<'a>)>(&mut self, mut f: F) {
        for stmt_ref in &self.statements {
            let mut stmt = stmt_ref.get();
            stmt.replace_args(&mut f);
            stmt_ref.set(stmt);
        }
    }
}

impl<'a> core::fmt::Display for Block<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:\n", self.id)?;

        for stmt in &self.statements {
            write!(f, "  {}\n", *stmt)?;
        }

        Ok(())
    }
}



// --- LocalId ---

impl LocalId {
    #[inline(always)]
    pub fn usize(self) -> usize { self.0 as usize }
}

impl core::fmt::Display for LocalId {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "l{}", self.0)
    }
}



// --- Function ---

impl<'a> Function<'a> {
    pub fn new() -> Self {
        Function {
            blocks:     vec![],
            stmts:      vec![],
            next_local: LocalId(0),
        }
    }


    pub fn new_local(&mut self) -> LocalId {
        let id = self.next_local;
        self.next_local.0 += 1;
        id
    }


    pub fn new_stmt_at(&mut self, source: SourceRange, data: StmtData<'a>) -> StmtRef<'a> {
        let id = StmtId(self.stmts.len() as u32);
        let rf = StmtRef(Box::leak(Box::new(Cell::new(Stmt { id, source, data }))));
        self.stmts.push(rf);
        rf
    }

    pub fn add_stmt_at(&mut self, bb: BlockId, source: SourceRange, data: StmtData<'a>) -> StmtRef<'a> {
        let stmt = self.new_stmt_at(source, data);

        let block = &mut self.blocks[bb.0 as usize];
        assert!(!block.terminated());
        block.statements.push(stmt);
        stmt
    }

    pub fn add_stmt(&mut self, bb: BlockId, at: &Ast, data: StmtData<'a>) -> StmtRef<'a> {
        self.add_stmt_at(bb, at.source, data)
    }


    pub fn new_block(&mut self) -> BlockId {
        let id = BlockId(self.blocks.len() as u32);
        self.blocks.push(Block::new(id));
        id
    }
}

