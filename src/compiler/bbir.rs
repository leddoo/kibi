use derive_more::{Deref, DerefMut};
use super::*;



// ### Statement ###

#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct StmtId(pub(crate) u32);


#[derive(Clone, Debug, Deref, DerefMut)]
pub struct Stmt {
    #[deref] #[deref_mut]
    pub data:   StmtData,
    pub id:     StmtId,
    pub source: SourceRange,
}

#[derive(Clone, Copy, Debug)]
pub enum StmtData {
    Copy        { src: StmtId },

    Phi         { map_id: PhiMapId },

    GetLocal    { src: LocalId },
    SetLocal    { dst: LocalId, src: StmtId },

    LoadNil,
    LoadBool    { value: bool },
    LoatInt     { value: i64 },
    LoadFloat   { value: f64 },

    Op1         { op: Op1, src: StmtId },
    Op2         { op: Op2, src1: StmtId, src2: StmtId },

    Jump        { target: BlockId },
    SwitchBool  { src: StmtId, on_true: BlockId, on_false: BlockId },
    Return      { src: StmtId },
}


#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct PhiMapId(pub(crate) u32);

#[derive(Deref, DerefMut)]
pub struct PhiMap {
    pub(crate) map: Vec<(BlockId, StmtId)>,
}



// ### Block ###

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BlockId(pub u32); // @temp

#[derive(Clone, Debug)]
pub struct Block {
    pub id: BlockId,
}



// ### Local ###

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LocalId(u32);



// ### Function ###

pub struct Function {
    // @temp: pub
    pub blocks:     Vec<Block>,
    pub stmts:      Vec<Stmt>,
    pub next_local: LocalId,
    pub phi_maps:   Vec<PhiMap>,
    // @temp: linked lists
    pub block_stmts: Vec<Vec<StmtId>>,
}



// --- StmtId ---

impl StmtId {
    #[inline(always)]
    pub fn usize(self) -> usize { self.0 as usize }

    #[inline(always)]
    pub fn get(self, fun: &Function) -> &Stmt { &fun.stmts[self.usize()] }
}

impl core::fmt::Display for StmtId {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "r{}", self.0)
    }
}



// --- Stmt ---

impl core::fmt::Display for Stmt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "r{} := ", self.id.0)?;

        use StmtData::*;
        match &self.data {
            Copy { src } => { write!(f, "copy {}", src) }

            Phi { map_id: map } => {
                write!(f, "phi p{}", map.0)
            }

            GetLocal { src }      => { write!(f, "get_local {}", src) }
            SetLocal { dst, src } => { write!(f, "set_local {}, {}", dst, src) }

            LoadNil             => { write!(f, "load_nil") }
            LoadBool  { value } => { write!(f, "load_bool {}", value) }
            LoatInt   { value } => { write!(f, "load_int {}", value) }
            LoadFloat { value } => { write!(f, "load_float {}", value) }

            Op1 { op, src }        => { write!(f, "{} {}",     op.str(), src) }
            Op2 { op, src1, src2 } => { write!(f, "{} {}, {}", op.str(), src1, src2) }

            Jump       { target }                 => { write!(f, "jump {}", target) }
            SwitchBool { src, on_true, on_false } => { write!(f, "switch_bool {}, {}, {}", src, on_true, on_false) }
            Return     { src }                    => { write!(f, "return {}", src) }
        }
    }
}



// --- StmtData ---

impl StmtData {
    #[inline(always)]
    pub fn is_copy(&self) -> bool {
        if let StmtData::Copy { src: _ } = self { true } else { false }
    }

    #[inline(always)]
    pub fn is_phi(&self) -> bool {
        if let StmtData::Phi { map_id: _ } = self { true } else { false }
    }

    #[inline(always)]
    pub fn is_terminator(&self) -> bool {
        use StmtData::*;
        match self {
            Jump { target: _ } |
            SwitchBool { src: _, on_true: _, on_false: _ } |
            Return { src: _ } => true,

            Copy { src: _ } |
            Phi { map_id: _ } |
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
            Phi { map_id: _ } |
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
    pub fn args<F: FnMut(StmtId)>(&self, phi_maps: &[PhiMap], mut f: F) {
        use StmtData::*;
        match self {
            Copy { src } => { f(*src) }

            Phi { map_id: map } => { for (_, src) in &*phi_maps[map.usize()] { f(*src) } }

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
    pub fn replace_args<F: FnMut(&mut StmtId)>(&mut self, phi_maps: &mut [PhiMap], mut f: F) {
        use StmtData::*;
        match self {
            Copy { src } => { f(src) }

            Phi { map_id: map } => {
                for (_, src) in &mut *phi_maps[map.usize()] {
                    f(src)
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

impl PhiMapId {
    #[inline(always)]
    pub fn usize(self) -> usize { self.0 as usize }
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

impl Block {
    pub fn new(id: BlockId) -> Self {
        Block {
            id,
        }
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

impl Function {
    pub fn new() -> Self {
        Function {
            blocks:     vec![],
            stmts:      vec![],
            next_local: LocalId(0),
            phi_maps:   vec![],
            block_stmts: vec![],
        }
    }


    pub fn new_local(&mut self) -> LocalId {
        let id = self.next_local;
        self.next_local.0 += 1;
        id
    }


    pub fn new_stmt_at(&mut self, source: SourceRange, data: StmtData) -> StmtId {
        let id = StmtId(self.stmts.len() as u32);
        self.stmts.push(Stmt { id, source, data });
        id
    }

    pub fn add_stmt_at(&mut self, bb: BlockId, source: SourceRange, data: StmtData) -> StmtId {
        let stmt = self.new_stmt_at(source, data);

        let stmts = &mut self.block_stmts[bb.usize()];
        if let Some(last) = stmts.last() {
            assert!(!self.stmts[last.usize()].is_terminator());
        }
        stmts.push(stmt);
        stmt
    }

    pub fn add_stmt(&mut self, bb: BlockId, at: &Ast, data: StmtData) -> StmtId {
        self.add_stmt_at(bb, at.source, data)
    }


    pub fn new_block(&mut self) -> BlockId {
        let id = BlockId(self.blocks.len() as u32);
        self.blocks.push(Block::new(id));
        self.block_stmts.push(vec![]);
        id
    }


    #[inline]
    pub fn block_successors<F: FnMut(BlockId)>(&self, bb: BlockId, mut f: F) {
        let stmts = &self.block_stmts[bb.usize()];

        let Some(last) = stmts.last() else { return };

        use StmtData::*;
        match last.get(self).data {
            Jump { target } => { f(target); }
            SwitchBool { src: _, on_true, on_false } => { f(on_true); f(on_false); }
            Return { src: _ } => {}

            _ => { unreachable!("called successors on unterminated block") }
        }
    }

    #[inline]
    pub fn block_args<F: FnMut(StmtId)>(&self, bb: BlockId, mut f: F) {
        for stmt_id in &self.block_stmts[bb.usize()] {
            self.stmts[stmt_id.usize()].args(&self.phi_maps, &mut f);
        }
    }

    #[inline]
    pub fn block_replace_args<F: FnMut(&mut StmtId)>(&mut self, bb: BlockId, mut f: F) {
        for stmt_id in &self.block_stmts[bb.usize()] {
            self.stmts[stmt_id.usize()].replace_args(&mut self.phi_maps, &mut f);
        }
    }

    #[inline]
    pub fn block_replace_args_ex<F: FnMut(&[Stmt], &mut StmtId)>(&mut self, bb: BlockId, mut f: F) {
        for stmt_id in &self.block_stmts[bb.usize()] {
            let mut data = self.stmts[stmt_id.usize()].data;
            data.replace_args(&mut self.phi_maps, |arg| f(&self.stmts, arg));
            self.stmts[stmt_id.usize()].data = data;
        }
    }

    #[inline]
    pub fn all_args<F: FnMut(StmtId)>(&self, mut f: F) {
        for stmt_ids in self.block_stmts.iter() {
            for stmt_id in stmt_ids.iter() {
                self.stmts[stmt_id.usize()].args(&self.phi_maps, &mut f);
            }
        }
    }
}

