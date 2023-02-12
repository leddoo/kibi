use derive_more::{Deref, DerefMut};
use super::*;



// ### Statement ###

#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct StmtId(u32);


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
pub struct PhiMapId(u32);

#[derive(Deref, DerefMut)]
pub struct PhiMap {
    map: Vec<(BlockId, StmtId)>,
}



// ### Block ###

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BlockId(u32);

#[derive(Clone, Debug)]
pub struct Block {
    pub id: BlockId,
}



// ### Local ###

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LocalId(u32);


#[allow(dead_code)] // @temp
#[derive(Debug)]
struct Local {
    id:     LocalId,
    name:   String,
    source: SourceRange,
}



// ### Function ###

pub struct Function {
    pub blocks: Blocks,
    pub stmts:  Stmts,
    pub locals: Locals,
}

pub struct Blocks {
    blocks: Vec<Block>,
    stmts:  Vec<Vec<StmtId>>,
}

pub struct Stmts {
    stmts:    Vec<Stmt>,
    phi_maps: Vec<PhiMap>,
}

pub struct Locals {
    locals: Vec<Local>,
}



// ### Iterators ###

pub struct StmtIdIter { at: u32, end: u32 }

pub struct BlockIdIter { at: u32, end: u32 }

pub struct BlockIter<'a> { blocks: &'a [Block] }

pub struct BlockStmtIter<'a> { stmts: &'a [StmtId] }

pub struct BlockStmtIterRev<'a> { stmts: &'a [StmtId] }




// --- StmtId ---

impl StmtId {
    #[inline(always)]
    pub fn usize(self) -> usize { self.0 as usize }

    #[inline(always)]
    pub fn get(self, fun: &Function) -> &Stmt { &fun.stmts.stmts[self.usize()] }
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
    pub fn args<F: FnMut(StmtId)>(&self, stmts: &Stmts, mut f: F) {
        use StmtData::*;
        match self {
            Copy { src } => { f(*src) }

            Phi { map_id: map } => { for (_, src) in &*stmts.phi_maps[map.usize()] { f(*src) } }

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
    pub fn replace_args<F: FnMut(&Stmts, &mut StmtId)>(&mut self, stmts: &mut Stmts, mut f: F) {
        use StmtData::*;
        match self {
            Copy { src } => { f(stmts, src) }

            Phi { map_id } => {
                let mut map = core::mem::take(&mut *stmts.phi_maps[map_id.usize()]);
                for (_, src) in &mut map {
                    f(stmts, src)
                }
                stmts.phi_maps[map_id.usize()] = PhiMap { map };
            }

            GetLocal { src: _ } => (),
            SetLocal { dst: _, src } => { f(stmts, src) }

            LoadNil |
            LoadBool  { value: _ } |
            LoatInt   { value: _ } |
            LoadFloat { value: _ } => (),


            Op1 { op: _, src }        => { f(stmts, src) }
            Op2 { op: _, src1, src2 } => { f(stmts, src1); f(stmts, src2) }

            Jump       { target: _ } => (),
            SwitchBool { src, on_true: _, on_false: _ } => { f(stmts, src) }
            Return     { src }                          => { f(stmts, src) },
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
            blocks: Blocks { blocks: vec![], stmts: vec![] },
            stmts:  Stmts { stmts: vec![], phi_maps: vec![] },
            locals: Locals { locals: vec![] },
        }
    }


    pub fn add_stmt_at(&mut self, bb: BlockId, source: SourceRange, data: StmtData) -> StmtId {
        let stmt = self.stmts.new(source, data);

        let stmts = &mut self.blocks.stmts[bb.usize()];
        if let Some(last) = stmts.last() {
            assert!(!self.stmts.stmts[last.usize()].is_terminator());
        }
        stmts.push(stmt);
        stmt
    }

    pub fn add_stmt(&mut self, bb: BlockId, at: &Ast, data: StmtData) -> StmtId {
        self.add_stmt_at(bb, at.source, data)
    }


    pub fn add_phi(&mut self, bb: BlockId, at: &Ast, map: &[(BlockId, StmtId)]) -> StmtId {
        let map_id = PhiMapId(self.stmts.phi_maps.len() as u32);
        self.stmts.phi_maps.push(PhiMap { map: map.into() });
        self.add_stmt(bb, at, StmtData::Phi { map_id })
    }


    #[inline]
    pub fn block_successors<F: FnMut(BlockId)>(&self, bb: BlockId, mut f: F) {
        let stmts = &self.blocks.stmts[bb.usize()];

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
        for stmt_id in &self.blocks.stmts[bb.usize()] {
            self.stmts.stmts[stmt_id.usize()].args(&self.stmts, &mut f);
        }
    }

    #[inline]
    pub fn block_replace_args<F: FnMut(&Stmts, &mut StmtId)>(&mut self, bb: BlockId, mut f: F) {
        for stmt_id in &self.blocks.stmts[bb.usize()] {
            let mut data = self.stmts.stmts[stmt_id.usize()].data;
            data.replace_args(&mut self.stmts, &mut f);
            self.stmts.stmts[stmt_id.usize()].data = data;
        }
    }

    #[inline]
    pub fn all_args<F: FnMut(StmtId)>(&self, mut f: F) {
        for stmt_ids in self.blocks.stmts.iter() {
            for stmt_id in stmt_ids.iter() {
                self.stmts.stmts[stmt_id.usize()].args(&self.stmts, &mut f);
            }
        }
    }


    pub fn dump(&self) {
        for bb in self.blocks.ids() {
            println!("{}:", bb);
            for stmt_id in self.blocks.stmts(bb) {
                println!("  {}", self.stmts.get(stmt_id));
            }
        }
    }
}


impl Blocks {
    pub fn new(&mut self) -> BlockId {
        let id = BlockId(self.blocks.len() as u32);
        self.blocks.push(Block::new(id));
        self.stmts.push(vec![]);
        id
    }


    #[inline(always)]
    pub fn id_from_usize(&self, id: usize) -> BlockId {
        debug_assert!(id < self.blocks.len());
        BlockId(id as u32)
    }


    #[inline(always)]
    pub fn len(&self) -> usize { self.blocks.len() }

    #[inline(always)]
    pub fn ids(&self) -> BlockIdIter { BlockIdIter { at: 0, end: self.blocks.len() as u32 } }

    #[inline(always)]
    pub fn iter(&self) -> BlockIter { BlockIter { blocks: &self.blocks } }

    #[inline(always)]
    pub fn stmts(&self, bb: BlockId) -> BlockStmtIter { BlockStmtIter { stmts: &self.stmts[bb.usize()] } }

    #[inline(always)]
    pub fn stmts_rev(&self, bb: BlockId) -> BlockStmtIterRev { BlockStmtIterRev { stmts: &self.stmts[bb.usize()] } }


    // @temp
    #[inline(always)]
    pub fn _stmts(&self) -> &Vec<Vec<StmtId>> { &self.stmts }
    // @temp
    #[inline(always)]
    pub fn _stmts_mut(&mut self) -> &mut Vec<Vec<StmtId>> { &mut self.stmts }
}


impl Stmts {
    pub fn new(&mut self, source: SourceRange, data: StmtData) -> StmtId {
        let id = StmtId(self.stmts.len() as u32);
        self.stmts.push(Stmt { id, source, data });
        id
    }

    pub fn new_phi(&mut self, source: SourceRange, map: &[(BlockId, StmtId)]) -> StmtId {
        let map_id = PhiMapId(self.phi_maps.len() as u32);
        self.phi_maps.push(PhiMap { map: map.into() });
        self.new(source, StmtData::Phi { map_id })
    }


    #[inline(always)]
    pub fn id_from_usize(&self, id: usize) -> StmtId {
        debug_assert!(id < self.stmts.len());
        StmtId(id as u32)
    }


    #[inline(always)]
    pub fn len(&self) -> usize { self.stmts.len() }

    #[inline(always)]
    pub fn ids(&self) -> StmtIdIter { StmtIdIter { at: 0, end: self.stmts.len() as u32 } }

    #[inline(always)]
    pub fn get(&self, stmt: StmtId) -> &Stmt { &self.stmts[stmt.usize()] }

    #[inline(always)]
    pub fn get_mut(&mut self, stmt: StmtId) -> &mut Stmt { &mut self.stmts[stmt.usize()] }


    pub fn phi_map(&self, stmt: StmtId) -> &[(BlockId, StmtId)] {
        let StmtData::Phi { map_id } = self.stmts[stmt.usize()].data else { unreachable!() };
        &self.phi_maps[map_id.usize()]
    }

    pub fn set_phi_map(&mut self, stmt: StmtId, map: &[(BlockId, StmtId)]) {
        let StmtData::Phi { map_id } = self.stmts[stmt.usize()].data else { unreachable!() };
        self.phi_maps[map_id.usize()] = PhiMap { map: map.into() };
    }
}

impl Locals {
    pub fn new(&mut self, name: &str, source: SourceRange) -> LocalId {
        let id = LocalId(self.locals.len() as u32);
        self.locals.push(Local { id, name: name.into(), source });
        id
    }


    #[inline]
    pub fn len(&self) -> usize { self.locals.len() }
}



// --- Iterators ---

impl Iterator for StmtIdIter {
    type Item = StmtId;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        if self.at < self.end {
            let result = StmtId(self.at);
            self.at += 1;
            return Some(result);
        }
        None
    }
}


impl Iterator for BlockIdIter {
    type Item = BlockId;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        if self.at < self.end {
            let result = BlockId(self.at);
            self.at += 1;
            return Some(result);
        }
        None
    }
}


impl<'a> Iterator for BlockIter<'a> {
    type Item = &'a Block;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        let (head, tail) = self.blocks.split_first()?;
        self.blocks = tail;
        Some(head)
    }
}


impl<'a> Iterator for BlockStmtIter<'a> {
    type Item = StmtId;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        let (head, tail) = self.stmts.split_first()?;
        self.stmts = tail;
        Some(*head)
    }
}


impl<'a> Iterator for BlockStmtIterRev<'a> {
    type Item = StmtId;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        let (tail, head) = self.stmts.split_last()?;
        self.stmts = head;
        Some(*tail)
    }
}

