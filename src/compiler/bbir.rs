use derive_more::{Deref, DerefMut};
use super::*;



// ### Statement ###

#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct StmtId(u32);

#[derive(Clone, Copy, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct OptStmtId(u32);


#[derive(Clone, Debug, Deref, DerefMut)]
pub struct Stmt {
    #[deref] #[deref_mut]
    pub data:   StmtData,
    pub source: SourceRange,
    id:         StmtId,
    prev:       OptStmtId,
    next:       OptStmtId,
    bb:         OptBlockId,
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
struct PhiMapImpl {
    map: Vec<(BlockId, StmtId)>,
}

#[derive(Clone, Copy, Debug, Deref)]
pub struct PhiMap<'a> {
    pub map: &'a [(BlockId, StmtId)],
}



// ### Block ###

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BlockId(u32);

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct OptBlockId(u32);


#[derive(Clone, Debug)]
pub struct Block {
    id: BlockId,
    first: OptStmtId,
    last:  OptStmtId,
    len: u32,
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
    stmts:      Vec<Stmt>,
    phi_maps:   Vec<PhiMapImpl>,
    blocks:     Vec<Block>,
    locals:     Vec<Local>,
}



// ### Iterators ###

pub struct StmtIdIter { at: u32, end: u32 }

pub struct BlockIdIter { at: u32, end: u32 }



// --- StmtId ---

impl StmtId {
    #[inline(always)]
    pub const fn usize(self) -> usize { self.0 as usize }

    #[inline(always)]
    pub fn from_usize(index: usize) -> StmtId {
        assert!(index < u32::MAX as usize / 2);
        StmtId(index as u32)
    }

    #[inline(always)]
    pub fn get(self, fun: &Function) -> &Stmt { &fun.stmts[self.usize()] }

    #[inline(always)]
    pub const fn some(self) -> OptStmtId { OptStmtId(self.0) }
}

impl core::fmt::Display for StmtId {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "r{}", self.0)
    }
}


impl OptStmtId {
    pub const NONE: OptStmtId = OptStmtId(u32::MAX);

    #[inline(always)]
    pub fn to_option(self) -> Option<StmtId> {
        (self != Self::NONE).then_some(StmtId(self.0))
    }
}

impl core::fmt::Debug for OptStmtId {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { self.to_option().fmt(f) }
}



// --- Stmt ---

impl Stmt {
    #[inline(always)] pub fn id(&self)   -> StmtId     { self.id }
    #[inline(always)] pub fn prev(&self) -> OptStmtId  { self.prev }
    #[inline(always)] pub fn next(&self) -> OptStmtId  { self.next }
    #[inline(always)] pub fn bb(&self)   -> OptBlockId { self.bb }

    #[inline(always)]
    pub fn read(&self) -> (StmtId, StmtData) { (self.id, self.data) }
}

impl core::fmt::Display for Stmt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} := ", self.id)?;

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
    pub fn args<F: FnMut(StmtId)>(&self, fun: &Function, mut f: F) {
        use StmtData::*;
        match self {
            Copy { src } => { f(*src) }

            Phi { map_id: map } => { for (_, src) in &*fun.phi_maps[map.usize()] { f(*src) } }

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
    pub fn replace_args<F: FnMut(&Function, &mut StmtId)>(&mut self, fun: &mut Function, mut f: F) {
        use StmtData::*;
        match self {
            Copy { src } => { f(fun, src) }

            Phi { map_id } => {
                let mut map = core::mem::take(&mut *fun.phi_maps[map_id.usize()]);
                for (_, src) in &mut map {
                    f(fun, src)
                }
                fun.phi_maps[map_id.usize()] = PhiMapImpl { map };
            }

            GetLocal { src: _ } => (),
            SetLocal { dst: _, src } => { f(fun, src) }

            LoadNil |
            LoadBool  { value: _ } |
            LoatInt   { value: _ } |
            LoadFloat { value: _ } => (),


            Op1 { op: _, src }        => { f(fun, src) }
            Op2 { op: _, src1, src2 } => { f(fun, src1); f(fun, src2) }

            Jump       { target: _ } => (),
            SwitchBool { src, on_true: _, on_false: _ } => { f(fun, src) }
            Return     { src }                          => { f(fun, src) },
        }
    }
}


impl PhiMapId {
    #[inline(always)]
    pub fn usize(self) -> usize { self.0 as usize }

    #[inline]
    pub fn get<'s>(self, fun: &'s Function) -> PhiMap<'s> {
        PhiMap { map: &fun.phi_maps[self.usize()] }
    }
}

impl<'a> PhiMap<'a> {
    pub fn get(self, bb: BlockId) -> Option<StmtId> {
        self.iter().find_map(|(from_bb, stmt_id)|
            (*from_bb == bb).then_some(*stmt_id))
    }
}



// --- BlockId ---

impl BlockId {
    pub const ENTRY: BlockId = BlockId(0);

    #[inline(always)]
    pub fn is_entry(self) -> bool { self == BlockId::ENTRY }


    #[inline(always)]
    pub const fn usize(self) -> usize { self.0 as usize }

    #[inline(always)]
    pub fn from_usize(index: usize) -> BlockId {
        assert!(index < u32::MAX as usize / 2);
        BlockId(index as u32)
    }

    #[inline(always)]
    pub const fn some(self) -> OptBlockId { OptBlockId(self.0) }
}

impl core::fmt::Display for BlockId {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "bb{}", self.0)
    }
}


impl OptBlockId {
    pub const NONE: OptBlockId = OptBlockId(u32::MAX);

    #[inline(always)]
    pub fn to_option(self) -> Option<BlockId> {
        (self != Self::NONE).then_some(BlockId(self.0))
    }
}

impl core::fmt::Debug for OptBlockId {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { self.to_option().fmt(f) }
}



// --- Block ---

impl Block {
    #[inline]
    pub fn new(id: BlockId) -> Self {
        Block {
            id,
            first: OptStmtId::NONE,
            last:  OptStmtId::NONE,
            len:   0,
        }
    }

    #[inline(always)] pub fn id(&self)    -> BlockId   { self.id }
    #[inline(always)] pub fn first(&self) -> OptStmtId { self.first }
    #[inline(always)] pub fn last(&self)  -> OptStmtId { self.last }
    #[inline(always)] pub fn len(&self)   -> usize     { self.len as usize }
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


// common
impl Function {
    pub fn new() -> Self {
        Function {
            stmts:      vec![],
            blocks:     vec![],
            phi_maps:   vec![],
            locals:     vec![],
        }
    }


    #[inline(always)]
    pub fn num_stmts(&self) -> usize { self.stmts.len() }

    #[inline(always)]
    pub fn stmt_ids(&self) -> StmtIdIter { StmtIdIter { at: 0, end: self.stmts.len() as u32 } }
    

    #[inline(always)]
    pub fn num_blocks(&self) -> usize { self.blocks.len() }

    #[inline(always)]
    pub fn block_ids(&self) -> BlockIdIter { BlockIdIter { at: 0, end: self.blocks.len() as u32 } }


    #[inline(always)]
    pub fn num_locals(&self) -> usize { self.locals.len() }
}


// statements
impl Function {
    pub fn new_stmt(&mut self, source: SourceRange, data: StmtData) -> StmtId {
        let id = StmtId(self.stmts.len() as u32);
        self.stmts.push(Stmt {
            data, source, id,
            prev: OptStmtId::NONE,
            next: OptStmtId::NONE,
            bb:   OptBlockId::NONE,
        });
        id
    }


    pub fn new_phi(&mut self, source: SourceRange, map: &[(BlockId, StmtId)]) -> StmtId {
        let map_id = PhiMapId(self.phi_maps.len() as u32);
        self.phi_maps.push(PhiMapImpl { map: map.into() });
        self.new_stmt(source, StmtData::Phi { map_id })
    }

    pub fn try_phi(&self, stmt: StmtId) -> Option<PhiMap> {
        if let StmtData::Phi { map_id } = self.stmts[stmt.usize()].data {
            return Some(PhiMap { map: &*self.phi_maps[map_id.usize()] });
        }
        None
    }

    // @todo: support Phi2.
    // @todo: def_phi variant.
    pub fn set_phi(&mut self, stmt: StmtId, map: &[(BlockId, StmtId)]) {
        let StmtData::Phi { map_id } = self.stmts[stmt.usize()].data else { unreachable!() };
        self.phi_maps[map_id.usize()] = PhiMapImpl { map: map.into() };
    }
    


    #[inline]
    pub fn all_args<F: FnMut(StmtId)>(&self, mut f: F) {
        for block in &self.blocks {
            let mut at = block.first;
            while let Some(id) = at.to_option() {
                let stmt = &self.stmts[id.usize()];
                stmt.args(self, &mut f);
                at = stmt.next;
            }
        }
    }
}
    

// blocks
impl Function {
    pub fn new_block(&mut self) -> BlockId {
        let id = BlockId(self.blocks.len() as u32);
        self.blocks.push(Block::new(id));
        id
    }


    #[inline(always)]
    pub fn num_block_stmts(&self, bb: BlockId) -> usize {
        self.blocks[bb.usize()].len()
    }


    #[inline]
    pub fn block_stmts<F: FnMut(&Stmt)>(&self, bb: BlockId, mut f: F) {
        let mut at = self.blocks[bb.usize()].first;
        while let Some(id) = at.to_option() {
            let stmt = &self.stmts[id.usize()];
            f(stmt);
            at = stmt.next;
        }
    }

    #[inline]
    pub fn block_stmts_ex<F: FnMut(&Stmt) -> bool>(&self, bb: BlockId, mut f: F) {
        let mut at = self.blocks[bb.usize()].first;
        while let Some(id) = at.to_option() {
            let stmt = &self.stmts[id.usize()];
            if !f(stmt) {
                break;
            }
            at = stmt.next;
        }
    }

    #[inline]
    pub fn block_stmts_mut<F: FnMut(&mut Stmt)>(&mut self, bb: BlockId, mut f: F) {
        let mut at = self.blocks[bb.usize()].first;
        while let Some(id) = at.to_option() {
            let stmt = &mut self.stmts[id.usize()];
            f(stmt);
            at = stmt.next;
        }
    }

    #[inline]
    pub fn block_stmts_rev<F: FnMut(&Stmt)>(&self, bb: BlockId, mut f: F) {
        let mut at = self.blocks[bb.usize()].last;
        while let Some(id) = at.to_option() {
            let stmt = &self.stmts[id.usize()];
            f(stmt);
            at = stmt.prev;
        }
    }


    #[inline]
    pub fn block_args<F: FnMut(StmtId)>(&self, bb: BlockId, mut f: F) {
        let mut at = self.blocks[bb.usize()].first;
        while let Some(id) = at.to_option() {
            let stmt = &self.stmts[id.usize()];
            stmt.args(self, &mut f);
            at = stmt.next;
        }
    }

    #[inline]
    pub fn block_replace_args<F: FnMut(&Function, &mut StmtId)>(&mut self, bb: BlockId, mut f: F) {
        let mut at = self.blocks[bb.usize()].first;
        while let Some(id) = at.to_option() {
            let mut data = self.stmts[id.usize()].data;
            data.replace_args(self, &mut f);

            let stmt = &mut self.stmts[id.usize()];
            stmt.data = data;
            at = stmt.next;
        }
    }


    #[inline]
    pub fn block_successors<F: FnMut(BlockId)>(&self, bb: BlockId, mut f: F) {
        let block = &self.blocks[bb.usize()];

        let Some(last) = block.last.to_option() else { return };

        use StmtData::*;
        match last.get(self).data {
            Jump { target } => { f(target); }
            SwitchBool { src: _, on_true, on_false } => { f(on_true); f(on_false); }
            Return { src: _ } => {}

            _ => { unreachable!("called successors on unterminated block") }
        }
    }
}


// locals
impl Function {
    pub fn new_local(&mut self, name: &str, source: SourceRange) -> LocalId {
        let id = LocalId(self.locals.len() as u32);
        self.locals.push(Local { id, name: name.into(), source });
        id
    }
}


// builder
impl Function {
    pub fn add_stmt_at(&mut self, bb: BlockId, source: SourceRange, data: StmtData) -> StmtId {
        assert!(self.stmts.len() < u32::MAX as usize / 2);
        let id = StmtId(self.stmts.len() as u32);

        let block = &mut self.blocks[bb.usize()];
        let old_last = block.last;

        // update linked list.
        if let Some(last) = old_last.to_option() {
            let last = &mut self.stmts[last.usize()];
            assert!(!last.data.is_terminator());
            last.next  = id.some();
            block.last = id.some();
            block.len += 1;
        }
        else {
            assert!(block.first.to_option().is_none());
            block.first = id.some();
            block.last  = id.some();
            block.len   = 1;
        }

        self.stmts.push(Stmt {
            data, source, id,
            prev: old_last,
            next: OptStmtId::NONE,
            bb:   bb.some(),
        });

        id
    }

    pub fn add_stmt(&mut self, bb: BlockId, at: &Ast, data: StmtData) -> StmtId {
        self.add_stmt_at(bb, at.source, data)
    }


    pub fn add_phi(&mut self, bb: BlockId, at: &Ast, map: &[(BlockId, StmtId)]) -> StmtId {
        let map_id = PhiMapId(self.phi_maps.len() as u32);
        self.phi_maps.push(PhiMapImpl { map: map.into() });
        self.add_stmt(bb, at, StmtData::Phi { map_id })
    }
}


// mutation
impl Function {
    // todo: insert_before. still assert stmt not in block, to detect bugs.
    // stmt_id must not be in a block.
    pub fn prepend_stmt(&mut self, bb: BlockId, stmt_id: StmtId) {
        let block = &mut self.blocks[bb.usize()];
        let stmt  = &mut self.stmts[stmt_id.usize()];
        assert!(stmt.bb.to_option().is_none());
        debug_assert!(stmt.id == stmt_id);
        debug_assert!(stmt.prev.to_option().is_none());
        debug_assert!(stmt.next.to_option().is_none());

        let old_first = block.first;
        block.first = stmt_id.some();
        block.len  += 1;
        stmt.bb     = OptBlockId(block.id.0);
        stmt.prev   = OptStmtId::NONE;
        stmt.next   = old_first;

        if let Some(first) = old_first.to_option() {
            let stmt = &mut self.stmts[first.usize()];
            debug_assert!(stmt.prev.to_option().is_none());
            stmt.prev = stmt_id.some();
        }
    }

    fn remove_stmt(block: &mut Block, stmts: &mut Vec<Stmt>, stmt_index: usize) -> OptStmtId {
        let stmt = &mut stmts[stmt_index];
        assert!(stmt.bb == block.id.some());

        let old_prev = stmt.prev;
        let old_next = stmt.next;
        stmt.prev = OptStmtId::NONE;
        stmt.next = OptStmtId::NONE;
        stmt.bb   = OptBlockId::NONE;

        if let Some(prev) = old_prev.to_option() {
            stmts[prev.usize()].next = old_next;
        }
        else {
            block.first = old_next;
        }

        if let Some(next) = old_next.to_option() {
            stmts[next.usize()].prev = old_prev;
        }
        else {
            block.last = old_prev;
        }

        block.len -= 1;

        old_next
    }

    #[inline]
    pub fn retain_block_stmts<F: FnMut(&Stmt) -> bool>(&mut self, bb: BlockId, mut f: F) {
        let block = &mut self.blocks[bb.usize()];

        let mut at = block.first;
        while let Some(current) = at.to_option() {
            let stmt = &self.stmts[current.usize()];

            if !f(stmt) {
                at = Self::remove_stmt(block, &mut self.stmts, current.usize());
            }
            else {
                at = stmt.next;
            }
        }
    }

    #[inline]
    pub fn retain_stmts<F: FnMut(&Stmt) -> bool>(&mut self, mut f: F) {
        for bb in 0..self.blocks.len() as u32 {
            self.retain_block_stmts(BlockId(bb), &mut f);
        }
    }
}


// other
impl Function {
    pub fn slow_integrity_check(&self) {
        let mut visited = vec![false; self.stmts.len()];

        for bb in self.block_ids() {
            let block = &self.blocks[bb.usize()];
            assert_eq!(block.id, bb);

            let mut in_phis = true;
            let mut has_terminator = false;
            let mut stmt_count = 0;

            let mut at = block.first;
            while let Some(current) = at.to_option() {
                assert!(!visited[current.usize()]);
                visited[current.usize()] = true;

                stmt_count += 1;

                // ids.
                let stmt = &self.stmts[current.usize()];
                assert_eq!(stmt.id, current);
                assert_eq!(stmt.bb, bb.some());

                // linked list first.
                if current.some() == block.first {
                    assert_eq!(stmt.prev, OptStmtId::NONE);
                }

                // linked list last.
                if current.some() == block.last {
                    assert_eq!(stmt.next, OptStmtId::NONE);
                }
                else {
                    let next = stmt.next.to_option().unwrap();
                    let next = &self.stmts[next.usize()];
                    assert_eq!(next.prev, current.some());
                }

                // phis.
                if stmt.is_phi() { assert!(in_phis); }
                else { in_phis = false; }

                // terminator.
                if stmt.is_terminator() {
                    assert!(!has_terminator);
                    has_terminator = true;
                }

                at = stmt.next;
            }

            assert_eq!(stmt_count, block.len());

            if block.first == OptStmtId::NONE {
                assert_eq!(block.last, OptStmtId::NONE);
            }
        }

        for stmt_id in self.stmt_ids() {
            if !visited[stmt_id.usize()] {
                let stmt = &self.stmts[stmt_id.usize()];
                assert_eq!(stmt.id, stmt_id);
                assert_eq!(stmt.bb, OptBlockId::NONE);
                assert_eq!(stmt.prev, OptStmtId::NONE);
                assert_eq!(stmt.next, OptStmtId::NONE);
            }
        }
    }


    pub fn dump(&self) {
        for bb in self.block_ids() {
            println!("{}:", bb);
            self.block_stmts(bb, |stmt| println!("  {}", stmt));
        }
    }
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

