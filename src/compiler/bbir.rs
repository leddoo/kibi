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
    PhiArg      { src: StmtId },

    GetLocal    { src: LocalId },
    SetLocal    { dst: LocalId, src: StmtId },

    LoadNil,
    LoadBool    { value: bool },
    LoadInt     { value: i64 },
    LoadFloat   { value: f64 },
    LoadString  { id: StringId },
    LoadEnv,

    ListNew,
    ListAppend { list: StmtId, value: StmtId },

    GetIndex { base: StmtId, index: StmtId },
    SetIndex { base: StmtId, index: StmtId, value: StmtId, is_define: bool },

    Call { func: StmtId, args_id: StmtListId },

    Op1         { op: Op1, src: StmtId },
    Op2         { op: Op2, src1: StmtId, src2: StmtId },

    Jump        { target: BlockId },
    SwitchBool  { src: StmtId, on_true: BlockId, on_false: BlockId },
    Return      { src: StmtId },
}


#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct PhiMapId(u32);

pub type PhiEntry = (BlockId, StmtId);

#[derive(Deref, DerefMut)]
struct PhiMapImpl {
    map: Vec<PhiEntry>,
}

#[derive(Clone, Copy, Debug, Deref)]
pub struct PhiMap<'a> {
    pub map: &'a [PhiEntry],
}


#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct StmtListId(u32);

#[derive(Deref, DerefMut)]
struct StmtListImpl {
    values: Vec<StmtId>,
}

#[derive(Clone, Copy, Debug, Deref)]
pub struct StmtList<'a> {
    pub values: &'a [StmtId],
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
    stmt_lists: Vec<StmtListImpl>,
    blocks:     Vec<Block>,
    locals:     Vec<Local>,
    strings:    Vec<String>,

    local_cursor:  OptStmtId,
    current_block: BlockId,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StringId(u32);



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
        write!(f, "s{}", self.0)
    }
}


impl OptStmtId {
    pub const NONE: OptStmtId = OptStmtId(u32::MAX);

    #[inline(always)]
    pub fn to_option(self) -> Option<StmtId> {
        (self != Self::NONE).then_some(StmtId(self.0))
    }
}

impl From<Option<StmtId>> for OptStmtId {
    #[inline(always)]
    fn from(value: Option<StmtId>) -> Self {
        if let Some(id) = value { id.some() }
        else { OptStmtId::NONE }
    }
}

impl From<OptStmtId> for Option<StmtId> {
    #[inline(always)]
    fn from(value: OptStmtId) -> Self { value.to_option() }
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

    #[inline(always)]
    pub fn fmt<'a>(&'a self, fun: &'a Function) -> StmtFmt<'a> { StmtFmt(self, fun) }
}

#[derive(Clone, Copy)]
pub struct StmtFmt<'a>(pub &'a Stmt, pub &'a Function);
    
impl<'a> core::fmt::Display for StmtFmt<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let StmtFmt (stmt, fun) = self;

        write!(f, "{} ", stmt.id)?;
        if stmt.has_value() { write!(f, ":= ")?; }
        else                { write!(f, "   ")?; }

        use StmtData::*;
        match &stmt.data {
            Copy { src } => { write!(f, "copy {}", src) }

            Phi { map_id } => { write!(f, "phi {}", map_id.get(fun)) }

            PhiArg { src } => write!(f, "phi_arg {}", src),

            GetLocal { src }      => { write!(f, "get_local {}", src) }
            SetLocal { dst, src } => { write!(f, "set_local {}, {}", dst, src) }

            LoadNil             => { write!(f, "load_nil") }
            LoadBool  { value } => { write!(f, "load_bool {}", value) }
            LoadInt   { value } => { write!(f, "load_int {}", value) }
            LoadFloat { value } => { write!(f, "load_float {}", value) }
            LoadString { id }   => { write!(f, "load_string {:?}", fun.strings[id.usize()]) }
            LoadEnv             => { write!(f, "get_env") }

            ListNew => { write!(f, "new_list") }
            ListAppend { list, value } => { write!(f, "list_append {}, {}", list, value) }

            GetIndex { base, index } => write!(f, "get_index {}, {}", base, index),

            SetIndex { base, index, value, is_define } => {
                if *is_define { write!(f, "def_index {}, {}, {}", base, index, value) }
                else          { write!(f, "set_index {}, {}, {}", base, index, value) }
            }

            Call { func, args_id } => write!(f, "call {}, {}", func, args_id.get(fun)),

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
    pub fn is_phi_arg(&self) -> bool {
        if let StmtData::PhiArg { src: _ } = self { true } else { false }
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
            PhiArg { src: _ } |
            GetLocal { src: _ } |
            SetLocal { dst: _, src: _ } |
            LoadNil |
            LoadBool { value: _ } |
            LoadInt { value: _ } |
            LoadFloat { value: _ } |
            LoadString { id: _ } |
            LoadEnv |
            ListNew |
            ListAppend { list: _, value: _ } |
            GetIndex { base: _, index: _ } |
            SetIndex { base: _, index: _, value: _, is_define: _ } |
            Call { func: _, args_id: _ } |
            Op1 { op: _, src: _ } |
            Op2 { op: _, src1: _, src2: _ } => false,
        }
    }

    #[inline(always)]
    pub fn has_value(&self) -> bool {
        use StmtData::*;
        match self {
            Copy { src: _ } |
            Phi { map_id: _ } |
            PhiArg { src: _ } |
            GetLocal { src: _ } |
            LoadNil |
            LoadBool { value: _ } |
            LoadInt { value: _ } |
            LoadFloat { value: _ } |
            LoadString { id: _ } |
            LoadEnv |
            ListNew |
            GetIndex { base: _, index: _ } |
            Call { func: _, args_id: _ } |
            Op1 { op: _, src: _ } |
            Op2 { op: _, src1: _, src2: _ } => true,

            SetLocal { dst: _, src: _ } |
            ListAppend { list: _, value: _ } |
            SetIndex { base: _, index: _, value: _, is_define: _ } |
            Jump { target: _ } |
            SwitchBool { src: _, on_true: _, on_false: _ } |
            Return { src: _ } => false,
        }
    }


    pub fn args<F: FnMut(StmtId)>(&self, fun: &Function, mut f: F) {
        use StmtData::*;
        match self {
            Copy { src } => { f(*src) }

            Phi { map_id } => { for (_, src) in map_id.get(fun).iter() { f(*src) } }

            PhiArg { src } => { f(*src) }

            GetLocal { src: _ } => (),
            SetLocal { dst: _, src } => { f(*src) }

            LoadNil |
            LoadBool  { value: _ } |
            LoadInt   { value: _ } |
            LoadFloat { value: _ } |
            LoadString { id: _ } |
            LoadEnv => (),

            ListNew => (),
            ListAppend { list, value } => { f(*list); f(*value) }

            GetIndex { base, index }                      => { f(*base); f(*index) }
            SetIndex { base, index, value, is_define: _ } => { f(*base); f(*index); f(*value) }

            Call { func, args_id } => { f(*func); for arg in args_id.get(fun).iter() { f(*arg) } }

            Op1 { op: _, src }        => { f(*src) }
            Op2 { op: _, src1, src2 } => { f(*src1); f(*src2) }

            Jump       { target: _ } => (),
            SwitchBool { src, on_true: _, on_false: _ } => { f(*src) }
            Return     { src }                          => { f(*src) },
        }
    }

    pub fn replace_args<F: FnMut(&Function, &mut StmtId)>(&mut self, fun: &mut Function, mut f: F) {
        use StmtData::*;
        match self {
            Copy { src } => { f(fun, src) }

            Phi { map_id: _ } => {
                // @todo: allow this?
                //  user should not change phis.
                //  that can break register allocation.
                //  changing phi inputs is done by changing the corresponding PhiArgs.
                /*
                let mut map = core::mem::take(&mut *fun.phi_maps[map_id.usize()]);
                for (_, src) in &mut map {
                    f(fun, src)
                }
                fun.phi_maps[map_id.usize()] = PhiMapImpl { map };
                */
            }

            PhiArg { src } => { f(fun, src) }

            GetLocal { src: _ } => (),
            SetLocal { dst: _, src } => { f(fun, src) }
            LoadEnv => (),

            LoadNil |
            LoadBool  { value: _ } |
            LoadInt   { value: _ } |
            LoadFloat { value: _ } |
            LoadString { id: _ } => (),

            ListNew => (),
            ListAppend { list, value } => { f(fun, list); f(fun, value) }

            GetIndex { base, index }                      => { f(fun, base); f(fun, index) }
            SetIndex { base, index, value, is_define: _ } => { f(fun, base); f(fun, index); f(fun, value) }

            Call { func, args_id } => {
                f(fun, func);

                let mut args = core::mem::take(&mut *fun.stmt_lists[args_id.usize()]);
                for arg in &mut args {
                    f(fun, arg)
                }
                fun.stmt_lists[args_id.usize()] = StmtListImpl { values: args };
            }

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

impl PhiMapImpl {
    #[inline]
    fn new(map: &[PhiEntry], fun: &Function) -> PhiMapImpl {
        for (_, stmt) in map {
            assert!(stmt.get(fun).is_phi_arg());
        }
        PhiMapImpl { map: map.into() }
    }

    #[inline(always)]
    fn phi_map(&self) -> PhiMap { PhiMap { map: &self.map } }
}

impl<'a> PhiMap<'a> {
    pub fn get(self, bb: BlockId) -> Option<StmtId> {
        self.iter().find_map(|(from_bb, stmt_id)|
            (*from_bb == bb).then_some(*stmt_id))
    }
}

impl<'a> core::fmt::Display for PhiMap<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;
        for (i, (bb, stmt)) in self.iter().enumerate() {
            write!(f, " {}: {}", bb, stmt)?;
            if i < self.len() - 1 {
                write!(f, ",")?;
            }
        }
        write!(f, " }}")
    }
}


impl StmtListId {
    #[inline(always)]
    pub fn usize(self) -> usize { self.0 as usize }

    #[inline]
    pub fn get<'s>(self, fun: &'s Function) -> StmtList<'s> {
        StmtList { values: &fun.stmt_lists[self.usize()] }
    }
}

impl<'a> core::fmt::Display for StmtList<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;
        for (i, stmt) in self.iter().enumerate() {
            write!(f, " {}", stmt)?;
            if i < self.len() - 1 {
                write!(f, ",")?;
            }
        }
        write!(f, " ]")
    }
}




// --- BlockId ---

impl BlockId {
    pub const ROOT:       BlockId = BlockId(0);
    pub const REAL_ENTRY: BlockId = BlockId(1);

    #[inline(always)]
    pub fn is_root(self) -> bool { self == BlockId::ROOT }


    #[inline(always)]
    pub const fn usize(self) -> usize { self.0 as usize }

    #[inline(always)]
    pub fn from_usize(index: usize) -> BlockId {
        assert!(index < u32::MAX as usize / 2);
        BlockId(index as u32)
    }

    #[inline(always)]
    pub fn get(self, fun: &Function) -> &Block { &fun.blocks[self.usize()] }

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

impl From<Option<BlockId>> for OptBlockId {
    #[inline(always)]
    fn from(value: Option<BlockId>) -> Self {
        if let Some(id) = value { id.some() }
        else { OptBlockId::NONE }
    }
}

impl From<OptBlockId> for Option<BlockId> {
    #[inline(always)]
    fn from(value: OptBlockId) -> Self { value.to_option() }
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
            first: None.into(),
            last:  None.into(),
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
        let mut fun = Function {
            stmts:      vec![],
            blocks:     vec![],
            phi_maps:   vec![],
            stmt_lists: vec![],
            locals:     vec![],
            strings:    vec![],
            local_cursor:  None.into(),
            current_block: BlockId::ROOT,
        };

        // block setup:
        //  - @param-block for locals & params.
        //  - real entry for user code.
        let param_block = fun.new_block();
        let real_entry  = fun.new_block();
        assert_eq!(param_block, BlockId::ROOT);
        assert_eq!(real_entry,  BlockId::REAL_ENTRY);
        fun.add_stmt(SourceRange::null(), StmtData::Jump { target: real_entry });
        fun.current_block = real_entry;

        fun
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


    #[inline(always)]
    pub fn num_strings(&self) -> usize { self.strings.len() }

    pub fn add_string(&mut self, value: &str) -> StringId {
        let found = self.strings.iter().position(|s| s == value);
        if let Some(index) = found {
            StringId(index as u32)
        }
        else {
            let id = self.strings.len() as u32;
            self.strings.push(value.into());
            StringId(id)
        }
    }
}


// statements
impl Function {
    pub fn new_stmt(&mut self, source: SourceRange, data: StmtData) -> StmtId {
        let id = StmtId(self.stmts.len() as u32);
        self.stmts.push(Stmt {
            data, source, id,
            prev: None.into(),
            next: None.into(),
            bb:   None.into(),
        });
        id
    }


    pub fn new_phi(&mut self, source: SourceRange, map: &[PhiEntry]) -> StmtId {
        let map_id = PhiMapId(self.phi_maps.len() as u32);
        self.phi_maps.push(PhiMapImpl::new(map, self));
        self.new_stmt(source, StmtData::Phi { map_id })
    }

    pub fn try_phi(&self, stmt: StmtId) -> Option<PhiMap> {
        if let StmtData::Phi { map_id } = self.stmts[stmt.usize()].data {
            return Some(self.phi_maps[map_id.usize()].phi_map());
        }
        None
    }

    // @todo: support Phi2.
    // @todo: def_phi variant.
    pub fn set_phi(&mut self, stmt: StmtId, map: &[PhiEntry]) {
        let StmtData::Phi { map_id } = self.stmts[stmt.usize()].data else { unreachable!() };
        self.phi_maps[map_id.usize()] = PhiMapImpl::new(map, self);
    }


    pub fn new_call(&mut self, source: SourceRange, func: StmtId, args: &[StmtId]) -> StmtId {
        let args_id = StmtListId(self.stmt_lists.len() as u32);
        self.stmt_lists.push(StmtListImpl { values: args.into() });
        self.new_stmt(source, StmtData::Call { func, args_id })
    }

    // @todo: try_call
    // @todo: set_call


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


    pub fn block_stmts<F: FnMut(&Stmt)>(&self, bb: BlockId, mut f: F) {
        let mut at = self.blocks[bb.usize()].first;
        while let Some(id) = at.to_option() {
            let stmt = &self.stmts[id.usize()];
            f(stmt);
            at = stmt.next;
        }
    }

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

    pub fn block_stmts_mut<F: FnMut(&mut Stmt)>(&mut self, bb: BlockId, mut f: F) {
        let mut at = self.blocks[bb.usize()].first;
        while let Some(id) = at.to_option() {
            let stmt = &mut self.stmts[id.usize()];
            f(stmt);
            at = stmt.next;
        }
    }

    pub fn block_stmts_rev<F: FnMut(&Stmt)>(&self, bb: BlockId, mut f: F) {
        let mut at = self.blocks[bb.usize()].last;
        while let Some(id) = at.to_option() {
            let stmt = &self.stmts[id.usize()];
            f(stmt);
            at = stmt.prev;
        }
    }


    pub fn block_args<F: FnMut(StmtId)>(&self, bb: BlockId, mut f: F) {
        let mut at = self.blocks[bb.usize()].first;
        while let Some(id) = at.to_option() {
            let stmt = &self.stmts[id.usize()];
            stmt.args(self, &mut f);
            at = stmt.next;
        }
    }

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

        // "hoist locals".
        let nil  = self.new_stmt(source, StmtData::LoadNil);
        let init = self.new_stmt(source, StmtData::SetLocal { dst: id, src: nil });
        self.insert_after(BlockId::ROOT, self.local_cursor, nil);
        self.insert_after(BlockId::ROOT, nil.some(), init);
        self.local_cursor = init.some();

        id
    }
}


// builder
impl Function {
    #[inline(always)]
    pub fn get_current_block(&mut self) -> BlockId {
        self.current_block
    }

    #[inline(always)]
    pub fn set_current_block(&mut self, bb: BlockId) {
        let block = bb.get(self);
        if let Some(last) = block.last.to_option() {
            assert!(!last.get(self).is_terminator());
        }

        self.current_block = bb;
    }


    pub fn add_stmt(&mut self, source: SourceRange, data: StmtData) -> StmtId {
        assert!(self.stmts.len() < u32::MAX as usize / 2);
        let id = StmtId(self.stmts.len() as u32);

        let bb = self.current_block;

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
            next: None.into(),
            bb:   bb.some(),
        });

        id
    }


    #[inline]
    pub fn stmt_copy(&mut self, source: SourceRange, src: StmtId) -> StmtId {
        self.add_stmt(source, StmtData::Copy { src })
    }

    pub fn stmt_phi(&mut self, source: SourceRange, map: &[PhiEntry]) -> StmtId {
        let map_id = PhiMapId(self.phi_maps.len() as u32);
        self.phi_maps.push(PhiMapImpl::new(map, self));
        self.add_stmt(source, StmtData::Phi { map_id })
    }

    #[inline]
    pub fn stmt_phi_arg(&mut self, source: SourceRange, src: StmtId) -> StmtId {
        self.add_stmt(source, StmtData::PhiArg { src })
    }

    #[inline]
    pub fn stmt_get_local(&mut self, source: SourceRange, src: LocalId) -> StmtId {
        self.add_stmt(source, StmtData::GetLocal { src })
    }

    #[inline]
    pub fn stmt_set_local(&mut self, source: SourceRange, dst: LocalId, src: StmtId) -> StmtId {
        self.add_stmt(source, StmtData::SetLocal { dst, src })
    }

    #[inline]
    pub fn stmt_load_nil(&mut self, source: SourceRange) -> StmtId {
        self.add_stmt(source, StmtData::LoadNil)
    }

    #[inline]
    pub fn stmt_load_bool(&mut self, source: SourceRange, value: bool) -> StmtId {
        self.add_stmt(source, StmtData::LoadBool { value })
    }

    #[inline]
    pub fn stmt_load_int(&mut self, source: SourceRange, value: i64) -> StmtId {
        self.add_stmt(source, StmtData::LoadInt { value })
    }

    #[inline]
    pub fn stmt_load_float(&mut self, source: SourceRange, value: f64) -> StmtId {
        self.add_stmt(source, StmtData::LoadFloat { value })
    }

    #[inline]
    pub fn stmt_load_string(&mut self, source: SourceRange, id: StringId) -> StmtId {
        self.add_stmt(source, StmtData::LoadString { id })
    }

    #[inline]
    pub fn stmt_load_env(&mut self, source: SourceRange) -> StmtId {
        self.add_stmt(source, StmtData::LoadEnv)
    }

    #[inline]
    pub fn stmt_list_new(&mut self, source: SourceRange) -> StmtId {
        self.add_stmt(source, StmtData::ListNew)
    }

    #[inline]
    pub fn stmt_list_append(&mut self, source: SourceRange, list: StmtId, value: StmtId) -> StmtId {
        self.add_stmt(source, StmtData::ListAppend { list, value })
    }

    #[inline]
    pub fn stmt_get_index(&mut self, source: SourceRange, base: StmtId, index: StmtId) -> StmtId {
        self.add_stmt(source, StmtData::GetIndex { base, index })
    }

    #[inline]
    pub fn stmt_set_index(&mut self, source: SourceRange, base: StmtId, index: StmtId, value: StmtId, is_define: bool) -> StmtId {
        self.add_stmt(source, StmtData::SetIndex { base, index, value, is_define })
    }

    #[inline]
    pub fn stmt_call(&mut self, source: SourceRange, func: StmtId, args: &[StmtId]) -> StmtId {
        let args_id = StmtListId(self.stmt_lists.len() as u32);
        self.stmt_lists.push(StmtListImpl { values: args.into() });
        self.add_stmt(source, StmtData::Call { func, args_id })
    }

    #[inline]
    pub fn stmt_op1(&mut self, source: SourceRange, op: Op1, src: StmtId) -> StmtId {
        self.add_stmt(source, StmtData::Op1 { op, src })
    }

    #[inline]
    pub fn stmt_op2(&mut self, source: SourceRange, op: Op2, src1: StmtId, src2: StmtId) -> StmtId {
        self.add_stmt(source, StmtData::Op2 { op, src1, src2 })
    }

    #[inline]
    pub fn stmt_jump(&mut self, source: SourceRange, target: BlockId) -> StmtId {
        self.add_stmt(source, StmtData::Jump { target })
    }

    #[inline]
    pub fn stmt_switch_bool(&mut self, source: SourceRange, src: StmtId, on_true: BlockId, on_false: BlockId) -> StmtId {
        self.add_stmt(source, StmtData::SwitchBool { src, on_true, on_false })
    }

    #[inline]
    pub fn stmt_return(&mut self, source: SourceRange, src: StmtId) -> StmtId {
        self.add_stmt(source, StmtData::Return { src })
    }
}


// mutation
impl Function {
    fn _insert(block: &mut Block, stmts: &mut Vec<Stmt>, stmt_id: StmtId, prev: OptStmtId, next: OptStmtId) {
        let stmt = &mut stmts[stmt_id.usize()];
        // @todo-cleanup: stmt.assert_orphan();
        assert_eq!(stmt.bb, None.into());
        debug_assert!(stmt.id == stmt_id);
        debug_assert_eq!(stmt.prev, None.into());
        debug_assert_eq!(stmt.next, None.into());

        stmt.bb   = block.id.some();
        stmt.prev = prev;
        stmt.next = next;
        block.len += 1;

        if let Some(prev) = prev.to_option() {
            stmts[prev.usize()].next = stmt_id.some();
        }
        else {
            block.first = stmt_id.some();
        }

        if let Some(next) = next.to_option() {
            stmts[next.usize()].prev = stmt_id.some();
        }
        else {
            block.last = stmt_id.some();
        }
    }

    pub fn insert_after(&mut self, bb: BlockId, ref_id: OptStmtId, stmt_id: StmtId) {
        let block = &mut self.blocks[bb.usize()];
        debug_assert_eq!(block.id, bb);

        let (prev, next) = 
            if let Some(ref_id) = ref_id.to_option() {
                let rf = &self.stmts[ref_id.usize()];
                assert_eq!(rf.bb, bb.some());
                (ref_id.some(), rf.next)
            }
            else {
                // prepend.
                (None.into(), block.first)
            };

        Self::_insert(block, &mut self.stmts, stmt_id, prev, next)
    }

    pub fn insert_before(&mut self, bb: BlockId, ref_id: OptStmtId, stmt_id: StmtId) {
        let block = &mut self.blocks[bb.usize()];
        debug_assert_eq!(block.id, bb);

        let (prev, next) = 
            if let Some(ref_id) = ref_id.to_option() {
                let rf = &self.stmts[ref_id.usize()];
                assert_eq!(rf.bb, bb.some());
                (rf.prev, ref_id.some())
            }
            else {
                // append.
                (block.last, None.into())
            };

        Self::_insert(block, &mut self.stmts, stmt_id, prev, next)
    }

    pub fn insert_before_terminator(&mut self, bb: BlockId, stmt_id: StmtId) {
        let block = &mut self.blocks[bb.usize()];
        debug_assert_eq!(block.id, bb);

        let last_id = block.last.to_option().unwrap();
        let last = &self.stmts[last_id.usize()];
        assert!(last.is_terminator());
        debug_assert_eq!(last.bb, bb.some());

        let (prev, next) = (last.prev, last_id.some());
        Self::_insert(block, &mut self.stmts, stmt_id, prev, next)
    }

    #[inline(always)]
    pub fn prepend_stmt(&mut self, bb: BlockId, stmt_id: StmtId) {
        self.insert_after(bb, None.into(), stmt_id)
    }

    #[inline(always)]
    pub fn append_stmt(&mut self, bb: BlockId, stmt_id: StmtId) {
        self.insert_before(bb, None.into(), stmt_id)
    }



    fn _remove(block: &mut Block, stmts: &mut Vec<Stmt>, stmt_index: usize) -> OptStmtId {
        let stmt = &mut stmts[stmt_index];
        assert!(stmt.bb == block.id.some());

        let old_prev = stmt.prev;
        let old_next = stmt.next;
        stmt.prev = None.into();
        stmt.next = None.into();
        stmt.bb   = None.into();

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

    pub fn retain_block_stmts<F: FnMut(&Stmt) -> bool>(&mut self, bb: BlockId, mut f: F) {
        let block = &mut self.blocks[bb.usize()];

        let mut at = block.first;
        while let Some(current) = at.to_option() {
            let stmt = &self.stmts[current.usize()];

            if !f(stmt) {
                at = Self::_remove(block, &mut self.stmts, current.usize());
            }
            else {
                at = stmt.next;
            }
        }
    }

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
            let mut in_phi_args = false;
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
                    assert_eq!(stmt.prev, None.into());
                }

                // linked list last.
                if current.some() == block.last {
                    assert_eq!(stmt.next, None.into());
                }
                else {
                    let next = stmt.next.to_option().unwrap();
                    let next = &self.stmts[next.usize()];
                    assert_eq!(next.prev, current.some());
                }

                // phis.
                if stmt.is_phi() {
                    assert!(in_phis);
                    for (_, arg) in self.try_phi(stmt.id()).unwrap().iter() {
                        let arg = arg.get(self);
                        assert!(arg.is_phi_arg());
                    }
                }
                else { in_phis = false; }

                // phi args.
                if !stmt.is_phi_arg() {
                    assert!(!in_phi_args || stmt.is_terminator());
                }
                else { in_phi_args = true }

                // terminator.
                if stmt.is_terminator() {
                    assert!(!has_terminator);
                    has_terminator = true;
                }

                at = stmt.next;
            }

            assert_eq!(stmt_count, block.len());

            if block.first == None.into() {
                assert_eq!(block.last, None.into());
            }
        }

        for stmt_id in self.stmt_ids() {
            if !visited[stmt_id.usize()] {
                let stmt = &self.stmts[stmt_id.usize()];
                assert_eq!(stmt.id, stmt_id);
                assert_eq!(stmt.bb,   None.into());
                assert_eq!(stmt.prev, None.into());
                assert_eq!(stmt.next, None.into());
            }
        }
    }


    pub fn dump(&self) {
        for bb in self.block_ids() {
            println!("{}:", bb);
            self.block_stmts(bb, |stmt| println!("  {}", stmt.fmt(self)));
        }
    }
}


impl StringId {
    #[inline(always)]
    pub fn usize(self) -> usize { self.0 as usize }

    #[inline(always)]
    pub fn from_usize(index: usize) -> StringId {
        StringId(index.try_into().unwrap())
    }

    #[inline(always)]
    pub fn get<'f>(self, fun: &'f Function) -> &'f str {
        &fun.strings[self.usize()]
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

