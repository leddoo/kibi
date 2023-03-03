use core::cell::{RefCell, Ref, RefMut};
use derive_more::{Deref, DerefMut};
use crate::index_vec::*;
use crate::macros::define_id;
use super::*;



// ### Statement ###

define_id!(StmtId, OptStmtId, "s{}");

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

    ParallelCopy { src: StmtId, copy_id: u32 },

    Param       { id: LocalId },
    Local       { id: LocalId },
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

    TupleNew { values: StmtListId },
    TupleNew0,

    NewFunction { id: FunctionId },

    GetIndex { base: StmtId, index: StmtId },
    SetIndex { base: StmtId, index: StmtId, value: StmtId, is_define: bool },

    Call { func: StmtId, args_id: StmtListId },

    Op1         { op: Op1, src: StmtId },
    Op2         { op: Op2, src1: StmtId, src2: StmtId },

    Jump        { target: BlockId },
    SwitchBool  { src: StmtId, on_true: BlockId, on_false: BlockId },
    SwitchNil   { src: StmtId, on_nil: BlockId, on_non_nil: BlockId },
    Return      { src: StmtId },
}


define_id!(PhiMapId);

pub type PhiEntry = (BlockId, StmtId);

#[derive(Deref, DerefMut)]
struct PhiMapImpl {
    map: Vec<PhiEntry>,
}

#[derive(Clone, Copy, Debug, Deref)]
pub struct PhiMap<'a> {
    pub map: &'a [PhiEntry],
}


define_id!(StmtListId);

#[derive(Deref, DerefMut)]
struct StmtListImpl {
    values: Vec<StmtId>,
}

#[derive(Clone, Copy, Debug, Deref)]
pub struct StmtList<'a> {
    pub values: &'a [StmtId],
}



// ### Block ###

define_id!(BlockId, OptBlockId, "bb{}");

#[derive(Clone, Debug)]
pub struct Block {
    id: BlockId,
    first: OptStmtId,
    last:  OptStmtId,
    len: u32,
}



// ### Local ###

define_id!(LocalId, "l{}");

#[allow(dead_code)] // @temp
#[derive(Debug)]
struct Local {
    id:     LocalId,
    name:   String,
    source: SourceRange,
}



// ### Function ###

define_id!(FunctionId, "fn{}");

pub struct Function {
    id: FunctionId,

    stmts:      IndexVec<StmtId,        Stmt>,
    phi_maps:   IndexVec<PhiMapId,      PhiMapImpl>,
    stmt_lists: IndexVec<StmtListId,    StmtListImpl>,
    blocks:     IndexVec<BlockId,       Block>,
    locals:     IndexVec<LocalId,       Local>,
    strings:    IndexVec<StringId,      String>,

    last_parallel_copy_id: u32,

    param_cursor: OptStmtId,
    num_params:   u32,

    local_cursor: OptStmtId,

    current_block: BlockId,
}

define_id!(StringId);



// ### Module ###

pub struct Module {
    inner: RefCell<ModuleInner>,
}

struct ModuleInner {
    functions: IndexVec<FunctionId, &'static RefCell<Function>>,
}



// ### Iterators ###

pub struct StmtIdIter { at: u32, end: u32 }

pub struct BlockIdIter { at: u32, end: u32 }



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

impl StmtId {
    #[inline(always)]
    pub fn get(self, fun: &Function) -> &Stmt { &fun.stmts[self] }

    #[inline(always)]
    pub fn get_mut(self, fun: &mut Function) -> &mut Stmt { &mut fun.stmts[self] }
}


#[derive(Clone, Copy)]
pub struct StmtFmt<'a>(pub &'a Stmt, pub &'a Function);
    
impl<'a> core::fmt::Display for StmtFmt<'a> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let StmtFmt (stmt, fun) = self;

        write!(f, "{} ", stmt.id)?;
        if stmt.has_value() { write!(f, ":= ")?; }
        else                { write!(f, "   ")?; }

        use StmtData::*;
        match stmt.data {
            Copy { src } => { write!(f, "copy {}", src) }

            Phi { map_id } => { write!(f, "phi {}", map_id.get(fun)) }

            ParallelCopy { src, copy_id: id } => write!(f, "parallel_copy {} ({})", src, id),

            Param { id }      => { write!(f, "param {}", id) }
            Local { id }      => { write!(f, "local {}", id) }
            GetLocal { src }      => { write!(f, "get_local {}", src) }
            SetLocal { dst, src } => { write!(f, "set_local {}, {}", dst, src) }

            LoadNil             => { write!(f, "load_nil") }
            LoadBool  { value } => { write!(f, "load_bool {}", value) }
            LoadInt   { value } => { write!(f, "load_int {}", value) }
            LoadFloat { value } => { write!(f, "load_float {}", value) }
            LoadString { id }   => { write!(f, "load_string {:?}", fun.strings[id]) }
            LoadEnv             => { write!(f, "get_env") }

            ListNew => { write!(f, "new_list") }
            ListAppend { list, value } => { write!(f, "list_append {}, {}", list, value) }

            TupleNew { values } => write!(f, "tuple_new {}", values.get(fun)),
            TupleNew0 => write!(f, "tuple_new []"),

            NewFunction { id } => write!(f, "new_function {}", id),

            GetIndex { base, index } => write!(f, "get_index {}, {}", base, index),

            SetIndex { base, index, value, is_define } => {
                if is_define { write!(f, "def_index {}, {}, {}", base, index, value) }
                else         { write!(f, "set_index {}, {}, {}", base, index, value) }
            }

            Call { func, args_id } => write!(f, "call {}, {}", func, args_id.get(fun)),

            Op1 { op, src }        => { write!(f, "{} {}",     op.str(), src) }
            Op2 { op, src1, src2 } => { write!(f, "{} {}, {}", op.str(), src1, src2) }

            Jump       { target }                  => { write!(f, "jump {}", target) }
            SwitchBool { src, on_true, on_false }  => { write!(f, "switch_bool {}, {}, {}", src, on_true, on_false) }
            SwitchNil  { src, on_nil, on_non_nil } => { write!(f, "switch_nil {}, {}, {}", src, on_nil, on_non_nil) }
            Return     { src }                     => { write!(f, "return {}", src) }
        }
    }
}


impl StmtData {
    #[inline(always)]
    pub fn is_copy(&self) -> bool {
        if let StmtData::Copy { src: _ } = self { true } else { false }
    }

    #[inline(always)]
    pub fn is_parallel_copy(&self) -> bool {
        if let StmtData::ParallelCopy { src: _, copy_id: _ } = self { true } else { false }
    }

    #[inline(always)]
    pub fn is_param(&self) -> bool {
        if let StmtData::Param { id: _ } = self { true } else { false }
    }

    #[inline(always)]
    pub fn is_local(&self) -> bool {
        if let StmtData::Local { id: _ } = self { true } else { false }
    }

    #[inline(always)]
    pub fn is_phi(&self) -> bool {
        if let StmtData::Phi { map_id: _ } = self { true } else { false }
    }

    #[inline(always)]
    pub fn try_any_copy(&self) -> Option<StmtId> {
        match self {
            StmtData::Copy { src }                     => Some(*src),
            StmtData::ParallelCopy { src, copy_id: _ } => Some(*src),
            _ => None,
        }
    }

    #[inline(always)]
    pub fn is_terminator(&self) -> bool {
        use StmtData::*;
        match self {
            Jump { target: _ } |
            SwitchBool { src: _, on_true: _, on_false: _ } |
            SwitchNil  { src: _, on_nil: _, on_non_nil: _ } |
            Return { src: _ } => true,

            Copy { src: _ } |
            Phi { map_id: _ } |
            ParallelCopy { src: _, copy_id: _ } |
            Param { id: _ } |
            Local { id: _ } |
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
            TupleNew { values: _ } |
            TupleNew0 |
            NewFunction { id: _ } |
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
            ParallelCopy { src: _, copy_id: _ } |
            Param { id: _ } |
            Local { id: _ } |
            GetLocal { src: _ } |
            LoadNil |
            LoadBool { value: _ } |
            LoadInt { value: _ } |
            LoadFloat { value: _ } |
            LoadString { id: _ } |
            LoadEnv |
            ListNew |
            TupleNew { values: _ } |
            TupleNew0 |
            NewFunction { id: _ } |
            GetIndex { base: _, index: _ } |
            Call { func: _, args_id: _ } |
            Op1 { op: _, src: _ } |
            Op2 { op: _, src1: _, src2: _ } => true,

            SetLocal { dst: _, src: _ } |
            ListAppend { list: _, value: _ } |
            SetIndex { base: _, index: _, value: _, is_define: _ } |
            Jump { target: _ } |
            SwitchBool { src: _, on_true: _, on_false: _ } |
            SwitchNil  { src: _, on_nil: _, on_non_nil: _ } |
            Return { src: _ } => false,
        }
    }


    pub fn args<F: FnMut(StmtId)>(&self, fun: &Function, mut f: F) {
        use StmtData::*;
        match self {
            Copy { src } => { f(*src) }

            Phi { map_id } => { for (_, src) in map_id.get(fun).iter() { f(*src) } }

            ParallelCopy { src, copy_id: _ } => { f(*src) }

            Param { id: _ } |
            Local { id: _ } |
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

            TupleNew { values } => { values.each(fun, f) }
            TupleNew0 => (),

            NewFunction { id: _ } => (),

            GetIndex { base, index }                      => { f(*base); f(*index) }
            SetIndex { base, index, value, is_define: _ } => { f(*base); f(*index); f(*value) }

            Call { func, args_id } => { f(*func); args_id.each(fun, f) }

            Op1 { op: _, src }        => { f(*src) }
            Op2 { op: _, src1, src2 } => { f(*src1); f(*src2) }

            Jump       { target: _ } => (),
            SwitchBool { src, on_true: _, on_false: _ }  => { f(*src) }
            SwitchNil  { src, on_nil: _, on_non_nil: _ } => { f(*src) }
            Return     { src }                           => { f(*src) }
        }
    }

    pub fn replace_args<F: FnMut(&Function, &mut StmtId)>(&mut self, fun: &mut Function, mut f: F) {
        use StmtData::*;
        match self {
            Copy { src } => { f(fun, src) }

            Phi { map_id } => {
                let mut map = core::mem::take(&mut *fun.phi_maps[*map_id]);
                for (_, src) in &mut map {
                    f(fun, src)
                }
                fun.phi_maps[*map_id] = PhiMapImpl { map };
            }

            ParallelCopy { src, copy_id: _ } => { f(fun, src) }

            Param { id: _ } |
            Local { id: _ } |
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

            TupleNew { values } => { values.each_mut(fun, f) }
            TupleNew0 => (),

            NewFunction { id: _ } => (),

            GetIndex { base, index }                      => { f(fun, base); f(fun, index) }
            SetIndex { base, index, value, is_define: _ } => { f(fun, base); f(fun, index); f(fun, value) }

            Call { func, args_id } => { f(fun, func); args_id.each_mut(fun, f) }

            Op1 { op: _, src }        => { f(fun, src) }
            Op2 { op: _, src1, src2 } => { f(fun, src1); f(fun, src2) }

            Jump       { target: _ } => (),
            SwitchBool { src, on_true: _, on_false: _ }  => { f(fun, src) }
            SwitchNil  { src, on_nil: _, on_non_nil: _ } => { f(fun, src) }
            Return     { src }                           => { f(fun, src) }
        }
    }
}


impl PhiMapId {
    #[inline]
    pub fn get<'s>(self, fun: &'s Function) -> PhiMap<'s> {
        PhiMap { map: &fun.phi_maps[self] }
    }
}

impl PhiMapImpl {
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
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
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
    #[inline]
    pub fn get<'s>(self, fun: &'s Function) -> StmtList<'s> {
        StmtList { values: &fun.stmt_lists[self] }
    }

    #[inline]
    pub fn each<F: FnMut(StmtId)>(self, fun: &Function, mut f: F) {
        for v in &*fun.stmt_lists[self] {
            f(*v)
        }
    }

    #[inline]
    pub fn each_mut<F: FnMut(&Function, &mut StmtId)>(self, fun: &mut Function, mut f: F) {
        let mut stmts = core::mem::take(&mut *fun.stmt_lists[self]);
        for stmt in &mut stmts {
            f(fun, stmt)
        }
        fun.stmt_lists[self] = StmtListImpl { values: stmts };
    }
}

impl<'a> core::fmt::Display for StmtList<'a> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
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
    pub const ENTRY: BlockId = BlockId(0);

    #[inline(always)]
    pub fn is_entry(self) -> bool { self == BlockId::ENTRY }


    #[inline(always)]
    pub fn get(self, fun: &Function) -> &Block { &fun.blocks[self] }
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



// --- Function ---

// common
impl Function {
    fn new(id: FunctionId) -> Self {
        let mut fun = Function {
            id,
            stmts:      index_vec![],
            blocks:     index_vec![],
            phi_maps:   index_vec![],
            stmt_lists: index_vec![],
            locals:     index_vec![],
            strings:    index_vec![],
            last_parallel_copy_id: 0,
            param_cursor: None.into(),
            num_params:   0,
            local_cursor: None.into(),
            current_block: BlockId::ENTRY,
        };
        fun.new_block();

        fun
    }

    #[inline(always)]
    pub fn id(&self) -> FunctionId { self.id }


    #[inline(always)]
    pub fn num_stmts(&self) -> usize { self.stmts.len() }

    #[inline(always)]
    pub fn stmt_ids(&self) -> StmtIdIter { StmtIdIter { at: 0, end: self.stmts.len() as u32 } }
    

    #[inline(always)]
    pub fn num_blocks(&self) -> usize { self.blocks.len() }

    #[inline(always)]
    pub fn block_ids(&self) -> BlockIdIter { BlockIdIter { at: 0, end: self.blocks.len() as u32 } }


    #[inline(always)]
    pub fn num_params(&self) -> usize { self.num_params as usize }

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

    #[inline]
    pub fn new_parallel_copy_id(&mut self) -> u32 {
        self.last_parallel_copy_id += 1;
        self.last_parallel_copy_id
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
        self.phi_maps.push(PhiMapImpl { map: map.into() });
        self.new_stmt(source, StmtData::Phi { map_id })
    }

    pub fn try_phi(&self, stmt: StmtId) -> Option<PhiMap> {
        if let StmtData::Phi { map_id } = self.stmts[stmt].data {
            return Some(self.phi_maps[map_id].phi_map());
        }
        None
    }

    // @todo: support Phi2.
    // @todo: def_phi variant.
    pub fn set_phi(&mut self, stmt: StmtId, map: &[PhiEntry]) {
        let StmtData::Phi { map_id } = self.stmts[stmt].data else { unreachable!() };
        self.phi_maps[map_id] = PhiMapImpl { map: map.into() };
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
                let stmt = &self.stmts[id];
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
        self.blocks[bb].len()
    }


    pub fn block_stmts<F: FnMut(&Stmt)>(&self, bb: BlockId, mut f: F) {
        let mut at = self.blocks[bb].first;
        while let Some(id) = at.to_option() {
            let stmt = &self.stmts[id];
            f(stmt);
            at = stmt.next;
        }
    }

    pub fn block_stmts_ex<F: FnMut(&Stmt) -> bool>(&self, bb: BlockId, mut f: F) {
        let mut at = self.blocks[bb].first;
        while let Some(id) = at.to_option() {
            let stmt = &self.stmts[id];
            if !f(stmt) {
                break;
            }
            at = stmt.next;
        }
    }

    pub fn block_stmts_mut<F: FnMut(&mut Stmt)>(&mut self, bb: BlockId, mut f: F) {
        let mut at = self.blocks[bb].first;
        while let Some(id) = at.to_option() {
            let stmt = &mut self.stmts[id];
            f(stmt);
            at = stmt.next;
        }
    }

    pub fn block_stmts_rev<F: FnMut(&Stmt)>(&self, bb: BlockId, mut f: F) {
        let mut at = self.blocks[bb].last;
        while let Some(id) = at.to_option() {
            let stmt = &self.stmts[id];
            f(stmt);
            at = stmt.prev;
        }
    }


    pub fn block_args<F: FnMut(StmtId)>(&self, bb: BlockId, mut f: F) {
        let mut at = self.blocks[bb].first;
        while let Some(id) = at.to_option() {
            let stmt = &self.stmts[id];
            stmt.args(self, &mut f);
            at = stmt.next;
        }
    }

    pub fn block_replace_args<F: FnMut(&Function, &mut StmtId)>(&mut self, bb: BlockId, mut f: F) {
        let mut at = self.blocks[bb].first;
        while let Some(id) = at.to_option() {
            let mut data = self.stmts[id].data;
            data.replace_args(self, &mut f);

            let stmt = &mut self.stmts[id];
            stmt.data = data;
            at = stmt.next;
        }
    }


    pub fn block_successors<F: FnMut(BlockId)>(&self, bb: BlockId, mut f: F) {
        let block = &self.blocks[bb];

        let Some(last) = block.last.to_option() else { unreachable!() };

        use StmtData::*;
        match last.get(self).data {
            Jump { target } => { f(target); }
            SwitchBool { src: _, on_true, on_false }  => { f(on_true); f(on_false); }
            SwitchNil  { src: _, on_nil, on_non_nil } => { f(on_nil); f(on_non_nil); }
            Return { src: _ } => {}

            _ => { unreachable!("called successors on unterminated block") }
        }
    }

    pub fn block_first_phi(&self, bb: BlockId) -> OptStmtId {
        if let Some(first) = bb.get(self).first.to_option() {
            if first.get(self).is_phi() {
                return first.some();
            }
        }
        OptStmtId::NONE
    }

    pub fn block_last_phi(&self, bb: BlockId) -> OptStmtId {
        let mut result = OptStmtId::NONE;
        self.block_stmts_ex(bb, |stmt| {
            if stmt.is_phi() {
                result = stmt.id.some();
                true
            }
            else { false }
        });
        result
    }

    pub fn block_terminator(&self, bb: BlockId) -> OptStmtId {
        if let Some(last) = bb.get(self).last.to_option() {
            if last.get(self).is_terminator() {
                return last.some();
            }
        }
        None.into()
    }


    pub fn remove_unreachable_blocks(&mut self) {
        fn visit(fun: &Function, bb: BlockId, visited: &mut IndexVec<BlockId, bool>) {
            visited[bb] = true;
            fun.block_successors(bb, |succ| {
                if !visited[succ] {
                    visit(fun, succ, visited);
                }
            });
        }

        // mark.
        let mut visited = index_vec![false; self.blocks.len()];
        visit(self, BlockId::ENTRY, &mut visited);

        // sweep.
        let mut new_ids = index_vec![None; self.blocks.len()];
        let mut next_id = BlockId(0);
        self.blocks.retain_mut(|block| {
            if visited[block.id] {
                new_ids[block.id] = Some(next_id);
                block.id = next_id;

                next_id.0 += 1;
                return true;
            }
            false
        });

        // rename.
        // @todo-perf: do this per block, can skip if not renamed.
        for stmt in self.stmt_ids() {
            let stmt = stmt.get_mut(self);

            // update bb & linked list.
            // @todo: free up the old statements.
            if let Some(old_bb) = stmt.bb.to_option() {
                if let Some(new_id) = new_ids[old_bb] {
                    stmt.bb = new_id.some();
                }
                else {
                    stmt.bb   = None.into();
                    stmt.prev = None.into();
                    stmt.next = None.into();
                    // @temp.
                    stmt.data = StmtData::LoadNil;
                }
            }

            // phis.
            if stmt.is_phi() {
                use StmtData::*;
                match &mut stmt.data {
                    Phi { map_id } => {
                        let map = *map_id;
                        let map = &mut self.phi_maps[map];
                        map.retain_mut(|(from_bb, _)| {
                            if let Some(new_id) = new_ids[*from_bb] {
                                *from_bb = new_id;
                                return true;
                            }
                            false
                        });
                    }

                    _ => unreachable!(),
                }
            }
            // terminators.
            else if stmt.is_terminator() {
                use StmtData::*;
                match &mut stmt.data {
                    Jump { target } => {
                        *target = new_ids[*target].unwrap();
                    }
                    SwitchBool { src: _, on_true, on_false } => {
                        *on_true  = new_ids[*on_true].unwrap();
                        *on_false = new_ids[*on_false].unwrap();
                    }
                    SwitchNil { src: _, on_nil, on_non_nil } => {
                        *on_nil     = new_ids[*on_nil].unwrap();
                        *on_non_nil = new_ids[*on_non_nil].unwrap();
                    }
                    Return { src: _ } => {}

                    _ => unreachable!(),
                }
            }
        }

        self.slow_integrity_check();
    }
}


// locals
impl Function {
    pub fn new_param(&mut self, name: &str, source: SourceRange) -> LocalId {
        let id = LocalId(self.locals.len() as u32);
        self.locals.push(Local { id, name: name.into(), source });

        let old_param_cursor = self.param_cursor;

        // "hoist params".
        let param = self.new_stmt(source, StmtData::Param { id });
        self.insert_after(BlockId::ENTRY, self.param_cursor, param);
        self.param_cursor = param.some();
        self.num_params  += 1;

        if self.local_cursor == old_param_cursor {
            self.local_cursor = self.param_cursor;
        }

        id
    }

    pub fn new_local(&mut self, name: &str, source: SourceRange) -> LocalId {
        let id = LocalId(self.locals.len() as u32);
        self.locals.push(Local { id, name: name.into(), source });

        // "hoist locals".
        let local = self.new_stmt(source, StmtData::Local { id });
        self.insert_after(BlockId::ENTRY, self.local_cursor, local);
        self.local_cursor = local.some();

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

        let block = &mut self.blocks[bb];
        let old_last = block.last;

        // update linked list.
        if let Some(last) = old_last.to_option() {
            let last = &mut self.stmts[last];
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
        self.phi_maps.push(PhiMapImpl { map: map.into() });
        self.add_stmt(source, StmtData::Phi { map_id })
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

    pub fn stmt_tuple_new(&mut self, source: SourceRange, values: &[StmtId]) -> StmtId {
        if values.len() == 0 {
            self.add_stmt(source, StmtData::TupleNew0)
        }
        else {
            let values_id = StmtListId(self.stmt_lists.len() as u32);
            self.stmt_lists.push(StmtListImpl { values: values.into() });
            self.add_stmt(source, StmtData::TupleNew { values: values_id })
        }
    }

    #[inline]
    pub fn stmt_load_unit(&mut self, source: SourceRange) -> StmtId {
        self.add_stmt(source, StmtData::TupleNew0)
    }

    #[inline]
    pub fn stmt_new_function(&mut self, source: SourceRange, id: FunctionId) -> StmtId {
        self.add_stmt(source, StmtData::NewFunction { id })
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
    pub fn stmt_switch_nil(&mut self, source: SourceRange, src: StmtId, on_nil: BlockId, on_non_nil: BlockId) -> StmtId {
        self.add_stmt(source, StmtData::SwitchNil { src, on_nil, on_non_nil })
    }

    #[inline]
    pub fn stmt_return(&mut self, source: SourceRange, src: StmtId) -> StmtId {
        self.add_stmt(source, StmtData::Return { src })
    }
}


// mutation
impl Function {
    fn _insert(block: &mut Block, stmts: &mut IndexVec<StmtId, Stmt>, stmt_id: StmtId, prev: OptStmtId, next: OptStmtId) {
        let stmt = &mut stmts[stmt_id];
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
            stmts[prev].next = stmt_id.some();
        }
        else {
            block.first = stmt_id.some();
        }

        if let Some(next) = next.to_option() {
            stmts[next].prev = stmt_id.some();
        }
        else {
            block.last = stmt_id.some();
        }
    }

    pub fn insert_after(&mut self, bb: BlockId, ref_id: OptStmtId, stmt_id: StmtId) {
        let block = &mut self.blocks[bb];
        debug_assert_eq!(block.id, bb);

        let (prev, next) = 
            if let Some(ref_id) = ref_id.to_option() {
                let rf = &self.stmts[ref_id];
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
        let block = &mut self.blocks[bb];
        debug_assert_eq!(block.id, bb);

        let (prev, next) = 
            if let Some(ref_id) = ref_id.to_option() {
                let rf = &self.stmts[ref_id];
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
        let block = &mut self.blocks[bb];
        debug_assert_eq!(block.id, bb);

        let last_id = block.last.to_option().unwrap();
        let last = &self.stmts[last_id];
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



    fn _remove(block: &mut Block, stmts: &mut IndexVec<StmtId, Stmt>, stmt_index: StmtId) -> OptStmtId {
        let stmt = &mut stmts[stmt_index];
        assert!(stmt.bb == block.id.some());

        let old_prev = stmt.prev;
        let old_next = stmt.next;
        stmt.prev = None.into();
        stmt.next = None.into();
        stmt.bb   = None.into();

        if let Some(prev) = old_prev.to_option() {
            stmts[prev].next = old_next;
        }
        else {
            block.first = old_next;
        }

        if let Some(next) = old_next.to_option() {
            stmts[next].prev = old_prev;
        }
        else {
            block.last = old_prev;
        }

        block.len -= 1;

        old_next
    }

    pub fn retain_block_stmts<F: FnMut(&Stmt) -> bool>(&mut self, bb: BlockId, mut f: F) {
        let block = &mut self.blocks[bb];

        let mut at = block.first;
        while let Some(current) = at.to_option() {
            let stmt = &self.stmts[current];

            if !f(stmt) {
                at = Self::_remove(block, &mut self.stmts, current);
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
        let preds = self.predecessors();
        let post_order = self.post_order();
        let post_indices = self.post_order_indices(&post_order);
        let idom = self.immediate_dominators(&preds, &post_order, &post_indices);

        let mut visited = index_vec![false; self.stmts.len()];

        // validate blocks.
        for bb in self.block_ids() {
            let block = &self.blocks[bb];
            assert_eq!(block.id, bb);

            let mut in_params = bb.is_entry();
            let mut in_locals = false;

            let mut in_phis = !bb.is_entry();
            let mut has_terminator = false;
            let mut stmt_count = 0;

            let mut at = block.first;
            while let Some(current) = at.to_option() {
                stmt_count += 1;

                // only in one bb.
                assert!(!visited[current]);
                visited[current] = true;

                // stmt & bb ids.
                let stmt = &self.stmts[current];
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
                // linked list prev/next.
                else {
                    let next = stmt.next.to_option().unwrap();
                    let next = &self.stmts[next];
                    assert_eq!(next.prev, current.some());
                }

                // params & locals.
                if stmt.is_param() {
                    assert!(in_params);
                }
                else if in_params {
                    in_params = false;
                    in_locals = true;
                }
                if stmt.is_local() {
                    assert!(in_locals);
                }
                else if !in_params {
                    in_locals = false;
                }

                // phis.
                if stmt.is_phi() {
                    assert!(in_phis);

                    // one arg for each pred.
                    // pred dominated by arg's bb.
                    let preds = &preds[bb];
                    let mut visited = vec![false; preds.len()];
                    let phi_map = self.try_phi(stmt.id).unwrap();
                    for (from_bb, src) in phi_map.iter().copied() {
                        let pred = preds.iter().position(|p| *p == from_bb).unwrap();
                        assert!(visited[pred] == false);
                        visited[pred] = true;

                        let src = src.get(self);
                        assert!(src.has_value());
                        let src_bb = src.bb.to_option().unwrap();
                        assert!(idom.is_dominated_by(from_bb, src_bb));
                    }
                }
                else { in_phis = false; }

                // bb dominated by (non-phi) arg bbs.
                if !stmt.is_phi() {
                    stmt.args(self, |arg| {
                        let arg = arg.get(self);
                        assert!(arg.has_value());
                        let arg_bb = arg.bb.to_option().unwrap();
                        assert!(idom.is_dominated_by(bb, arg_bb));
                    });
                }

                // terminator: at most one.
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

        // validate statements that are not in blocks.
        for stmt_id in self.stmt_ids() {
            if !visited[stmt_id] {
                let stmt = &self.stmts[stmt_id];
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
    pub fn get<'f>(self, fun: &'f Function) -> &'f str {
        &fun.strings[self]
    }
}



// --- Module ---

impl Module {
    pub fn new() -> Module {
        Module { inner: RefCell::new(ModuleInner {
            functions: index_vec![],
        })}
    }

    pub fn new_function(&self) -> RefMut<'static, Function> {
        let mut this = self.inner.borrow_mut();
        let id = FunctionId(this.functions.len() as u32);
        let function = Box::leak(Box::new(RefCell::new(Function::new(id))));
        let result = function.borrow_mut();
        this.functions.push(function);
        result
    }

    pub fn read_function(&self, id: FunctionId) -> Ref<'static, Function> {
        let this = self.inner.borrow();
        this.functions[id].borrow()
    }

    pub fn write_function(&self, id: FunctionId) -> RefMut<'static, Function> {
        let this = self.inner.borrow();
        this.functions[id].borrow_mut()
    }

    pub fn temp_load(self, vm: &mut crate::Vm) {
        let this = self.inner.borrow();

        let mut fun_protos = vec![];
        for i in 0..this.functions.len() {
            fun_protos.push((vm.inner.func_protos.len() + i) as u32);
        }

        for fun in this.functions.iter() {
            let mut fun = fun.borrow_mut();
            //fun.dump();

            fun.remove_unreachable_blocks();
            //fun.dump();

            // for local in &fun.locals {
            //     println!("{:?}", local);
            // }

            let preds = fun.predecessors();

            let post_order = fun.post_order();

            let post_indices = fun.post_order_indices(&post_order);

            let idoms = fun.immediate_dominators(&preds, &post_order, &post_indices);

            let dom_tree = fun.dominator_tree(&idoms);

            let dom_frontiers = fun.dominance_frontiers(&preds, &idoms);

            opt::local2reg_ex(&mut fun, &preds, &dom_tree, &dom_frontiers);
            //println!("local2reg done");
            //fun.dump();

            opt::copy_propagation_ex(&mut fun, &dom_tree);
            //println!("copy propagation done");
            //fun.dump();

            opt::dead_copy_elim(&mut fun);
            //println!("dead copy elim done");
            //fun.dump();

            transform::convert_to_cssa_naive(&mut fun, &preds);
            //println!("cssa");
            //fun.dump();

            let (code, constants, num_regs) = fun.compile_ex(&post_order, &idoms, &dom_tree, &fun_protos);
            //println!("bytecode:");
            //crate::bytecode::dump(&code);

            use crate::{Constant, Value};
            let constants = constants.into_iter().map(|c| { match c {
                Constant::Nil              => Value::Nil,
                Constant::Bool   { value } => Value::Bool { value },
                Constant::Number { value } => Value::Number { value },
                Constant::String { value } => vm.inner.string_new(&value),
            }}).collect();

            vm.inner.func_protos.push(crate::FuncProto {
                code: crate::FuncCode::ByteCode(code),
                constants,
                num_params: fun.num_params,
                stack_size: num_regs,
            });
        }

        assert_eq!(vm.inner.func_protos.len(), *fun_protos.last().unwrap() as usize + 1);

        vm.inner.push_func(fun_protos[0] as usize);
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

