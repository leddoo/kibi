use core::cell::{RefCell, Ref, RefMut};
use derive_more::{Deref, DerefMut, Display};
use crate::index_vec::*;
use crate::macros::define_id;
use super::*;



// ### Instruction ###

define_id!(InstrId, OptInstrId, "s{}");

#[derive(Clone, Debug, Deref, DerefMut)]
pub struct Instr {
    #[deref] #[deref_mut]
    pub data:   InstrData,
    pub source: SourceRange,
    id:         InstrId,
    prev:       OptInstrId,
    next:       OptInstrId,
    bb:         OptBlockId,
}

#[derive(Clone, Copy, Debug)]
pub enum InstrData {
    Copy        { src: InstrId },

    Phi         { map_id: PhiMapId },

    ParallelCopy { src: InstrId, copy_id: u32 },

    Param       { id: LocalId },
    Local       { id: LocalId },
    GetLocal    { src: LocalId },
    SetLocal    { dst: LocalId, src: InstrId },

    LoadNil,
    LoadBool    { value: bool },
    LoadInt     { value: i64 },
    LoadFloat   { value: f64 },
    LoadString  { id: StringId },
    LoadEnv,

    ListNew { values: InstrListId },

    TupleNew { values: InstrListId },
    TupleNew0,

    NewFunction { id: FunctionId },

    ReadPath { path_id: PathId },
    WritePath { path_id: PathId, value: InstrId, is_def: bool },

    Call { func: InstrId, args_id: InstrListId },

    Op1         { op: Op1, src: InstrId },
    Op2         { op: Op2, src1: InstrId, src2: InstrId },

    Jump        { target: BlockId },
    SwitchBool  { src: InstrId, on_true: BlockId, on_false: BlockId },
    SwitchNil   { src: InstrId, on_nil: BlockId, on_non_nil: BlockId },
    Return      { src: InstrId },
}


define_id!(PhiMapId);

pub type PhiEntry = (BlockId, InstrId);

#[derive(Deref, DerefMut)]
struct PhiMapImpl {
    map: Vec<PhiEntry>,
}

#[derive(Clone, Copy, Debug, Deref)]
pub struct PhiMap<'a> {
    pub map: &'a [PhiEntry],
}


define_id!(InstrListId);

#[derive(Deref, DerefMut)]
struct InstrListImpl {
    values: Vec<InstrId>,
}

#[derive(Clone, Copy, Debug, Deref)]
pub struct InstrList<'a> {
    pub values: &'a [InstrId],
}


define_id!(PathId);

#[derive(Clone, Copy, Debug, Display)]
pub enum PathBase {
    Env,
    Instr(InstrId),
}

#[derive(Clone, Copy, Debug, Display)]
pub enum PathKey {
    Field(StringId),
    Index(InstrId),
}

#[derive(Clone, Debug)]
pub struct PathImpl {
    pub base: PathBase,
    pub keys: Vec<PathKey>,
}

#[derive(Clone, Copy, Debug)]
pub struct Path<'a> {
    pub base: PathBase,
    pub keys: &'a [PathKey],
}




// ### Block ###

define_id!(BlockId, OptBlockId, "bb{}");

#[derive(Clone, Debug)]
pub struct Block {
    id: BlockId,
    first: OptInstrId,
    last:  OptInstrId,
    len: u32,
}



// ### Local ###

define_id!(LocalId, OptLocalId, "l{}");

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

    instrs:         IndexVec<InstrId,       Instr>,
    phi_maps:       IndexVec<PhiMapId,      PhiMapImpl>,
    paths:          IndexVec<PathId,        PathImpl>,
    instr_lists:    IndexVec<InstrListId,   InstrListImpl>,
    blocks:         IndexVec<BlockId,       Block>,
    locals:         IndexVec<LocalId,       Local>,
    strings:        IndexVec<StringId,      String>,

    last_parallel_copy_id: u32,

    param_cursor: OptInstrId,
    num_params:   u32,

    local_cursor: OptInstrId,

    current_block: BlockId,
}

define_id!(StringId, "str{}");



// ### Module ###

pub struct Module {
    inner: RefCell<ModuleInner>,
}

struct ModuleInner {
    functions: IndexVec<FunctionId, &'static RefCell<Function>>,
}



// ### Iterators ###

pub struct InstrIdIter { at: u32, end: u32 }

pub struct BlockIdIter { at: u32, end: u32 }



// --- Instruction ---

impl Instr {
    #[inline(always)] pub fn id(&self)   -> InstrId     { self.id }
    #[inline(always)] pub fn prev(&self) -> OptInstrId  { self.prev }
    #[inline(always)] pub fn next(&self) -> OptInstrId  { self.next }
    #[inline(always)] pub fn bb(&self)   -> OptBlockId { self.bb }

    #[inline(always)]
    pub fn read(&self) -> (InstrId, InstrData) { (self.id, self.data) }

    #[inline(always)]
    pub fn fmt<'a>(&'a self, fun: &'a Function) -> InstrFmt<'a> { InstrFmt(self, fun) }
}

impl InstrId {
    #[inline(always)]
    pub fn get(self, fun: &Function) -> &Instr { &fun.instrs[self] }

    #[inline(always)]
    pub fn get_mut(self, fun: &mut Function) -> &mut Instr { &mut fun.instrs[self] }
}


#[derive(Clone, Copy)]
pub struct InstrFmt<'a>(pub &'a Instr, pub &'a Function);
    
impl<'a> core::fmt::Display for InstrFmt<'a> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let InstrFmt (instr, fun) = self;

        write!(f, "{} ", instr.id)?;
        if instr.has_value() { write!(f, ":= ")?; }
        else                { write!(f, "   ")?; }

        use InstrData::*;
        match instr.data {
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

            ListNew { values } => write!(f, "new_list {}", values.get(fun)),

            TupleNew { values } => write!(f, "tuple_new {}", values.get(fun)),
            TupleNew0 => write!(f, "tuple_new []"),

            NewFunction { id } => write!(f, "new_function {}", id),

            ReadPath { path_id } => write!(f, "read_path {}", path_id.get(fun)),

            WritePath { path_id, value, is_def } => {
                write!(f, "write_path")?;
                if is_def { write!(f, "(d)")? }
                write!(f, " {} {}", path_id.get(fun), value)
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


impl InstrData {
    #[inline(always)]
    pub fn is_copy(&self) -> bool {
        if let InstrData::Copy { src: _ } = self { true } else { false }
    }

    #[inline(always)]
    pub fn is_parallel_copy(&self) -> bool {
        if let InstrData::ParallelCopy { src: _, copy_id: _ } = self { true } else { false }
    }

    #[inline(always)]
    pub fn is_param(&self) -> bool {
        if let InstrData::Param { id: _ } = self { true } else { false }
    }

    #[inline(always)]
    pub fn is_local(&self) -> bool {
        if let InstrData::Local { id: _ } = self { true } else { false }
    }

    #[inline(always)]
    pub fn is_phi(&self) -> bool {
        if let InstrData::Phi { map_id: _ } = self { true } else { false }
    }

    #[inline(always)]
    pub fn try_any_copy(&self) -> Option<InstrId> {
        match self {
            InstrData::Copy { src }                     => Some(*src),
            InstrData::ParallelCopy { src, copy_id: _ } => Some(*src),
            _ => None,
        }
    }

    #[inline(always)]
    pub fn is_terminator(&self) -> bool {
        use InstrData::*;
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
            ListNew { values: _ } |
            TupleNew { values: _ } |
            TupleNew0 |
            NewFunction { id: _ } |
            ReadPath { path_id: _ } |
            WritePath { path_id: _, value: _, is_def: _ } |
            Call { func: _, args_id: _ } |
            Op1 { op: _, src: _ } |
            Op2 { op: _, src1: _, src2: _ } => false,
        }
    }

    #[inline(always)]
    pub fn has_value(&self) -> bool {
        use InstrData::*;
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
            ListNew { values: _ } |
            TupleNew { values: _ } |
            TupleNew0 |
            NewFunction { id: _ } |
            ReadPath { path_id: _ } |
            WritePath { path_id: _, value: _, is_def: _ } |
            Call { func: _, args_id: _ } |
            Op1 { op: _, src: _ } |
            Op2 { op: _, src1: _, src2: _ } => true,

            SetLocal { dst: _, src: _ } |
            Jump { target: _ } |
            SwitchBool { src: _, on_true: _, on_false: _ } |
            SwitchNil  { src: _, on_nil: _, on_non_nil: _ } |
            Return { src: _ } => false,
        }
    }


    pub fn args<F: FnMut(InstrId)>(&self, fun: &Function, mut f: F) {
        use InstrData::*;
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

            ListNew { values } => { values.each(fun, f) }

            TupleNew { values } => { values.each(fun, f) }
            TupleNew0 => (),

            NewFunction { id: _ } => (),

            ReadPath { path_id } => { path_id.each_instr(fun, f) }
            WritePath { path_id, value, is_def: _ } => { path_id.each_instr(fun, &mut f); f(*value) }

            Call { func, args_id } => { f(*func); args_id.each(fun, f) }

            Op1 { op: _, src }        => { f(*src) }
            Op2 { op: _, src1, src2 } => { f(*src1); f(*src2) }

            Jump       { target: _ } => (),
            SwitchBool { src, on_true: _, on_false: _ }  => { f(*src) }
            SwitchNil  { src, on_nil: _, on_non_nil: _ } => { f(*src) }
            Return     { src }                           => { f(*src) }
        }
    }

    pub fn replace_args<F: FnMut(&Function, &mut InstrId)>(&mut self, fun: &mut Function, mut f: F) {
        use InstrData::*;
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

            ListNew { values } => { values.each_mut(fun, f) }

            TupleNew { values } => { values.each_mut(fun, f) }
            TupleNew0 => (),

            NewFunction { id: _ } => (),

            ReadPath { path_id } => { path_id.each_instr_mut(fun, f) }
            WritePath { path_id, value, is_def: _ } => { path_id.each_instr_mut(fun, &mut f); f(fun, value) }

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
    #[inline(always)]
    pub fn get<'s>(self, fun: &'s Function) -> PhiMap<'s> {
        fun.phi_maps[self].phi_map()
    }
}

impl PhiMapImpl {
    #[inline(always)]
    fn phi_map(&self) -> PhiMap { PhiMap { map: &self.map } }
}

impl<'a> PhiMap<'a> {
    pub fn get(self, bb: BlockId) -> Option<InstrId> {
        self.iter().find_map(|(from_bb, instr_id)|
            (*from_bb == bb).then_some(*instr_id))
    }
}

impl<'a> core::fmt::Display for PhiMap<'a> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{{")?;
        for (i, (bb, instr)) in self.iter().enumerate() {
            write!(f, " {}: {}", bb, instr)?;
            if i < self.len() - 1 {
                write!(f, ",")?;
            }
        }
        write!(f, " }}")
    }
}


impl PathId {
    #[inline(always)]
    pub fn get<'s>(self, fun: &'s Function) -> Path<'s> {
        let path = &fun.paths[self];
        Path { base: path.base, keys: &path.keys }
    }

    pub fn set_base(self, fun: &mut Function, base: PathBase) {
        fun.paths[self].base = base;
    }

    #[inline]
    pub fn each_instr<F: FnMut(InstrId)>(self, fun: &Function, mut f: F) {
        let path = &fun.paths[self];

        match path.base {
            PathBase::Env => (),
            PathBase::Instr(instr) => f(instr),
        }

        for key in &path.keys {
            match key {
                PathKey::Field(_) => (),
                PathKey::Index(instr) => f(*instr),
            }
        }
    }

    #[inline]
    pub fn each_instr_mut<F: FnMut(&Function, &mut InstrId)>(self, fun: &mut Function, mut f: F) {
        let mut path = core::mem::replace(&mut fun.paths[self], PathImpl { base: PathBase::Env, keys: vec![] });

        match &mut path.base {
            PathBase::Env => (),
            PathBase::Instr(instr) => f(fun, instr),
        }

        for key in &mut path.keys {
            match key {
                PathKey::Field(_) => (),
                PathKey::Index(instr) => f(fun, instr),
            }
        }
        fun.paths[self] = path;
    }
}

impl<'a> core::fmt::Display for Path<'a> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}, [", self.base)?;
        for (i, key) in self.keys.iter().enumerate() {
            write!(f, "{}", key)?;
            if i < self.keys.len() - 1 {
                write!(f, ", ")?;
            }
        }
        write!(f, "]")
    }
}


impl InstrListId {
    #[inline]
    pub fn get<'s>(self, fun: &'s Function) -> InstrList<'s> {
        InstrList { values: &fun.instr_lists[self] }
    }

    #[inline]
    pub fn each<F: FnMut(InstrId)>(self, fun: &Function, mut f: F) {
        for v in &*fun.instr_lists[self] {
            f(*v)
        }
    }

    #[inline]
    pub fn each_mut<F: FnMut(&Function, &mut InstrId)>(self, fun: &mut Function, mut f: F) {
        let mut instrs = core::mem::take(&mut *fun.instr_lists[self]);
        for instr in &mut instrs {
            f(fun, instr)
        }
        fun.instr_lists[self] = InstrListImpl { values: instrs };
    }
}

impl<'a> core::fmt::Display for InstrList<'a> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "[")?;
        for (i, instr) in self.iter().enumerate() {
            write!(f, " {}", instr)?;
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
    #[inline(always)] pub fn first(&self) -> OptInstrId { self.first }
    #[inline(always)] pub fn last(&self)  -> OptInstrId { self.last }
    #[inline(always)] pub fn len(&self)   -> usize     { self.len as usize }
}



// --- Function ---

// common
impl Function {
    fn new(id: FunctionId) -> Self {
        let mut fun = Function {
            id,
            instrs:      index_vec![],
            blocks:     index_vec![],
            phi_maps:   index_vec![],
            paths:      index_vec![],
            instr_lists: index_vec![],
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
    pub fn num_instrs(&self) -> usize { self.instrs.len() }

    #[inline(always)]
    pub fn instr_ids(&self) -> InstrIdIter { InstrIdIter { at: 0, end: self.instrs.len() as u32 } }
    

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


// instructions
impl Function {
    pub fn new_instr(&mut self, source: SourceRange, data: InstrData) -> InstrId {
        let id = InstrId(self.instrs.len() as u32);
        self.instrs.push(Instr {
            data, source, id,
            prev: None.into(),
            next: None.into(),
            bb:   None.into(),
        });
        id
    }


    pub fn new_phi(&mut self, source: SourceRange, map: &[PhiEntry]) -> InstrId {
        let map_id = PhiMapId(self.phi_maps.len() as u32);
        self.phi_maps.push(PhiMapImpl { map: map.into() });
        self.new_instr(source, InstrData::Phi { map_id })
    }

    pub fn try_phi(&self, instr: InstrId) -> Option<PhiMap> {
        if let InstrData::Phi { map_id } = self.instrs[instr].data {
            return Some(self.phi_maps[map_id].phi_map());
        }
        None
    }

    // @todo: support Phi2.
    // @todo: def_phi variant.
    pub fn set_phi(&mut self, instr: InstrId, map: &[PhiEntry]) {
        let InstrData::Phi { map_id } = self.instrs[instr].data else { unreachable!() };
        self.phi_maps[map_id] = PhiMapImpl { map: map.into() };
    }


    pub fn new_call(&mut self, source: SourceRange, func: InstrId, args: &[InstrId]) -> InstrId {
        let args_id = InstrListId(self.instr_lists.len() as u32);
        self.instr_lists.push(InstrListImpl { values: args.into() });
        self.new_instr(source, InstrData::Call { func, args_id })
    }

    // @todo: try_call
    // @todo: set_call


    pub fn all_args<F: FnMut(InstrId)>(&self, mut f: F) {
        for block in &self.blocks {
            let mut at = block.first;
            while let Some(id) = at.to_option() {
                let instr = &self.instrs[id];
                instr.args(self, &mut f);
                at = instr.next;
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
    pub fn num_block_instrs(&self, bb: BlockId) -> usize {
        self.blocks[bb].len()
    }


    pub fn block_instrs<F: FnMut(&Instr)>(&self, bb: BlockId, mut f: F) {
        let mut at = self.blocks[bb].first;
        while let Some(id) = at.to_option() {
            let instr = &self.instrs[id];
            f(instr);
            at = instr.next;
        }
    }

    pub fn block_instrs_ex<F: FnMut(&Instr) -> bool>(&self, bb: BlockId, mut f: F) {
        let mut at = self.blocks[bb].first;
        while let Some(id) = at.to_option() {
            let instr = &self.instrs[id];
            if !f(instr) {
                break;
            }
            at = instr.next;
        }
    }

    pub fn block_instr_mut<F: FnMut(&mut Instr)>(&mut self, bb: BlockId, mut f: F) {
        let mut at = self.blocks[bb].first;
        while let Some(id) = at.to_option() {
            let instr = &mut self.instrs[id];
            f(instr);
            at = instr.next;
        }
    }

    pub fn block_instr_rev<F: FnMut(&Instr)>(&self, bb: BlockId, mut f: F) {
        let mut at = self.blocks[bb].last;
        while let Some(id) = at.to_option() {
            let instr = &self.instrs[id];
            f(instr);
            at = instr.prev;
        }
    }


    pub fn block_args<F: FnMut(InstrId)>(&self, bb: BlockId, mut f: F) {
        let mut at = self.blocks[bb].first;
        while let Some(id) = at.to_option() {
            let instr = &self.instrs[id];
            instr.args(self, &mut f);
            at = instr.next;
        }
    }

    pub fn block_replace_args<F: FnMut(&Function, &mut InstrId)>(&mut self, bb: BlockId, mut f: F) {
        let mut at = self.blocks[bb].first;
        while let Some(id) = at.to_option() {
            let mut data = self.instrs[id].data;
            data.replace_args(self, &mut f);

            let instr = &mut self.instrs[id];
            instr.data = data;
            at = instr.next;
        }
    }


    pub fn block_successors<F: FnMut(BlockId)>(&self, bb: BlockId, mut f: F) {
        let block = &self.blocks[bb];

        let Some(last) = block.last.to_option() else { unreachable!() };

        use InstrData::*;
        match last.get(self).data {
            Jump { target } => { f(target); }
            SwitchBool { src: _, on_true, on_false }  => { f(on_true); f(on_false); }
            SwitchNil  { src: _, on_nil, on_non_nil } => { f(on_nil); f(on_non_nil); }
            Return { src: _ } => {}

            _ => { unreachable!("called successors on unterminated block") }
        }
    }

    pub fn block_first_phi(&self, bb: BlockId) -> OptInstrId {
        if let Some(first) = bb.get(self).first.to_option() {
            if first.get(self).is_phi() {
                return first.some();
            }
        }
        OptInstrId::NONE
    }

    pub fn block_last_phi(&self, bb: BlockId) -> OptInstrId {
        let mut result = OptInstrId::NONE;
        self.block_instrs_ex(bb, |instr| {
            if instr.is_phi() {
                result = instr.id.some();
                true
            }
            else { false }
        });
        result
    }

    pub fn block_terminator(&self, bb: BlockId) -> OptInstrId {
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
        for instr in self.instr_ids() {
            let instr = instr.get_mut(self);

            // update bb & linked list.
            // @todo: free up the old instructions.
            if let Some(old_bb) = instr.bb.to_option() {
                if let Some(new_id) = new_ids[old_bb] {
                    instr.bb = new_id.some();
                }
                else {
                    instr.bb   = None.into();
                    instr.prev = None.into();
                    instr.next = None.into();
                    // @temp.
                    instr.data = InstrData::LoadNil;
                }
            }

            // phis.
            if instr.is_phi() {
                use InstrData::*;
                match &mut instr.data {
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
            else if instr.is_terminator() {
                use InstrData::*;
                match &mut instr.data {
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
        let param = self.new_instr(source, InstrData::Param { id });
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
        let local = self.new_instr(source, InstrData::Local { id });
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


    pub fn add_instr(&mut self, source: SourceRange, data: InstrData) -> InstrId {
        assert!(self.instrs.len() < u32::MAX as usize / 2);
        let id = InstrId(self.instrs.len() as u32);

        let bb = self.current_block;

        let block = &mut self.blocks[bb];
        let old_last = block.last;

        // update linked list.
        if let Some(last) = old_last.to_option() {
            let last = &mut self.instrs[last];
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

        self.instrs.push(Instr {
            data, source, id,
            prev: old_last,
            next: None.into(),
            bb:   bb.some(),
        });

        id
    }


    #[inline]
    pub fn instr_copy(&mut self, source: SourceRange, src: InstrId) -> InstrId {
        self.add_instr(source, InstrData::Copy { src })
    }

    pub fn instr_phi(&mut self, source: SourceRange, map: &[PhiEntry]) -> InstrId {
        let map_id = PhiMapId(self.phi_maps.len() as u32);
        self.phi_maps.push(PhiMapImpl { map: map.into() });
        self.add_instr(source, InstrData::Phi { map_id })
    }

    #[inline]
    pub fn instr_get_local(&mut self, source: SourceRange, src: LocalId) -> InstrId {
        self.add_instr(source, InstrData::GetLocal { src })
    }

    #[inline]
    pub fn instr_set_local(&mut self, source: SourceRange, dst: LocalId, src: InstrId) -> InstrId {
        self.add_instr(source, InstrData::SetLocal { dst, src })
    }

    #[inline]
    pub fn instr_load_nil(&mut self, source: SourceRange) -> InstrId {
        self.add_instr(source, InstrData::LoadNil)
    }

    #[inline]
    pub fn instr_load_bool(&mut self, source: SourceRange, value: bool) -> InstrId {
        self.add_instr(source, InstrData::LoadBool { value })
    }

    #[inline]
    pub fn instr_load_int(&mut self, source: SourceRange, value: i64) -> InstrId {
        self.add_instr(source, InstrData::LoadInt { value })
    }

    #[inline]
    pub fn instr_load_float(&mut self, source: SourceRange, value: f64) -> InstrId {
        self.add_instr(source, InstrData::LoadFloat { value })
    }

    #[inline]
    pub fn instr_load_string(&mut self, source: SourceRange, id: StringId) -> InstrId {
        self.add_instr(source, InstrData::LoadString { id })
    }

    #[inline]
    pub fn instr_load_env(&mut self, source: SourceRange) -> InstrId {
        self.add_instr(source, InstrData::LoadEnv)
    }

    #[inline]
    pub fn instr_list_new(&mut self, source: SourceRange, values: &[InstrId]) -> InstrId {
        let values_id = InstrListId(self.instr_lists.len() as u32);
        self.instr_lists.push(InstrListImpl { values: values.into() });
        self.add_instr(source, InstrData::ListNew { values: values_id })
    }

    pub fn instr_tuple_new(&mut self, source: SourceRange, values: &[InstrId]) -> InstrId {
        if values.len() == 0 {
            self.add_instr(source, InstrData::TupleNew0)
        }
        else {
            let values_id = InstrListId(self.instr_lists.len() as u32);
            self.instr_lists.push(InstrListImpl { values: values.into() });
            self.add_instr(source, InstrData::TupleNew { values: values_id })
        }
    }

    #[inline]
    pub fn instr_load_unit(&mut self, source: SourceRange) -> InstrId {
        self.add_instr(source, InstrData::TupleNew0)
    }

    #[inline]
    pub fn instr_new_function(&mut self, source: SourceRange, id: FunctionId) -> InstrId {
        self.add_instr(source, InstrData::NewFunction { id })
    }

    #[inline]
    pub fn instr_read_path(&mut self, source: SourceRange, base: PathBase, keys: &[PathKey]) -> InstrId {
        assert!(keys.len() > 0);
        let path_id = PathId(self.paths.len() as u32);
        self.paths.push(PathImpl { base, keys: keys.into() });
        self.add_instr(source, InstrData::ReadPath { path_id })
    }

    #[inline]
    pub fn instr_write_path(&mut self, source: SourceRange, base: PathBase, keys: &[PathKey], value: InstrId, is_def: bool) -> InstrId {
        assert!(keys.len() > 0);
        let path_id = PathId(self.paths.len() as u32);
        self.paths.push(PathImpl { base, keys: keys.into() });
        self.add_instr(source, InstrData::WritePath { path_id, value, is_def })
    }

    #[inline]
    pub fn instr_call(&mut self, source: SourceRange, func: InstrId, args: &[InstrId]) -> InstrId {
        let args_id = InstrListId(self.instr_lists.len() as u32);
        self.instr_lists.push(InstrListImpl { values: args.into() });
        self.add_instr(source, InstrData::Call { func, args_id })
    }

    #[inline]
    pub fn instr_op1(&mut self, source: SourceRange, op: Op1, src: InstrId) -> InstrId {
        self.add_instr(source, InstrData::Op1 { op, src })
    }

    #[inline]
    pub fn instr_op2(&mut self, source: SourceRange, op: Op2, src1: InstrId, src2: InstrId) -> InstrId {
        self.add_instr(source, InstrData::Op2 { op, src1, src2 })
    }

    #[inline]
    pub fn instr_jump(&mut self, source: SourceRange, target: BlockId) -> InstrId {
        self.add_instr(source, InstrData::Jump { target })
    }

    #[inline]
    pub fn instr_switch_bool(&mut self, source: SourceRange, src: InstrId, on_true: BlockId, on_false: BlockId) -> InstrId {
        self.add_instr(source, InstrData::SwitchBool { src, on_true, on_false })
    }

    #[inline]
    pub fn instr_switch_nil(&mut self, source: SourceRange, src: InstrId, on_nil: BlockId, on_non_nil: BlockId) -> InstrId {
        self.add_instr(source, InstrData::SwitchNil { src, on_nil, on_non_nil })
    }

    #[inline]
    pub fn instr_return(&mut self, source: SourceRange, src: InstrId) -> InstrId {
        self.add_instr(source, InstrData::Return { src })
    }
}


// mutation
impl Function {
    fn _insert(block: &mut Block, instrs: &mut IndexVec<InstrId, Instr>, instr_id: InstrId, prev: OptInstrId, next: OptInstrId) {
        let instr = &mut instrs[instr_id];
        // @todo-cleanup: instr.assert_orphan();
        assert_eq!(instr.bb, None.into());
        debug_assert!(instr.id == instr_id);
        debug_assert_eq!(instr.prev, None.into());
        debug_assert_eq!(instr.next, None.into());

        instr.bb   = block.id.some();
        instr.prev = prev;
        instr.next = next;
        block.len += 1;

        if let Some(prev) = prev.to_option() {
            instrs[prev].next = instr_id.some();
        }
        else {
            block.first = instr_id.some();
        }

        if let Some(next) = next.to_option() {
            instrs[next].prev = instr_id.some();
        }
        else {
            block.last = instr_id.some();
        }
    }

    pub fn insert_after(&mut self, bb: BlockId, ref_id: OptInstrId, instr_id: InstrId) {
        let block = &mut self.blocks[bb];
        debug_assert_eq!(block.id, bb);

        let (prev, next) = 
            if let Some(ref_id) = ref_id.to_option() {
                let rf = &self.instrs[ref_id];
                assert_eq!(rf.bb, bb.some());
                (ref_id.some(), rf.next)
            }
            else {
                // prepend.
                (None.into(), block.first)
            };

        Self::_insert(block, &mut self.instrs, instr_id, prev, next)
    }

    pub fn insert_before(&mut self, bb: BlockId, ref_id: OptInstrId, instr_id: InstrId) {
        let block = &mut self.blocks[bb];
        debug_assert_eq!(block.id, bb);

        let (prev, next) = 
            if let Some(ref_id) = ref_id.to_option() {
                let rf = &self.instrs[ref_id];
                assert_eq!(rf.bb, bb.some());
                (rf.prev, ref_id.some())
            }
            else {
                // append.
                (block.last, None.into())
            };

        Self::_insert(block, &mut self.instrs, instr_id, prev, next)
    }

    pub fn insert_before_terminator(&mut self, bb: BlockId, instr_id: InstrId) {
        let block = &mut self.blocks[bb];
        debug_assert_eq!(block.id, bb);

        let last_id = block.last.to_option().unwrap();
        let last = &self.instrs[last_id];
        assert!(last.is_terminator());
        debug_assert_eq!(last.bb, bb.some());

        let (prev, next) = (last.prev, last_id.some());
        Self::_insert(block, &mut self.instrs, instr_id, prev, next)
    }

    #[inline(always)]
    pub fn prepend_instr(&mut self, bb: BlockId, instr_id: InstrId) {
        self.insert_after(bb, None.into(), instr_id)
    }

    #[inline(always)]
    pub fn append_instr(&mut self, bb: BlockId, instr_id: InstrId) {
        self.insert_before(bb, None.into(), instr_id)
    }



    fn _remove(block: &mut Block, instrs: &mut IndexVec<InstrId, Instr>, instr_index: InstrId) -> OptInstrId {
        let instr = &mut instrs[instr_index];
        assert!(instr.bb == block.id.some());

        let old_prev = instr.prev;
        let old_next = instr.next;
        instr.prev = None.into();
        instr.next = None.into();
        instr.bb   = None.into();

        if let Some(prev) = old_prev.to_option() {
            instrs[prev].next = old_next;
        }
        else {
            block.first = old_next;
        }

        if let Some(next) = old_next.to_option() {
            instrs[next].prev = old_prev;
        }
        else {
            block.last = old_prev;
        }

        block.len -= 1;

        old_next
    }

    pub fn retain_block_instr<F: FnMut(&Instr) -> bool>(&mut self, bb: BlockId, mut f: F) {
        let block = &mut self.blocks[bb];

        let mut at = block.first;
        while let Some(current) = at.to_option() {
            let instr = &self.instrs[current];

            if !f(instr) {
                at = Self::_remove(block, &mut self.instrs, current);
            }
            else {
                at = instr.next;
            }
        }
    }

    pub fn retain_instrs<F: FnMut(&Instr) -> bool>(&mut self, mut f: F) {
        for bb in 0..self.blocks.len() as u32 {
            self.retain_block_instr(BlockId(bb), &mut f);
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

        let mut visited = index_vec![false; self.instrs.len()];

        // validate blocks.
        for bb in self.block_ids() {
            let block = &self.blocks[bb];
            assert_eq!(block.id, bb);

            let mut in_params = bb.is_entry();
            let mut in_locals = false;

            let mut in_phis = !bb.is_entry();
            let mut has_terminator = false;
            let mut instr_count = 0;

            let mut at = block.first;
            while let Some(current) = at.to_option() {
                instr_count += 1;

                // only in one bb.
                assert!(!visited[current]);
                visited[current] = true;

                // instr & bb ids.
                let instr = &self.instrs[current];
                assert_eq!(instr.id, current);
                assert_eq!(instr.bb, bb.some());

                // linked list first.
                if current.some() == block.first {
                    assert_eq!(instr.prev, None.into());
                }

                // linked list last.
                if current.some() == block.last {
                    assert_eq!(instr.next, None.into());
                }
                // linked list prev/next.
                else {
                    let next = instr.next.to_option().unwrap();
                    let next = &self.instrs[next];
                    assert_eq!(next.prev, current.some());
                }

                // params & locals.
                if instr.is_param() {
                    assert!(in_params);
                }
                else if in_params {
                    in_params = false;
                    in_locals = true;
                }
                if instr.is_local() {
                    assert!(in_locals);
                }
                else if !in_params {
                    in_locals = false;
                }

                // phis.
                if instr.is_phi() {
                    assert!(in_phis);

                    // one arg for each pred.
                    // pred dominated by arg's bb.
                    let preds = &preds[bb];
                    let mut visited = vec![false; preds.len()];
                    let phi_map = self.try_phi(instr.id).unwrap();
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
                if !instr.is_phi() {
                    instr.args(self, |arg| {
                        let arg = arg.get(self);
                        assert!(arg.has_value());
                        let arg_bb = arg.bb.to_option().unwrap();
                        assert!(idom.is_dominated_by(bb, arg_bb));
                    });
                }

                // terminator: at most one.
                if instr.is_terminator() {
                    assert!(!has_terminator);
                    has_terminator = true;
                }

                at = instr.next;
            }

            assert_eq!(instr_count, block.len());

            if block.first == None.into() {
                assert_eq!(block.last, None.into());
            }
        }

        // validate instructions that are not in blocks.
        for instr_id in self.instr_ids() {
            if !visited[instr_id] {
                let instr = &self.instrs[instr_id];
                assert_eq!(instr.id, instr_id);
                assert_eq!(instr.bb,   None.into());
                assert_eq!(instr.prev, None.into());
                assert_eq!(instr.next, None.into());
            }
        }
    }


    pub fn dump(&self) {
        for bb in self.block_ids() {
            println!("{}:", bb);
            self.block_instrs(bb, |instr| println!("  {}", instr.fmt(self)));
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
                Constant::String { value } => vm.temp_string_new(&value),
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

impl Iterator for InstrIdIter {
    type Item = InstrId;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        if self.at < self.end {
            let result = InstrId(self.at);
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

