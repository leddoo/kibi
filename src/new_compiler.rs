use crate::new_parser::*;
use core::cell::Cell;


#[derive(Debug)]
pub struct CompileError {
    pub source: SourceRange,
    pub data:   CompileErrorData,
}

impl CompileError {
    #[inline]
    pub fn at(ast: &Ast, data: CompileErrorData) -> CompileError {
        CompileError { source: ast.source, data }
    }
}


#[derive(Debug)]
pub enum CompileErrorData {
    UnexpectedLocal,
    InvalidAssignTarget,
}

pub type CompileResult<T> = Result<T, CompileError>;



pub struct Compiler {
}

impl Compiler {
    pub fn compile_chunk(&mut self, source: SourceRange, block: &ast::Block) -> CompileResult<()> {
        let mut fb = FunctionBuilder::new();
        let mut bb = fb.new_block();
        self.compile_block(&mut fb, &mut bb, source, block, false)?;

        let nil = fb.add_stmt_at(bb, source, StatementData::LoadNil);
        fb.terminate_at(bb, source, TerminatorData::Return { src: nil });

        for bb in &fb.blocks {
            println!("{}", bb);
        }


        let (predecessors, post_order) = {
            let mut predecessors = vec![vec![]; fb.blocks.len()];
            let mut post_order = vec![];
            let mut visited = vec![false; fb.blocks.len()];

            fn visit(fb: &FunctionBuilder, bb: BlockId,
                predecessors: &mut Vec<Vec<BlockId>>,
                post_order: &mut Vec<BlockId>,
                visited: &mut Vec<bool>,
            ) {
                let block = &fb.blocks[bb.usize()];

                block.successors(|succ| {
                    predecessors[succ.usize()].push(bb);

                    if !visited[succ.usize()] {
                        visited[succ.usize()] = true;
                        visit(fb, succ, predecessors, post_order, visited);
                    }
                });

                post_order.push(bb);
            }
            visit(&fb, BlockId::ENTRY, &mut predecessors, &mut post_order, &mut visited);

            for bb in post_order.iter().cloned() {
                if !bb.is_entry() {
                    assert!(predecessors[bb.usize()].len() > 0);
                }
            }

            (predecessors, post_order)
        };

        let post_indices = {
            let mut indices = vec![usize::MAX; fb.blocks.len()];
            for (index, bb) in post_order.iter().cloned().enumerate() {
                indices[bb.usize()] = index;
            }
            indices
        };

        let immediate_dominators = {
            let mut doms = vec![None; fb.blocks.len()];

            #[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
            struct PostIndex(usize);

            impl PostIndex {
                #[inline(always)]
                fn usize(self) -> usize { self.0 }
            }

            let bb0 = PostIndex(post_indices[BlockId::ENTRY.usize()]);
            doms[bb0.usize()] = Some(bb0);

            let mut changed = true;
            while changed {
                changed = false;

                for bb_id in post_order.iter().rev().cloned() {
                    if bb_id.is_entry() { continue }

                    let preds = &predecessors[bb_id.usize()];
                    let bb = PostIndex(post_indices[bb_id.usize()]);

                    let mut new_dom = PostIndex(post_indices[preds[0].usize()]);

                    for pred_id in preds.iter().skip(1) {
                        let pred = PostIndex(post_indices[pred_id.usize()]);

                        // intersect.
                        if doms[pred.usize()].is_some() {
                            let mut x = new_dom;
                            let mut y = pred;

                            while x != y {
                                while x < y {
                                    x = doms[x.usize()].unwrap();
                                }
                                while y < x {
                                    y = doms[y.usize()].unwrap();
                                }
                            }

                            new_dom = x;
                        }
                    }

                    if doms[bb.usize()] != Some(new_dom) {
                        doms[bb.usize()] = Some(new_dom);
                        changed = true;
                    }
                }
            }

            fb.blocks.iter()
                .map(|block| {
                    let bb = block.id;
                    let pi = post_indices[bb.usize()];
                    let idomi = doms[pi].unwrap();
                    let idom  = post_order[idomi.usize()];
                    idom
                })
                .collect::<Vec<BlockId>>()
        };

        let dom_frontiers = {
            let mut dfs = vec![vec![]; fb.blocks.len()];

            for block in fb.blocks.iter() {
                let bb = block.id;

                let preds = &predecessors[bb.usize()];
                if preds.len() < 2 { continue }

                let idom = immediate_dominators[bb.usize()];
                for pred in preds {
                    let mut at = *pred;
                    while at != idom {
                        let df = &mut dfs[at.usize()];
                        if !df.contains(&bb) {
                            df.push(bb);
                        }
                        at = immediate_dominators[at.usize()];
                    }
                }
            }

            dfs
        };

        println!("df:");
        for df in &dom_frontiers {
            println!(" {:?}", df);
        }

        Ok(())
    }

    pub fn compile_ast<'a>(&mut self, fb: &mut FunctionBuilder<'a>, bb: &mut BlockId,
        ast: &Ast<'a>, need_value: bool) -> CompileResult<Option<StmtRef<'a>>>
    {
        match &ast.data {
            AstData::Nil => {
                Ok(Some(fb.add_stmt(*bb, ast, StatementData::LoadNil)))
            }

            AstData::Bool (value) => {
                Ok(Some(fb.add_stmt(*bb, ast, StatementData::LoadBool { value: *value })))
            }

            AstData::Number (value) => {
                let _ = value;
                unimplemented!()
            }

            AstData::QuotedString (value) => {
                let _ = value;
                unimplemented!()
            }

            AstData::Ident (name) => {
                Ok(Some(if let Some(decl) = fb.find_decl(name) {
                    fb.add_stmt(*bb, ast, StatementData::GetLocal { src: decl.id })
                }
                else {
                    unimplemented!()
                }))
            }

            AstData::Tuple (tuple) => {
                let _ = tuple;
                unimplemented!()
            }

            AstData::List (list) => {
                let _ = list;
                unimplemented!()
            }

            AstData::Table (table) => {
                let _ = table;
                unimplemented!()
            }

            AstData::Block (block) => {
                self.compile_block(fb, bb, ast.source, block, need_value)
            }

            AstData::SubExpr (sub_expr) => {
                self.compile_ast(fb, bb, sub_expr, need_value)
            }

            AstData::Local (_) => {
                Err(CompileError { source: ast.source, data: CompileErrorData::UnexpectedLocal })
            }

            AstData::Op1 (op) => {
                let src = self.compile_ast(fb, bb, &op.child, true)?.unwrap();
                Ok(Some(fb.add_stmt(*bb, ast, match op.kind {
                    ast::Op1Kind::Not    => StatementData::Not    { src },
                    ast::Op1Kind::BitNot => StatementData::BitNot { src },
                    ast::Op1Kind::Neg    => StatementData::Neg    { src },
                    ast::Op1Kind::Plus   => StatementData::Plus   { src },
                })))
            }

            AstData::Op2 (op) => {
                use ast::Op2Kind as OpKind;

                if op.kind == OpKind::Assign {
                    let value = self.compile_ast(fb, bb, &op.children[1], true)?.unwrap();
                    self.compile_assign(fb, bb, &op.children[0], value)?;

                    Ok(if need_value {
                        Some(fb.add_stmt(*bb, ast, StatementData::LoadNil))
                    }
                    else { None })
                }
                else if op.kind.is_comp_assign() {
                    let src1 = self.compile_ast(fb, bb, &op.children[0], true)?.unwrap();
                    let src2 = self.compile_ast(fb, bb, &op.children[1], true)?.unwrap();

                    let value = fb.add_stmt(*bb, ast, match op.kind {
                        OpKind::AddAssign     => StatementData::Add    { src1, src2 },
                        OpKind::SubAssign     => StatementData::Sub    { src1, src2 },
                        OpKind::MulAssign     => StatementData::Mul    { src1, src2 },
                        OpKind::DivAssign     => StatementData::Div    { src1, src2 },
                        OpKind::IntDivAssign  => StatementData::IntDiv { src1, src2 },
                        OpKind::OrElseAssign  => StatementData::OrElse { src1, src2 },

                        _ => unreachable!(),
                    });

                    self.compile_assign(fb, bb, &op.children[0], value)?;

                    Ok(if need_value {
                        Some(fb.add_stmt(*bb, ast, StatementData::LoadNil))
                    }
                    else { None })
                }
                else {
                    let src1 = self.compile_ast(fb, bb, &op.children[0], true)?.unwrap();
                    let src2 = self.compile_ast(fb, bb, &op.children[1], true)?.unwrap();

                    Ok(Some(fb.add_stmt(*bb, ast, match op.kind {
                        OpKind::And     => StatementData::And    { src1, src2 },
                        OpKind::Or      => StatementData::Or     { src1, src2 },
                        OpKind::Add     => StatementData::Add    { src1, src2 },
                        OpKind::Sub     => StatementData::Sub    { src1, src2 },
                        OpKind::Mul     => StatementData::Mul    { src1, src2 },
                        OpKind::Div     => StatementData::Div    { src1, src2 },
                        OpKind::IntDiv  => StatementData::IntDiv { src1, src2 },
                        OpKind::CmpEq   => StatementData::CmpEq  { src1, src2 },
                        OpKind::CmpNe   => StatementData::CmpNe  { src1, src2 },
                        OpKind::CmpLe   => StatementData::CmpLe  { src1, src2 },
                        OpKind::CmpLt   => StatementData::CmpLt  { src1, src2 },
                        OpKind::CmpGe   => StatementData::CmpGe  { src1, src2 },
                        OpKind::CmpGt   => StatementData::CmpGt  { src1, src2 },
                        OpKind::OrElse  => StatementData::OrElse { src1, src2 },

                        OpKind::Assign |
                        OpKind::AddAssign | OpKind::SubAssign | OpKind::MulAssign |
                        OpKind::DivAssign | OpKind::IntDivAssign |
                        OpKind::OrElseAssign => unreachable!()
                    })))
                }
            }

            AstData::Field (field) => {
                let _ = field;
                unimplemented!()
            }

            AstData::OptChain (opt_chain) => {
                let _ = opt_chain;
                unimplemented!()
            }

            AstData::Index (index) => {
                let _ = index;
                unimplemented!()
            }

            AstData::Call (call) => {
                let _ = call;
                unimplemented!()
            }

            AstData::If (iff) => {
                let mut bb_true = fb.new_block();
                let mut bb_false = fb.new_block();
                let after_if = fb.new_block();

                // condition.
                let cond = self.compile_ast(fb, bb, &iff.condition, true)?.unwrap();
                fb.terminate(*bb, ast, TerminatorData::SwitchBool {
                    src:      cond,
                    on_true:  bb_true,
                    on_false: bb_false,
                });
                *bb = after_if;

                // on_true
                let value_true = self.compile_ast(fb, &mut bb_true, &iff.on_true, need_value)?;
                fb.terminate_at(bb_true,
                    iff.on_true.source.end.to_range(),
                    TerminatorData::Jump { target: after_if });

                // on_false
                let (value_false, on_false_src) =
                    if let Some(on_false) = &iff.on_false {
                        let v = self.compile_ast(fb, &mut bb_false, on_false, need_value)?;
                        (v, on_false.source.end.to_range())
                    }
                    else {
                        let source = ast.source.end.to_range();
                        let v = need_value.then(|| fb.add_stmt_at(bb_false, source, StatementData::LoadNil));
                        (v, source)
                    };
                fb.terminate_at(bb_false, on_false_src,
                    TerminatorData::Jump { target: after_if });

                if need_value {
                    let map = Box::leak(Box::new([
                        Cell::new((bb_true,  value_true.unwrap())),
                        Cell::new((bb_false, value_false.unwrap())),
                    ]));
                    let result = fb.add_stmt(after_if, ast, StatementData::Phi { map });
                    Ok(Some(result))
                }
                else { Ok(None) }
            }

            AstData::While (whilee) => {
                let _ = whilee;
                unimplemented!()
            }

            AstData::Break => {
                unimplemented!()
            }

            AstData::Continue => {
                unimplemented!()
            }

            AstData::Return (returnn) => {
                let _ = returnn;
                unimplemented!()
            }

            AstData::Fn (fnn) => {
                let _ = fnn;
                unimplemented!()
            }
        }
    }

    pub fn compile_block<'a>(&mut self, fb: &mut FunctionBuilder<'a>, bb: &mut BlockId,
        block_source: SourceRange, block: &ast::Block<'a>, need_value: bool) -> CompileResult<Option<StmtRef<'a>>>
    {
        let scope = fb.begin_scope();

        let mut stmts_end = block.children.len();
        if block.last_is_expr { stmts_end -= 1 }

        // visit statements.
        // handle locals.
        for i in 0..stmts_end {
            let node = &block.children[i];

            // local decls.
            if let AstData::Local(local) = &node.data {
                let lid = fb.add_decl(local.name);

                let v = 
                    if let Some(value) = &local.value {
                        self.compile_ast(fb, bb, value, true)?.unwrap()
                    }
                    else {
                        fb.add_stmt(*bb, node, StatementData::LoadNil)
                    };
                fb.add_stmt(*bb, node, StatementData::SetLocal { dst: lid, src: v });
            }
            else {
                self.compile_ast(fb, bb, node, false)?;
            }
        }

        // last statement (or expression).
        let result =
            if block.last_is_expr {
                self.compile_ast(fb, bb, &block.children[stmts_end], need_value)?
            }
            else if need_value {
                let source = block_source.end.to_range();
                // @todo: return empty tuple.
                Some(fb.add_stmt_at(*bb, source, StatementData::LoadNil))
            }
            else { None };

        fb.end_scope(scope);
        Ok(result)
    }

    pub fn compile_assign<'a>(&mut self, fb: &mut FunctionBuilder<'a>, bb: &mut BlockId,
        ast: &Ast<'a>, value: StmtRef<'a>) -> CompileResult<()>
    {
        match &ast.data {
            AstData::Ident (name) => {
                if let Some(decl) = fb.find_decl(name) {
                    fb.add_stmt(*bb, ast, StatementData::SetLocal { dst: decl.id, src: value });
                }
                else {
                    unimplemented!()
                }

                Ok(())
            }

            AstData::Field (field) => {
                let _ = field;
                unimplemented!()
            }

            AstData::Index (index) => {
                let _ = index;
                unimplemented!()
            }

            _ => Err(CompileError::at(ast, CompileErrorData::InvalidAssignTarget)),
        }
    }
}



#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
pub struct StmtId(u32);

impl StmtId {
    #[inline(always)]
    pub fn usize(self) -> usize { self.0 as usize }
}


#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct StmtRef<'a>(&'a Cell<Statement<'a>>);

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

impl<'a> core::ops::Deref for StmtRef<'a> {
    type Target = Cell<Statement<'a>>;
    #[inline]
    fn deref(&self) -> &Self::Target { self.0 }
}

impl<'a> core::fmt::Display for StmtRef<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let stmt = self.get();

        write!(f, "r{} := ", stmt.id.0)?;

        use StatementData::*;
        match &stmt.data {
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

            Not    { src } => { write!(f, "not r{}",     src.get().id.0) }
            BitNot { src } => { write!(f, "bit_not r{}", src.get().id.0) }
            Neg    { src } => { write!(f, "neg r{}",     src.get().id.0) }
            Plus   { src } => { write!(f, "plus r{}",    src.get().id.0) }

            And    { src1, src2 } => { write!(f, "and r{}, r{}",     src1.get().id.0, src2.get().id.0) }
            Or     { src1, src2 } => { write!(f, "or r{}, r{}",      src1.get().id.0, src2.get().id.0) }
            Add    { src1, src2 } => { write!(f, "add r{}, r{}",     src1.get().id.0, src2.get().id.0) }
            Sub    { src1, src2 } => { write!(f, "sub r{}, r{}",     src1.get().id.0, src2.get().id.0) }
            Mul    { src1, src2 } => { write!(f, "mul r{}, r{}",     src1.get().id.0, src2.get().id.0) }
            Div    { src1, src2 } => { write!(f, "div r{}, r{}",     src1.get().id.0, src2.get().id.0) }
            IntDiv { src1, src2 } => { write!(f, "int_div r{}, r{}", src1.get().id.0, src2.get().id.0) }
            CmpEq  { src1, src2 } => { write!(f, "cmp_eq r{}, r{}",  src1.get().id.0, src2.get().id.0) }
            CmpNe  { src1, src2 } => { write!(f, "cmp_ne r{}, r{}",  src1.get().id.0, src2.get().id.0) }
            CmpLe  { src1, src2 } => { write!(f, "cmp_le r{}, r{}",  src1.get().id.0, src2.get().id.0) }
            CmpLt  { src1, src2 } => { write!(f, "cmp_lt r{}, r{}",  src1.get().id.0, src2.get().id.0) }
            CmpGe  { src1, src2 } => { write!(f, "cmp_ge r{}, r{}",  src1.get().id.0, src2.get().id.0) }
            CmpGt  { src1, src2 } => { write!(f, "cmp_gt r{}, r{}",  src1.get().id.0, src2.get().id.0) }
            OrElse { src1, src2 } => { write!(f, "or_else r{}, r{}", src1.get().id.0, src2.get().id.0) }
        }
    }
}


#[derive(Clone, Copy, Debug)]
pub struct Statement<'a> {
    pub id:     StmtId,
    pub source: SourceRange,
    pub data:   StatementData<'a>,
}

impl<'a> core::ops::Deref for Statement<'a> {
    type Target = StatementData<'a>;
    #[inline(always)]
    fn deref(&self) -> &Self::Target { &self.data }
}


#[derive(Clone, Copy, Debug)]
pub enum StatementData<'a> {
    Copy        { src: StmtRef<'a> },

    Phi         { map: &'a [Cell<(BlockId, StmtRef<'a>)>] },

    GetLocal    { src: LocalId },
    SetLocal    { dst: LocalId, src: StmtRef<'a> },

    LoadNil,
    LoadBool    { value: bool },
    LoatInt     { value: i64 },
    LoadFloat   { value: f64 },

    Not         { src: StmtRef<'a> },
    BitNot      { src: StmtRef<'a> },
    Neg         { src: StmtRef<'a> },
    Plus        { src: StmtRef<'a> },

    And         { src1: StmtRef<'a>, src2: StmtRef<'a> },
    Or          { src1: StmtRef<'a>, src2: StmtRef<'a> },
    Add         { src1: StmtRef<'a>, src2: StmtRef<'a> },
    Sub         { src1: StmtRef<'a>, src2: StmtRef<'a> },
    Mul         { src1: StmtRef<'a>, src2: StmtRef<'a> },
    Div         { src1: StmtRef<'a>, src2: StmtRef<'a> },
    IntDiv      { src1: StmtRef<'a>, src2: StmtRef<'a> },
    CmpEq       { src1: StmtRef<'a>, src2: StmtRef<'a> },
    CmpNe       { src1: StmtRef<'a>, src2: StmtRef<'a> },
    CmpLe       { src1: StmtRef<'a>, src2: StmtRef<'a> },
    CmpLt       { src1: StmtRef<'a>, src2: StmtRef<'a> },
    CmpGe       { src1: StmtRef<'a>, src2: StmtRef<'a> },
    CmpGt       { src1: StmtRef<'a>, src2: StmtRef<'a> },
    OrElse      { src1: StmtRef<'a>, src2: StmtRef<'a> },
}


#[derive(Clone, Debug)]
pub struct Terminator<'a> {
    pub source: SourceRange,
    pub data:   TerminatorData<'a>,
}

impl<'a> core::ops::Deref for Terminator<'a> {
    type Target = TerminatorData<'a>;
    #[inline(always)]
    fn deref(&self) -> &Self::Target { &self.data }
}

impl<'a> core::fmt::Display for Terminator<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use TerminatorData::*;
        match &self.data {
            None => {
                write!(f, "none")
            }
            Jump { target } => {
                write!(f, "jump {}", target)
            }
            SwitchBool { src, on_true, on_false } => {
                write!(f, "switch_bool r{}, {}, {}", src.get().id.0, on_true, on_false)
            }
            Return { src } => {
                write!(f, "return r{}", src.get().id.0)
            }
        }
    }
}


#[derive(Clone, Debug)]
pub enum TerminatorData<'a> {
    None,
    Jump        { target: BlockId },
    SwitchBool  { src: StmtRef<'a>, on_true: BlockId, on_false: BlockId },
    Return      { src: StmtRef<'a> },
}

impl<'a> TerminatorData<'a> {
    #[inline]
    pub fn is_none(&self) -> bool {
        if let TerminatorData::None = self { true } else { false }
    }
}



#[derive(Clone, Copy, Debug, PartialEq)]
pub struct BlockId(u32);

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


#[derive(Clone, Debug)]
pub struct Block<'a> {
    pub id: BlockId,
    pub statements: Vec<StmtRef<'a>>,
    pub terminator: Terminator<'a>,
}

impl<'a> Block<'a> {
    pub fn new(id: BlockId) -> Self {
        Block {
            id,
            statements: vec![],
            terminator: Terminator {
                source: SourceRange::null(),
                data:   TerminatorData::None,
            },
        }
    }

    #[inline]
    pub fn terminated(&self) -> bool {
        !self.terminator.data.is_none()
    }

    #[inline]
    pub fn successors<F: FnMut(BlockId)>(&self, mut f: F) {
        use TerminatorData::*;
        match &self.terminator.data {
            None => { unreachable!("called successors on unterminated block") }

            Jump { target } => { f(*target); }

            SwitchBool { src: _, on_true, on_false } => { f(*on_true); f(*on_false); }

            Return { src: _ } => {}
        }
    }
}

impl<'a> core::fmt::Display for Block<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:\n", self.id)?;

        for stmt in &self.statements {
            write!(f, "  {}\n", *stmt)?;
        }

        write!(f, "  {}\n", self.terminator)
    }
}


#[derive(Clone, Debug)]
pub struct Function<'a> {
    pub blocks: Vec<Block<'a>>,
}


#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
pub struct LocalId(u32);

impl core::fmt::Display for LocalId {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "l{}", self.0)
    }
}


#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
pub struct ScopeId(u32);


#[derive(Clone, Debug)]
pub struct Decl<'a> {
    pub name:  &'a str,
    pub id:    LocalId,
    pub scope: ScopeId,
}


pub struct FunctionBuilder<'a> {
    blocks:     Vec<Block<'a>>,
    decls:      Vec<Decl<'a>>,
    scope:      ScopeId,
    next_local: LocalId,
    next_stmt:  StmtId,
}

impl<'a> FunctionBuilder<'a> {
    pub fn new() -> Self {
        FunctionBuilder {
            blocks:     vec![],
            decls:      vec![],
            scope:      ScopeId(0),
            next_local: LocalId(0),
            next_stmt:  StmtId(0),
        }
    }

    pub fn new_block(&mut self) -> BlockId {
        let id = BlockId(self.blocks.len() as u32);
        self.blocks.push(Block::new(id));
        id
    }

    pub fn terminate_at(&mut self, bb: BlockId, source: SourceRange, data: TerminatorData<'a>) {
        let block = &mut self.blocks[bb.0 as usize];
        assert!(!block.terminated());
        block.terminator = Terminator { source, data };
    }

    pub fn terminate(&mut self, bb: BlockId, at: &Ast, data: TerminatorData<'a>) {
        self.terminate_at(bb, at.source, data)
    }

    pub fn new_local(&mut self) -> LocalId {
        let id = self.next_local;
        self.next_local.0 += 1;
        id
    }

    pub fn add_stmt_at(&mut self, bb: BlockId, source: SourceRange, data: StatementData<'a>) -> StmtRef<'a> {
        let block = &mut self.blocks[bb.0 as usize];
        assert!(!block.terminated());

        let id = self.next_stmt;
        self.next_stmt.0 += 1;

        let stmt = StmtRef(Box::leak(Box::new(Cell::new(Statement { id, source, data }))));
        block.statements.push(stmt);
        stmt
    }

    pub fn add_stmt(&mut self, bb: BlockId, at: &Ast, data: StatementData<'a>) -> StmtRef<'a> {
        self.add_stmt_at(bb, at.source, data)
    }

    pub fn add_decl(&mut self, name: &'a str) -> LocalId {
        let id = self.new_local();
        self.decls.push(Decl { name, id, scope: self.scope });
        id
    }

    pub fn find_decl(&self, name: &str) -> Option<&Decl<'a>> {
        self.decls.iter().rev().find(|decl| decl.name == name)
    }

    pub fn begin_scope(&mut self) -> ScopeId {
        self.scope.0 += 1;
        self.scope
    }

    pub fn end_scope(&mut self, scope: ScopeId) {
        assert_eq!(self.scope, scope);
        self.decls.retain(|decl| decl.scope < self.scope);
        self.scope.0 -= 1;
    }
}

