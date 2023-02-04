use crate::new_parser::*;


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
        let reg = fb.new_reg();
        self.compile_block(&mut fb, &mut bb, source, block, reg)?;
        println!("{:#?}", fb.blocks);
        Ok(())
    }

    pub fn compile_ast<'a>(&mut self, fb: &mut FunctionBuilder<'a>, bb: &mut BlockId, ast: &Ast<'a>, dst: Reg) -> CompileResult<()> {
        match &ast.data {
            AstData::Nil => {
                fb.add_stmt(*bb, ast, StatementData::LoadNil { dst });
                Ok(())
            }

            AstData::Bool (value) => {
                fb.add_stmt(*bb, ast, StatementData::LoadBool { dst, value: *value });
                Ok(())
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
                if let Some(decl) = fb.find_decl(name) {
                    fb.add_stmt(*bb, ast, StatementData::Copy { dst, src: decl.reg });
                }
                else {
                    unimplemented!()
                }

                Ok(())
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
                self.compile_block(fb, bb, ast.source, block, dst)
            }

            AstData::SubExpr (sub_expr) => {
                self.compile_ast(fb, bb, sub_expr, dst)
            }

            AstData::Local (_) => {
                Err(CompileError { source: ast.source, data: CompileErrorData::UnexpectedLocal })
            }

            AstData::Op1 (op) => {
                let src = fb.new_reg();
                self.compile_ast(fb, bb, &op.child, src)?;

                fb.add_stmt(*bb, ast, match op.kind {
                    ast::Op1Kind::Not    => StatementData::Not { dst, src },
                    ast::Op1Kind::BitNot => StatementData::BitNot { dst, src },
                    ast::Op1Kind::Neg    => StatementData::Neg { dst, src },
                    ast::Op1Kind::Plus   => StatementData::Plus { dst, src },
                });

                Ok(())
            }

            AstData::Op2 (op) => {
                use ast::Op2Kind as OpKind;

                if op.kind == OpKind::Assign {
                    let res = fb.new_reg();
                    self.compile_ast(fb, bb, &op.children[1], res)?;

                    self.compile_assign(fb, bb, &op.children[0], res)?;

                    fb.add_stmt(*bb, ast, StatementData::LoadNil { dst });
                    Ok(())
                }
                else if op.kind.is_comp_assign() {
                    let src1 = fb.new_reg();
                    self.compile_ast(fb, bb, &op.children[0], src1)?;
                    let src2 = fb.new_reg();
                    self.compile_ast(fb, bb, &op.children[1], src2)?;

                    let res = fb.new_reg();
                    fb.add_stmt(*bb, ast, match op.kind {
                        OpKind::AddAssign     => StatementData::Add { dst: res, src1, src2 },
                        OpKind::SubAssign     => StatementData::Sub { dst: res, src1, src2 },
                        OpKind::MulAssign     => StatementData::Mul { dst: res, src1, src2 },
                        OpKind::DivAssign     => StatementData::Div { dst: res, src1, src2 },
                        OpKind::IntDivAssign  => StatementData::IntDiv { dst: res, src1, src2 },
                        OpKind::OrElseAssign  => StatementData::OrElse { dst: res, src1, src2 },

                        _ => unreachable!(),
                    });

                    self.compile_assign(fb, bb, &op.children[0], res)?;

                    fb.add_stmt(*bb, ast, StatementData::LoadNil { dst });
                    Ok(())
                }
                else {
                    let src1 = fb.new_reg();
                    self.compile_ast(fb, bb, &op.children[0], src1)?;
                    let src2 = fb.new_reg();
                    self.compile_ast(fb, bb, &op.children[1], src2)?;

                    fb.add_stmt(*bb, ast, match op.kind {
                        OpKind::And     => StatementData::And    { dst, src1, src2 },
                        OpKind::Or      => StatementData::Or     { dst, src1, src2 },
                        OpKind::Add     => StatementData::Add    { dst, src1, src2 },
                        OpKind::Sub     => StatementData::Sub    { dst, src1, src2 },
                        OpKind::Mul     => StatementData::Mul    { dst, src1, src2 },
                        OpKind::Div     => StatementData::Div    { dst, src1, src2 },
                        OpKind::IntDiv  => StatementData::IntDiv { dst, src1, src2 },
                        OpKind::CmpEq   => StatementData::CmpEq  { dst, src1, src2 },
                        OpKind::CmpNe   => StatementData::CmpNe  { dst, src1, src2 },
                        OpKind::CmpLe   => StatementData::CmpLe  { dst, src1, src2 },
                        OpKind::CmpLt   => StatementData::CmpLt  { dst, src1, src2 },
                        OpKind::CmpGe   => StatementData::CmpGe  { dst, src1, src2 },
                        OpKind::CmpGt   => StatementData::CmpGt  { dst, src1, src2 },
                        OpKind::OrElse  => StatementData::OrElse { dst, src1, src2 },

                        OpKind::Assign |
                        OpKind::AddAssign | OpKind::SubAssign | OpKind::MulAssign |
                        OpKind::DivAssign | OpKind::IntDivAssign |
                        OpKind::OrElseAssign => unreachable!()
                    });
                    Ok(())
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
                let cond = fb.new_reg();
                self.compile_ast(fb, bb, &iff.condition, cond)?;
                fb.terminate(*bb, ast, TerminatorData::SwitchBool {
                    reg:      cond,
                    on_true:  bb_true,
                    on_false: bb_false,
                });
                *bb = after_if;

                // on_true
                self.compile_ast(fb, &mut bb_true, &iff.on_true, dst)?;
                fb.terminate_at(bb_true,
                    iff.on_true.source.end.to_range(),
                    TerminatorData::Jump { target: after_if });

                // on_false
                let false_term_src =
                    if let Some(on_false) = &iff.on_false {
                        self.compile_ast(fb, &mut bb_false, on_false, dst)?;
                        on_false.source.end.to_range()
                    }
                    else {
                        let source = ast.source.end.to_range();
                        fb.add_stmt_at(bb_false, source, StatementData::LoadNil { dst });
                        source
                    };
                fb.terminate_at(bb_false, false_term_src,
                    TerminatorData::Jump { target: after_if });

                Ok(())
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
        block_source: SourceRange, block: &ast::Block<'a>, dst: Reg) -> CompileResult<()>
    {
        let scope = fb.begin_scope();

        let mut stmts_end = block.children.len();
        if block.last_is_expr { stmts_end -= 1 }

        // visit statements.
        // handle locals.
        for i in 0..stmts_end {
            let node = &block.children[i];

            if let AstData::Local(local) = &node.data {
                let reg = fb.add_decl(local.name);

                if let Some(value) = &local.value {
                    self.compile_ast(fb, bb, value, reg)?;
                }
                else {
                    fb.add_stmt(*bb, node, StatementData::LoadNil { dst: reg });
                }
            }
            else {
                let reg = fb.new_reg();
                self.compile_ast(fb, bb, node, reg)?;
            }
        }

        // last statement (or expression).
        if block.last_is_expr {
            self.compile_ast(fb, bb, &block.children[stmts_end], dst)?;
        }
        else {
            let source = block_source.end.to_range();
            // @todo: return empty tuple.
            fb.add_stmt_at(*bb, source, StatementData::LoadNil { dst });
        }

        fb.end_scope(scope);
        Ok(())
    }

    pub fn compile_assign<'a>(&mut self, fb: &mut FunctionBuilder<'a>, bb: &mut BlockId,
        ast: &Ast<'a>, src: Reg) -> CompileResult<()>
    {
        match &ast.data {
            AstData::Ident (name) => {
                if let Some(decl) = fb.find_decl(name) {
                    fb.add_stmt(*bb, ast, StatementData::Copy { dst: decl.reg, src });
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



#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Reg(u32);


#[derive(Clone, Debug)]
pub struct Statement {
    pub source: SourceRange,
    pub data:   StatementData,
}

impl Statement {
    #[inline]
    pub fn at(ast: &Ast, data: StatementData) -> Statement {
        Statement { source: ast.source, data }
    }
}


#[derive(Clone, Debug)]
pub enum StatementData {
    Copy        { dst: Reg, src: Reg },

    LoadNil     { dst: Reg },
    LoadBool    { dst: Reg, value: bool },
    LoatInt     { dst: Reg, value: i64 },
    LoadFloat   { dst: Reg, value: f64 },

    Not         { dst: Reg, src: Reg },
    BitNot      { dst: Reg, src: Reg },
    Neg         { dst: Reg, src: Reg },
    Plus        { dst: Reg, src: Reg },

    And         { dst: Reg, src1: Reg, src2: Reg },
    Or          { dst: Reg, src1: Reg, src2: Reg },
    Add         { dst: Reg, src1: Reg, src2: Reg },
    Sub         { dst: Reg, src1: Reg, src2: Reg },
    Mul         { dst: Reg, src1: Reg, src2: Reg },
    Div         { dst: Reg, src1: Reg, src2: Reg },
    IntDiv      { dst: Reg, src1: Reg, src2: Reg },
    CmpEq       { dst: Reg, src1: Reg, src2: Reg },
    CmpNe       { dst: Reg, src1: Reg, src2: Reg },
    CmpLe       { dst: Reg, src1: Reg, src2: Reg },
    CmpLt       { dst: Reg, src1: Reg, src2: Reg },
    CmpGe       { dst: Reg, src1: Reg, src2: Reg },
    CmpGt       { dst: Reg, src1: Reg, src2: Reg },
    OrElse      { dst: Reg, src1: Reg, src2: Reg },
}


#[derive(Clone, Debug)]
pub struct Terminator {
    pub source: SourceRange,
    pub data:   TerminatorData,
}

#[derive(Clone, Debug)]
pub enum TerminatorData {
    None,
    Jump        { target: BlockId },
    SwitchBool  { reg: Reg, on_true: BlockId, on_false: BlockId },
    Return      { reg: Reg },
}

impl TerminatorData {
    #[inline]
    pub fn is_none(&self) -> bool {
        if let TerminatorData::None = self { true } else { false }
    }
}



#[derive(Clone, Copy, Debug, PartialEq)]
pub struct BlockId(u32);

#[derive(Clone, Debug)]
pub struct Block {
    pub statements: Vec<Statement>,
    pub terminator: Terminator,
}

impl Block {
    pub fn new() -> Block {
        Block {
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
}


#[derive(Clone, Debug)]
pub struct Function {
    pub blocks: Vec<Block>,
}

impl Function {
    pub fn new() -> Function {
        Function { blocks: vec![] }
    }
}


#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
pub struct ScopeId(u32);


#[derive(Clone, Debug)]
pub struct Decl<'a> {
    pub name:  &'a str,
    pub reg:   Reg,
    pub scope: ScopeId,
}


pub struct FunctionBuilder<'a> {
    blocks:     Vec<Block>,
    decls:      Vec<Decl<'a>>,
    scope:      ScopeId,
    next_reg:   Reg,
}

impl<'a> FunctionBuilder<'a> {
    pub fn new() -> Self {
        FunctionBuilder {
            blocks:     vec![],
            decls:      vec![],
            scope:      ScopeId(0),
            next_reg:   Reg(0),
        }
    }

    pub fn new_block(&mut self) -> BlockId {
        let id = BlockId(self.blocks.len() as u32);
        self.blocks.push(Block::new());
        id
    }

    pub fn terminate_at(&mut self, bb: BlockId, source: SourceRange, data: TerminatorData) {
        let block = &mut self.blocks[bb.0 as usize];
        assert!(!block.terminated());
        block.terminator = Terminator { source, data };
    }

    pub fn terminate(&mut self, bb: BlockId, at: &Ast, data: TerminatorData) {
        self.terminate_at(bb, at.source, data)
    }

    pub fn new_reg(&mut self) -> Reg {
        self.next_reg.0 += 1;
        self.next_reg
    }

    pub fn add_stmt_at(&mut self, bb: BlockId, source: SourceRange, data: StatementData) {
        let block = &mut self.blocks[bb.0 as usize];
        assert!(!block.terminated());
        block.statements.push(Statement { source, data });
    }

    pub fn add_stmt(&mut self, bb: BlockId, at: &Ast, data: StatementData) {
        self.add_stmt_at(bb, at.source, data)
    }

    pub fn add_decl(&mut self, name: &'a str) -> Reg {
        let reg = self.new_reg();
        self.decls.push(Decl { name, reg, scope: self.scope });
        reg
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

