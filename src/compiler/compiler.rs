use crate::bytecode::Instruction;
use super::*;


#[derive(Debug)]
pub struct CompileError {
    pub source: SourceRange,
    pub data:   CompileErrorData,
}


#[derive(Debug)]
pub enum CompileErrorData {
    UnexpectedLocal,
    InvalidAssignTarget,
}

pub type CompileResult<T> = Result<T, CompileError>;



#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
pub struct ScopeId(u32);


#[derive(Clone, Debug)]
pub struct Decl<'a> {
    pub name:  &'a str,
    pub id:    LocalId,
    pub scope: ScopeId,
}


pub struct Compiler {
}


pub struct Ctx<'a> {
    scope: ScopeId,
    decls: Vec<Decl<'a>>,
}



impl CompileError {
    #[inline(always)]
    pub fn at(ast: &Ast, data: CompileErrorData) -> CompileError {
        CompileError { source: ast.source, data }
    }
}


impl Compiler {
    pub fn compile_chunk(&mut self, source: SourceRange, block: &ast::Block) -> CompileResult<(Vec<Instruction>, u32)> {
        let mut fun = {
            let mut ctx = Ctx::new();
            let mut fun = Function::new();
            self.compile_block(&mut ctx, &mut fun, source, block, false)?;

            let nil = fun.add_load_nil(source);
            fun.add_return(source, nil);

            fun.dump();
            fun
        };


        let (preds, post_order) = fun.preds_and_post_order();

        let post_indices = post_order.indices();

        let idoms = fun.immediate_dominators(&preds, &post_order, &post_indices);

        let dom_tree = fun.dominator_tree(&idoms);

        let dom_frontiers = fun.dominance_frontiers(&preds, &idoms);

        opt::local2reg_ex(&mut fun, &preds, &dom_tree, &dom_frontiers);
        println!("local2reg done");
        fun.dump();

        opt::copy_propagation_ex(&mut fun, &dom_tree);
        println!("copy propagation done");
        fun.dump();

        opt::dead_copy_elim(&mut fun);
        println!("dead copy elim done");
        fun.dump();


        let (code, num_regs) = fun.compile_mut_ex(&post_order, &idoms, &dom_tree);
        println!("bytecode:");
        crate::bytecode::dump(&code);

        Ok((code, num_regs))
    }

    pub fn compile_ast<'a>(&mut self,
        ctx: &mut Ctx<'a>, fun: &mut Function,
        ast: &Ast<'a>, need_value: bool,
    ) -> CompileResult<Option<StmtId>> {
        match &ast.data {
            AstData::Nil => {
                Ok(Some(fun.add_load_nil(ast.source)))
            }

            AstData::Bool (value) => {
                Ok(Some(fun.add_load_bool(ast.source, *value)))
            }

            AstData::Number (value) => {
                let value = value.parse().unwrap();
                Ok(Some(fun.add_load_int(ast.source, value)))
            }

            AstData::QuotedString (value) => {
                let _ = value;
                unimplemented!()
            }

            AstData::Ident (name) => {
                Ok(Some(if let Some(decl) = ctx.find_decl(name) {
                    fun.add_get_local(ast.source, decl.id)
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
                let values = &list.values;

                let list = fun.add_list_new(ast.source);
                for value in values {
                    let v = self.compile_ast(ctx, fun, value, true)?.unwrap();
                    fun.add_list_append(value.source, list, v);
                }

                Ok(Some(list))
            }

            AstData::Table (table) => {
                let _ = table;
                unimplemented!()
            }

            AstData::Block (block) => {
                self.compile_block(ctx, fun, ast.source, block, need_value)
            }

            AstData::SubExpr (sub_expr) => {
                self.compile_ast(ctx, fun, sub_expr, need_value)
            }

            AstData::Local (_) => {
                Err(CompileError { source: ast.source, data: CompileErrorData::UnexpectedLocal })
            }

            AstData::Op1 (op1) => {
                let src = self.compile_ast(ctx, fun, &op1.child, true)?.unwrap();
                let op  = op1.kind.0;
                Ok(Some(fun.add_op1(ast.source, op, src)))
            }

            AstData::Op2 (op2) => {
                match op2.kind {
                    ast::Op2Kind::Assign | ast::Op2Kind::Define => {
                        let value = self.compile_ast(ctx, fun, &op2.children[1], true)?.unwrap();
                        self.compile_assign(ctx, fun, &op2.children[0], value)?;

                        Ok(if need_value {
                            Some(fun.add_load_nil(ast.source))
                        }
                        else { None })
                    }

                    ast::Op2Kind::Op2Assign(op) => {
                        let src1 = self.compile_ast(ctx, fun, &op2.children[0], true)?.unwrap();
                        let src2 = self.compile_ast(ctx, fun, &op2.children[1], true)?.unwrap();

                        let value = fun.add_op2(ast.source, op, src1, src2);
                        self.compile_assign(ctx, fun, &op2.children[0], value)?;

                        Ok(if need_value {
                            Some(fun.add_load_nil(ast.source))
                        }
                        else { None })
                    }

                    ast::Op2Kind::Op2(op) => {
                        let src1 = self.compile_ast(ctx, fun, &op2.children[0], true)?.unwrap();
                        let src2 = self.compile_ast(ctx, fun, &op2.children[1], true)?.unwrap();
                        Ok(Some(fun.add_op2(ast.source, op, src1, src2)))
                    }
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
                let bb_true = fun.new_block();
                let bb_false = fun.new_block();
                let after_if = fun.new_block();

                // condition.
                let cond = self.compile_ast(ctx, fun, &iff.condition, true)?.unwrap();
                fun.add_switch_bool(ast.source, cond, bb_true, bb_false);


                // on_true
                fun.set_current_block(bb_true);
                let value_true = self.compile_ast(ctx, fun, &iff.on_true, need_value)?;
                fun.add_jump(iff.on_true.source.end.to_range(), after_if);
                let bb_true = fun.get_current_block();


                // on_false
                fun.set_current_block(bb_false);
                let (value_false, on_false_src) =
                    if let Some(on_false) = &iff.on_false {
                        let v = self.compile_ast(ctx, fun, on_false, need_value)?;
                        (v, on_false.source.end.to_range())
                    }
                    else {
                        let source = ast.source.end.to_range();
                        let v = need_value.then(|| fun.add_load_nil(source));
                        (v, source)
                    };
                fun.add_stmt(on_false_src, StmtData::Jump { target: after_if });
                let bb_false = fun.get_current_block();


                fun.set_current_block(after_if);
                if need_value {
                    let result = fun.add_phi(ast.source, &[
                        (bb_true,  value_true.unwrap()),
                        (bb_false, value_false.unwrap()),
                    ]);
                    Ok(Some(result))
                }
                else { Ok(None) }
            }

            AstData::While (whilee) => {
                let bb_head  = fun.new_block();
                let bb_body  = fun.new_block();
                let bb_after = fun.new_block();

                fun.add_jump(ast.source, bb_head);


                // head.
                fun.set_current_block(bb_head);
                let cond = self.compile_ast(ctx, fun, &whilee.condition, true)?.unwrap();
                fun.add_switch_bool(ast.source, cond, bb_body, bb_after);
                let bb_head = fun.get_current_block();


                // body.
                fun.set_current_block(bb_body);
                self.compile_ast(ctx, fun, &whilee.body, false)?;
                fun.add_jump(ast.source, bb_head);


                fun.set_current_block(bb_after);
                Ok(need_value.then(|| fun.add_load_nil(ast.source)))
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

    pub fn compile_block<'a>(&mut self,
        ctx: &mut Ctx<'a>, fun: &mut Function,
        block_source: SourceRange, block: &ast::Block<'a>, need_value: bool
    ) -> CompileResult<Option<StmtId>> {
        let scope = ctx.begin_scope();

        let mut stmts_end = block.children.len();
        if block.last_is_expr { stmts_end -= 1 }

        // visit statements.
        // handle locals.
        for i in 0..stmts_end {
            let node = &block.children[i];

            // local decls.
            if let AstData::Local(local) = &node.data {
                let lid = fun.new_local(local.name, node.source);
                ctx.add_decl(local.name, lid);

                let v =
                    if let Some(value) = &local.value {
                        self.compile_ast(ctx, fun, value, true)?.unwrap()
                    }
                    else {
                        fun.add_load_nil(node.source)
                    };
                fun.add_set_local(node.source, lid, v);
            }
            else {
                self.compile_ast(ctx, fun, node, false)?;
            }
        }

        // last statement (or expression).
        let result =
            if block.last_is_expr {
                self.compile_ast(ctx, fun, &block.children[stmts_end], need_value)?
            }
            else if need_value {
                let source = block_source.end.to_range();
                // @todo: return empty tuple.
                Some(fun.add_stmt(source, StmtData::LoadNil))
            }
            else { None };

        ctx.end_scope(scope);
        Ok(result)
    }

    pub fn compile_assign<'a>(&mut self,
        ctx: &mut Ctx<'a>, fun: &mut Function,
        ast: &Ast<'a>, value: StmtId) -> CompileResult<()>
    {
        match &ast.data {
            AstData::Ident (name) => {
                if let Some(decl) = ctx.find_decl(name) {
                    fun.add_set_local(ast.source, decl.id, value);
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


impl<'a> Ctx<'a> {
    fn new() -> Self {
        Ctx {
            scope: ScopeId(0),
            decls: vec![],
        }
    }

    fn add_decl(&mut self, name: &'a str, id: LocalId) {
        self.decls.push(Decl { name, id, scope: self.scope });
    }

    fn find_decl(&self, name: &str) -> Option<&Decl<'a>> {
        self.decls.iter().rev().find(|decl| decl.name == name)
    }

    fn begin_scope(&mut self) -> ScopeId {
        self.scope.0 += 1;
        self.scope
    }

    fn end_scope(&mut self, scope: ScopeId) {
        assert_eq!(self.scope, scope);
        self.decls.retain(|decl| decl.scope < self.scope);
        self.scope.0 -= 1;
    }
}


