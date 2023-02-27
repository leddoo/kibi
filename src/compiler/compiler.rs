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
    module: Module,
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
    pub fn compile_chunk(stmts: &[Ast]) -> CompileResult<Module> {
        let mut this = Compiler {
            module: Module::new()
        };

        let source = SourceRange::null();

        let mut ctx = Ctx::new();
        let mut fun = this.module.new_function();
        let needs_value  = false;
        this.compile_do_block(&mut ctx, &mut fun, source, false, stmts, needs_value)?;

        let nil = fun.stmt_load_nil(source);
        fun.stmt_return(source, nil);

        Ok(this.module)
    }

    pub fn compile_ast<'a>(&mut self,
        ctx: &mut Ctx<'a>, fun: &mut Function,
        ast: &Ast<'a>, need_value: bool,
    ) -> CompileResult<Option<StmtId>> {
        match &ast.data {
            AstData::Nil => {
                Ok(Some(fun.stmt_load_nil(ast.source)))
            }

            AstData::Bool (value) => {
                Ok(Some(fun.stmt_load_bool(ast.source, *value)))
            }

            AstData::Number (value) => {
                let value = value.parse().unwrap();
                Ok(Some(fun.stmt_load_int(ast.source, value)))
            }

            AstData::QuotedString (value) => {
                let string = fun.add_string(value);
                Ok(Some(fun.stmt_load_string(ast.source, string)))
            }

            AstData::Ident (name) => {
                if let Some(decl) = ctx.find_decl(name) {
                    Ok(Some(fun.stmt_get_local(ast.source, decl.id)))
                }
                else {
                    // @todo-opt: get_global.
                    let env = fun.stmt_load_env(ast.source);
                    let name = fun.add_string(name);
                    let name = fun.stmt_load_string(ast.source, name);
                    Ok(Some(fun.stmt_get_index(ast.source, env, name)))
                }
            }

            AstData::Tuple (tuple) => {
                let _ = tuple;
                unimplemented!()
            }

            AstData::List (list) => {
                let values = &list.values;

                let list = fun.stmt_list_new(ast.source);
                for value in values {
                    let v = self.compile_ast(ctx, fun, value, true)?.unwrap();
                    fun.stmt_list_append(value.source, list, v);
                }

                Ok(Some(list))
            }

            AstData::Table (table) => {
                let _ = table;
                unimplemented!()
            }

            AstData::Do (doo) => {
                self.compile_block(ctx, fun, ast.source, doo, need_value)
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
                Ok(Some(fun.stmt_op1(ast.source, op, src)))
            }

            AstData::Op2 (op2) => {
                match op2.kind {
                    ast::Op2Kind::Assign | ast::Op2Kind::Define => {
                        let value = self.compile_ast(ctx, fun, &op2.children[1], true)?.unwrap();
                        let is_define = op2.kind == ast::Op2Kind::Define;
                        self.compile_assign(ctx, fun, &op2.children[0], value, is_define)?;

                        Ok(if need_value {
                            Some(fun.stmt_load_nil(ast.source))
                        }
                        else { None })
                    }

                    ast::Op2Kind::Op2Assign(op) => {
                        let src1 = self.compile_ast(ctx, fun, &op2.children[0], true)?.unwrap();
                        let src2 = self.compile_ast(ctx, fun, &op2.children[1], true)?.unwrap();

                        let value = fun.stmt_op2(ast.source, op, src1, src2);
                        let is_define = false;
                        self.compile_assign(ctx, fun, &op2.children[0], value, is_define)?;

                        Ok(if need_value {
                            Some(fun.stmt_load_nil(ast.source))
                        }
                        else { None })
                    }

                    ast::Op2Kind::Op2(op) => {
                        let src1 = self.compile_ast(ctx, fun, &op2.children[0], true)?.unwrap();
                        let src2 = self.compile_ast(ctx, fun, &op2.children[1], true)?.unwrap();
                        Ok(Some(fun.stmt_op2(ast.source, op, src1, src2)))
                    }
                }
            }

            AstData::Field (field) => {
                // @todo-opt: get_field?
                let base  = self.compile_ast(ctx, fun, &field.base, true)?.unwrap();
                let index = fun.add_string(field.name);
                let index = fun.stmt_load_string(ast.source, index);
                Ok(Some(fun.stmt_get_index(ast.source, base, index)))
            }

            AstData::OptChain (opt_chain) => {
                let _ = opt_chain;
                unimplemented!()
            }

            AstData::Index (index) => {
                let base  = self.compile_ast(ctx, fun, &index.base,  true)?.unwrap();
                let index = self.compile_ast(ctx, fun, &index.index, true)?.unwrap();
                Ok(Some(fun.stmt_get_index(ast.source, base, index)))
            }

            AstData::Call (call) => {
                let func = self.compile_ast(ctx, fun, &call.func, true)?.unwrap();
                let mut args = vec![];
                for arg in &call.args {
                    args.push(self.compile_ast(ctx, fun, arg, true)?.unwrap());
                }
                Ok(Some(fun.stmt_call(ast.source, func, &args)))
            }

            AstData::If (iff) => {
                let bb_true = fun.new_block();
                let bb_false = fun.new_block();
                let after_if = fun.new_block();

                // condition.
                let cond = self.compile_ast(ctx, fun, &iff.condition, true)?.unwrap();
                fun.stmt_switch_bool(ast.source, cond, bb_true, bb_false);


                // on_true
                fun.set_current_block(bb_true);
                let value_true = self.compile_block(ctx, fun, ast.source, &iff.on_true, need_value)?;
                let on_true_src = SourceRange::null(); // @todo-dbg-info
                fun.stmt_jump(on_true_src, after_if);
                let bb_true = fun.get_current_block();


                // on_false
                fun.set_current_block(bb_false);
                let (value_false, on_false_src) =
                    if let Some(on_false) = &iff.on_false {
                        let v = self.compile_block(ctx, fun, ast.source, on_false, need_value)?;
                        (v, SourceRange::null()) // @todo-dbg-info
                    }
                    else {
                        let source = ast.source.end.to_range();
                        let v = need_value.then(|| fun.stmt_load_nil(source));
                        (v, source)
                    };
                fun.stmt_jump(on_false_src, after_if);
                let bb_false = fun.get_current_block();


                fun.set_current_block(after_if);
                if need_value {
                    let result = fun.stmt_phi(ast.source, &[
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

                fun.stmt_jump(ast.source, bb_head);


                // head.
                fun.set_current_block(bb_head);
                let cond = self.compile_ast(ctx, fun, &whilee.condition, true)?.unwrap();
                fun.stmt_switch_bool(ast.source, cond, bb_body, bb_after);
                let bb_head = fun.get_current_block();


                // body.
                fun.set_current_block(bb_body);
                self.compile_do_block(ctx, fun, ast.source, false, &whilee.body, false)?;
                fun.stmt_jump(ast.source, bb_head);


                fun.set_current_block(bb_after);
                Ok(need_value.then(|| fun.stmt_load_nil(ast.source)))
            }

            AstData::Break => {
                unimplemented!()
            }

            AstData::Continue => {
                unimplemented!()
            }

            AstData::Return (returnn) => {
                let value =
                    if let Some(value) = &returnn.value {
                        self.compile_ast(ctx, fun, value, true)?.unwrap()
                    }
                    else {
                        fun.stmt_load_nil(ast.source)
                    };
                fun.stmt_return(ast.source, value);

                let new_block = fun.new_block();
                fun.set_current_block(new_block);

                Ok(need_value.then(|| fun.stmt_load_nil(ast.source)))
            }

            AstData::Fn (fnn) => {
                let mut inner_fun = self.module.new_function();
                let mut inner_ctx = Ctx::new();

                for param in &fnn.params {
                    let id = inner_fun.new_param(param.name, SourceRange::null());
                    inner_ctx.add_decl(param.name, id);
                }


                let value = self.compile_do_block(&mut inner_ctx, &mut inner_fun,
                    ast.source, false, &fnn.body, true)?.unwrap();
                inner_fun.stmt_return(ast.source, value);

                Ok(Some(fun.stmt_new_function(ast.source, inner_fun.id())))
            }

            AstData::Env => {
                Ok(Some(fun.stmt_load_env(ast.source)))
            }
        }
    }

    pub fn compile_do_block<'a>(&mut self,
        ctx: &mut Ctx<'a>, fun: &mut Function,
        block_source: SourceRange, is_do: bool, stmts: &[Ast<'a>], need_value: bool
    ) -> CompileResult<Option<StmtId>> {
        let scope = ctx.begin_scope();

        if !is_do && need_value && stmts.len() == 1 {
            let result = self.compile_ast(ctx, fun, &stmts[0], true);
            ctx.end_scope(scope);
            return result;
        }

        assert!(!is_do || !need_value);

        // visit statements.
        // handle locals.
        for stmt in stmts.iter() {
            // local decls.
            if let AstData::Local(local) = &stmt.data {
                let v =
                    if let Some(value) = &local.value {
                        self.compile_ast(ctx, fun, value, true)?.unwrap()
                    }
                    else {
                        fun.stmt_load_nil(stmt.source)
                    };

                let lid = fun.new_local(local.name, stmt.source);
                ctx.add_decl(local.name, lid);

                fun.stmt_set_local(stmt.source, lid, v);
            }
            else {
                self.compile_ast(ctx, fun, stmt, false)?;
            }
        }

        let result = need_value.then(|| {
            let source = block_source.end.to_range();
            fun.add_stmt(source, StmtData::LoadNil)
        });

        ctx.end_scope(scope);
        Ok(result)
    }

    pub fn compile_block<'a>(&mut self,
        ctx: &mut Ctx<'a>, fun: &mut Function,
        block_source: SourceRange, block: &ast::Block<'a>, need_value: bool
    ) -> CompileResult<Option<StmtId>> {
        self.compile_do_block(ctx, fun, block_source, block.is_do, &block.stmts, need_value)
    }

    pub fn compile_assign<'a>(&mut self,
        ctx: &mut Ctx<'a>, fun: &mut Function,
        ast: &Ast<'a>, value: StmtId, is_define: bool) -> CompileResult<()>
    {
        match &ast.data {
            AstData::Ident (name) => {
                if let Some(decl) = ctx.find_decl(name) {
                    fun.stmt_set_local(ast.source, decl.id, value);
                }
                else {
                    // @temp: compile error.
                    assert!(is_define == false);

                    // @todo-opt: set_global.
                    let env = fun.stmt_load_env(ast.source);
                    let name = fun.add_string(name);
                    let name = fun.stmt_load_string(ast.source, name);
                    fun.stmt_set_index(ast.source, env, name, value, false);
                }

                Ok(())
            }

            AstData::Field (field) => {
                // @todo-opt: set_field?
                let base  = self.compile_ast(ctx, fun, &field.base, true)?.unwrap();
                let index = fun.add_string(field.name);
                let index = fun.stmt_load_string(ast.source, index);
                fun.stmt_set_index(ast.source, base, index, value, is_define);
                Ok(())
            }

            AstData::Index (index) => {
                let base  = self.compile_ast(ctx, fun, &index.base, true)?.unwrap();
                let index = self.compile_ast(ctx, fun, &index.index, true)?.unwrap();
                fun.stmt_set_index(ast.source, base, index, value, is_define);

                Ok(())
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


