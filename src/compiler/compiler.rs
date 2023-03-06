use super::*;


#[derive(Debug)]
pub struct CompileError {
    pub source: SourceRange,
    pub data:   CompileErrorData,
}


#[derive(Debug)]
pub enum CompileErrorData {
    InvalidAssignTarget,
    InvalidPathBase,
    NoBreakTarget,
    NoContinueTarget,
    BreakTargetTakesNoValue,
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
    break_scopes: Vec<BreakScope<'a>>,
}


#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
pub struct BreakScopeId(u32);

struct BreakScope<'a> {
    label:       Option<&'a str>,
    bb_after:    BlockId,
    bb_continue: OptBlockId,
    values:      Option<Vec<PhiEntry>>,
}



impl CompileError {
    #[inline(always)]
    pub fn at(source: SourceRange, data: CompileErrorData) -> CompileError {
        CompileError { source, data }
    }
}


impl Compiler {
    pub fn compile_chunk(stmts: &[Stmt], as_value_block: bool) -> CompileResult<Module> {
        let mut this = Compiler {
            module: Module::new()
        };

        let mut ctx = Ctx::new();
        let mut fun = this.module.new_function();
        let value = 
            if as_value_block {
                this.compile_value_block(&mut ctx, &mut fun, SourceRange::null(), stmts, true)?.unwrap()
            }
            else {
                this.compile_block(&mut ctx, &mut fun, stmts)?;
                fun.instr_load_unit(SourceRange::null())
            };
        fun.instr_return(SourceRange::null(), value);

        Ok(this.module)
    }

    pub fn compile_expr<'a>(&mut self,
        ctx: &mut Ctx<'a>, fun: &mut Function,
        expr: &Expr<'a>, need_value: bool,
    ) -> CompileResult<Option<InstrId>> {
        match &expr.data {
            ExprData::Nil => {
                Ok(Some(fun.instr_load_nil(expr.source)))
            }

            ExprData::Bool (value) => {
                Ok(Some(fun.instr_load_bool(expr.source, *value)))
            }

            ExprData::Number (value) => {
                let value = value.parse().unwrap();
                Ok(Some(fun.instr_load_int(expr.source, value)))
            }

            ExprData::QuotedString (value) => {
                let string = fun.add_string(value);
                Ok(Some(fun.instr_load_string(expr.source, string)))
            }

            ExprData::Ident (name) => {
                if let Some(decl) = ctx.find_decl(name) {
                    Ok(Some(fun.instr_get_local(expr.source, decl.id)))
                }
                else {
                    let name = fun.add_string(name);
                    Ok(Some(fun.instr_read_path(expr.source, PathBase::Env, &[PathKey::Field(name)])))
                }
            }

            ExprData::Tuple (tuple) => {
                let mut values = vec![];
                for v in &tuple.values {
                    values.push(self.compile_expr(ctx, fun, v, true)?.unwrap());
                }
                Ok(Some(fun.instr_tuple_new(expr.source, &values)))
            }

            ExprData::List (list) => {
                let mut values = Vec::with_capacity(list.values.len());
                for v in &list.values {
                    values.push(self.compile_expr(ctx, fun, v, true)?.unwrap());
                }
                Ok(Some(fun.instr_list_new(expr.source, &values)))
            }

            ExprData::Do (doo) => {
                self.compile_do_block(ctx, fun, expr.source, doo.label, &doo.stmts, need_value)
            }

            ExprData::SubExpr (sub_expr) => {
                self.compile_expr(ctx, fun, sub_expr, need_value)
            }

            ExprData::Op1 (op1) => {
                let src = self.compile_expr(ctx, fun, &op1.child, true)?.unwrap();
                let op  = op1.kind.0;
                Ok(Some(fun.instr_op1(expr.source, op, src)))
            }

            ExprData::Op2 (op2) => {
                match op2.kind {
                    data::Op2Kind::Assign | data::Op2Kind::Define => {
                        if let ExprData::Tuple(lhs) = &op2.children[0].data {
                            if op2.kind != data::Op2Kind::Assign {
                                // todo: error.
                                unimplemented!()
                            }

                            let lhs = &lhs.values;

                            if let ExprData::Tuple(rhs) = &op2.children[1].data {
                                let rhs = &rhs.values;
                                if lhs.len() != rhs.len() {
                                    // todo: error.
                                    unimplemented!()
                                }

                                let mut values = Vec::with_capacity(rhs.len());
                                for v in rhs {
                                    values.push(self.compile_expr(ctx, fun, v, true)?.unwrap());
                                }

                                for i in 0..lhs.len() {
                                    self.compile_assign(ctx, fun, &lhs[i], values[i], false)?;
                                }
                            }
                            else {
                                unimplemented!()
                            }
                        }
                        else {
                            let value = self.compile_expr(ctx, fun, &op2.children[1], true)?.unwrap();
                            let is_define = op2.kind == data::Op2Kind::Define;
                            self.compile_assign(ctx, fun, &op2.children[0], value, is_define)?;
                        }
                        Ok(need_value.then(|| fun.instr_load_unit(expr.source)))
                    }

                    data::Op2Kind::Op2Assign(op) => {
                        if op.is_cancelling() {
                            unimplemented!()
                        }

                        let src1 = self.compile_expr(ctx, fun, &op2.children[0], true)?.unwrap();
                        let src2 = self.compile_expr(ctx, fun, &op2.children[1], true)?.unwrap();

                        let value = fun.instr_op2(expr.source, op, src1, src2);
                        let is_define = false;
                        self.compile_assign(ctx, fun, &op2.children[0], value, is_define)?;

                        Ok(need_value.then(|| fun.instr_load_unit(expr.source)))
                    }

                    data::Op2Kind::Op2(op) => {
                        if op.is_cancelling() {
                            let bb_2 = fun.new_block();
                            let bb_after = fun.new_block();

                            // first value + cancel.
                            let src1 = self.compile_expr(ctx, fun, &op2.children[0], true)?.unwrap();
                            match op {
                                Op2::And     => { fun.instr_switch_bool(expr.source, src1, bb_2, bb_after); }
                                Op2::Or      => { fun.instr_switch_bool(expr.source, src1, bb_after, bb_2); }
                                Op2::OrElse  => { fun.instr_switch_nil(expr.source, src1, bb_2, bb_after); }

                                _ => unreachable!()
                            }
                            let bb_1 = fun.get_current_block();

                            // second value.
                            fun.set_current_block(bb_2);
                            let src2 = self.compile_expr(ctx, fun, &op2.children[1], true)?.unwrap();
                            fun.instr_jump(expr.source, bb_after);
                            let bb_2 = fun.get_current_block();

                            // join.
                            fun.set_current_block(bb_after);
                            Ok(Some(fun.instr_phi(expr.source, &[(bb_1, src1), (bb_2, src2)])))
                        }
                        else {
                            let src1 = self.compile_expr(ctx, fun, &op2.children[0], true)?.unwrap();
                            let src2 = self.compile_expr(ctx, fun, &op2.children[1], true)?.unwrap();
                            Ok(Some(fun.instr_op2(expr.source, op, src1, src2)))
                        }
                    }
                }
            }

            ExprData::Field (_) => {
                self.compile_read_path(ctx, fun, expr)
            }

            ExprData::OptChain (opt_chain) => {
                let _ = opt_chain;
                unimplemented!()
            }

            ExprData::Index (_) => {
                self.compile_read_path(ctx, fun, expr)
            }

            ExprData::Call (call) => {
                let func = self.compile_expr(ctx, fun, &call.func, true)?.unwrap();
                let mut args = vec![];
                for arg in &call.args {
                    args.push(self.compile_expr(ctx, fun, arg, true)?.unwrap());
                }
                Ok(Some(fun.instr_call(expr.source, func, &args)))
            }

            ExprData::If (iff) => {
                let bb_true = fun.new_block();
                let bb_false = fun.new_block();
                let after_if = fun.new_block();

                // condition.
                let cond = self.compile_expr(ctx, fun, &iff.condition, true)?.unwrap();
                fun.instr_switch_bool(expr.source, cond, bb_true, bb_false);


                // on_true
                fun.set_current_block(bb_true);
                let value_true = self.compile_if_block(ctx, fun, expr.source, &iff.on_true, need_value)?;
                let on_true_src = SourceRange::null(); // @todo-dbg-info
                fun.instr_jump(on_true_src, after_if);
                let bb_true = fun.get_current_block();


                // on_false
                fun.set_current_block(bb_false);
                let (value_false, on_false_src) =
                    if let Some(on_false) = &iff.on_false {
                        let v = self.compile_if_block(ctx, fun, expr.source, on_false, need_value)?;
                        (v, SourceRange::null()) // @todo-dbg-info
                    }
                    else {
                        let source = expr.source.end.to_range();
                        let v = need_value.then(|| fun.instr_load_unit(source));
                        (v, source)
                    };
                fun.instr_jump(on_false_src, after_if);
                let bb_false = fun.get_current_block();


                fun.set_current_block(after_if);
                if need_value {
                    let result = fun.instr_phi(expr.source, &[
                        (bb_true,  value_true.unwrap()),
                        (bb_false, value_false.unwrap()),
                    ]);
                    Ok(Some(result))
                }
                else { Ok(None) }
            }

            ExprData::While (whilee) => {
                let bb_head  = fun.new_block();
                let bb_body  = fun.new_block();
                let bb_after = fun.new_block();

                fun.instr_jump(expr.source, bb_head);


                // head.
                fun.set_current_block(bb_head);
                let cond = self.compile_expr(ctx, fun, &whilee.condition, true)?.unwrap();
                fun.instr_switch_bool(expr.source, cond, bb_body, bb_after);
                let bb_head = fun.get_current_block();


                let bs = ctx.begin_break_scope(whilee.label, bb_after, bb_head.some(), false);

                // body.
                fun.set_current_block(bb_body);
                self.compile_block(ctx, fun, &whilee.body)?;
                fun.instr_jump(expr.source, bb_head);

                ctx.end_break_scope(bs);


                fun.set_current_block(bb_after);
                Ok(need_value.then(|| fun.instr_load_unit(expr.source)))
            }

            ExprData::Break(breakk) => {
                let value =
                    if let Some(v) = &breakk.value {
                        Some(self.compile_expr(ctx, fun, v, true)?.unwrap())
                    } else { None };

                let scope = ctx.current_break_target(expr.source, breakk.label)?;
                let bb_break = scope.bb_after;

                if let Some(values) = &mut scope.values {
                    let value = value.unwrap_or_else(||
                        fun.instr_load_unit(expr.source));
                    values.push((fun.get_current_block(), value));
                }
                else if value.is_some() {
                    return Err(CompileError::at(expr.source, CompileErrorData::BreakTargetTakesNoValue));
                }

                fun.instr_jump(expr.source, bb_break);

                let bb_unreach = fun.new_block();
                fun.set_current_block(bb_unreach);
                Ok(need_value.then(|| fun.instr_load_unit(expr.source)))
            }

            ExprData::Continue(cont) => {
                let bb_continue = ctx.current_continue_target(expr.source, cont.label)?;
                fun.instr_jump(expr.source, bb_continue);

                let bb_unreach = fun.new_block();
                fun.set_current_block(bb_unreach);
                Ok(need_value.then(|| fun.instr_load_unit(expr.source)))
            }

            ExprData::Return (returnn) => {
                let value =
                    if let Some(value) = &returnn.value {
                        self.compile_expr(ctx, fun, value, true)?.unwrap()
                    }
                    else {
                        fun.instr_load_unit(expr.source)
                    };
                fun.instr_return(expr.source, value);

                let new_block = fun.new_block();
                fun.set_current_block(new_block);

                Ok(need_value.then(|| fun.instr_load_unit(expr.source)))
            }

            ExprData::Fn (fnn) => {
                let mut inner_fun = self.module.new_function();
                let mut inner_ctx = Ctx::new();

                for param in &fnn.params {
                    let id = inner_fun.new_param(param.name, SourceRange::null());
                    inner_ctx.add_decl(param.name, id);
                }


                let value = self.compile_value_block(&mut inner_ctx, &mut inner_fun,
                    expr.source, &fnn.body, true)?.unwrap();
                inner_fun.instr_return(expr.source, value);

                Ok(Some(fun.instr_new_function(expr.source, inner_fun.id())))
            }

            ExprData::Env => {
                Ok(Some(fun.instr_load_env(expr.source)))
            }
        }
    }

    pub fn compile_block<'a>(&mut self, ctx: &mut Ctx<'a>, fun: &mut Function, stmts: &[Stmt<'a>]) -> CompileResult<()> {
        let scope = ctx.begin_scope();

        for stmt in stmts.iter() {
            match &stmt.data {
                StmtData::Local(local) => {
                    let v =
                        if let Some(value) = &local.value {
                            self.compile_expr(ctx, fun, value, true)?.unwrap()
                        }
                        else {
                            fun.instr_load_unit(stmt.source)
                        };

                    let lid = fun.new_local(local.name, stmt.source);
                    ctx.add_decl(local.name, lid);

                    fun.instr_set_local(stmt.source, lid, v);
                }

                StmtData::Expr (expr) => {
                    self.compile_expr(ctx, fun, expr, false)?;
                }

                StmtData::Empty => (),

                StmtData::Item => {
                    unimplemented!()
                }
            }
        }

        ctx.end_scope(scope);
        Ok(())
    }

    pub fn compile_do_block<'a>(&mut self, ctx: &mut Ctx<'a>, fun: &mut Function,
        block_source: SourceRange, label: Option<&'a str>, stmts: &[Stmt<'a>], need_value: bool
    ) -> CompileResult<Option<InstrId>> {
        let bb_after = fun.new_block();

        let bs = ctx.begin_break_scope(label, bb_after, None.into(), need_value);
        self.compile_block(ctx, fun, stmts)?;
        let values = ctx.end_break_scope(bs);

        let default_block = fun.get_current_block();
        let default_value = need_value.then(||
            fun.instr_load_unit(block_source));
        fun.instr_jump(block_source, bb_after);
        fun.set_current_block(bb_after);

        if need_value {
            let mut values = values.unwrap();
            values.push((default_block, default_value.unwrap()));
            Ok(Some(fun.instr_phi(block_source, &values)))
        }
        else { Ok(None) }
    }

    pub fn compile_value_block<'a>(&mut self, ctx: &mut Ctx<'a>, fun: &mut Function,
        block_source: SourceRange, stmts: &[Stmt<'a>], need_value: bool
    ) -> CompileResult<Option<InstrId>> {
        if stmts.len() == 1 {
            if let StmtData::Expr(expr) = &stmts[0].data {
                return self.compile_expr(ctx, fun, expr, need_value);
            }
        }

        self.compile_block(ctx, fun, stmts)?;
        Ok(need_value.then(|| fun.instr_load_unit(block_source)))
    }

    pub fn compile_if_block<'a>(&mut self, ctx: &mut Ctx<'a>, fun: &mut Function,
        block_source: SourceRange, block: &data::IfBlock<'a>, need_value: bool
    ) -> CompileResult<Option<InstrId>> {
        if block.is_do {
            self.compile_do_block(ctx, fun, block_source, None, &block.stmts, need_value)
        }
        else {
            self.compile_value_block(ctx, fun, block_source, &block.stmts, need_value)
        }
    }

    // bool: env was explicit base.
    pub fn compile_path<'a>(&mut self, ctx: &mut Ctx<'a>, fun: &mut Function, expr: &Expr<'a>) -> CompileResult<(PathBase, OptLocalId, Vec<PathKey>)> {
        fn rec<'a>(this: &mut Compiler, ctx: &mut Ctx<'a>, fun: &mut Function, expr: &Expr<'a>, keys: &mut Vec<PathKey>) -> CompileResult<(PathBase, OptLocalId)> {
            match &expr.data {
                ExprData::Field(field) => {
                    let base = rec(this, ctx, fun, &field.base, keys)?;
                    keys.push(PathKey::Field(
                        fun.add_string(field.name)));
                    Ok(base)
                }

                ExprData::Index(index) => {
                    let base = rec(this, ctx, fun, &index.base, keys)?;
                    keys.push(PathKey::Index(
                        this.compile_expr(ctx, fun, &index.index, true)?.unwrap()));
                    Ok(base)
                }

                ExprData::Ident(ident) => {
                    if let Some(decl) = ctx.find_decl(ident) {
                        let lid = decl.id;
                        Ok((PathBase::Instr(fun.instr_get_local(expr.source, lid)), lid.some()))
                    }
                    else {
                        keys.push(PathKey::Field(fun.add_string(ident)));
                        Ok((PathBase::Env, None.into()))
                    }
                }

                ExprData::Env => {
                    Ok((PathBase::Env, None.into()))
                }

                _ => return Err(CompileError::at(expr.source, CompileErrorData::InvalidPathBase))
            }
        }

        let mut keys = vec![];
        let (base, lid) = rec(self, ctx, fun, expr, &mut keys)?;
        Ok((base, lid, keys))
    }

    pub fn compile_read_path<'a>(&mut self, ctx: &mut Ctx<'a>, fun: &mut Function, expr: &Expr<'a>) -> CompileResult<Option<InstrId>> {
        let (base, _, keys) = self.compile_path(ctx, fun, expr)?;
        Ok(Some(fun.instr_read_path(expr.source, base, &keys)))
    }

    pub fn compile_assign<'a>(&mut self,
        ctx: &mut Ctx<'a>, fun: &mut Function,
        lhs: &Expr<'a>, rhs: InstrId, is_define: bool) -> CompileResult<()>
    {
        if let ExprData::Ident(name) = lhs.data {
            if let Some(decl) = ctx.find_decl(name) {
                fun.instr_set_local(lhs.source, decl.id, rhs);
            }
            else {
                assert!(is_define == false);
                let name = fun.add_string(name);
                fun.instr_write_path(lhs.source, PathBase::Env, &[PathKey::Field(name)], rhs, is_define);
            }
        }
        else {
            let (base, lid, keys) = self.compile_path(ctx, fun, lhs)?;

            let new_value = fun.instr_write_path(lhs.source, base, &keys, rhs, is_define);
            if let Some(lid) = lid.to_option() {
                fun.instr_set_local(lhs.source, lid, new_value);
            }
        }
        Ok(())
    }
}


impl<'a> Ctx<'a> {
    fn new() -> Self {
        Ctx {
            scope: ScopeId(0),
            decls: vec![],
            break_scopes: vec![],
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

    fn begin_break_scope(&mut self, label: Option<&'a str>, bb_after: BlockId, bb_continue: OptBlockId, need_value: bool) -> BreakScopeId {
        let values = need_value.then(|| vec![]);
        self.break_scopes.push(BreakScope { label, bb_after, bb_continue, values });
        BreakScopeId(self.break_scopes.len() as u32)
    }

    fn end_break_scope(&mut self, scope: BreakScopeId) -> Option<Vec<PhiEntry>> {
        assert_eq!(self.break_scopes.len(), scope.0 as usize);
        self.break_scopes.pop().unwrap().values
    }

    fn current_break_target(&mut self, source: SourceRange, label: Option<&'a str>) -> CompileResult<&mut BreakScope<'a>> {
        if label.is_some() {
            for scope in self.break_scopes.iter_mut().rev() {
                if scope.label == label {
                    return Ok(scope);
                }
            }
            // @todo: no break target with matching label.
            return Err(CompileError::at(source, CompileErrorData::NoBreakTarget));
        }
        else {
            if let Some(scope) = self.break_scopes.last_mut() {
                return Ok(scope);
            }
            return Err(CompileError::at(source, CompileErrorData::NoBreakTarget));
        }
    }

    fn current_continue_target(&self, source: SourceRange, label: Option<&'a str>) -> CompileResult<BlockId> {
        for scope in self.break_scopes.iter().rev() {
            if label.is_none() || scope.label == label {
                if let Some(bb_continue) = scope.bb_continue.to_option() {
                    return Ok(bb_continue);
                }
            }
        }
        return Err(CompileError::at(source, CompileErrorData::NoContinueTarget));
    }
}


