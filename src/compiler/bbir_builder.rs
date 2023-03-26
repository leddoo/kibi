use crate::index_vec::*;
use crate::ast::*;
use crate::infer;
use crate::bbir::{*, self};
use crate::ast::ItemData;


pub struct Builder {
    pub krate: bbir::Crate,
}

impl Builder {
    pub fn new() -> Self {
        Builder {
            krate: bbir::Crate::new(),
        }
    }

    pub fn build(&mut self, module: &item::Module) {
        self.build_module(NodeId::new_unck(1), module);
    }

    fn build_module(&mut self, module_id: NodeId, module: &item::Module) {
        let mut fun = self.krate.new_function();
        let mut ctx = Ctx::new(&mut fun, module_id, &[]);

        let stmts = &module.block.stmts;

        let as_value_block = false;
        let value = 
            if as_value_block {
                self.build_value_block(&mut ctx, module_id, stmts, true).unwrap()
            }
            else {
                self.build_block(&mut ctx, stmts);
                ctx.fun.instr_load_unit((None.into(), None.into()))
            };
        ctx.fun.instr_return(None.into(), value);
    }

    fn build_stmt(&mut self, ctx: &mut Ctx, stmt: &Stmt) {
        match &stmt.data {
            StmtData::Item(item) => {
                match &item.data {
                    ItemData::Module(module) => {
                        let _ = module;
                        unimplemented!()
                    }

                    ItemData::Func(func) => {
                        let func_id = self.build_func(ctx, stmt.id, func);
                        self.krate.def_item(item.id, bbir::Item {
                            data: bbir::ItemData::Func(func_id)
                        });
                    }
                }
            }

            StmtData::Local(local) => {
                let v =
                    if let Some(value) = &local.value {
                        self.build_expr(ctx, value, true).unwrap()
                    }
                    else {
                        ctx.fun.instr_load_unit((stmt.id.some(), None.into()))
                    };

                let lid = ctx.add_local_decl(stmt.id, local.name,
                    stmt.id, local.info.unwrap().id);
                ctx.fun.instr_set_local((stmt.id.some(), stmt.id.some()), lid, v);
            }

            StmtData::Expr (expr) => {
                self.build_expr(ctx, expr, false);
            }

            StmtData::Empty => (),
        }
    }

    fn build_expr(&mut self, ctx: &mut Ctx, expr: &Expr, need_value: bool) -> Option<InstrId> {
        match &expr.data {
            ExprData::Nil => {
                Some(ctx.fun.instr_load_nil((expr.id.some(), expr.id.some())))
            }

            ExprData::Bool (value) => {
                Some(ctx.fun.instr_load_bool((expr.id.some(), expr.id.some()), *value))
            }

            ExprData::Number (value) => {
                let value = value.parse().unwrap();
                Some(ctx.fun.instr_load_int((expr.id.some(), expr.id.some()), value))
            }

            ExprData::QuotedString (value) => {
                let string = ctx.fun.add_string(value);
                Some(ctx.fun.instr_load_string((expr.id.some(), expr.id.some()), string))
            }

            ExprData::Ident (ident) => {
                let info = ident.info.unwrap();

                match info.target {
                    expr::IdentTarget::Item(item) => {
                        let index = ctx.fun.instr_load_int((expr.id.some(), None.into()), item.value() as i64);
                        Some(ctx.fun.instr_read_path((expr.id.some(), expr.id.some()), PathBase::Items, &[PathKey::Index(index)]))
                    }

                    expr::IdentTarget::Local { node, local } => {
                        let local = ctx.get_local_id(node, local);
                        Some(ctx.fun.instr_get_local((expr.id.some(), expr.id.some()), local))
                    }

                    expr::IdentTarget::Dynamic => {
                        let name = ctx.fun.add_string(ident.name);
                        Some(ctx.fun.instr_read_path((expr.id.some(), expr.id.some()), PathBase::Env, &[PathKey::Field(name)]))
                    }
                }
            }

            ExprData::Tuple (tuple) => {
                let mut values = vec![];
                for v in &tuple.values {
                    values.push(self.build_expr(ctx, v, true).unwrap());
                }
                Some(ctx.fun.instr_tuple_new((expr.id.some(), expr.id.some()), &values))
            }

            ExprData::List (list) => {
                let mut values = Vec::with_capacity(list.values.len());
                for v in &list.values {
                    values.push(self.build_expr(ctx, v, true).unwrap());
                }
                Some(ctx.fun.instr_list_new((expr.id.some(), expr.id.some()), &values))
            }

            ExprData::Do (doo) => {
                self.build_do_block(ctx, expr.id, &doo.stmts, need_value)
            }

            ExprData::SubExpr (sub_expr) => {
                self.build_expr(ctx, sub_expr, need_value)
            }

            ExprData::Op1 (op1) => {
                let src = self.build_expr(ctx, &op1.child, true).unwrap();
                let op  = op1.kind.0;
                Some(ctx.fun.instr_op1((expr.id.some(), expr.id.some()), op, src))
            }

            ExprData::Op2 (op2) => {
                match op2.kind {
                    expr::Op2Kind::Assign | expr::Op2Kind::Define => {
                        if let ExprData::Tuple(lhs) = &op2.children[0].data {
                            if op2.kind != expr::Op2Kind::Assign {
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
                                    values.push(self.build_expr(ctx, v, true).unwrap());
                                }

                                for i in 0..lhs.len() {
                                    self.build_assign(ctx, &lhs[i], values[i], false);
                                }
                            }
                            else {
                                unimplemented!()
                            }
                        }
                        else {
                            let value = self.build_expr(ctx, &op2.children[1], true).unwrap();
                            let is_define = op2.kind == expr::Op2Kind::Define;
                            self.build_assign(ctx, &op2.children[0], value, is_define);
                        }
                        need_value.then(|| ctx.fun.instr_load_unit((expr.id.some(), expr.id.some())))
                    }

                    expr::Op2Kind::Op2Assign(op) => {
                        if op.is_cancelling() {
                            unimplemented!()
                        }

                        let src1 = self.build_expr(ctx, &op2.children[0], true).unwrap();
                        let src2 = self.build_expr(ctx, &op2.children[1], true).unwrap();

                        let value = ctx.fun.instr_op2((expr.id.some(), None.into()), op, src1, src2);
                        let is_def = false;
                        self.build_assign(ctx, &op2.children[0], value, is_def);

                        need_value.then(|| ctx.fun.instr_load_unit((expr.id.some(), expr.id.some())))
                    }

                    expr::Op2Kind::Op2(op) => {
                        if op.is_cancelling() {
                            let bb_2 = ctx.fun.new_block();
                            let bb_after = ctx.fun.new_block();

                            // first value + cancel.
                            let src1 = self.build_expr(ctx, &op2.children[0], true).unwrap();
                            match op {
                                Op2::And     => { ctx.fun.instr_switch_bool(expr.id.some(), src1, bb_2, bb_after); }
                                Op2::Or      => { ctx.fun.instr_switch_bool(expr.id.some(), src1, bb_after, bb_2); }
                                Op2::OrElse  => { ctx.fun.instr_switch_nil(expr.id.some(), src1, bb_2, bb_after); }

                                _ => unreachable!()
                            }
                            let bb_1 = ctx.fun.get_current_block();

                            // second value.
                            ctx.fun.set_current_block(bb_2);
                            let src2 = self.build_expr(ctx, &op2.children[1], true).unwrap();
                            ctx.fun.instr_jump(expr.id.some(), bb_after);
                            let bb_2 = ctx.fun.get_current_block();

                            // join.
                            ctx.fun.set_current_block(bb_after);
                            Some(ctx.fun.instr_phi((expr.id.some(), expr.id.some()), &[(bb_1, src1), (bb_2, src2)]))
                        }
                        else {
                            let src1 = self.build_expr(ctx, &op2.children[0], true).unwrap();
                            let src2 = self.build_expr(ctx, &op2.children[1], true).unwrap();
                            Some(ctx.fun.instr_op2((expr.id.some(), expr.id.some()), op, src1, src2))
                        }
                    }
                }
            }

            ExprData::Field (_) => {
                self.build_read_path(ctx, expr)
            }

            ExprData::Index (_) => {
                self.build_read_path(ctx, expr)
            }

            ExprData::Call (call) => {
                let func = self.build_expr(ctx, &call.func, true).unwrap();
                let mut args = vec![];
                for arg in &call.args {
                    args.push(self.build_expr(ctx, arg, true).unwrap());
                }
                Some(ctx.fun.instr_call((expr.id.some(), expr.id.some()), func, &args))
            }

            ExprData::If (iff) => {
                let bb_true = ctx.fun.new_block();
                let bb_false = ctx.fun.new_block();
                let after_if = ctx.fun.new_block();

                // condition.
                let cond = self.build_expr(ctx, &iff.condition, true).unwrap();
                ctx.fun.instr_switch_bool(expr.id.some(), cond, bb_true, bb_false);


                // on_true
                ctx.fun.set_current_block(bb_true);
                let value_true = self.build_if_block(ctx, expr.id, &iff.on_true, need_value);
                let on_true_src = None.into(); // @todo-dbg-info
                ctx.fun.instr_jump(on_true_src, after_if);
                let bb_true = ctx.fun.get_current_block();


                // on_false
                ctx.fun.set_current_block(bb_false);
                let (value_false, on_false_src) =
                    if let Some(on_false) = &iff.on_false {
                        let v = self.build_if_block(ctx, expr.id, on_false, need_value);
                        (v, None.into()) // @todo-dbg-info
                    }
                    else {
                        let v = need_value.then(|| ctx.fun.instr_load_unit((expr.id.some(), None.into())));
                        (v, expr.id.some())
                    };
                ctx.fun.instr_jump(on_false_src, after_if);
                let bb_false = ctx.fun.get_current_block();


                ctx.fun.set_current_block(after_if);
                need_value.then(||
                    ctx.fun.instr_phi((expr.id.some(), expr.id.some()), &[
                        (bb_true,  value_true.unwrap()),
                        (bb_false, value_false.unwrap()),
                    ]))
            }

            ExprData::While (whilee) => {
                let bb_head  = ctx.fun.new_block();
                let bb_body  = ctx.fun.new_block();
                let bb_after = ctx.fun.new_block();

                ctx.fun.instr_jump(expr.id.some(), bb_head);


                // head.
                ctx.fun.set_current_block(bb_head);
                let cond = self.build_expr(ctx, &whilee.condition, true).unwrap();
                ctx.fun.instr_switch_bool(expr.id.some(), cond, bb_body, bb_after);
                let bb_head = ctx.fun.get_current_block();


                let bs = ctx.begin_break_scope(expr.id, bb_after, bb_head.some(), false);

                // body.
                ctx.fun.set_current_block(bb_body);
                self.build_block(ctx, &whilee.body);
                ctx.fun.instr_jump(expr.id.some(), bb_head);

                ctx.end_break_scope(bs);


                ctx.fun.set_current_block(bb_after);
                need_value.then(|| ctx.fun.instr_load_unit((expr.id.some(), expr.id.some())))
            }

            ExprData::Break(brk) => {
                let value =
                    if let Some(v) = &brk.value {
                        Some(self.build_expr(ctx, v, true).unwrap())
                    } else { None };

                let info = brk.info.unwrap();

                if let Some(info) = info {
                    let scope = &mut ctx.break_scopes[info.scope_index as usize];
                    assert_eq!(scope.node, info.node);
                    let bb_break = scope.bb_break;

                    if let Some(values) = &mut scope.values {
                        let value = value.unwrap_or_else(||
                            ctx.fun.instr_load_unit((expr.id.some(), None.into())));
                        values.push((ctx.fun.get_current_block(), value));
                    }
                    else if value.is_some() {
                        println!("info: ignoring error BreakTargetTakesNoValue.");
                    }

                    ctx.fun.instr_jump(expr.id.some(), bb_break);

                    let bb_unreach = ctx.fun.new_block();
                    ctx.fun.set_current_block(bb_unreach);
                }

                need_value.then(|| ctx.fun.instr_load_unit((expr.id.some(), expr.id.some())))
            }

            ExprData::Continue(cont) => {
                let info = cont.info.unwrap();

                if let Some(info) = info {
                    let scope = &mut ctx.break_scopes[info.scope_index as usize];
                    assert_eq!(scope.node, info.node);
                    let bb_continue = scope.bb_continue.unwrap();

                    ctx.fun.instr_jump(expr.id.some(), bb_continue);

                    let bb_unreach = ctx.fun.new_block();
                    ctx.fun.set_current_block(bb_unreach);
                }

                need_value.then(|| ctx.fun.instr_load_unit((expr.id.some(), expr.id.some())))
            }

            ExprData::Return (returnn) => {
                let value =
                    if let Some(value) = &returnn.value {
                        self.build_expr(ctx, value, true).unwrap()
                    }
                    else {
                        ctx.fun.instr_load_unit((expr.id.some(), None.into()))
                    };
                ctx.fun.instr_return(expr.id.some(), value);

                let new_block = ctx.fun.new_block();
                ctx.fun.set_current_block(new_block);

                need_value.then(|| ctx.fun.instr_load_unit((expr.id.some(), expr.id.some())))
            }

            ExprData::Env => {
                // @temp-no-env-access.
                //Some(ctx.fun.instr_load_env(expr.source))
                println!("ignoring error: no env access");
                need_value.then(|| ctx.fun.instr_load_unit((expr.id.some(), None.into())))
            }
        }
    }

    fn build_block(&mut self, ctx: &mut Ctx, block: &[Stmt]) {
        for stmt in block {
            self.build_stmt(ctx, stmt);
        }
    }

    fn build_do_block(&mut self, ctx: &mut Ctx, node: NodeId, block: &[Stmt], need_value: bool) -> Option<InstrId> {
        let bb_after = ctx.fun.new_block();

        let bs = ctx.begin_break_scope(node, bb_after, None.into(), need_value);
        self.build_block(ctx, block);
        let values = ctx.end_break_scope(bs);

        let default_block = ctx.fun.get_current_block();
        let default_value = need_value.then(||
            ctx.fun.instr_load_unit((None.into(), None.into())));
        ctx.fun.instr_jump(None.into(), bb_after);
        ctx.fun.set_current_block(bb_after);

        need_value.then(|| {
            let mut values = values.unwrap();
            values.push((default_block, default_value.unwrap()));
            ctx.fun.instr_phi((None.into(), node.some()), &values)
        })
    }

    fn build_value_block(&mut self, ctx: &mut Ctx, node: NodeId, block: &[Stmt], need_value: bool) -> Option<InstrId> {
        if block.len() == 1 {
            if let StmtData::Expr(expr) = &block[0].data {
                return self.build_expr(ctx, expr, need_value);
            }
        }

        self.build_block(ctx, block);
        need_value.then(|| ctx.fun.instr_load_unit((None.into(), node.some())))
    }

    fn build_if_block(&mut self, ctx: &mut Ctx, node: NodeId, block: &expr::IfBlock, need_value: bool) -> Option<InstrId> {
        if block.is_do {
            self.build_do_block(ctx, node, &block.stmts, need_value)
        }
        else {
            self.build_value_block(ctx, node, &block.stmts, need_value)
        }
    }

    fn build_path(&mut self, ctx: &mut Ctx, expr: &Expr) -> Option<(PathBase, bbir::OptLocalId, Vec<PathKey>)> {
        fn rec(this: &mut Builder, ctx: &mut Ctx, expr: &Expr, keys: &mut Vec<PathKey>) -> Option<(PathBase, bbir::OptLocalId)> {
            match &expr.data {
                ExprData::Field(field) => {
                    let result = rec(this, ctx, &field.base, keys)?;
                    keys.push(PathKey::Field(
                        ctx.fun.add_string(field.name)));
                    Some(result)
                }

                ExprData::Index(index) => {
                    let result = rec(this, ctx, &index.base, keys)?;
                    keys.push(PathKey::Index(
                        this.build_expr(ctx, &index.index, true).unwrap()));
                    Some(result)
                }

                ExprData::Ident(ident) => {
                    let info = ident.info.unwrap();

                    match info.target {
                        expr::IdentTarget::Item(item) => {
                            let _ = item;
                            unimplemented!()
                        }

                        expr::IdentTarget::Local { node, local } => {
                            let local = ctx.get_local_id(node, local);
                            Some((PathBase::Instr(ctx.fun.instr_get_local((expr.id.some(), expr.id.some()), local)), local.some()))
                        }

                        expr::IdentTarget::Dynamic => {
                            keys.push(PathKey::Field(ctx.fun.add_string(ident.name)));
                            Some((PathBase::Env, None.into()))
                        }
                    }
                }

                ExprData::Env => {
                    Some((PathBase::Env, None.into()))
                }

                _ => {
                    println!("ignoring error: invalid path base");
                    None
                }
            }
        }

        let mut keys = vec![];
        let (base, lid) = rec(self, ctx, expr, &mut keys)?;
        Some((base, lid, keys))
    }

    fn build_read_path(&mut self, ctx: &mut Ctx, expr: &Expr) -> Option<InstrId> {
        if let Some((base, _, keys)) = self.build_path(ctx, expr) {
            return Some(ctx.fun.instr_read_path((expr.id.some(), expr.id.some()), base, &keys))
        }
        // ignore error.
        Some(ctx.fun.instr_load_unit((expr.id.some(), expr.id.some())))
    }

    fn build_assign(&mut self, ctx: &mut Ctx, lhs: &Expr, rhs: InstrId, is_def: bool) {
        if let ExprData::Ident(ident) = lhs.data {
            let info = ident.info.unwrap();

            match info.target {
                expr::IdentTarget::Item(item) => {
                    let index = ctx.fun.instr_load_int((lhs.id.some(), None.into()), item.value() as i64);
                    ctx.fun.instr_write_path((lhs.id.some(), None.into()), PathBase::Items, &[PathKey::Index(index)], rhs, is_def);
                }

                expr::IdentTarget::Local { node, local } => {
                    let local = ctx.get_local_id(node, local);
                    ctx.fun.instr_set_local((lhs.id.some(), lhs.id.some()), local, rhs);
                }

                expr::IdentTarget::Dynamic => {
                    let name = ctx.fun.add_string(ident.name);
                    ctx.fun.instr_write_path((lhs.id.some(), None.into()), PathBase::Env, &[PathKey::Field(name)], rhs, is_def);
                }
            }
        }
        else if let ExprData::Env = lhs.data {
            println!("ignored error: tried to assign to ENV");
        }
        else if let ExprData::Field(_) | ExprData::Index(_) = lhs.data {
            if let Some((base, lid, keys)) = self.build_path(ctx, lhs) {
                let new_value = ctx.fun.instr_write_path((lhs.id.some(), None.into()), base, &keys, rhs, is_def);
                if let Some(lid) = lid.to_option() {
                    // todo: this is scuffed.
                    ctx.fun.instr_set_local((lhs.id.some(), None.into()), lid, new_value);
                }
            }
        }
        else {
            println!("ignoring error: invalid assign target");
        }
    }

    fn build_func(&mut self, ctx: &mut Ctx, node: NodeId, func: &item::Func) -> FunctionId {
        let _ = ctx;

        let mut inner_fun = self.krate.new_function();
        let mut inner_ctx = Ctx::new(&mut inner_fun, node, &func.params);

        let value = self.build_value_block(&mut inner_ctx, node, &func.body, true).unwrap();
        inner_ctx.fun.instr_return(None.into(), value);

        inner_ctx.fun.id()
    }
}



struct BreakScope {
    node:        NodeId,
    bb_break:    BlockId,
    bb_continue: OptBlockId,
    values:      Option<Vec<PhiEntry>>,
}



struct Ctx<'a> {
    fun:            &'a mut Function,
    locals:         IndexVec<infer::LocalId, (NodeId, bbir::LocalId)>,
    break_scopes:   Vec<BreakScope>,
}

impl<'a> Ctx<'a> {
    #[inline(always)]
    pub fn new(fun: &'a mut Function, node: NodeId, params: &[item::FuncParam]) -> Self {
        let mut locals = index_vec![];
        for param in params {
            let lid = fun.new_param(param.name, node);
            locals.push((node, lid));
        }

        Ctx { fun, locals, break_scopes: vec![] }
    }

    pub fn add_local_decl(&mut self, source: NodeId, name: &str, node: NodeId, local: infer::LocalId) -> bbir::LocalId {
        assert_eq!(local.value(), self.locals.len() as u32);
        let lid = self.fun.new_local(name, source);
        self.locals.push((node, lid));
        lid
    }

    pub fn get_local_id(&mut self, node: NodeId, local: infer::LocalId) -> bbir::LocalId {
        let (entry_node, lid) = self.locals[local];
        assert_eq!(node, entry_node);
        lid
    }

    pub fn begin_break_scope(&mut self, node: NodeId, bb_break: BlockId, bb_continue: OptBlockId, has_value: bool) -> u32 {
        let index = self.break_scopes.len() as u32;
        self.break_scopes.push(BreakScope {
            node, bb_break, bb_continue,
            values: has_value.then(|| vec![]),
        });
        index
    }

    pub fn end_break_scope(&mut self, scope: u32) -> Option<Vec<PhiEntry>> {
        assert_eq!(scope + 1, self.break_scopes.len() as u32);
        self.break_scopes.pop().unwrap().values
    }
}

