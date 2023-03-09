use crate::macros::define_id;
use super::ast::*;


#[derive(Clone, Debug)]
pub enum Type {
    None,
    Error,

    Any,
    Nil,
    Bool,
    Number,
    String,
    Unit,
    Tuple       (Box<[Type]>), // this is actually 16 bytes, oops.
    List        (Box<Type>),
    Map         (Box<(Type, Type)>),
    Func        (Box<(Box<[Type]>, Type)>),
}



pub struct Infer {
    prev_item_id: ItemId,
    prev_node_id: NodeId,
}

impl Infer {
    pub fn new() -> Self {
        Infer {
            prev_item_id: ItemId::ZERO,
            prev_node_id: NodeId::ZERO,
        }
    }

    #[inline(always)]
    fn next_item_id(&mut self) -> ItemId { self.prev_item_id.inc() }

    #[inline(always)]
    fn next_node_id(&mut self) -> NodeId { self.prev_node_id.inc() }

    pub fn assign_ids(&mut self, module: &mut item::Module) {
        self.assign_ids_block(&mut module.block.stmts);
    }

    fn assign_ids_stmt(&mut self, stmt: &mut Stmt) {
        stmt.id = self.next_node_id();

        match &mut stmt.data {
            StmtData::Item (item) => {
                item.id = self.next_item_id();

                let id0 = self.prev_node_id;
                match &mut item.data {
                    ItemData::Module(module) => {
                        let _ = module;
                        unimplemented!()
                    }

                    ItemData::Func(func) => {
                        self.assign_ids_block(&mut func.body);
                    }
                }
                let id1 = self.prev_node_id;
                item.num_nodes = id1.value() - id0.value();
            }

            StmtData::Local (local) => {
                if let Some(value) = &mut local.value {
                    self.assign_ids_expr(value);
                }
            }

            StmtData::Expr (expr) => { self.assign_ids_expr(expr); }

            StmtData::Empty => (),
        }
    }

    fn assign_ids_expr(&mut self, expr: &mut Expr) {
        expr.id = self.next_node_id();

        match &mut expr.data {
            ExprData::Nil |
            ExprData::Bool (_) |
            ExprData::Number (_) |
            ExprData::QuotedString (_) |
            ExprData::Ident (_) => {}


            ExprData::Tuple (tuple) => {
                for value in &mut tuple.values {
                    self.assign_ids_expr(value);
                }
            }

            ExprData::List (list) => {
                for value in &mut list.values {
                    self.assign_ids_expr(value);
                }
            }

            ExprData::Do (doo) => {
                self.assign_ids_block(&mut doo.stmts);
            }

            ExprData::SubExpr (sub_expr) => {
                self.assign_ids_expr(sub_expr);
            }

            ExprData::Op1 (op1) => {
                self.assign_ids_expr(&mut op1.child);
            }

            ExprData::Op2 (op2) => {
                self.assign_ids_expr(&mut op2.children[0]);
                self.assign_ids_expr(&mut op2.children[1]);
            }

            ExprData::Field (field) => {
                self.assign_ids_expr(&mut field.base);
            }

            ExprData::Index (index) => {
                self.assign_ids_expr(&mut index.base);
                self.assign_ids_expr(&mut index.index);
            }

            ExprData::Call (call) => {
                self.assign_ids_expr(&mut call.func);
                for arg in &mut call.args {
                    self.assign_ids_expr(arg);
                }
            }

            ExprData::If (iff) => {
                self.assign_ids_expr(&mut iff.condition);
                self.assign_ids_block(&mut iff.on_true.stmts);
                if let Some(on_false) = &mut iff.on_false {
                    self.assign_ids_block(&mut on_false.stmts);
                }
            }

            ExprData::While (whilee) => {
                self.assign_ids_expr(&mut whilee.condition);
                self.assign_ids_block(&mut whilee.body);
            }

            ExprData::Break (brk) => {
                if let Some(value) = &mut brk.value {
                    self.assign_ids_expr(value);
                }
            }

            ExprData::Continue (_) => {}

            ExprData::Return (ret) => {
                if let Some(value) = &mut ret.value {
                    self.assign_ids_expr(value);
                }
            }

            ExprData::Env => {}
        }
    }

    fn assign_ids_block(&mut self, block: &mut [Stmt]) {
        for stmt in block.iter_mut() {
            self.assign_ids_stmt(stmt);
        }
    }


    pub fn infer(&mut self, module: &mut item::Module) {
        self.infer_module(module);
    }

    fn infer_module(&mut self, module: &mut item::Module) {
        let mut ctx = InferCtx::new(None);
        self.infer_block(&mut ctx, &mut module.block.stmts);
    }

    fn infer_stmt(&mut self, ctx: &mut InferCtx, stmt: &mut Stmt) {
        match &mut stmt.data {
            StmtData::Item (item) => {
                match &mut item.data {
                    ItemData::Module(module) => {
                        let _ = module;
                        unimplemented!()
                    }

                    ItemData::Func(func) => {
                        let mut fctx = InferCtx::new(Some(ctx));

                        for param in &func.params {
                            fctx.add_local_decl(stmt.id, param.name);
                        }

                        self.infer_value_block(&mut fctx, &mut func.body, None);
                    }
                }
            }

            StmtData::Local (local) => {
                let lid = ctx.add_local_decl(stmt.id, local.name);
                if let Some(value) = &mut local.value {
                    self.infer_expr(ctx, value, None);
                }
                local.info = Some(expr::LocalInfo { id: lid });
            }

            StmtData::Expr (expr) => { self.infer_expr(ctx, expr, None); }

            StmtData::Empty => (),
        }
    }

    fn infer_expr(&mut self, ctx: &mut InferCtx, expr: &mut Expr, expected_ty: Option<&Type>) -> Type {
        let ty = match &mut expr.data {
            ExprData::Nil => {
                Type::Any
            }

            ExprData::Bool (_) => {
                Type::Bool
            }

            ExprData::Number (_) => {
                Type::Number
            }

            ExprData::QuotedString (_) => {
                Type::String
            }

            ExprData::Ident (ident) => {
                if let Some(decl) = ctx.find_decl(ident.name) {
                    ident.info = Some(expr::IdentInfo { target: decl.target });
                }
                else {
                    ident.info = Some(expr::IdentInfo { target: expr::IdentTarget::Dynamic });
                }
                Type::Any
            }


            ExprData::Tuple (tuple) => {
                let mut types = Vec::with_capacity(tuple.values.len());
                for value in &mut tuple.values {
                    types.push(self.infer_expr(ctx, value, None));
                }
                Type::Tuple(types.into_boxed_slice())
            }

            ExprData::List (list) => {
                for value in &mut list.values {
                    self.infer_expr(ctx, value, None);
                }
                Type::List(Box::new(Type::Any))
            }

            ExprData::Do (doo) => {
                self.infer_do_block(ctx, expr.id, doo.label, &mut doo.stmts, expected_ty)
            }

            ExprData::SubExpr (sub_expr) => {
                self.infer_expr(ctx, sub_expr, expected_ty)
            }

            ExprData::Op1 (op1) => {
                self.infer_expr(ctx, &mut op1.child, None);
                Type::Any
            }

            ExprData::Op2 (op2) => {
                match op2.kind {
                    expr::Op2Kind::Assign | expr::Op2Kind::Define => {
                        let [op_lhs, op_rhs] = &mut op2.children;

                        if let ExprData::Tuple(lhs) = &mut op_lhs.data {
                            if op2.kind != expr::Op2Kind::Assign {
                                println!("error: tried to define tuple");
                            }

                            let lhs = &mut lhs.values;

                            if let ExprData::Tuple(rhs) = &mut op_rhs.data {
                                let rhs = &mut rhs.values;
                                if lhs.len() != rhs.len() {
                                    println!("error: tuple assign length mismatch");
                                }

                                for i in 0..lhs.len() {
                                    if let Some(rhs) = rhs.get_mut(i) {
                                        let rhs_ty = self.infer_expr(ctx, rhs, None);
                                        self.infer_assign(ctx, &mut lhs[i], &rhs_ty, false);
                                    }
                                }

                                op_rhs.ty = Some(Type::Any);
                            }
                            else {
                                unimplemented!()
                            }

                            op_lhs.ty = Some(Type::Any);
                        }
                        else {
                            let is_def = op2.kind == expr::Op2Kind::Define;
                            let rhs = self.infer_expr(ctx, &mut op2.children[1], None);
                            self.infer_assign(ctx, &mut op2.children[0], &rhs, is_def);
                        }
                        Type::Any
                    }

                    expr::Op2Kind::Op2Assign(op) => {
                        let [src1, src2] = &mut op2.children;
                        let src1 = self.infer_expr(ctx, src1, None);
                        let src2 = self.infer_expr(ctx, src2, None);

                        // todo: do op analysis w/ src1,2.
                        let _ = (op, src1, src2);
                        let value = Type::Any;

                        let is_define = false;
                        self.infer_assign(ctx, &mut op2.children[0], &value, is_define);

                        Type::Unit
                    }

                    expr::Op2Kind::Op2(op) => {
                        let [src1, src2] = &mut op2.children;
                        let src1 = self.infer_expr(ctx, src1, None);
                        let src2 = self.infer_expr(ctx, src2, None);

                        // todo: do op analysis w/ src1,2.
                        let _ = (op, src1, src2);
                        let result = Type::Any;

                        result
                    }
                }
            }

            ExprData::Field (_) |
            ExprData::Index (_) => {
                self.infer_path(ctx, expr, expected_ty)
            }

            ExprData::Call (call) => {
                self.infer_expr(ctx, &mut call.func, None);
                for arg in &mut call.args {
                    self.infer_expr(ctx, arg, None);
                }
                Type::Any
            }

            ExprData::If (iff) => {
                self.infer_expr(ctx, &mut iff.condition, Some(&Type::Bool));
                self.infer_if_block(ctx, expr.id, &mut iff.on_true, None);
                if let Some(on_false) = &mut iff.on_false {
                    self.infer_if_block(ctx, expr.id, on_false, None);
                }
                Type::Any
            }

            ExprData::While (whilee) => {
                self.infer_expr(ctx, &mut whilee.condition, Some(&Type::Bool));

                let bs = ctx.begin_break_scope(expr.id, whilee.label, true, Type::None);
                self.infer_block(ctx, &mut whilee.body);
                ctx.end_break_scope(bs);

                Type::Unit
            }

            ExprData::Break (brk) => {
                let target = ctx.current_break_target(expr.source, brk.label);
                brk.info = Some(target.map(|bs| expr::BreakInfo {
                    node: bs.node, scope_index: bs.index }));

                if let Some(value) = &mut brk.value {
                    let ty = target.map(|bs| bs.ty.clone()).unwrap_or(Type::Any);
                    self.infer_expr(ctx, value, Some(&ty));
                }

                Type::Unit
            }

            ExprData::Continue (cont) => {
                let target = ctx.current_continue_target(expr.source, cont.label);
                cont.info = Some(target.map(|bs| expr::BreakInfo {
                    node: bs.node, scope_index: bs.index }));

                Type::Unit
            }

            ExprData::Return (ret) => {
                if let Some(value) = &mut ret.value {
                    self.infer_expr(ctx, value, None);
                }
                Type::Unit
            }

            ExprData::Env => {
                // @temp-no-env-access.
                println!("error {}: can't read ENV.", expr.source);
                Type::Any
            }
        };
        expr.ty = Some(ty.clone());
        ty
    }

    fn infer_path(&mut self, ctx: &mut InferCtx, expr: &mut Expr, expected_ty: Option<&Type>) -> Type {
        // @todo: use.
        let _ = expected_ty;

        match &mut expr.data {
            ExprData::Field (field) => {
                let _ = self.infer_path(ctx, &mut field.base, None);
                Type::Any
            }

            ExprData::Index (index) => {
                let _ = self.infer_path(ctx, &mut index.base,  None);
                self.infer_expr(ctx, &mut index.index, None);
                Type::Any
            }

            ExprData::Ident(ident) => {
                if let Some(decl) = ctx.find_decl(ident.name) {
                    ident.info = Some(expr::IdentInfo { target: decl.target });
                }
                else {
                    ident.info = Some(expr::IdentInfo { target: expr::IdentTarget::Dynamic });
                }
                Type::Any
            }

            ExprData::Env => {
                Type::Any
            }

            _ => {
                println!("error {}: invalid path base", expr.source);
                Type::Error
            }
        }
    }

    fn infer_assign(&mut self, ctx: &mut InferCtx, lhs: &mut Expr, rhs: &Type, is_def: bool) {
        if let ExprData::Ident(ident) = &mut lhs.data {
            if let Some(decl) = ctx.find_decl(ident.name) {
                ident.info = Some(expr::IdentInfo { target: decl.target });
            }
            else {
                if is_def != false {
                    println!("error: tried to define global");
                }
                ident.info = Some(expr::IdentInfo { target: expr::IdentTarget::Dynamic });
            }
            lhs.ty = Some(Type::Any);
        }
        else if let ExprData::Env = lhs.data {
            println!("error: tried to assign to ENV");
            lhs.ty = Some(Type::Error);
        }
        else if let ExprData::Field(_) | ExprData::Index(_) = lhs.data {
            lhs.ty = Some(self.infer_path(ctx, lhs, Some(rhs)));
        }
        else {
            println!("error {}: invalid assign target", lhs.source);
            lhs.ty = Some(Type::Error);
        }
    }

    fn infer_block(&mut self, ctx: &mut InferCtx, block: &mut [Stmt]) {
        // collect items.
        let item_scope = ctx.begin_scope();
        for stmt in block.iter() {
            if let StmtData::Item(item) = &stmt.data {
                match &item.data {
                    ItemData::Module(module) => {
                        let _ = module;
                        unimplemented!()
                    }

                    ItemData::Func(func) => {
                        if let Some(name) = func.name {
                            ctx.add_item_decl(name, item.id);
                        }
                    }
                }
            }
        }

        // infer stmts.
        let block_scope = ctx.begin_scope();
        for stmt in block.iter_mut() {
            self.infer_stmt(ctx, stmt);
        }

        ctx.end_scope(block_scope);
        ctx.end_scope(item_scope);
    }

    fn infer_do_block(&mut self, ctx: &mut InferCtx, node: NodeId, label: Option<&str>, block: &mut [Stmt], expected_ty: Option<&Type>) -> Type {
        // @todo: use.
        let _ = expected_ty;

        let bs = ctx.begin_break_scope(node, label, false, Type::Any);
        self.infer_block(ctx, block);
        ctx.end_break_scope(bs);

        Type::Any
    }

    fn infer_value_block(&mut self, ctx: &mut InferCtx, block: &mut [Stmt], expected_ty: Option<&Type>) -> Type {
        // @todo: use.
        let _ = expected_ty;

        self.infer_block(ctx, block);
        Type::Any
    }

    fn infer_if_block(&mut self, ctx: &mut InferCtx, node: NodeId, block: &mut expr::IfBlock, expected_ty: Option<&Type>) -> Type {
        if block.is_do {
            self.infer_do_block(ctx, node, None, &mut block.stmts, expected_ty)
        }
        else {
            self.infer_value_block(ctx, &mut block.stmts, expected_ty)
        }
    }
}


define_id!(LocalId);

#[derive(Clone)]
struct Decl {
    name:   String,
    scope:  u32,
    target: expr::IdentTarget,
}

struct BreakScope {
    index: u32,
    node:  NodeId,
    ty:    Type,
    label: Option<String>,
    can_continue: bool,
}

struct InferCtx {
    scope:          u32,
    decls:          Vec<Decl>,
    locals:         Vec<()>,
    break_scopes:   Vec<BreakScope>,
}

impl InferCtx {
    pub fn new(parent: Option<&InferCtx>) -> InferCtx {
        let mut decls = vec![];
        let mut scope = 0;

        if let Some(parent) = parent {
            decls = parent.decls.iter()
                .filter(|decl| { decl.target.is_item() })
                .cloned()
                .collect();
            scope = parent.scope + 1;
        }

        InferCtx {
            scope,
            decls,
            locals: vec![],
            break_scopes: vec![],
        }
    }

    fn add_local_decl(&mut self, node: NodeId, name: &str) -> LocalId {
        let id = LocalId(self.locals.len() as u32);
        self.locals.push(());
        self.decls.push(Decl {
            name:   name.to_string(),
            scope:  self.scope,
            target: expr::IdentTarget::Local { node, local: id },
        });
        id
    }

    fn add_item_decl(&mut self, name: &str, id: ItemId) {
        if let Some(decl) = self.find_decl(name) {
            if decl.scope == self.scope {
                println!("duplicate definition of {name:?}");
            }
        }
        self.decls.push(Decl {
            name:   name.to_string(),
            scope:  self.scope,
            target: expr::IdentTarget::Item(id)
        });
    }

    fn find_decl(&self, name: &str) -> Option<&Decl> {
        self.decls.iter().rev().find(|decl| decl.name == name)
    }

    fn begin_scope(&mut self) -> u32 {
        self.scope += 1;
        self.scope
    }

    fn end_scope(&mut self, scope: u32) {
        assert_eq!(self.scope, scope);
        self.decls.retain(|decl| decl.scope < self.scope);
        self.scope -= 1;
    }


    fn begin_break_scope(&mut self, node: NodeId, label: Option<&str>, can_continue: bool, ty: Type) -> u32 {
        let index = self.break_scopes.len() as u32;
        self.break_scopes.push(BreakScope {
            index, node, ty,
            label: label.map(str::to_string),
            can_continue,
        });
        index
    }

    fn end_break_scope(&mut self, scope: u32) {
        assert_eq!(scope + 1, self.break_scopes.len() as u32);
        self.break_scopes.pop();
    }

    fn current_break_target(&self, source: SourceRange, label: Option<&str>) -> Option<&BreakScope> {
        if let Some(label) = label {
            for scope in self.break_scopes.iter().rev() {
                if scope.label.as_deref() == Some(label) {
                    return Some(scope);
                }
            }
            println!("error {source}: no break target with label {label}");
            return None;
        }
        else {
            if let Some(scope) = self.break_scopes.last() {
                return Some(scope);
            }
            println!("error {source}: no break target");
            return None;
        }
    }

    fn current_continue_target(&self, source: SourceRange, label: Option<&str>) -> Option<&BreakScope> {
        if let Some(label) = label {
            for scope in self.break_scopes.iter().rev() {
                if scope.label.as_deref() == Some(label) {
                    if !scope.can_continue {
                        println!("error {source}: {label} is not a continue target");
                        return None;
                    }
                    else {
                        return Some(scope);
                    }
                }
            }
            println!("error {source}: no continue target with label {label}");
            return None;
        }
        else {
            for scope in self.break_scopes.iter().rev() {
                if scope.can_continue {
                    return Some(scope);
                }
            }
            println!("error {source}: no continue target");
            return None;
        }
    }
}

