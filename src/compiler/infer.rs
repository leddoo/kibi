use crate::index_vec::*;
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


#[derive(Debug)]
pub struct ItemInfo {
    pub item: ItemId,
    pub data: ItemInfoData,
}

#[derive(Debug)]
pub enum ItemInfoData {
    None,
    Fn      (FnInfo),
}


#[derive(Debug)]
pub struct NodeInfo {
    pub node: NodeId,
    pub data: NodeInfoData,
    pub ty:   Type,
}

#[derive(Debug)]
pub enum NodeInfoData {
    None,
    Local       (LocalInfo),
    Ident       (IdentInfo),
    Break       (Option<BreakInfo>),
    Continue    (Option<BreakInfo>),
    Fn          (Box<FnInfo>),
}


#[derive(Clone, Copy, Debug)]
pub struct LocalInfo {
    pub id: LocalId,
}


#[derive(Clone, Copy, Debug)]
pub struct IdentInfo {
    pub target: IdentTarget,
}

#[derive(Clone, Copy, Debug)]
pub enum IdentTarget {
    Dynamic,
    Local(LocalId),
    Item (ItemId),
}


#[derive(Clone, Copy, Debug)]
pub struct BreakInfo {
    pub node:        NodeId,
    pub scope_index: u32,
}


#[derive(Debug)]
pub struct FnInfo {
    pub node_infos: IndexVec<NodeId, NodeInfo>,
    pub num_locals: u32,
}




pub struct Infer {
    item_infos: IndexVec<ItemId, ItemInfo>,
}

impl Infer {
    pub fn new() -> Self {
        Infer {
            item_infos: index_vec![ ItemInfo { item: ItemId::ZERO, data: ItemInfoData::None } ],
        }
    }

    pub fn temp_done(self) -> IndexVec<ItemId, ItemInfo> {
        self.item_infos
    }

    fn next_item_id(&mut self) -> ItemId {
        let id = ItemId::from_usize(self.item_infos.len());
        self.item_infos.push(ItemInfo { item: id, data: ItemInfoData::None });
        id
    }

    pub fn assign_ids_module(&mut self, module: &mut Module) {
        let mut id = NodeId::ZERO;
        self.assign_ids_block(&mut id, &mut module.block.stmts);
        module.num_nodes = id.inc().value();
    }

    fn assign_ids_stmt(&mut self, id: &mut NodeId, stmt: &mut Stmt) {
        stmt.id = id.inc();

        match &mut stmt.data {
            StmtData::Item (item) => {
                item.id = self.next_item_id();

                match &mut item.data {
                    ItemData::Fn(fun) => {
                        self.assign_ids_fn(fun);
                    }
                }
            }

            StmtData::Local (local) => {
                if let Some(value) = &mut local.value {
                    self.assign_ids_expr(id, value);
                }
            }

            StmtData::Expr (expr) => { self.assign_ids_expr(id, expr); }

            StmtData::Empty => (),
        }
    }

    fn assign_ids_expr(&mut self, id: &mut NodeId, expr: &mut Expr) {
        expr.id = id.inc();

        match &mut expr.data {
            ExprData::Nil |
            ExprData::Bool (_) |
            ExprData::Number (_) |
            ExprData::QuotedString (_) |
            ExprData::Ident (_) => {}


            ExprData::Tuple (tuple) => {
                for value in &mut tuple.values {
                    self.assign_ids_expr(id, value);
                }
            }

            ExprData::List (list) => {
                for value in &mut list.values {
                    self.assign_ids_expr(id, value);
                }
            }

            ExprData::Do (doo) => {
                self.assign_ids_block(id, &mut doo.stmts);
            }

            ExprData::SubExpr (sub_expr) => {
                self.assign_ids_expr(id, sub_expr);
            }

            ExprData::Op1 (op1) => {
                self.assign_ids_expr(id, &mut op1.child);
            }

            ExprData::Op2 (op2) => {
                self.assign_ids_expr(id, &mut op2.children[0]);
                self.assign_ids_expr(id, &mut op2.children[1]);
            }

            ExprData::Field (field) => {
                self.assign_ids_expr(id, &mut field.base);
            }

            ExprData::Index (index) => {
                self.assign_ids_expr(id, &mut index.base);
                self.assign_ids_expr(id, &mut index.index);
            }

            ExprData::Call (call) => {
                self.assign_ids_expr(id, &mut call.func);
                for arg in &mut call.args {
                    self.assign_ids_expr(id, arg);
                }
            }

            ExprData::If (iff) => {
                self.assign_ids_expr(id, &mut iff.condition);
                self.assign_ids_block(id, &mut iff.on_true.stmts);
                if let Some(on_false) = &mut iff.on_false {
                    self.assign_ids_block(id, &mut on_false.stmts);
                }
            }

            ExprData::While (whilee) => {
                self.assign_ids_expr(id, &mut whilee.condition);
                self.assign_ids_block(id, &mut whilee.body);
            }

            ExprData::Break (brk) => {
                if let Some(value) = &mut brk.value {
                    self.assign_ids_expr(id, value);
                }
            }

            ExprData::Continue (_) => {}

            ExprData::Return (ret) => {
                if let Some(value) = &mut ret.value {
                    self.assign_ids_expr(id, value);
                }
            }

            ExprData::Fn (fun) => {
                self.assign_ids_fn(fun)
            }

            ExprData::Env => {}
        }
    }

    fn assign_ids_fn(&mut self, fun: &mut data::Fn) {
        let mut fun_id = NodeId::ZERO;
        self.assign_ids_block(&mut fun_id, &mut fun.body);
        fun.num_nodes = fun_id.inc().value();
    }

    fn assign_ids_block(&mut self, id: &mut NodeId, block: &mut [Stmt]) {
        for stmt in block.iter_mut() {
            self.assign_ids_stmt(id, stmt);
        }
    }


    pub fn infer_module(&mut self, module: &Module) -> FnInfo {
        let mut ctx = InferCtx::new(module.num_nodes);
        self.infer_block(&mut ctx, &module.block.stmts);
        FnInfo { node_infos: ctx.node_infos, num_locals: ctx.locals.len() as u32 }
    }

    fn infer_stmt(&mut self, ctx: &mut InferCtx, stmt: &Stmt) {
        match &stmt.data {
            StmtData::Item (item) => {
                match &item.data {
                    ItemData::Fn(fun) => {
                        let (_, fn_info) = self.infer_fn(ctx, fun);
                        self.item_infos[item.id].data = ItemInfoData::Fn(fn_info);
                    }
                }
            }

            StmtData::Local (local) => {
                let lid = ctx.add_local_decl(local.name);
                if let Some(value) = &local.value {
                    self.infer_expr(ctx, value, None);
                }
                ctx.node_infos[stmt.id].data = NodeInfoData::Local(LocalInfo { id: lid });
            }

            StmtData::Expr (expr) => { self.infer_expr(ctx, expr, None); }

            StmtData::Empty => (),
        }
    }

    fn infer_expr(&mut self, ctx: &mut InferCtx, expr: &Expr, expected_ty: Option<&Type>) -> Type {
        let ty = match &expr.data {
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

            ExprData::Ident (name) => {
                if let Some(decl) = ctx.find_decl(name) {
                    ctx.node_infos[expr.id].data = NodeInfoData::Ident(
                        IdentInfo { target: decl.target });
                }
                else {
                    ctx.node_infos[expr.id].data = NodeInfoData::Ident(
                        IdentInfo { target: IdentTarget::Dynamic });
                }
                Type::Any
            }


            ExprData::Tuple (tuple) => {
                let mut types = Vec::with_capacity(tuple.values.len());
                for value in &tuple.values {
                    types.push(self.infer_expr(ctx, value, None));
                }
                Type::Tuple(types.into_boxed_slice())
            }

            ExprData::List (list) => {
                for value in &list.values {
                    self.infer_expr(ctx, value, None);
                }
                Type::List(Box::new(Type::Any))
            }

            ExprData::Do (doo) => {
                self.infer_do_block(ctx, expr.id, doo.label, &doo.stmts, expected_ty)
            }

            ExprData::SubExpr (sub_expr) => {
                self.infer_expr(ctx, sub_expr, expected_ty)
            }

            ExprData::Op1 (op1) => {
                self.infer_expr(ctx, &op1.child, None);
                Type::Any
            }

            ExprData::Op2 (op2) => {
                match op2.kind {
                    data::Op2Kind::Assign | data::Op2Kind::Define => {
                        let [op_lhs, op_rhs] = &op2.children;

                        if let ExprData::Tuple(lhs) = &op_lhs.data {
                            if op2.kind != data::Op2Kind::Assign {
                                println!("error: tried to define tuple");
                            }

                            let lhs = &lhs.values;

                            if let ExprData::Tuple(rhs) = &op_rhs.data {
                                let rhs = &rhs.values;
                                if lhs.len() != rhs.len() {
                                    println!("error: tuple assign length mismatch");
                                }

                                for i in 0..lhs.len() {
                                    if let Some(rhs) = rhs.get(i) {
                                        let rhs_ty = self.infer_expr(ctx, rhs, None);
                                        self.infer_assign(ctx, &lhs[i], &rhs_ty, false);
                                    }
                                }
                            }
                            else {
                                unimplemented!()
                            }
                        }
                        else {
                            let is_def = op2.kind == data::Op2Kind::Define;
                            let rhs = self.infer_expr(ctx, &op2.children[1], None);
                            self.infer_assign(ctx, &op2.children[0], &rhs, is_def);
                        }
                        Type::Any
                    }

                    data::Op2Kind::Op2Assign(op) => {
                        let src1 = self.infer_expr(ctx, &op2.children[0], None);
                        let src2 = self.infer_expr(ctx, &op2.children[1], None);

                        // todo: do op analysis w/ src1,2.
                        let _ = (op, src1, src2);
                        let value = Type::Any;

                        let is_define = false;
                        self.infer_assign(ctx, &op2.children[0], &value, is_define);

                        Type::Unit
                    }

                    data::Op2Kind::Op2(op) => {
                        let src1 = self.infer_expr(ctx, &op2.children[0], None);
                        let src2 = self.infer_expr(ctx, &op2.children[1], None);

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
                self.infer_expr(ctx, &call.func, None);
                for arg in &call.args {
                    self.infer_expr(ctx, arg, None);
                }
                Type::Any
            }

            ExprData::If (iff) => {
                self.infer_expr(ctx, &iff.condition, Some(&Type::Bool));
                self.infer_if_block(ctx, expr.id, &iff.on_true, None);
                if let Some(on_false) = &iff.on_false {
                    self.infer_if_block(ctx, expr.id, on_false, None);
                }
                Type::Any
            }

            ExprData::While (whilee) => {
                self.infer_expr(ctx, &whilee.condition, Some(&Type::Bool));

                let bs = ctx.begin_break_scope(expr.id, whilee.label, true, Type::None);
                self.infer_block(ctx, &whilee.body);
                ctx.end_break_scope(bs);

                Type::Unit
            }

            ExprData::Break (brk) => {
                let target = ctx.current_break_target(expr.source, brk.label);
                let break_info = target.map(|bs| BreakInfo { node: bs.node, scope_index: bs.index });

                if let Some(value) = &brk.value {
                    let ty = target.map(|bs| bs.ty.clone()).unwrap_or(Type::Any);
                    self.infer_expr(ctx, value, Some(&ty));
                }

                ctx.node_infos[expr.id].data = NodeInfoData::Break(break_info);

                Type::Unit
            }

            ExprData::Continue (cont) => {
                let target = ctx.current_continue_target(expr.source, cont.label);
                ctx.node_infos[expr.id].data = NodeInfoData::Continue(
                    target.map(|bs| BreakInfo { node: bs.node, scope_index: bs.index }));

                Type::Unit
            }

            ExprData::Return (ret) => {
                if let Some(value) = &ret.value {
                    self.infer_expr(ctx, value, None);
                }
                Type::Unit
            }

            ExprData::Fn (fun) => {
                let (ty, fn_info) = self.infer_fn(ctx, fun);
                ctx.node_infos[expr.id].data = NodeInfoData::Fn(Box::new(fn_info));
                ty
            }

            ExprData::Env => {
                Type::Any
            }
        };
        ctx.node_infos[expr.id].ty = ty.clone();
        ty
    }

    fn infer_path(&mut self, ctx: &mut InferCtx, expr: &Expr, expected_ty: Option<&Type>) -> Type {
        // @todo: use.
        let _ = expected_ty;

        match &expr.data {
            ExprData::Field (field) => {
                let _ = self.infer_path(ctx, &field.base, None);
                Type::Any
            }

            ExprData::Index (index) => {
                let _ = self.infer_path(ctx, &index.base,  None);
                self.infer_expr(ctx, &index.index, None);
                Type::Any
            }

            ExprData::Ident(name) => {
                if let Some(decl) = ctx.find_decl(name) {
                    ctx.node_infos[expr.id].data = NodeInfoData::Ident(
                        IdentInfo { target: decl.target });
                }
                else {
                    ctx.node_infos[expr.id].data = NodeInfoData::Ident(
                        IdentInfo { target: IdentTarget::Dynamic });
                }
                Type::Any
            }

            ExprData::Env => {
                Type::Any
            }

            _ => {
                println!("invalid path base");
                Type::Error
            }
        }
    }

    fn infer_assign(&mut self, ctx: &mut InferCtx, lhs: &Expr, rhs: &Type, is_def: bool) {
        if let ExprData::Ident(name) = lhs.data {
            if let Some(decl) = ctx.find_decl(name) {
                // @todo: use for tyck.
                ctx.node_infos[lhs.id].data = NodeInfoData::Ident(
                    IdentInfo { target: decl.target });
            }
            else {
                if is_def != false {
                    println!("error: tried to define global");
                }
                ctx.node_infos[lhs.id].data = NodeInfoData::Ident(
                    IdentInfo { target: IdentTarget::Dynamic });
            }
        }
        else if let ExprData::Env = lhs.data {
            println!("error: tried to assign to ENV");
        }
        else if let ExprData::Field(_) | ExprData::Index(_) = lhs.data {
            let lhs_ty = self.infer_path(ctx, lhs, Some(rhs));
            ctx.node_infos[lhs.id].ty = lhs_ty;
        }
        else {
            println!("error {}: invalid assign target", lhs.source);
        }
    }

    fn infer_block(&mut self, ctx: &mut InferCtx, block: &[Stmt]) {
        // collect items.
        let item_scope = ctx.begin_scope();
        for stmt in block.iter() {
            if let StmtData::Item(item) = &stmt.data {
                match &item.data {
                    ItemData::Fn(fun) => {
                        if let Some(name) = fun.name {
                            ctx.add_item_decl(name, item.id);
                        }
                    }
                }
            }
        }

        // infer stmts.
        let block_scope = ctx.begin_scope();
        for stmt in block.iter() {
            self.infer_stmt(ctx, stmt);
        }

        ctx.end_scope(block_scope);
        ctx.end_scope(item_scope);
    }

    fn infer_do_block(&mut self, ctx: &mut InferCtx, node: NodeId, label: Option<&str>, block: &[Stmt], expected_ty: Option<&Type>) -> Type {
        // @todo: use.
        let _ = expected_ty;

        let bs = ctx.begin_break_scope(node, label, false, Type::Any);
        self.infer_block(ctx, block);
        ctx.end_break_scope(bs);

        Type::Any
    }

    fn infer_value_block(&mut self, ctx: &mut InferCtx, block: &[Stmt], expected_ty: Option<&Type>) -> Type {
        // @todo: use.
        let _ = expected_ty;

        self.infer_block(ctx, block);
        Type::Any
    }

    fn infer_if_block(&mut self, ctx: &mut InferCtx, node: NodeId, block: &data::IfBlock, expected_ty: Option<&Type>) -> Type {
        if block.is_do {
            self.infer_do_block(ctx, node, None, &block.stmts, expected_ty)
        }
        else {
            self.infer_value_block(ctx, &block.stmts, expected_ty)
        }
    }

    fn infer_fn(&mut self, ctx: &mut InferCtx, fun: &data::Fn) -> (Type, FnInfo) {
        // @temp: need ctx for closures.
        let _ = ctx;

        let mut fctx = InferCtx::new(fun.num_nodes);

        for param in &fun.params {
            fctx.add_local_decl(param.name);
        }

        self.infer_value_block(&mut fctx, &fun.body, None);

        (Type::Any, FnInfo {
            node_infos: fctx.node_infos,
            num_locals: fctx.locals.len() as u32,
        })
    }
}


define_id!(LocalId);

struct Decl {
    name:   String,
    scope:  u32,
    target: IdentTarget,
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
    locals:         Vec<()>,
    decls:          Vec<Decl>,
    node_infos:     IndexVec<NodeId, NodeInfo>,
    break_scopes:   Vec<BreakScope>,
}

impl InferCtx {
    pub fn new(num_nodes: u32) -> InferCtx {
        assert!(num_nodes > 0);

        let mut infos = Vec::with_capacity(num_nodes as usize);
        for i in 0..num_nodes {
            infos.push(NodeInfo {
                node: NodeId::new_unck(i),
                data: NodeInfoData::None,
                ty:   Type::None,
            });
        }
        InferCtx {
            scope:  0,
            locals: vec![],
            decls:  vec![],
            node_infos:  infos.into(),
            break_scopes: vec![],
        }
    }

    fn add_local_decl(&mut self, name: &str) -> LocalId {
        let id = LocalId(self.locals.len() as u32);
        self.locals.push(());
        self.decls.push(Decl {
            name:   name.to_string(),
            scope:  self.scope,
            target: IdentTarget::Local(id),
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
            target: IdentTarget::Item(id)
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

