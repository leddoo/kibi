use sti::traits::CopyIt;

use crate::string_table::OptAtom;
use crate::ast::*;
use crate::tt::*;

use super::*;

impl<'me, 'c, 'out> Elaborator<'me, 'c, 'out> {
    pub fn elab_do(&mut self, expr_id: ExprId, flags: ExprFlags, block: expr::Block, expected_ty: Option<Term<'out>>)
        -> (Term<'out>, Term<'out>)
    {
        if block.stmts.len() == 0 {
            return (Term::UNIT_MK, Term::UNIT);
        }

        let old_scope = self.lctx.current;
        let old_locals = self.locals.clone();

        let source = expr_id.some();

        let result_ty = match expected_ty {
            Some(ex) => {
                let ex = self.instantiate_term_vars(ex);
                if ex.has_ivars() {
                    self.error(expr_id, ElabError::TempStr("expected type must not have ivars"));
                    return self.mkt_ax_error_from_expected(expected_ty, source);
                }
                ex
            }

            None => {
                self.error(expr_id, ElabError::TempStr("expected type must be known"));
                return self.mkt_ax_error_from_expected(expected_ty, source);
            }
        };

        let mut this = ElabDo::new(self, result_ty);
        let (ret, ret_ty) = this.elab_do_block(expr_id, flags, block, Some(result_ty));//.unwrap();
        // @cleanup: dedup.
        if !this.ensure_def_eq(ret_ty, result_ty) {
            let expected = this.instantiate_term_vars(result_ty);
            let ty       = this.instantiate_term_vars(ret_ty);
            let expected = this.reduce_ex(expected, false);
            let ty       = this.reduce_ex(ty, false);
            this.elab.error(expr_id, {
                let mut pp = TermPP::new(this.elab.env, &this.elab.strings, &this.elab.lctx, this.elab.alloc);
                let expected = pp.pp_term(expected);
                let found    = pp.pp_term(ty);
                ElabError::TypeMismatch { expected, found }
            });
            return self.mkt_ax_error_from_expected(expected_ty, source);
        }
        this.end_jp(ret);

        for (_, jp) in this.jps.iter() {
            if jp.reachable {
                let mut ty = this.result_ty;
                for local in jp.locals.copy_it().rev() {
                    ty = this.mk_binder(ty, local, true, TERM_SOURCE_NONE);
                }
                for param in this.locals[..this.num_params].copy_it().rev() {
                    ty = this.mk_binder(ty, param.id, true, TERM_SOURCE_NONE);
                }
                assert!(this.elab.ensure_def_eq(jp.ty, ty));

                this.elab.aux_defs.push(AuxDef {
                    name: atoms::jp,
                    ivar: jp.ivar.try_ivar().unwrap(),
                    ty,
                    value: jp.value.unwrap(),
                });
            }
            else {
                let ty  = this.elab.mkt_ax_unreach(Term::SORT_1, TERM_SOURCE_NONE);
                let val = this.elab.mkt_ax_unreach(ty, TERM_SOURCE_NONE);
                assert!(this.elab.ensure_def_eq(jp.ty,   ty));
                assert!(this.elab.ensure_def_eq(jp.ivar, val));
            }
        }

        this.elab.lctx.current = old_scope;
        // @cleanup: sti vec assign/_from_slice.
        this.elab.locals.clear();
        this.elab.locals.extend_from_slice(&old_locals);

        let entry = this.jps[JoinPoint::ZERO].ivar;
        let local_terms = Vec::from_iter(self.locals.copy_map_it(|local| self.alloc.mkt_local(local.id, source)));
        let result = self.alloc.mkt_apps(entry, &local_terms, source);
        return (result, result_ty);
    }
}


sti::define_key!(u32, JoinPoint, opt: OptJoinPoint);

struct ElabDo<'me, 'e, 'c, 'out> {
    elab: &'me mut Elaborator<'e, 'c, 'out>,

    param_scope: OptScopeId,
    num_params: usize,

    result_ty: Term<'out>,

    jps: KVec<JoinPoint, JoinPointData<'out>>,

    jump_targets: Vec<JumpTarget<'out>>,

    current_jp: JoinPoint,
    stmts: Vec<Stmt<'out>>,
}

#[derive(Clone, Copy)]
struct JumpTarget<'a> {
    label: OptAtom,
    break_jp: JoinPoint,
    break_ty: Option<Term<'a>>,
    break_used: bool,
    continue_jp: OptJoinPoint,
    else_jp:     Option<OptJoinPoint>,
}

struct JoinPointData<'a> {
    ivar: Term<'a>,
    ty: Term<'a>,
    // this is kinda scuffed:
    // the local for the arg is added by the caller after begin_jp.
    locals: Vec<ScopeId>,
    arg_ty: Option<Term<'a>>,
    value: Option<Term<'a>>,
    reachable: bool,
}

#[derive(Clone, Copy)]
enum Stmt<'out> {
    Local(ScopeId),
    Term((Term<'out>, Term<'out>)),
}

impl<'me, 'e, 'c, 'out> ElabDo<'me, 'e, 'c, 'out> {
    fn new(elab: &'me mut Elaborator<'e, 'c, 'out>, result_ty: Term<'out>) -> Self {
        let param_scope = elab.lctx.current;
        let num_params = elab.locals.len();
        let mut this = ElabDo {
            elab,
            param_scope,
            num_params,
            result_ty,
            jps: KVec::new(),
            jump_targets: Vec::new(),
            current_jp: JoinPoint::MAX,
            stmts: Vec::new(),
        };

        let entry = this.new_jp_with_locals(None);
        assert_eq!(entry, JoinPoint::ZERO);
        this.begin_jp(entry, true);

        return this;
    }

    fn new_jp(&mut self, locals: Vec<ScopeId>, arg_ty: Option<Term<'out>>) -> JoinPoint {
        let (ivar, ty) = self.new_term_var();
        self.jps.push(JoinPointData { 
            ivar,
            ty,
            locals,
            arg_ty,
            value: None,
            reachable: true,
        })
    }

    fn new_jp_with_locals(&mut self, arg_ty: Option<Term<'out>>) -> JoinPoint {
        let locals = &self.elab.locals[self.num_params..];
        let locals = Vec::from_iter(locals.copy_map_it(|l| l.id));
        self.new_jp(locals, arg_ty)
    }

    fn new_jp_with_locals_of(&mut self, jp: JoinPoint, arg_ty: Option<Term<'out>>) -> JoinPoint {
        let locals = self.jps[jp].locals.clone();
        self.new_jp(locals, arg_ty)
    }

    fn begin_jp(&mut self, jp: JoinPoint, reachable: bool) {
        assert_eq!(self.current_jp, JoinPoint::MAX);
        assert_eq!(self.stmts.len(), 0);

        self.jps[jp].reachable = reachable;

        // parameterize locals
        let locals = &mut self.jps[jp].locals;
        self.elab.lctx.current = self.param_scope;
        self.elab.locals.truncate(self.num_params + locals.len());
        for (i, id) in locals.iter_mut().enumerate() {
            let entry = self.elab.lctx.lookup(*id).clone();
            *id = self.elab.lctx.push(entry.name, entry.ty, ScopeKind::Binder(BinderKind::Explicit));

            let local = &mut self.elab.locals[self.num_params + i];
            assert_eq!(local.name, entry.name);
            local.id = *id;
        }

        self.current_jp = jp;
    }

    fn mk_jump(&self, jp: JoinPoint, value: Option<Term<'out>>) -> Term<'out> {
        let target = &self.jps[jp];
        assert!(target.arg_ty.is_some() == value.is_some());

        let locals = &self.locals[..self.num_params + target.locals.len()];
        let locals = Vec::from_iter(locals.copy_map_it(|local| self.alloc.mkt_local(local.id, TERM_SOURCE_NONE)));
        let result = self.alloc.mkt_apps(target.ivar, &locals, TERM_SOURCE_NONE);
        if let Some(value) = value {
            self.alloc.mkt_apply(result, value, TERM_SOURCE_NONE)
        }
        else { result }
    }

    fn end_jp(&mut self, ret: Term<'out>) -> bool {
        let entry = &mut self.jps[self.current_jp];
        assert!(entry.value.is_none());

        self.current_jp = JoinPoint::MAX;
        if !entry.reachable {
            self.stmts.clear();
            return false;
        }

        let mut value = ret;
        for stmt in self.stmts.copy_it().rev() {
            match stmt {
                Stmt::Local(id) => {
                    value = self.elab.mk_let(value, id, false, TERM_SOURCE_NONE);
                    self.elab.lctx.pop(id);
                }

                Stmt::Term((term, ty)) => {
                    value = self.elab.alloc.mkt_let(Atom::NULL, ty, term, value, TERM_SOURCE_NONE);
                }
            }
        }
        self.stmts.clear();

        for local in entry.locals.copy_it().rev() {
            value = self.elab.mk_binder(value, local, false, TERM_SOURCE_NONE);
        }
        for param in self.elab.locals[..self.num_params].copy_it().rev() {
            value = self.elab.mk_binder(value, param.id, false, TERM_SOURCE_NONE);
        }
        entry.value = Some(value);

        return true;
    }

    fn elab_do_block(&mut self, expr_id: ExprId, flags: ExprFlags, block: expr::Block, expected_ty: Option<Term<'out>>) -> (Term<'out>, Term<'out>) {
        let jump_target = (block.is_do && block.label != atoms::_hole.some() && flags.has_jump).then(|| {
            let expected = expected_ty.unwrap_or_else(|| self.new_ty_var().0);
            let jp = self.new_jp_with_locals(Some(expected));
            self.jump_targets.push(JumpTarget {
                label: block.label,
                break_jp: jp,
                break_ty: Some(expected),
                break_used: false,
                continue_jp: None.into(),
                else_jp:     None.into(),
            });
            jp
        });

        self.elab_do_stmts(block.stmts);

        if let Some(jp) = jump_target {
            let target = self.jump_targets.pop().unwrap();
            assert_eq!(target.break_jp, jp);

            let result_ty = target.break_ty.unwrap();

            let jump_val =
                if !self.jps[self.current_jp].reachable {
                    if let Some(ivar) = result_ty.try_ivar() {
                        if ivar.value(self).is_none() {
                            assert!(self.ensure_def_eq(result_ty, Term::UNIT));
                        }
                    }
                    self.mkt_ax_unreach(result_ty, TERM_SOURCE_NONE)
                }
                else if self.ensure_def_eq(result_ty, Term::UNIT) {
                    Term::UNIT_MK
                }
                else {
                    self.error(expr_id, ElabError::TempStr("block end reachable, but type not unit"));
                    self.mkt_ax_error(result_ty, TERM_SOURCE_NONE).0
                };

            let reachable = self.end_jp(self.mk_jump(jp, Some(jump_val)));

            self.begin_jp(jp, reachable || target.break_used);
            let result_id = self.lctx.push(Atom::NULL, result_ty, ScopeKind::Binder(BinderKind::Explicit));
            self.jps[jp].locals.push(result_id);

            return (self.alloc.mkt_local(result_id, TERM_SOURCE_NONE), result_ty);
        }
        else {
            if !self.jps[self.current_jp].reachable {
                if let Some(expected) = expected_ty {
                    return (self.mkt_ax_unreach(expected, TERM_SOURCE_NONE), expected);
                }
            }
            // type validated by caller.
            return (Term::UNIT_MK, Term::UNIT);
        }
    }

    fn elab_do_stmts(&mut self, stmts: &[StmtId]) {
        let old_num_locals = self.locals.len();

        for stmt_id in stmts.copy_it() {
            let stmt = self.parse.stmts[stmt_id];
            match stmt.kind {
                StmtKind::Error => (),

                StmtKind::Let(it) => {
                    let ty = if let Some(ty) = it.ty.to_option() {
                        let ty_expr = self.parse.exprs[ty];
                        if ty_expr.flags.has_loop || ty_expr.flags.has_jump || ty_expr.flags.has_assign {
                            // @todo: add local to prevent error cascade.
                            self.error(ty, ElabError::TempStr("type has loop/jump/assign"));
                            continue;
                        }
                        self.elab_expr_as_type(ty).0
                    }
                    else { self.new_ty_var().0 };

                    let val = if let Some(val) = it.val.to_option() {
                        self.elab_do_expr(val, Some(ty)).0
                    }
                    else {
                        self.mkt_ax_uninit(ty, TERM_SOURCE_NONE)
                    };


                    // create local.
                    let name = it.name.value.to_option().unwrap_or(Atom::NULL);
                    let id = self.lctx.push(name, ty, ScopeKind::Local(val));
                    self.locals.push(Local { name, id, mutable: it.is_var });

                    self.stmts.push(Stmt::Local(id));
                }

                StmtKind::Assign(lhs, rhs) => {
                    let lhs_expr = self.parse.exprs[lhs];
                    let ExprKind::Ident(ident) = lhs_expr.kind else {
                        self.error(lhs, ElabError::TempStr("invalid assign lhs"));
                        continue;
                    };

                    // find local.
                    let mut local = None;
                    for (index, l) in self.locals.copy_it().enumerate().rev() {
                        if l.name == ident.value {
                            local = Some((index, l.id, l.mutable));
                            break;
                        }
                    }
                    let Some((index, id, mutable)) = local else {
                        self.elab.error(ident.source, ElabError::UnresolvedName(
                            self.elab.alloc.alloc_str(&self.strings[ident.value])));
                        continue;
                    };

                    let ty = self.lctx.lookup(id).ty;
                    let (value, _) = self.elab_do_expr(rhs, Some(ty));

                    if !mutable {
                        self.elab.error(ident.source, ElabError::TempStr("variable not assignable"));
                    }
                    else {
                        // create new local.
                        let new_id = self.lctx.push(ident.value, ty, ScopeKind::Local(value));
                        self.locals[index].id = new_id;

                        self.stmts.push(Stmt::Local(new_id));
                    }
                }

                StmtKind::Expr(it) => {
                    let term = self.elab_do_expr(it, None);
                    self.stmts.push(Stmt::Term(term));
                }
            }
        }

        self.locals.truncate(old_num_locals);
    }

    fn elab_do_expr(&mut self, expr_id: ExprId, expected_ty: Option<Term<'out>>) -> (Term<'out>, Term<'out>) {
        let expr = self.parse.exprs[expr_id];

        // simple expr.
        let flags = expr.flags;
        if !flags.has_loop && !flags.has_jump && !flags.has_assign {
            return self.elab_expr_checking_type(expr_id, expected_ty);
        }

        let (term, ty) = self.elab_do_expr_core(expr_id, expected_ty);

        // @todo: dedup (validate_type)
        #[cfg(debug_assertions)]
        {
            let n = self.ivars.assignment_gen;
            let inferred = self.infer_type(term).unwrap();
            if !self.ensure_def_eq(ty, inferred) {
                eprintln!("---\nbug: elab_do_expr_core returned term\n{}\nwith type\n{}\nbut has type\n{}\n---",
                    self.pp(term, 80),
                    self.pp(ty, 80),
                    self.pp(inferred, 80));
                assert!(false);
            }
            assert_eq!(n, self.ivars.assignment_gen);
        }

        // ensure type.
        // @cleanup: dedup.
        if let Some(expected) = expected_ty {
            let source = expr_id.some();
            if !self.ensure_def_eq(ty, expected) {
                let expected = self.instantiate_term_vars(expected);
                let ty       = self.instantiate_term_vars(ty);
                let expected = self.reduce_ex(expected, false);
                let ty       = self.reduce_ex(ty, false);
                self.elab.error(expr_id, {
                    let mut pp = TermPP::new(self.env, &self.strings, &self.lctx, self.alloc);
                    let expected = pp.pp_term(expected);
                    let found    = pp.pp_term(ty);
                    ElabError::TypeMismatch { expected, found }
                });
                return self.elab.mkt_ax_error(expected, source);
            }
        }

        // expr info.
        debug_assert!(self.elab.elab.expr_infos[expr_id].is_none());
        self.elab.elab.expr_infos[expr_id] = Some(ExprInfo { term, ty });

        return (term, ty);
    }

    fn elab_do_expr_core(&mut self, expr_id: ExprId, expected_ty: Option<Term<'out>>) -> (Term<'out>, Term<'out>) {
        let source = expr_id.some();
        let expr = self.parse.exprs[expr_id];
        match expr.kind {
            ExprKind::Error => self.mkt_ax_error_from_expected(expected_ty, source),

            ExprKind::Let(_) => {
                self.error(expr_id, ElabError::TempStr("unimp do let"));
                self.mkt_ax_error_from_expected(expected_ty, source)
            }

            ExprKind::Parens(it) => {
                return self.elab_do_expr(it, expected_ty);
            }

            ExprKind::Ref(_) => {
                self.error(expr_id, ElabError::TempStr("unimp do ref"));
                self.mkt_ax_error_from_expected(expected_ty, source)
            }

            ExprKind::Deref(_) => {
                self.error(expr_id, ElabError::TempStr("unimp do deref"));
                self.mkt_ax_error_from_expected(expected_ty, source)
            }


            ExprKind::Op1(_) => {
                self.error(expr_id, ElabError::TempStr("unimp do op1"));
                self.mkt_ax_error_from_expected(expected_ty, source)
            }

            ExprKind::Op2(_) => {
                self.error(expr_id, ElabError::TempStr("unimp do op2"));
                self.mkt_ax_error_from_expected(expected_ty, source)
            }

            ExprKind::Field(_) => {
                self.error(expr_id, ElabError::TempStr("unimp do field"));
                self.mkt_ax_error_from_expected(expected_ty, source)
            }

            ExprKind::Index(_) => {
                self.error(expr_id, ElabError::TempStr("unimp do index"));
                self.mkt_ax_error_from_expected(expected_ty, source)
            }

            ExprKind::Call(_) => {
                self.error(expr_id, ElabError::TempStr("unimp do call"));
                self.mkt_ax_error_from_expected(expected_ty, source)
            }

            ExprKind::Do(it) => {
                self.elab_do_block(expr_id, expr.flags, it, expected_ty)
            }

            ExprKind::If(_) => {
                return self.elab_control_flow(expr_id, expected_ty);
            }

            ExprKind::While(_) => {
                return self.elab_control_flow(expr_id, expected_ty);
            }

            ExprKind::Loop(it) => {
                let body_jp = self.new_jp_with_locals(None);

                let after_jp = (it.is_do && it.label != atoms::_hole.some() && expr.flags.has_jump).then(|| {
                    let expected = expected_ty.unwrap_or_else(|| self.new_ty_var().0);
                    let jp = self.new_jp_with_locals(Some(expected));
                    self.jump_targets.push(JumpTarget {
                        label: it.label,
                        break_jp: jp,
                        break_ty: Some(expected),
                        break_used: false,
                        continue_jp: body_jp.some(),
                        else_jp:     None.into(),
                    });
                    jp
                });

                let body_reachable = self.end_jp(self.mk_jump(body_jp, None));
                self.begin_jp(body_jp, body_reachable);
                self.elab_do_stmts(it.stmts);
                self.end_jp(self.mk_jump(body_jp, None));

                if let Some(jp) = after_jp {
                    let target = self.jump_targets.pop().unwrap();
                    assert_eq!(target.break_jp, jp);

                    let result_ty = target.break_ty.unwrap();
                    if let Some(ivar) = result_ty.try_ivar() {
                        if ivar.value(self).is_none() {
                            assert!(self.ensure_def_eq(result_ty, Term::UNIT));
                        }
                    }

                    let after_reachable = body_reachable && target.break_used;
                    self.begin_jp(jp, after_reachable);

                    let result_id = self.lctx.push(Atom::NULL, result_ty, ScopeKind::Binder(BinderKind::Explicit));
                    self.jps[jp].locals.push(result_id);

                    return (self.alloc.mkt_local(result_id, source), result_ty);
                }
                else {
                    let jp_unreach = self.new_jp_with_locals(None);
                    self.begin_jp(jp_unreach, false);

                    let expected = expected_ty.unwrap_or(Term::UNIT);
                    return (self.mkt_ax_unreach(expected, source), expected);
                }
            }

            ExprKind::Break(it) => {
                if it.label == atoms::_hole.some() {
                    self.error(expr_id, ElabError::TempStr("invalid label"));
                }

                let mut target = self.jump_targets.last_mut();
                if it.label.is_some() {
                    target = None;
                    for t in self.jump_targets.iter_mut().rev() {
                        if t.label == it.label {
                            target = Some(t);
                        }
                    }
                }
                // @todo: this is currently unreachable.
                // if we decide that function blocks are `do` blocks,
                // this can become an unwrap.
                let Some(target) = target else {
                    if it.label != atoms::_hole.some() {
                        self.error(expr_id, ElabError::TempStr("no break target"));
                    }
                    return self.mkt_ax_error_from_expected(expected_ty, source);
                };
                target.break_used = true;
                let target = *target;

                if let Some(expected) = target.break_ty {
                    let value = if let Some(value) = it.value.to_option() {
                        self.elab_do_expr(value, Some(expected)).0
                    }
                    else {
                        if self.ensure_def_eq(expected, Term::UNIT) {
                            Term::UNIT_MK
                        }
                        else {
                            self.error(expr_id, ElabError::TempStr("break needs value"));
                            self.mkt_ax_error(expected, source).0
                        }
                    };

                    self.end_jp(self.mk_jump(target.break_jp, Some(value)));
                }
                else {
                    if let Some(value) = it.value.to_option() {
                        self.elab_do_expr(value, Some(Term::UNIT));
                    }

                    self.end_jp(self.mk_jump(target.break_jp, None));
                }

                let jp_unreach = self.new_jp_with_locals(None);
                self.begin_jp(jp_unreach, false);

                let expected = expected_ty.unwrap_or(Term::UNIT);
                (self.mkt_ax_unreach(expected, source), expected)
            }

            ExprKind::Continue(label) => {
                if label == atoms::_hole.some() {
                    self.error(expr_id, ElabError::TempStr("invalid label"));
                }

                for target in self.jump_targets.iter().rev() {
                    if label.is_some() && target.label != label { continue }

                    let Some(jp) = target.continue_jp.to_option() else { continue };
                    self.end_jp(self.mk_jump(jp, None));

                    let jp_unreach = self.new_jp_with_locals(None);
                    self.begin_jp(jp_unreach, false);

                    let expected = expected_ty.unwrap_or(Term::UNIT);
                    return (self.mkt_ax_unreach(expected, source), expected);
                }
                if label != atoms::_hole.some() {
                    self.error(expr_id, ElabError::TempStr("no continue target found"));
                }
                return self.mkt_ax_error_from_expected(expected_ty, source);
            }

            ExprKind::ContinueElse(label) => {
                if label == atoms::_hole.some() {
                    self.error(expr_id, ElabError::TempStr("invalid label"));
                }

                for target in self.jump_targets.iter().rev() {
                    if label.is_some() && target.label != label { continue }

                    let Some(jp) = target.else_jp else { continue };
                    if let Some(jp) = jp.to_option() {
                        self.end_jp(self.mk_jump(jp, None));

                        let jp_unreach = self.new_jp_with_locals(None);
                        self.begin_jp(jp_unreach, false);

                        let expected = expected_ty.unwrap_or(Term::UNIT);
                        return (self.mkt_ax_unreach(expected, source), expected);
                    }
                    else {
                        self.error(expr_id, ElabError::TempStr("do expr has no else"));
                        return self.mkt_ax_error_from_expected(expected_ty, source);
                    }
                }
                if label != atoms::_hole.some() {
                    self.error(expr_id, ElabError::TempStr("no continue else target found"));
                }
                return self.mkt_ax_error_from_expected(expected_ty, source);
            }

            ExprKind::Return(it) => {
                let expected = self.result_ty;

                let value = if let Some(value) = it.to_option() {
                    self.elab_do_expr(value, Some(expected)).0
                }
                else {
                    if !self.ensure_def_eq(expected, Term::UNIT) {
                        self.error(expr_id, ElabError::TempStr("return needs value"));
                    }
                    Term::UNIT_MK
                };
                self.end_jp(value);

                let jp_unreach = self.new_jp_with_locals(None);
                self.begin_jp(jp_unreach, false);

                let expected = expected_ty.unwrap_or(Term::UNIT);
                (self.mkt_ax_unreach(expected, source), expected)
            }

            ExprKind::TypeHint(_) => {
                self.error(expr_id, ElabError::TempStr("unimp do type hint"));
                self.mkt_ax_error_from_expected(expected_ty, source)
            }

            // error.
            ExprKind::Sort(_) |
            ExprKind::Forall(_) |
            ExprKind::Lambda(_) |
            ExprKind::Eq(_, _) => {
                self.error(expr_id, ElabError::TempStr("not supported in do"));
                self.mkt_ax_error_from_expected(expected_ty, source)
            }

            // expr flags are invalid.
            ExprKind::Hole |
            ExprKind::Ident(_) |
            ExprKind::DotIdent(_) |
            ExprKind::Path(_) |
            ExprKind::Levels(_) |
            ExprKind::Bool(_) |
            ExprKind::Number(_) |
            ExprKind::String(_) => unreachable!(),

            // @by_no_flags
            ExprKind::By(_) => unreachable!(),
        }
    }

    fn elab_control_flow(&mut self, expr_id: ExprId, expected_ty: Option<Term<'out>>) -> (Term<'out>, Term<'out>) {
        let needs_value = expected_ty.is_some();
        let after_jp = self.new_jp_with_locals(expected_ty);

        let mut all_then_unreachable = true;

        let mut curr = expr_id;
        loop {
            let source = curr.some();
            let expr = self.parse.exprs[curr];
            match expr.kind {
                ExprKind::If(it) => {
                    let (cond, _) = self.elab_do_expr(it.cond, Some(Term::BOOL));

                    let then_jp = self.new_jp_with_locals_of(after_jp, None);

                    let (else_jp, else_arg) = if it.els.is_some() {
                        let else_jp = self.new_jp_with_locals_of(after_jp, None);
                        (else_jp, None)
                    }
                    else {
                        if let Some(expected) = expected_ty {
                            let jump_val =
                                if self.ensure_def_eq(expected, Term::UNIT) {
                                    Term::UNIT_MK
                                }
                                else {
                                    self.error(curr, ElabError::TempStr("else is unit thing"));
                                    self.mkt_ax_error(expected, source).0
                                };
                            (after_jp, Some(jump_val))
                        }
                        else { (after_jp, None) }
                    };

                    let cond_reachable = self.end_jp(
                        self.alloc.mkt_apps(Term::ITE, &[
                            self.result_ty,
                            cond,
                            self.mk_jump(then_jp, None),
                            self.mk_jump(else_jp, else_arg),
                        ], source));

                    self.begin_jp(then_jp, cond_reachable);

                    if it.is_do && it.label != atoms::_hole.some() {
                        self.jump_targets.push(JumpTarget {
                            label: it.label,
                            break_jp: after_jp,
                            break_ty: expected_ty,
                            break_used: false,
                            continue_jp: None.into(),
                            else_jp: Some(if it.els.is_some() { else_jp.some() } else { None.into() }),
                        });
                    }

                    let (then_val, _) = self.elab_do_expr(it.then, expected_ty);
                    let then_reachable = self.end_jp(
                        self.mk_jump(after_jp, needs_value.then_some(then_val)));
                    if then_reachable {
                        all_then_unreachable = false;
                    }

                    if it.is_do {
                        let t = self.jump_targets.pop().unwrap();
                        assert_eq!(t.break_jp, after_jp);
                    }

                    self.begin_jp(else_jp, cond_reachable);

                    if let Some(els) = it.els.to_option() {
                        curr = els;
                    }
                    else { break }
                }

                ExprKind::While(it) => {
                    let head_jp = self.new_jp_with_locals_of(after_jp, None);
                    let body_jp = self.new_jp_with_locals_of(after_jp, None);

                    // dedup?
                    let (else_jp, else_arg) = if it.els.is_some() {
                        let else_jp = self.new_jp_with_locals_of(after_jp, None);
                        (else_jp, None)
                    }
                    else {
                        if let Some(expected) = expected_ty {
                            let jump_val =
                                if self.ensure_def_eq(expected, Term::UNIT) {
                                    Term::UNIT_MK
                                }
                                else {
                                    self.error(curr, ElabError::TempStr("else is unit thing"));
                                    self.mkt_ax_error(expected, source).0
                                };
                            (after_jp, Some(jump_val))
                        }
                        else { (after_jp, None) }
                    };


                    let head_reachable = self.end_jp(self.mk_jump(head_jp, None));

                    self.begin_jp(head_jp, head_reachable);
                    let (cond, _) = self.elab_do_expr(it.cond, Some(Term::BOOL));
                    let cond_reachable = self.end_jp(
                        self.alloc.mkt_apps(Term::ITE, &[
                            self.result_ty,
                            cond,
                            self.mk_jump(body_jp, None),
                            self.mk_jump(else_jp, else_arg),
                        ], source));

                    self.begin_jp(body_jp, cond_reachable);

                    if it.is_do && it.label != atoms::_hole.some() {
                        self.jump_targets.push(JumpTarget {
                            label: it.label,
                            break_jp: after_jp,
                            break_ty: expected_ty,
                            break_used: false,
                            continue_jp: head_jp.some(),
                            else_jp: Some(if it.els.is_some() { else_jp.some() } else { None.into() }),
                        });
                    }

                    self.elab_do_expr(it.body, None);
                    self.end_jp(self.mk_jump(head_jp, None));

                    if it.is_do {
                        let t = self.jump_targets.pop().unwrap();
                        assert_eq!(t.break_jp, after_jp);
                    }

                    self.begin_jp(else_jp, cond_reachable);

                    if let Some(els) = it.els.to_option() {
                        curr = els;
                    }
                    else { break }
                }

                // else.
                _ => {
                    let (els_val, _) = self.elab_do_expr(curr, expected_ty);
                    let els_reachable = self.end_jp(
                        self.mk_jump(after_jp, needs_value.then_some(els_val)));

                    self.begin_jp(after_jp, els_reachable || !all_then_unreachable);
                    break;
                }
            };
        }

        if let Some(result_ty) = expected_ty {
            let result_id = self.lctx.push(Atom::NULL, result_ty, ScopeKind::Binder(BinderKind::Explicit));
            self.jps[after_jp].locals.push(result_id);

            (self.alloc.mkt_local(result_id, expr_id.some()), result_ty)
        }
        else { (Term::UNIT_MK, Term::UNIT) }
    }
}

impl<'me, 'e, 'c, 'out> core::ops::Deref for ElabDo<'me, 'e, 'c, 'out> {
    type Target = Elaborator<'e, 'c, 'out>;
    #[inline(always)]
    fn deref(&self) -> &Self::Target { self.elab }
}

impl<'me, 'e, 'c, 'out> core::ops::DerefMut for ElabDo<'me, 'e, 'c, 'out> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut Self::Target { self.elab }
}


