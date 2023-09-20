use sti::traits::CopyIt;

use crate::ast::*;
use crate::tt::*;

use super::*;

impl<'me, 'c, 'out> Elaborator<'me, 'c, 'out> {
    pub fn elab_do(&mut self, expr_id: ExprId, flags: ExprFlags, block: expr::Block, expected_ty: Option<Term<'out>>)
        -> (Term<'out>, Term<'out>)
    {
        let may_need_joins = flags.has_loop || flags.has_jump || (flags.has_if && flags.has_assign);
        if !may_need_joins {
            if block.stmts.len() == 0 {
                return (Term::UNIT_MK, Term::UNIT);
            }
            // @todo: maybe not cause `if ... then foo else bar`.
            // then a "not is do" block would just be a `do`
            // with a transparent label.
            else if !block.is_do && block.stmts.len() == 1 {
                let stmt = block.stmts[0];
                if let StmtKind::Expr(it) = self.parse.stmts[stmt].kind {
                    // @todo: expected type.
                    return self.elab_expr(it);
                }
            }

            // @todo: elab_let_chain.
            // chain also for regular let, so we can do the multi-abstract thing.
            self.error(expr_id, ElabError::TempStr("unimp do without joins"));
            self.mkt_ax_error_from_expected(expected_ty)
        }
        else {
            println!("---\n");

            let old_scope = self.lctx.current;
            let old_locals = self.locals.clone();

            let result_ty = expected_ty.unwrap_or_else(|| self.new_term_var().0);

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
                return self.mkt_ax_error_from_expected(expected_ty);
            }
            this.end_jp(ret);

            self.lctx.current = old_scope;
            // @cleanup: sti vec assign/_from_slice.
            self.locals.clear();
            self.locals.extend_from_slice(&old_locals);

            return self.mkt_ax_error_from_expected(expected_ty);

            /*
            for jp in this.jps.range() {
                let jp = &mut this.jps[jp];
                if !jp.reachable {
                    continue;
                }

                // @temp: item_symbol::jp{n}.
                let n = this.elab.env.symbol(SymbolId::ROOT).children.len();
                let name = this.elab.strings.insert(&format!("__jp_{n}"));
                let symbol_id = this.elab.env.new_symbol(SymbolId::ROOT, name, SymbolKind::Pending).unwrap();
                let symbol = this.elab.alloc.mkt_global(symbol_id, &[]); // @temp: levels.
                let ok = this.elab.ensure_def_eq(jp.symbol, symbol);
                assert!(ok);

                jp.symbol_id = symbol_id.some();
            }

            for jp in this.jps.range() {
                let jp = &this.jps[jp];
                if !jp.reachable {
                    continue;
                }

                let (term, ty) = jp.term.unwrap();

                let term = this.elab.instantiate_term_vars(term);
                let ty   = this.elab.instantiate_term_vars(ty);
                if term.has_ivars() || ty.has_ivars() {
                    this.elab.error(expr_id, ElabError::TempStr("jp has ivars"));
                    return self.mkt_ax_error_from_expected(expected_ty);
                }

                this.elab.env.resolve_pending(jp.symbol_id.unwrap(),
                    SymbolKind::Def(symbol::Def {
                        val: Some(term),
                        ty,
                        num_levels: 0, // @temp: jp levels.
                    }));
            }

            //let entry = &this.jps[entry];
            //let entry = entry.symbol;

            self.lctx.current = old_scope;
            // @cleanup: sti vec assign/_from_slice.
            self.locals.clear();
            self.locals.extend_from_slice(&old_locals);

            let local_terms = Vec::from_iter(self.locals.copy_map_it(|(_, local)| self.alloc.mkt_local(local)));
            //let result = self.alloc.mkt_apps(entry, &local_terms);
            //return (result, result_ty);
            unimplemented!()
            */
        }
    }
}


sti::define_key!(u32, JoinPoint, opt: OptJoinPoint);

struct ElabDo<'me, 'e, 'c, 'out> {
    elab: &'me mut Elaborator<'e, 'c, 'out>,

    jps: KVec<JoinPoint, JoinPointData<'out>>,
    result_ty: Term<'out>,

    jump_targets: Vec<JumpTarget<'out>>,

    current_jp: JoinPoint,
    stmts: Vec<Stmt<'out>>,
}

#[derive(Clone, Copy)]
struct JumpTarget<'a> {
    jp: JoinPoint,
    result_ty: Option<Term<'a>>,
}

struct JoinPointData<'a> {
    symbol_id: OptSymbolId,
    symbol: Term<'a>,
    params: Vec<ScopeId>,
    needs_value: bool,
    term: Option<(Term<'a>, Term<'a>)>,
    reachable: bool,
}

#[derive(Clone, Copy)]
enum Stmt<'out> {
    Local(ScopeId),
    Term((Term<'out>, Term<'out>)),
}

impl<'me, 'e, 'c, 'out> ElabDo<'me, 'e, 'c, 'out> {
    fn new(elab: &'me mut Elaborator<'e, 'c, 'out>, result_ty: Term<'out>) -> Self {
        let mut this = ElabDo {
            elab,
            jps: KVec::new(),
            jump_targets: Vec::new(),
            result_ty,
            current_jp: JoinPoint::ZERO,
            stmts: Vec::new(),
        };

        let entry = this.new_jp_with_locals(false);
        assert_eq!(entry, JoinPoint::ZERO);
        this.begin_jp(entry, true);

        return this;
    }

    fn new_jp_with_locals(&mut self, needs_value: bool) -> JoinPoint {
        let params = Vec::from_iter(self.locals.copy_map_it(|(_, id)| id));
        let symbol = self.new_term_var().0;
        self.jps.push(JoinPointData { 
            symbol_id: None.into(),
            symbol,
            params, needs_value,
            term: None,
            reachable: true,
        })
    }

    fn new_jp_with_params_of(&mut self, jp: JoinPoint, needs_value: bool) -> JoinPoint {
        let params = self.jps[jp].params.clone();
        let symbol = self.new_term_var().0;
        self.jps.push(JoinPointData { 
            symbol_id: None.into(),
            symbol,
            params, needs_value,
            term: None,
            reachable: true,
        })
    }

    fn begin_jp(&mut self, jp: JoinPoint, reachable: bool) {
        assert!(jp == JoinPoint::ZERO || self.jps[self.current_jp].term.is_some());
        assert_eq!(self.stmts.len(), 0);

        self.jps[jp].reachable = reachable;

        // parameterize locals
        self.elab.lctx.current = None.into();
        self.elab.locals.clear();
        for id in &mut self.jps[jp].params {
            let entry = self.elab.lctx.lookup(*id).clone();
            *id = self.elab.lctx.push(entry.binder_kind, entry.name, entry.ty, None);
            self.elab.locals.push((entry.name, *id));
        }

        self.current_jp = jp;
    }

    fn mk_jump(&self, jp: JoinPoint, value: Option<Term<'out>>) -> Term<'out> {
        let target = &self.jps[jp];
        assert!(target.needs_value == value.is_some());

        let locals = &self.locals[..target.params.len()];
        let locals = Vec::from_iter(locals.copy_map_it(|(_, local)| self.alloc.mkt_local(local)));
        let result = self.alloc.mkt_apps(target.symbol, &locals);
        if let Some(value) = value {
            self.alloc.mkt_apply(result, value)
        }
        else { result }
    }

    fn end_jp(&mut self, ret: Term<'out>) -> bool {
        let entry = &mut self.jps[self.current_jp];
        assert!(entry.term.is_none());

        let mut result    = ret;
        let mut result_ty = self.result_ty;
        for stmt in self.stmts.copy_it().rev() {
            match stmt {
                Stmt::Local(id) => {
                    result    = self.elab.mk_let(result,    id, false);
                    result_ty = self.elab.mk_let(result_ty, id, true);
                    self.elab.lctx.pop(id);
                }

                Stmt::Term((term, ty)) => {
                    result = self.elab.alloc.mkt_let(Atom::NULL, ty, term, result);
                }
            }
        }
        self.stmts.clear();

        for local in entry.params.copy_it().rev() {
            result    = self.elab.mk_binder(result,    local, false);
            result_ty = self.elab.mk_binder(result_ty, local, true);
        }
        entry.term = Some((result, result_ty));

        println!("{:?}:\n{}\n", self.current_jp, self.elab.pp(result, 50));
        return entry.reachable;
    }

    fn elab_do_block(&mut self, expr_id: ExprId, flags: ExprFlags, block: expr::Block, expected_ty: Option<Term<'out>>) -> (Term<'out>, Term<'out>) {
        let old_num_locals = self.locals.len();

        let jump_target = (block.is_do && flags.has_jump).then(|| {
            let jp = self.new_jp_with_locals(expected_ty.is_some());
            self.jump_targets.push(JumpTarget {
                jp,
                result_ty: expected_ty,
            });
            jp
        });

        for stmt_id in block.stmts.copy_it() {
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
                        self.mkt_ax_uninit(ty)
                    };


                    // create local.
                    let name = it.name.value.to_option().unwrap_or(Atom::NULL);
                    let id = self.lctx.push(BinderKind::Explicit, name, ty, Some(val));
                    self.locals.push((name, id));

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
                    for (index, (name, id)) in self.locals.copy_it().enumerate().rev() {
                        if name == ident.value {
                            local = Some((index, id));
                            break;
                        }
                    }
                    let Some((index, id)) = local else {
                        self.elab.error(ident.source, ElabError::UnresolvedName(
                            self.elab.alloc.alloc_str(&self.strings[ident.value])));
                        continue;
                    };

                    let ty = self.lctx.lookup(id).ty;
                    let (value, _) = self.elab_do_expr(rhs, Some(ty));

                    // create new local.
                    let new_id = self.lctx.push(BinderKind::Explicit, ident.value, ty, Some(value));
                    self.locals[index].1 = new_id;

                    self.stmts.push(Stmt::Local(new_id));
                }

                StmtKind::Expr(it) => {
                    let term = self.elab_do_expr(it, None);
                    self.stmts.push(Stmt::Term(term));
                }
            }
        }

        self.locals.truncate(old_num_locals);

        if let Some(jp) = jump_target {
            let target = self.jump_targets.pop().unwrap();
            assert_eq!(target.jp, jp);

            let result_ty = target.result_ty.unwrap_or(Term::UNIT);

            let jump_val =
                if let Some(result_ty) = target.result_ty {
                    if !self.jps[self.current_jp].reachable {
                        Some(self.mkt_ax_unreach(result_ty))
                    }
                    else if self.ensure_def_eq(result_ty, Term::UNIT) {
                        Some(Term::UNIT_MK)
                    }
                    else {
                        self.error(expr_id, ElabError::TempStr("block is unit, but unit is no good"));
                        Some(self.mkt_ax_error(result_ty).0)
                    }
                }
                else { None };

            let reachable = self.end_jp(self.mk_jump(jp, jump_val));

            self.begin_jp(jp, reachable);
            let result_id = self.lctx.push(BinderKind::Explicit, Atom::NULL, result_ty, None);
            self.jps[jp].params.push(result_id);

            return (self.alloc.mkt_local(result_id), result_ty);
        }
        else {
            // type validated by caller.
            return (Term::UNIT_MK, Term::UNIT);
        }
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
                return self.elab.mkt_ax_error(expected);
            }
        }

        // expr info.
        debug_assert!(self.elab.elab.expr_infos[expr_id].is_none());
        self.elab.elab.expr_infos[expr_id] = Some(ExprInfo { term, ty });

        return (term, ty);
    }

    fn elab_do_expr_core(&mut self, expr_id: ExprId, expected_ty: Option<Term<'out>>) -> (Term<'out>, Term<'out>) {
        let expr = self.parse.exprs[expr_id];
        match expr.kind {
            ExprKind::Error => self.mkt_ax_error_from_expected(expected_ty),

            ExprKind::Let(_) => {
                self.error(expr_id, ElabError::TempStr("unimp do let"));
                self.mkt_ax_error_from_expected(expected_ty)
            }

            ExprKind::Parens(it) => {
                return self.elab_do_expr(it, expected_ty);
            }

            ExprKind::Ref(_) => {
                self.error(expr_id, ElabError::TempStr("unimp do ref"));
                self.mkt_ax_error_from_expected(expected_ty)
            }

            ExprKind::Deref(_) => {
                self.error(expr_id, ElabError::TempStr("unimp do deref"));
                self.mkt_ax_error_from_expected(expected_ty)
            }


            ExprKind::Op1(_) => {
                self.error(expr_id, ElabError::TempStr("unimp do op1"));
                self.mkt_ax_error_from_expected(expected_ty)
            }

            ExprKind::Op2(_) => {
                self.error(expr_id, ElabError::TempStr("unimp do op2"));
                self.mkt_ax_error_from_expected(expected_ty)
            }

            ExprKind::Field(_) => {
                self.error(expr_id, ElabError::TempStr("unimp do field"));
                self.mkt_ax_error_from_expected(expected_ty)
            }

            ExprKind::Index(_) => {
                self.error(expr_id, ElabError::TempStr("unimp do index"));
                self.mkt_ax_error_from_expected(expected_ty)
            }

            ExprKind::Call(_) => {
                self.error(expr_id, ElabError::TempStr("unimp do call"));
                self.mkt_ax_error_from_expected(expected_ty)
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

            ExprKind::Loop(_) => {
                self.error(expr_id, ElabError::TempStr("unimp do loop"));
                self.mkt_ax_error_from_expected(expected_ty)
            }

            ExprKind::Break(it) => {
                // @todo: this is currently unreachable.
                // if we decide that function blocks are `do` blocks,
                // this can become an unwrap.
                let Some(target) = self.jump_targets.last().copied() else {
                    self.error(expr_id, ElabError::TempStr("no break target"));
                    return self.mkt_ax_error_from_expected(expected_ty);
                };

                if let Some(expected) = target.result_ty {
                    let value = if let Some(value) = it.value.to_option() {
                        self.elab_do_expr(value, Some(expected)).0
                    }
                    else {
                        if self.ensure_def_eq(expected, Term::UNIT) {
                            Term::UNIT_MK
                        }
                        else {
                            self.error(expr_id, ElabError::TempStr("break needs value"));
                            self.mkt_ax_error(expected).0
                        }
                    };

                    self.end_jp(self.mk_jump(target.jp, Some(value)));
                }
                else {
                    if let Some(value) = it.value.to_option() {
                        self.elab_do_expr(value, Some(Term::UNIT));
                    }

                    self.end_jp(self.mk_jump(target.jp, None));
                }

                let jp_unreach = self.new_jp_with_locals(false);
                self.begin_jp(jp_unreach, false);

                let expected = expected_ty.unwrap_or(Term::UNIT);
                (self.mkt_ax_unreach(expected), expected)
            }

            ExprKind::Continue(_) => {
                self.error(expr_id, ElabError::TempStr("unimp do continue"));
                self.mkt_ax_error_from_expected(expected_ty)
            }

            ExprKind::ContinueElse(_) => {
                self.error(expr_id, ElabError::TempStr("unimp do continue else"));
                self.mkt_ax_error_from_expected(expected_ty)
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

                let jp_unreach = self.new_jp_with_locals(false);
                self.begin_jp(jp_unreach, false);

                let expected = expected_ty.unwrap_or(Term::UNIT);
                (self.mkt_ax_unreach(expected), expected)
            }

            ExprKind::TypeHint(_) => {
                self.error(expr_id, ElabError::TempStr("unimp do type hint"));
                self.mkt_ax_error_from_expected(expected_ty)
            }

            // error.
            ExprKind::Sort(_) |
            ExprKind::Forall(_) |
            ExprKind::Lambda(_) |
            ExprKind::Eq(_, _) => {
                self.error(expr_id, ElabError::TempStr("not supported in do"));
                self.mkt_ax_error_from_expected(expected_ty)
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
        }
    }

    fn elab_control_flow(&mut self, expr_id: ExprId, expected_ty: Option<Term<'out>>) -> (Term<'out>, Term<'out>) {
        let expected = expected_ty.unwrap_or(Term::UNIT);

        let needs_value = expected_ty.is_some();
        let after_jp = self.new_jp_with_locals(needs_value);

        let mut all_then_unreachable = true;

        let mut curr = expr_id;
        loop {
            let expr = self.parse.exprs[curr];
            match expr.kind {
                ExprKind::If(it) => {
                    let (cond, _) = self.elab_do_expr(it.cond, Some(Term::BOOL));

                    let then_jp = self.new_jp_with_params_of(after_jp, false);

                    let (else_jp, else_arg) = if it.els.is_some() {
                        let else_jp = self.new_jp_with_params_of(after_jp, false);
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
                                    self.mkt_ax_error(expected).0
                                };
                            (after_jp, Some(jump_val))
                        }
                        else { (after_jp, None) }
                    };

                    let cond_reachable = self.end_jp(
                        self.alloc.mkt_apps(Term::ITE, &[
                            expected,
                            cond,
                            self.mk_jump(then_jp, None),
                            self.mk_jump(else_jp, else_arg)]));

                    self.begin_jp(then_jp, cond_reachable);

                    let (then_val, _) = self.elab_do_expr(it.then, expected_ty);
                    let then_reachable = self.end_jp(
                        self.mk_jump(after_jp, needs_value.then_some(then_val)));
                    if then_reachable {
                        all_then_unreachable = false;
                    }

                    self.begin_jp(else_jp, cond_reachable);

                    if let Some(els) = it.els.to_option() {
                        curr = els;
                    }
                    else { break }
                }

                ExprKind::While(_) => {
                    unimplemented!()
                }

                // else.
                _ => {
                    let (els_val, _) = self.elab_do_expr(curr, expected_ty);
                    let els_reachable = self.end_jp(
                        self.mk_jump(after_jp, needs_value.then_some(els_val)));

                    self.begin_jp(after_jp, !els_reachable && all_then_unreachable);
                    break;
                }
            };
        }

        if let Some(result_ty) = expected_ty {
            let result_id = self.lctx.push(BinderKind::Explicit, Atom::NULL, result_ty, None);
            self.jps[after_jp].params.push(result_id);

            (self.alloc.mkt_local(result_id), result_ty)
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


