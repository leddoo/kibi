use sti::traits::CopyIt;

use crate::ast::*;
use crate::tt::*;

use super::*;

impl<'me, 'c, 'out> Elaborator<'me, 'c, 'out> {
    pub fn elab_do(&mut self, expr_id: ExprId, flags: ExprFlags, block: expr::Block) -> Option<(Term<'out>, Term<'out>)> {
        let may_need_joins = flags.has_loop || (flags.has_if && flags.has_assign);
        if !may_need_joins {
            // @todo: elab_let_chain.
            // chain also for regular let, so we can do the multi-abstract thing.
            self.error(expr_id, ElabError::TempStr("unimp do without joins"));
            None
        }
        else {
            let mut state = State::new(self);

            let old_scope = self.lctx.current;
            let old_locals = self.locals.len();

            self.elab_do_block(&mut state, block)?;

            state.terminate_jp(Term::UNIT_MK, self);

            //assert_eq!(self.lctx.current, old_scope);
            if self.lctx.current != old_scope {
                eprintln!("bug: elab_do messed up the lctx.");
                self.lctx.current = old_scope;
            }
            self.locals.truncate(old_locals);

            Some((Term::UNIT_MK, Term::UNIT))
        }
    }
}


sti::define_key!(u32, JoinPoint);

struct State<'out> {
    jps: KVec<JoinPoint, (SymbolId, Option<Term<'out>>)>,
    current_jp: JoinPoint,
    stmts: Vec<Stmt<'out>>,
}

#[derive(Clone, Copy)]
enum Stmt<'out> {
    Local(ScopeId),
    Term((Term<'out>, Term<'out>)),
}

impl<'out> State<'out> {
    fn new(elab: &mut Elaborator) -> Self {
        let mut this = State {
            jps: KVec::new(),
            current_jp: JoinPoint::ZERO,
            stmts: Vec::new(),
        };

        let (entry_jp, _) = this.new_jp(elab);
        assert_eq!(entry_jp, this.current_jp);

        return this;
    }

    fn new_jp(&mut self, elab: &mut Elaborator) -> (JoinPoint, SymbolId) {
        // @temp: temp alloc, symbols under current symbol.
        let n = elab.env.symbol(SymbolId::ROOT).children.len();
        let name = elab.strings.insert(&sti::format!("$jp_{}", n));
        let symbol = elab.env.new_symbol(SymbolId::ROOT, name, SymbolKind::Pending).unwrap();
        (self.jps.push((symbol, None)), symbol)
    }

    #[inline]
    fn set_jp(&mut self, jp: JoinPoint) {
        self.current_jp = jp;
    }

    fn terminate_jp(&mut self, ret: Term<'out>, elab: &mut Elaborator<'_, '_, 'out>) {
        let mut result = ret;
        for stmt in self.stmts.copy_it().rev() {
            match stmt {
                Stmt::Local(id) => {
                    result = elab.mk_let(result, id, false);
                    elab.lctx.pop(id);
                }

                Stmt::Term((term, ty)) => {
                    result = elab.alloc.mkt_let(Atom::NULL, ty, term, result);
                }
            }
        }
        self.stmts.clear();

        println!("\nterminated {:?} {:?}: {}\n", self.current_jp, self.jps[self.current_jp].0, elab.pp(result, 80));

        let entry = &mut self.jps[self.current_jp];
        assert!(entry.1.is_none());
        entry.1 = Some(result);
    }
}

impl<'me, 'c, 'out> Elaborator<'me, 'c, 'out> {
    fn elab_do_block(&mut self, state: &mut State<'out>, block: expr::Block) -> Option<()> {
        for stmt_id in block.stmts.copy_it() {
            let stmt = self.parse.stmts[stmt_id];
            match stmt.kind {
                StmtKind::Error => (),

                StmtKind::Let(it) => {
                    let ty = if let Some(ty) = it.ty.to_option() {
                        let ty_expr = self.parse.exprs[ty];
                        if ty_expr.flags.has_loop || ty_expr.flags.has_assign {
                            self.error(ty, ElabError::TempTBD);
                            return None;
                        }
                        self.elab_expr_as_type(ty)?.0
                    }
                    else { self.new_ty_var().0 };

                    let val = if let Some(val) = it.val.to_option() {
                        self.elab_expr_checking_type(val, Some(ty))?.0
                    }
                    // @todo: uninit axiom.
                    else { unimplemented!() };


                    // create local.
                    let name = it.name.value.to_option().unwrap_or(Atom::NULL);
                    let id = self.lctx.push(BinderKind::Explicit, name, ty, Some(val));
                    self.locals.push((name, id));

                    state.stmts.push(Stmt::Local(id));
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
                        self.error(ident.source, ElabError::UnresolvedName(
                            self.alloc.alloc_str(&self.strings[ident.value])));
                        continue;
                    };

                    let ty = self.lctx.lookup(id).ty;
                    let Some((value, _)) = self.elab_do_expr(state, rhs, Some(ty)) else { continue };

                    // create new local.
                    let new_id = self.lctx.push(BinderKind::Explicit, ident.value, ty, Some(value));
                    self.locals[index].1 = new_id;

                    state.stmts.push(Stmt::Local(new_id));
                }

                StmtKind::Expr(it) => {
                    if let Some(term) = self.elab_do_expr(state, it, None) {
                        state.stmts.push(Stmt::Term(term));
                    }
                }
            }
        }

        Some(())
    }

    fn elab_do_expr(&mut self, state: &mut State<'out>, expr_id: ExprId, expected_ty: Option<Term<'out>>) -> Option<(Term<'out>, Term<'out>)> {
        let expr = self.parse.exprs[expr_id];

        // simple expr.
        let flags = expr.flags;
        if !flags.has_loop && !flags.has_assign {
            return self.elab_expr_checking_type(expr_id, expected_ty);
        }

        let result = self.elab_do_expr_core(state, expr_id, expected_ty);

        // @todo: dedup (validate_type)
        #[cfg(debug_assertions)]
        if let Some((term, ty)) = result {
            let n = self.ivars.assignment_gen;
            let inferred = self.infer_type(term).unwrap();
            if !self.ensure_def_eq(ty, inferred) {
                eprintln!("---\nbug: elab_expr_core returned term\n{}\nwith type\n{}\nbut has type\n{}\n---",
                    self.pp(term, 80),
                    self.pp(ty, 80),
                    self.pp(inferred, 80));
                assert!(false);
            }
            assert_eq!(n, self.ivars.assignment_gen);
        }

        if let Some((term, ty)) = result {
            debug_assert!(self.elab.expr_infos[expr_id].is_none());
            self.elab.expr_infos[expr_id] = Some(ExprInfo { term, ty });
        }

        return result;
    }

    fn elab_do_expr_core(&mut self, state: &mut State<'out>, expr_id: ExprId, expected_ty: Option<Term<'out>>) -> Option<(Term<'out>, Term<'out>)> {
        let expr = self.parse.exprs[expr_id];
        Some(match expr.kind {
            ExprKind::Error => return None,

            ExprKind::Let(_) => {
                self.error(expr_id, ElabError::TempStr("unimp do let"));
                return None;
            }

            ExprKind::Parens(it) => {
                return self.elab_do_expr(state, it, expected_ty);
            }

            ExprKind::Ref(_) => {
                self.error(expr_id, ElabError::TempStr("unimp do ref"));
                return None;
            }

            ExprKind::Deref(_) => {
                self.error(expr_id, ElabError::TempStr("unimp do deref"));
                return None;
            }


            ExprKind::Op1(_) => {
                self.error(expr_id, ElabError::TempStr("unimp do op1"));
                return None;
            }

            ExprKind::Op2(_) => {
                self.error(expr_id, ElabError::TempStr("unimp do op2"));
                return None;
            }

            ExprKind::Field(_) => {
                self.error(expr_id, ElabError::TempStr("unimp do field"));
                return None;
            }

            ExprKind::Index(_) => {
                self.error(expr_id, ElabError::TempStr("unimp do index"));
                return None;
            }

            ExprKind::Call(_) => {
                self.error(expr_id, ElabError::TempStr("unimp do call"));
                return None;
            }

            ExprKind::Do(it) => {
                self.elab_do_block(state, it)?;
                (Term::UNIT_MK, Term::UNIT)
            }

            ExprKind::If(it) => {
                let (cond, _) = self.elab_do_expr(state, it.cond, Some(Term::BOOL))?;

                let locals = self.locals.clone();
                let local_terms = Vec::from_iter(self.locals.copy_map_it(|(_, local)| self.alloc.mkt_local(local)));

                let (then_jp, then_id) = state.new_jp(self);
                let (else_jp, else_id) = state.new_jp(self);
                let (after_jp, after_id) = state.new_jp(self);
                let then_app = self.alloc.mkt_apps(self.alloc.mkt_global(then_id, &[]), &local_terms);
                let else_app = self.alloc.mkt_apps(self.alloc.mkt_global(else_id, &[]), &local_terms);
                let ite = self.alloc.mkt_apps(Term::ITE, &[Term::UNIT, cond, then_app, else_app]);
                state.terminate_jp(ite, self);

                let after = self.alloc.mkt_global(after_id, &[]);

                // everything is now a param, so we don't have access to the values anymore.
                // todo: we may not want that for `if`.
                for (_, local) in self.locals.copy_it() {
                    self.lctx.lookup_mut(local).value = None;
                }
                let old_scope = self.lctx.current;

                state.set_jp(then_jp);
                let (then_val, result_ty) = self.elab_do_expr(state, it.then, None)?;
                let then_after =
                    self.alloc.mkt_apply(
                        self.alloc.mkt_apps(after,
                            &Vec::from_iter(self.locals.copy_map_it(|(_, local)| self.alloc.mkt_local(local)))),
                        then_val);
                state.terminate_jp(then_after, self);

                self.locals.clear();
                self.locals.extend_from_slice(&locals);
                self.lctx.current = old_scope;
                state.set_jp(else_jp);
                let else_val = if let Some(els) = it.els.to_option() {
                    let (else_val, _) = self.elab_do_expr(state, els, Some(result_ty))?;
                    else_val
                }
                else {
                    if !self.ensure_def_eq(result_ty, Term::UNIT) {
                        // @todo: type mismatch or special error.
                        self.error(expr_id, ElabError::TempArgFailed);
                        return None;
                    }
                    Term::UNIT_MK
                };
                let else_after =
                    self.alloc.mkt_apply(
                        self.alloc.mkt_apps(after,
                            &Vec::from_iter(self.locals.copy_map_it(|(_, local)| self.alloc.mkt_local(local)))),
                        else_val);
                state.terminate_jp(else_after, self);

                self.locals.clear();
                self.locals.extend_from_slice(&locals);
                self.lctx.current = old_scope;
                let result_id = self.lctx.push(BinderKind::Explicit, Atom::NULL, result_ty, None);
                self.locals.push((Atom::NULL, result_id));
                state.set_jp(after_jp);

                (self.alloc.mkt_local(result_id), result_ty)
            }

            ExprKind::Loop(_) => {
                self.error(expr_id, ElabError::TempStr("unimp do loop"));
                return None;
            }

            ExprKind::TypeHint(_) => {
                self.error(expr_id, ElabError::TempStr("unimp do type hint"));
                return None;
            }

            // error.
            ExprKind::Sort(_) |
            ExprKind::Forall(_) |
            ExprKind::Lambda(_) |
            ExprKind::Eq(_, _) => {
                self.error(expr_id, ElabError::TempStr("not supported in do"));
                return None;
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
        })
    }
}

