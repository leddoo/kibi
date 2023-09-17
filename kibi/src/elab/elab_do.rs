use sti::traits::CopyIt;

use crate::ast::*;
use crate::tt::*;

use super::*;

impl<'me, 'c, 'out> Elaborator<'me, 'c, 'out> {
    pub fn elab_do(&mut self, expr_id: ExprId, flags: ExprFlags, block: expr::Block) -> Option<(Term<'out>, Term<'out>)> {
        if !flags.has_control_flow && !flags.has_assignments {
            // @todo: elab_let_chain.
            // chain also for regular let, so we can do the multi-abstract thing.
            self.error(expr_id, ElabError::TempUnimplemented);
            None
        }
        else {
            let mut state = State {
                locals: Vec::new(),
            };

            let old_scope = self.lctx.current;
            let old_locals = self.locals.len();

            self.elab_do_block(&mut state, block)?;

            // @temp
            while self.lctx.current != old_scope {
                self.lctx.pop(self.lctx.current.unwrap());
            }
            self.locals.truncate(old_locals);
            Some((Term::NAT_ZERO, Term::NAT))
        }
    }
}


struct State {
    locals: Vec<Local>,
}

struct Local {
    orig_id: ScopeId,
    index: usize,
}

impl<'me, 'c, 'out> Elaborator<'me, 'c, 'out> {
    fn elab_do_block(&mut self, state: &mut State, block: expr::Block) -> Option<()> {
        for stmt_id in block.stmts.copy_it() {
            let stmt = self.parse.stmts[stmt_id];
            match stmt.kind {
                StmtKind::Error => (),

                StmtKind::Let(it) => {
                    let ty = if let Some(ty) = it.ty.to_option() {
                        let ty_expr = self.parse.exprs[ty];
                        if ty_expr.flags.has_control_flow || ty_expr.flags.has_assignments {
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
                    state.locals.push(Local {
                        orig_id: id,
                        index: self.locals.len(),
                    });
                    self.locals.push((name, id));
                }

                StmtKind::Assign(lhs, rhs) => {
                    let lhs_expr = self.parse.exprs[lhs];
                    let ExprKind::Ident(ident) = lhs_expr.kind else {
                        self.error(lhs, ElabError::TempUnimplemented);
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
                }

                StmtKind::Expr(it) => {
                    if let Some(_) = self.elab_do_expr(state, it, None) {
                    }
                }
            }
        }

        Some(())
    }

    fn elab_do_expr(&mut self, state: &mut State, expr_id: ExprId, expected_ty: Option<Term<'out>>) -> Option<(Term<'out>, Term<'out>)> {
        let expr = self.parse.exprs[expr_id];

        if !expr.flags.has_control_flow && !expr.flags.has_assignments {
            return self.elab_expr_checking_type(expr_id, expected_ty);
        }

        Some(match expr.kind {
            ExprKind::Error => return None,

            ExprKind::Let(_) => {
                unimplemented!()
            }

            ExprKind::Parens(it) => {
                return self.elab_do_expr(state, it, expected_ty);
            }

            ExprKind::Ref(_) => {
                unimplemented!()
            }

            ExprKind::Deref(_) => {
                unimplemented!()
            }


            ExprKind::Op1(_) => unimplemented!(),

            ExprKind::Op2(_) => {
                unimplemented!()
            }

            ExprKind::Field(_) => unimplemented!(),
            ExprKind::Index(_) => unimplemented!(),

            ExprKind::Call(it) => {
                unimplemented!()
            }

            ExprKind::Do(it) => {
                self.elab_do_block(state, it)?;
                return None
            }

            ExprKind::If(_) => unimplemented!(),
            ExprKind::Loop(_) => unimplemented!(),

            ExprKind::TypeHint(_) => unimplemented!(),

            // error.
            ExprKind::Sort(_) |
            ExprKind::Forall(_) |
            ExprKind::Lambda(_) |
            ExprKind::Eq(_, _) => {
                unimplemented!()
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

