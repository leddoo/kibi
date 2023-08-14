use sti::growing_arena::GrowingArena;
use sti::vec::Vec;

use crate::ast::*;
use crate::tt::{self, Term, TermRef, LocalCtx, LocalId};


pub struct Elab<'a> {
    arena: &'a GrowingArena,
    alloc: tt::Alloc<'a>,

    lctx: LocalCtx<'a>,
    locals: Vec<(&'a str, LocalId)>,
}

impl<'a> Elab<'a> {
    #[inline(always)]
    pub fn new(arena: &'a GrowingArena) -> Self {
        let alloc = tt::Alloc::new(arena);
        Self {
            arena,
            alloc,
            lctx: LocalCtx::new(alloc),
            locals: Vec::new(),
        }
    }

    pub fn elab_level(&mut self, level: &Level<'a>) -> Option<tt::LevelRef<'a>> {
        Some(match &level.kind {
            LevelKind::Nat(n) => {
                self.alloc.mkl_nat(*n)
            }

            LevelKind::Add((l, offset)) => {
                let l = self.elab_level(l)?;
                l.offset(*offset, self.alloc)
            }

            LevelKind::Max((lhs, rhs)) => {
                let lhs = self.elab_level(lhs)?;
                let rhs = self.elab_level(rhs)?;
                self.alloc.mkl_max(lhs, rhs)
            }

            LevelKind::IMax((lhs, rhs)) => {
                let lhs = self.elab_level(lhs)?;
                let rhs = self.elab_level(rhs)?;
                self.alloc.mkl_imax(lhs, rhs)
            }

            LevelKind::Var(_) => todo!(),
        })
    }

    pub fn elab_term(&mut self, expr: &Expr<'a>) -> Option<TermRef<'a>> {
        Some(match &expr.kind {
            ExprKind::Ident(ident) => {
                match *ident {
                    "Nat" => Term::NAT,
                    "NatZero" => Term::NAT_ZERO,
                    "NatSucc" => Term::NAT_SUCC,
                    "NatRec" => unimplemented!(),

                    _ => {
                        for (name, id) in self.locals.iter().rev() {
                            if name == ident {
                                return Some(self.alloc.mkt_local(*id));
                            }
                        }
                        return None;
                    }
                }
            }

            ExprKind::Levels(it) => {
                match it.ident {
                    "NatRec" => {
                        if it.levels.len() != 1 {
                            return None;
                        }

                        let l = self.elab_level(&it.levels[0])?;
                        self.alloc.mkt_nat_rec(l)
                    }

                    _ => todo!(),
                }
            }

            ExprKind::Forall(it) => {
                unimplemented!()
            }

            ExprKind::Lambda(it) => {
                let save = self.lctx.save();
                let num_locals = self.locals.len();

                for param in it.binders.iter() {
                    let ty = self.elab_term(param.ty.as_ref()?)?;
                    let id = self.lctx.extend(ty, None);
                    let name = param.name.unwrap_or("");
                    self.locals.push((name, id));
                }

                let value = self.elab_term(it.value)?;

                let mut result = value;
                for i in (num_locals..self.locals.len()).rev() {
                    let (_, id) = self.locals[i];
                    result = self.lctx.abstracc_lambda(result, id);
                }
                self.lctx.restore(save);
                self.locals.truncate(num_locals);

                result
            }

            ExprKind::Call(it) => {
                let mut result = self.elab_term(it.func)?;

                for arg in it.args.iter() {
                    match arg {
                        expr::CallArg::Positional(arg) => {
                            let arg = self.elab_term(arg)?;
                            result = self.alloc.mkt_apply(result, arg);
                        }

                        expr::CallArg::Named(_) => todo!(),
                    }
                }

                result
            }

            ExprKind::Number(n) => {
                unimplemented!()
            }

            _ => return None,
        })
    }
}

