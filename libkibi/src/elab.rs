use sti::growing_arena::GrowingArena;
use sti::vec::Vec;

use crate::ast::{self, *};
use crate::tt::{self, *};


pub struct Elab<'a> {
    alloc: tt::Alloc<'a>,

    lctx: LocalCtx<'a>,
    locals: Vec<(&'a str, LocalId)>,
}

impl<'a> Elab<'a> {
    #[inline(always)]
    pub fn new(arena: &'a GrowingArena) -> Self {
        let alloc = tt::Alloc::new(arena);
        Self {
            alloc,
            lctx: LocalCtx::new(alloc),
            locals: Vec::new(),
        }
    }

    pub fn elab_level(&mut self, level: &ast::Level<'a>) -> Option<tt::LevelRef<'a>> {
        Some(match &level.kind {
            ast::LevelKind::Nat(n) => {
                self.alloc.mkl_nat(*n)
            }

            ast::LevelKind::Add((l, offset)) => {
                let l = self.elab_level(l)?;
                l.offset(*offset, self.alloc)
            }

            ast::LevelKind::Max((lhs, rhs)) => {
                let lhs = self.elab_level(lhs)?;
                let rhs = self.elab_level(rhs)?;
                self.alloc.mkl_max(lhs, rhs)
            }

            ast::LevelKind::IMax((lhs, rhs)) => {
                let lhs = self.elab_level(lhs)?;
                let rhs = self.elab_level(rhs)?;
                self.alloc.mkl_imax(lhs, rhs)
            }

            ast::LevelKind::Var(_) => todo!(),
        })
    }

    pub fn elab_expr(&mut self, expr: &Expr<'a>) -> Option<(TermRef<'a>, TermRef<'a>)> {
        self.elab_expr_ex(expr, None)
    }

    pub fn elab_expr_ex(&mut self, expr: &Expr<'a>, expected_ty: Option<TermRef<'a>>) -> Option<(TermRef<'a>, TermRef<'a>)> {
        Some(match &expr.kind {
            ExprKind::Ident(ident) => {
                match *ident {
                    "Nat"     => (Term::NAT, Term::SORT_1),
                    "NatZero" => (Term::NAT_ZERO, Term::NAT),
                    "NatSucc" => (Term::NAT_SUCC, Term::NAT_SUCC_TY),

                    "NatRec" => unimplemented!(),

                    _ => {
                        for (name, id) in self.locals.iter().rev() {
                            if name == ident {
                                let ty = self.lctx.lookup(*id).ty;
                                return Some((self.alloc.mkt_local(*id), ty));
                            }
                        }

                        println!("unknown ident {:?}", ident);
                        return None;
                    }
                }
            }

            ExprKind::Levels(it) => {
                match it.ident {
                    "NatRec" => {
                        if it.levels.len() != 1 {
                            println!("NatRec requires exactly one level");
                            return None;
                        }

                        let l = self.elab_level(&it.levels[0])?;
                        (self.alloc.mkt_nat_rec(l),
                         self.alloc.mkt_nat_rec_ty(l))
                    }

                    _ => todo!(),
                }
            }

            ExprKind::Forall(_) => {
                unimplemented!()
            }

            ExprKind::Lambda(it) => {
                let save = self.lctx.save();
                let num_locals = self.locals.len();

                for param in it.binders.iter() {
                    let (ty, _) = self.elab_expr_as_type(param.ty.as_ref()?)?;
                    let id = self.lctx.extend(ty, None);
                    let name = param.name.unwrap_or("");
                    self.locals.push((name, id));
                }

                let (mut result, mut result_ty) = self.elab_expr(it.value)?;

                for i in (num_locals..self.locals.len()).rev() {
                    let (_, id) = self.locals[i];
                    result    = self.lctx.abstract_lambda(result, id);
                    result_ty = self.lctx.abstract_forall(result_ty, id);
                }
                self.lctx.restore(save);
                self.locals.truncate(num_locals);

                (result, result_ty)
            }
            
            ExprKind::Parens(it) => {
                return self.elab_expr_ex(it, expected_ty);
            }

            ExprKind::Call(it) => {
                let (mut result, mut result_ty) = self.elab_expr(it.func)?;

                //println!("call {:#?}\n{:#?}\n{:#?}", expr, result, result_ty);

                for arg in it.args.iter() {
                    let expr::CallArg::Positional(arg) = arg else { unimplemented!() };

                    let TermKind::Forall(b) = result_ty.kind else { return None };

                    let (arg, _) = self.elab_expr_checking_type(arg, Some(b.ty))?;

                    result = self.alloc.mkt_apply(result, arg);
                    result_ty = b.val.instantiate(arg, self.alloc);
                }

                (result, result_ty)
            }

            ExprKind::Number(n) => {
                let n = u32::from_str_radix(n, 10).unwrap();
                (self.alloc.mkt_nat_val(n), Term::NAT)
            }

            _ => {
                println!("unsupported expr kind");
                return None
            }
        })
    }

    fn elab_expr_checking_type(&mut self, expr: &Expr<'a>, expected_ty: Option<TermRef<'a>>) -> Option<(TermRef<'a>, TermRef<'a>)> {
        let (term, ty) = self.elab_expr_ex(expr, expected_ty)?;

        if let Some(expected) = expected_ty {
            let mut tc = self.tc();
            if !tc.def_eq(ty, expected) {
                println!("type mismatch.\nexpected {:?}\ngot      {:?}\n", expected, ty);
                return None;
            }
        }

        Some((term, ty))
    }

    fn elab_expr_as_type(&mut self, expr: &Expr<'a>) -> Option<(TermRef<'a>, tt::LevelRef<'a>)> {
        let (term, ty) = self.elab_expr_ex(expr, None)?;

        let mut tc = self.tc();

        let ty = tc.whnf(ty);
        if let TermKind::Sort(l) = ty.kind {
            return Some((term, l));
        }

        println!("type expected");
        return None;
    }

    #[inline(always)]
    pub fn tc<'l>(&mut self) -> TyCtx<'a, '_> {
        TyCtx::new(self.alloc, &mut self.lctx)
    }
}

