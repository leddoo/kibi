use sti::growing_arena::GrowingArena;
use sti::vec::Vec;

use crate::ast::{self, *};
use crate::tt::{self, *};
use crate::env::*;


pub struct Elab<'a, 'e> {
    alloc: tt::Alloc<'a>,

    env: &'e mut Env<'a>,
    ns: NamespaceId,

    lctx: LocalCtx<'a>,
    locals: Vec<(&'a str, LocalId)>,
}

impl<'a, 'e> Elab<'a, 'e> {
    #[inline(always)]
    pub fn new(env: &'e mut Env<'a>, ns: NamespaceId, arena: &'a GrowingArena) -> Self {
        let alloc = tt::Alloc::new(arena);
        Self {
            alloc,
            env,
            ns,
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
            ExprKind::Ident(name) => {
                if let Some(local) = self.lookup_local(name) {
                    let ty = self.lctx.lookup(local).ty;
                    (self.alloc.mkt_local(local), ty)
                }
                else {
                    let symbol = self.lookup_symbol_ident(name)?;
                    self.elab_symbol(symbol, &[])?
                }
            }

            ExprKind::Path(path) => {
                let symbol = self.lookup_symbol_path(path)?;
                self.elab_symbol(symbol, &[])?
            }

            ExprKind::Levels(it) => {
                let symbol = self.lookup_symbol_expr(it.expr)?;
                self.elab_symbol(symbol, it.levels)?
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
                println!("unimp expr kind {:?}", expr);
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


    fn lookup_local(&self, name: &str) -> Option<LocalId> {
        for (n, id) in self.locals.iter().rev().copied() {
            if n == name {
                return Some(id);
            }
        }
        None
    }

    fn lookup_symbol_ident(&self, name: &str) -> Option<SymbolId> {
        let Some(entry) = self.env.lookup(self.ns, name) else {
            println!("symbol not found: {:?}", name);
            return None;
        };
        Some(entry.symbol)
    }

    fn lookup_symbol_path(&self, path: &expr::Path) -> Option<SymbolId> {
        if path.local {
            let mut result = self.lookup_symbol_ident(path.parts[0])?;

            for part in &path.parts[1..] {
                let symbol = self.env.symbol(result);

                let Some(ns) = symbol.own_ns.to_option() else {
                    println!("symbol doesn't have ns");
                    return None;
                };

                let Some(entry) = self.env.lookup(ns, part) else {
                    println!("symbol not found: {:?}", part);
                    return None;
                };
                result = entry.symbol;
            }

            Some(result)
        }
        else {
            unimplemented!()
        }
    }

    fn lookup_symbol_expr(&self, expr: &Expr) -> Option<SymbolId> {
        match &expr.kind {
            ExprKind::Ident(name) => {
                if self.lookup_local(*name).is_some() {
                    println!("symbol shadowed by local");
                    return None;
                }

                self.lookup_symbol_ident(*name)
            }

            ExprKind::Path(path) => {
                self.lookup_symbol_path(path)
            }

            _ => {
                println!("invalid symbol expr");
                return None;
            }
        }
    }


    fn elab_symbol(&mut self, id: SymbolId, levels: &[ast::Level<'a>]) -> Option<(TermRef<'a>, TermRef<'a>)> {
        let symbol = self.env.symbol(id);
        Some(match symbol.kind {
            SymbolKind::BuiltIn(b) => {
                match b {
                    symbol::BuiltIn::Nat => {
                        if levels.len() != 0 {
                            println!("Nat takes no levels");
                            return None;
                        }
                        (Term::NAT, Term::SORT_1)
                    }

                    symbol::BuiltIn::NatZero => {
                        if levels.len() != 0 {
                            println!("Nat.zero takes no levels");
                            return None;
                        }
                        (Term::NAT_ZERO, Term::NAT)
                    }

                    symbol::BuiltIn::NatSucc => {
                        if levels.len() != 0 {
                            println!("Nat.succ takes no levels");
                            return None;
                        }
                        (Term::NAT_SUCC, Term::NAT_SUCC_TY)
                    }

                    symbol::BuiltIn::NatRec => {
                        if levels.len() != 1 {
                            println!("Nat.rec takes exactly 1 level");
                            return None;
                        }

                        let l = self.elab_level(&levels[0])?;
                        (self.alloc.mkt_nat_rec(l),
                         self.alloc.mkt_nat_rec_ty(l))
                    }
                }
            }

            _ => unimplemented!()
        })
    }


    #[inline(always)]
    pub fn tc<'l>(&mut self) -> TyCtx<'a, '_> {
        TyCtx::new(self.alloc, &mut self.lctx)
    }
}

