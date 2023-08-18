use sti::growing_arena::GrowingArena;

use crate::pp::*;
use crate::env::{Env, NamespaceId};
use super::*;


pub struct TermPP<'me, 'a> {
    pub pp: PP<'a>,
    pub env: &'me Env<'me>,
}

impl<'me, 'a> TermPP<'me, 'a> {
    pub fn new(arena: &'a GrowingArena, env: &'me Env<'me>) -> Self {
        Self {
            pp: PP::new(arena),
            env,
        }
    }

    pub fn pp_level(&mut self, l: LevelRef) -> DocRef<'a> {
        let (l, offset) = l.to_offset();

        match l.kind {
            LevelKind::Zero => {
                // @temp.
                self.pp.text(self.pp.alloc_str(&format!("{offset}")))
            }

            LevelKind::Succ(_) => unreachable!(),

            LevelKind::Max(p) |
            LevelKind::IMax(p) => {
                let lhs = self.pp_level(p.lhs);
                let rhs = self.pp_level(p.rhs);

                self.pp.group(self.pp.cats(&[
                    self.pp.text(if l.is_max() { "max(" } else { "imax(" }),

                    self.pp.indent(2, self.pp.cats(&[
                        self.pp.line(),
                        lhs, self.pp.text(","),

                        self.pp.line_or_sp(),
                        rhs, self.pp.text(")"),
                    ])),

                    if offset != 0 {
                        self.pp.cat(
                            self.pp.text("+ "),
                            // @temp.
                            self.pp.text(self.pp.alloc_str(&format!("{offset}"))))
                    }
                    else { self.pp.nil() },
                ]))
            }

            LevelKind::Param(p) => {
                self.pp.text(self.pp.alloc_str(p.name))
            }
        }
    }

    pub fn pp_term(&mut self, t: TermRef) -> DocRef<'a> {
        match t.kind {
            TermKind::Sort(l) => {
                if l.is_zero() {
                    self.pp.text("Prop")
                }
                else if let Some(1) = l.to_nat() {
                    self.pp.text("Type")
                }
                else {
                    let l = self.pp_level(l);
                    self.pp.cats(&[
                        self.pp.text("Sort("),
                        l,
                        self.pp.text(")")
                    ])
                }
            }

            TermKind::BVar(BVar(i)) => {
                // @temp
                self.pp.text(self.pp.alloc_str(&format!("${i}")))
            }

            TermKind::Local(i) => {
                // @temp
                self.pp.text(self.pp.alloc_str(&format!("%{}", i.value())))
            }

            TermKind::Global(g) => {
                let symbol = self.env.symbol(g.id);

                let mut name = self.pp.text(self.pp.alloc_str(symbol.name));
                let mut at = symbol.parent_ns;
                while at != NamespaceId::ROOT {
                    let symbol = self.env.namespace(at).symbol.unwrap();
                    let symbol = self.env.symbol(symbol);
                    name = self.pp.cats(&[
                        self.pp.text(self.pp.alloc_str(symbol.name)),
                        self.pp.text("::"),
                        name]);
                    at = symbol.parent_ns;
                }

                if g.levels.len() > 0 {
                    self.pp.cat(
                        name,
                        self.pp.text(".{tbd}"))
                }
                else { name }
            }

            TermKind::Forall(b) => {
                let ty  = self.pp_term(b.ty);
                let val = self.pp_term(b.val);
                self.pp.group(self.pp.cats(&[
                    self.pp.text("Π("),
                    self.pp.group(self.pp.indent(2, self.pp.cats(&[
                        self.pp.text("_: "),
                        self.pp.line(),
                        ty,
                    ]))),
                    self.pp.text(") ->"),
                    self.pp.group(self.pp.indent(2, self.pp.cats(&[
                        self.pp.line_or_sp(),
                        val,
                    ]))),
                ]))
            }

            TermKind::Lambda(b) => {
                let ty  = self.pp_term(b.ty);
                let val = self.pp_term(b.val);
                self.pp.group(self.pp.cats(&[
                    self.pp.text("λ("),
                    self.pp.group(self.pp.indent(2, self.pp.cats(&[
                        self.pp.text("_: "),
                        self.pp.line(),
                        ty,
                    ]))),
                    self.pp.text(") =>"),
                    self.pp.group(self.pp.indent(2, self.pp.cats(&[
                        self.pp.line_or_sp(),
                        val,
                    ]))),
                ]))
            }

            TermKind::Apply(app) => {
                if let TermKind::NatSucc = app.fun.kind {
                    let mut offset = 1;
                    let mut at = app.arg;
                    loop {
                        let TermKind::Apply(app) = at.kind else { break };
                        let TermKind::NatSucc = app.fun.kind else { break };
                        offset += 1;
                        at = app.arg;
                    }

                    if let TermKind::NatZero = at.kind {
                        return self.pp.text(self.pp.alloc_str(&format!("{offset}")))
                    }
                    else {
                        // @todo: `() + offset`.
                    }
                }

                let (fun_term, fun, args) = self.pp_apply(&app);

                let needs_parens = match fun_term.kind {
                    TermKind::Forall(_) |
                    TermKind::Lambda(_) => true,
                    _ => false,
                    // @pp_needs_parens
                };

                let fun = if needs_parens {
                    self.pp.cats(&[
                        self.pp.text("("),
                        self.pp.group(self.pp.cat(
                            self.pp.indent(1, fun),
                            self.pp.line())),
                        self.pp.text(")"),
                    ])
                }
                else { fun };

                self.pp.group(self.pp.cats(&[
                    fun,
                    self.pp.text("("),
                    self.pp.group(
                        self.pp.indent(2,
                            self.pp.cat(self.pp.line(), args))),
                    self.pp.text(")"),
                ]))
            }

            TermKind::Nat => self.pp.text("Nat"),

            TermKind::NatZero => self.pp.text("0"),

            TermKind::NatSucc => self.pp.text("Nat::succ"),

            TermKind::NatRec(l) => {
                let l = self.pp_level(l);
                self.pp.cats(&[
                    self.pp.text("Nat::rec.{"),
                    l,
                    self.pp.text("}"),
                ])
            }

            TermKind::Eq(l) => {
                let l = self.pp_level(l);
                self.pp.cats(&[
                    self.pp.text("Eq.{"),
                    l,
                    self.pp.text("}"),
                ])
            }

            TermKind::EqRefl(_) => {
                unimplemented!()
            }

            TermKind::EqRec(_, _) => {
                unimplemented!()
            }
        }
    }

    fn pp_apply<'t>(&mut self, app: &term::Apply<'t>) -> (TermRef<'t>, DocRef<'a>, DocRef<'a>) {
        if let TermKind::Apply(a) = &app.fun.kind {
            let (fun_term, fun, args) = self.pp_apply(a);
            let arg = self.pp_term(app.arg);
            let args = self.pp.cats(&[
                args,
                self.pp.text(","),
                self.pp.group(self.pp.cat(self.pp.line_or_sp(), arg))
            ]);
            return (fun_term, fun, args);
        }
        else {
            return (app.fun, self.pp_term(app.fun), self.pp_term(app.arg))
        }
    }
}

impl<'me, 'a> core::ops::Deref for TermPP<'me, 'a> {
    type Target = PP<'a>;

    #[inline(always)]
    fn deref(&self) -> &Self::Target { &self.pp }
}

