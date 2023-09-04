use sti::arena::Arena;

use crate::pp::*;
use crate::string_table::{Atom, StringTable, atoms};
use crate::env::{Env, SymbolId};
use super::*;


pub struct TermPP<'me, 'a> {
    pub strings: &'me StringTable<'me>,
    pub pp: PP<'a>,
    pub env: &'me Env<'me>,
}

impl<'me, 'a> TermPP<'me, 'a> {
    pub fn new(env: &'me Env<'me>, strings: &'me StringTable<'me>, arena: &'a Arena) -> Self {
        Self {
            strings,
            pp: PP::new(arena),
            env,
        }
    }

    pub fn alloc_atom(&self, atom: Atom) -> &'a str {
        self.pp.alloc_str(&self.strings[atom])
    }

    pub fn pp_level(&mut self, l: Level) -> DocRef<'a> {
        let (l, offset) = l.to_offset();

        match l.data() {
            LevelData::Zero => {
                // @temp: sti string module.
                self.pp.text(self.pp.alloc_str(&format!("{offset}")))
            }

            LevelData::Succ(_) => unreachable!(),

            LevelData::Max(p) |
            LevelData::IMax(p) => {
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
                        // @temp: sti string module.
                        self.pp.text(self.pp.alloc_str(&format!("+ {offset}")))
                    }
                    else { self.pp.nil() },
                ]))
            }

            LevelData::Param(p) => {
                self.pp.text(self.alloc_atom(p.name))
            }

            LevelData::IVar(var) => {
                // @temp: sti string module.
                self.pp.text(self.pp.alloc_str(&format!("?{}", var.inner())))
            }
        }
    }

    pub fn pp_term(&mut self, t: Term) -> DocRef<'a> {
        match t.data() {
            TermData::Sort(l) => {
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

            TermData::Bound(BVar { offset }) => {
                // @temp: sti string module.
                self.pp.text(self.pp.alloc_str(&format!("${offset}")))
            }

            TermData::Local(i) => {
                // @temp: sti string module.
                self.pp.text(self.pp.alloc_str(&format!("%{}", i.inner())))
            }

            TermData::Global(g) => {
                let symbol = self.env.symbol(g.id);

                let mut name = self.pp.text(self.alloc_atom(symbol.name));
                let mut at = symbol.parent;
                while at != SymbolId::ROOT {
                    let symbol = self.env.symbol(at);
                    name = self.pp.cats(&[
                        self.pp.text(self.alloc_atom(symbol.name)),
                        self.pp.text("::"),
                        name]);
                    at = symbol.parent;
                }

                if g.levels.len() > 0 {
                    self.pp.cat(
                        name,
                        self.pp.text(".{tbd}"))
                }
                else { name }
            }

            TermData::IVar(var) => {
                // @temp: sti string module.
                self.pp.text(self.pp.alloc_str(&format!("?{}", var.inner())))
            }

            TermData::Forall(b) => {
                let name = if b.name == Atom::NULL { atoms::_hole } else { b.name };
                let ty  = self.pp_term(b.ty);
                let val = self.pp_term(b.val);
                self.pp.group(self.pp.cats(&[
                    self.pp.text("Π("),
                    self.pp.group(self.pp.indent(2, self.pp.cats(&[
                        self.pp.text(self.alloc_atom(name)),
                        self.pp.text(": "),
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

            TermData::Lambda(b) => {
                let name = if b.name == Atom::NULL { atoms::_hole } else { b.name };
                let ty  = self.pp_term(b.ty);
                let val = self.pp_term(b.val);
                self.pp.group(self.pp.cats(&[
                    self.pp.text("λ("),
                    self.pp.group(self.pp.indent(2, self.pp.cats(&[
                        self.pp.text(self.alloc_atom(name)),
                        self.pp.text(": "),
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

            TermData::Apply(app) => {
                /*
                if app.fun.kind() == TermKind::NatSucc {
                    let mut offset = 1;
                    let mut at = app.arg;
                    loop {
                        let Some(app) = at.try_apply() else { break };
                        if app.fun.kind() != TermKind::NatSucc { break }
                        offset += 1;
                        at = app.arg;
                    }

                    if at.kind() == TermKind::NatZero {
                        return self.pp.text(self.pp.alloc_str(&format!("{offset}")))
                    }
                    else {
                        // @todo: `() + offset`.
                    }
                }
                */

                let (fun_term, fun, args) = self.pp_apply(&app);

                let needs_parens = match fun_term.data() {
                    TermData::Forall(_) |
                    TermData::Lambda(_) => true,
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
        }
    }

    fn pp_apply<'t>(&mut self, app: &term::Apply<'t>) -> (Term<'t>, DocRef<'a>, DocRef<'a>) {
        if let Some(f_app) = app.fun.try_apply() {
            let (fun_term, fun, args) = self.pp_apply(&f_app);
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

