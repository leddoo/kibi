use crate::string_table::Atom;
use crate::ast;
use crate::tt::*;
use crate::env::*;

use super::*;


impl<'me, 'err, 'a> Elab<'me, 'err, 'a> {
    pub fn lookup_local(&self, name: Atom) -> Option<ScopeId> {
        for (n, id) in self.locals.iter().rev().copied() {
            if n == name {
                return Some(id);
            }
        }
        None
    }

    pub fn lookup_symbol_ident(&self, source: SourceRange, name: Atom) -> Option<SymbolId> {
        let Some(symbol) = self.env.lookup(self.root_symbol, name) else {
            self.error(source, |alloc|
                ElabError::UnresolvedName { base: "",
                    name: alloc.alloc_str(&self.strings[name]) });
            return None;
        };
        Some(symbol)
    }

    pub fn lookup_symbol_path(&self, source: SourceRange, local: bool, parts: &[Atom]) -> Option<SymbolId> {
        if local {
            let mut result = self.lookup_symbol_ident(source, parts[0])?;

            for part in parts[1..].iter().copied() {
                let Some(symbol) = self.env.lookup(result, part) else {
                    // @todo: proper base.
                    self.error(source, |alloc|
                        ElabError::UnresolvedName { base: "",
                            name: alloc.alloc_str(&self.strings[part]) });
                    return None;
                };

                result = symbol;
            }

            Some(result)
        }
        else {
            unimplemented!()
        }
    }


    pub fn elab_symbol(&mut self, source: SourceRange, id: SymbolId, levels: &[ast::Level<'a>]) -> Option<(Term<'a>, Term<'a>)> {
        let symbol = self.env.symbol(id);
        Some(match symbol.kind {
            SymbolKind::Root => unreachable!(),

            SymbolKind::BuiltIn(b) => {
                match b {
                    symbol::BuiltIn::Nat => {
                        if levels.len() != 0 {
                            self.error(source, |_|
                                ElabError::LevelMismatch {
                                    expected: 0, found: levels.len() as u32 });
                            return None;
                        }
                        (Term::NAT, Term::SORT_1)
                    }

                    symbol::BuiltIn::NatZero => {
                        if levels.len() != 0 {
                            self.error(source, |_|
                                ElabError::LevelMismatch {
                                    expected: 0, found: levels.len() as u32 });
                            return None;
                        }
                        (Term::NAT_ZERO, Term::NAT)
                    }

                    symbol::BuiltIn::NatSucc => {
                        if levels.len() != 0 {
                            self.error(source, |_|
                                ElabError::LevelMismatch {
                                    expected: 0, found: levels.len() as u32 });
                            return None;
                        }
                        (Term::NAT_SUCC, Term::NAT_SUCC_TY)
                    }

                    symbol::BuiltIn::NatRec => {
                        let r = if levels.len() == 0 {
                            self.new_level_var()
                        }
                        else {
                            if levels.len() != 1 {
                                self.error(source, |_|
                                    ElabError::LevelMismatch {
                                        expected: 1, found: levels.len() as u32 });
                                return None;
                            }
                            self.elab_level(&levels[0])?
                        };

                        (self.alloc.mkt_nat_rec(r),
                         self.alloc.mkt_nat_rec_ty(r))
                    }

                    symbol::BuiltIn::Eq => {
                        let l = if levels.len() == 0 {
                            self.new_level_var()
                        }
                        else {
                            if levels.len() != 1 {
                                self.error(source, |_|
                                    ElabError::LevelMismatch {
                                        expected: 1, found: levels.len() as u32 });
                                return None;
                            }
                            self.elab_level(&levels[0])?
                        };

                        (self.alloc.mkt_eq(l),
                         self.alloc.mkt_eq_ty(l))
                    }

                    symbol::BuiltIn::EqRefl => {
                        let l = if levels.len() == 0 {
                            self.new_level_var()
                        }
                        else {
                            if levels.len() != 1 {
                                self.error(source, |_|
                                    ElabError::LevelMismatch {
                                        expected: 1, found: levels.len() as u32 });
                                return None;
                            }
                            self.elab_level(&levels[0])?
                        };

                        (self.alloc.mkt_eq_refl(l),
                         self.alloc.mkt_eq_refl_ty(l))
                    }

                    symbol::BuiltIn::EqRec => {
                        let (l, r) = if levels.len() == 0 {
                            (self.new_level_var(),
                             self.new_level_var())
                        }
                        else {
                            if levels.len() != 2 {
                                self.error(source, |_|
                                    ElabError::LevelMismatch {
                                        expected: 2, found: levels.len() as u32 });
                                return None;
                            }
                            (self.elab_level(&levels[0])?,
                             self.elab_level(&levels[1])?)
                        };

                        (self.alloc.mkt_eq_rec(l, r),
                         self.alloc.mkt_eq_rec_ty(l, r))
                    }
                }
            }

            SymbolKind::IndTy(it) => {
                let num_levels = it.num_levels as usize;

                // @cleanup: dedup.
                let levels = if levels.len() == 0 {
                    let mut ls = Vec::with_cap_in(num_levels, self.alloc);
                    for _ in 0..num_levels {
                        ls.push(self.new_level_var());
                    }
                    ls.leak()
                }
                else {
                    if levels.len() != num_levels {
                        self.error(source, |_|
                            ElabError::LevelMismatch {
                                expected: it.num_levels, found: levels.len() as u32 });
                        return None;
                    }

                    let mut ls = Vec::with_cap_in(levels.len(), self.alloc);
                    for l in levels {
                        ls.push(self.elab_level(l)?);
                    }
                    ls.leak()
                };

                (self.alloc.mkt_global(id, levels),
                 it.ty.instantiate_level_params(levels, self.alloc))
            }

            SymbolKind::Def(def) => {
                let num_levels = def.num_levels as usize;

                // @cleanup: dedup.
                let levels = if levels.len() == 0 {
                    let mut ls = Vec::with_cap_in(num_levels, self.alloc);
                    for _ in 0..num_levels {
                        ls.push(self.new_level_var());
                    }
                    ls.leak()
                }
                else {
                    if levels.len() != num_levels {
                        self.error(source, |_|
                            ElabError::LevelMismatch {
                                expected: def.num_levels, found: levels.len() as u32 });
                        return None;
                    }

                    let mut ls = Vec::with_cap_in(levels.len(), self.alloc);
                    for l in levels {
                        ls.push(self.elab_level(l)?);
                    }
                    ls.leak()
                };

                (self.alloc.mkt_global(id, levels),
                 def.ty.instantiate_level_params(levels, self.alloc))
            }
        })
    }
}

