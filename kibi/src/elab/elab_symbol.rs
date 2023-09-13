use sti::traits::{CopyIt, FromIn};

use crate::string_table::Atom;
use crate::ast;
use crate::tt::*;

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

    pub fn lookup_symbol_ident(&self, source: ErrorSource, name: Atom) -> Option<SymbolId> {
        let Some(symbol) = self.env.lookup(self.root_symbol, name) else {
            self.error(source, |alloc|
                ElabError::UnresolvedName { base: "",
                    name: alloc.alloc_str(&self.strings[name]) });
            return None;
        };
        Some(symbol)
    }

    pub fn lookup_symbol_path(&self, source: ErrorSource, local: bool, parts: &[Atom]) -> Option<SymbolId> {
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


    pub fn elab_symbol(&mut self, source: ErrorSource, id: SymbolId, levels: &[ast::LevelId]) -> Option<(Term<'a>, Term<'a>)> {
        let symbol = self.env.symbol(id);
        Some(match symbol.kind {
            SymbolKind::Root |
            SymbolKind::Predeclared |
            SymbolKind::Pending => unreachable!(),

            SymbolKind::IndAxiom(it) => {
                let num_levels = it.num_levels as usize;

                // @cleanup: dedup.
                let levels = if levels.len() == 0 {
                    Vec::from_in(self.alloc,
                        (0..num_levels).map(|_| self.new_level_var())
                    ).leak()
                }
                else {
                    if levels.len() != num_levels {
                        self.error(source, |_|
                            ElabError::LevelMismatch {
                                expected: it.num_levels, found: levels.len() as u32 });
                        return None;
                    }

                    let mut ls = Vec::with_cap_in(self.alloc, levels.len());
                    for l in levels.copy_it() {
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
                    Vec::from_in(self.alloc,
                        (0..num_levels).map(|_| self.new_level_var())
                    ).leak()
                }
                else {
                    if levels.len() != num_levels {
                        self.error(source, |_|
                            ElabError::LevelMismatch {
                                expected: def.num_levels, found: levels.len() as u32 });
                        return None;
                    }

                    let mut ls = Vec::with_cap_in(self.alloc, levels.len());
                    for l in levels.copy_it() {
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

