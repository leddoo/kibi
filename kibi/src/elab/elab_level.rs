use crate::ast;
use crate::tt::{self, *};

use super::*;


impl<'me, 'c, 'out> Elaborator<'me, 'c, 'out> {
    pub fn elab_level(&mut self, level_id: ast::LevelId) -> Option<tt::Level<'out>> {
        let level = self.parse.levels[level_id];
        Some(match level.kind {
            ast::LevelKind::Error => return None,

            ast::LevelKind::Hole => {
                self.new_level_var()
            }

            ast::LevelKind::Ident(name) => {
                for i in 0..self.level_params.len() {
                    if name.value == self.level_params[i] {
                        return Some(self.alloc.mkl_param(name.value, i as u32));
                    }
                }
                self.error(level_id,
                    ElabError::UnresolvedLevel(
                        self.alloc.alloc_str(&self.strings[name.value])));
                return None;
            }

            ast::LevelKind::Nat(n) => {
                self.alloc.mkl_nat(n)
            }

            ast::LevelKind::Add((l, offset)) => {
                let l = self.elab_level(l)?;
                l.offset(offset, self.alloc)
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
        })
    }
}

