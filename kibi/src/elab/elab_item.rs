use crate::ast::{ItemId, ItemKind, item};

use super::*;

impl<'me, 'c, 'out, 'a> Elaborator<'me, 'c, 'out, 'a> {
    pub fn elab_item(&mut self, item_id: ItemId) -> Option<()> {
        let item = &self.parse.items[item_id];
        match &item.kind {
            ItemKind::Error => None,

            ItemKind::Axiom(it) => self.elab_axiom(item_id, it).map(|_| ()),

            ItemKind::Def(it) => self.elab_def(item_id, it).map(|_| ()),

            ItemKind::Reduce(it) => {
                spall::trace_scope!("kibi/elab/reduce");

                let (term, _) = self.elab_expr(*it)?;
                let _r = self.reduce(term);

                /*
                if printing {
                    let temp = sti::arena_pool::ArenaPool::tls_get_temp();
                    let mut pp = TermPP::new(&self.elab.env, &self.elab.strings, &*temp);
                    let r = pp.pp_term(r);
                    let r = pp.indent(9, r);
                    let r = pp.render(r, 80);
                    let r = r.layout_string();
                    println!("reduced: {}", r);
                }
                */
                Some(())
            }

            ItemKind::Inductive(it) => {
                spall::trace_scope!("kibi/elab/inductive"; "{}",
                    &self.strings[it.name]);

                let _ = self.elab_inductive(item_id, it)?;

                Some(())
            }

            ItemKind::Trait(it) => {
                match it {
                    item::Trait::Inductive(ind) => {
                        spall::trace_scope!("kibi/elab/trait-ind",
                            &self.strings[ind.name]);

                        let symbol = self.elab_inductive(item_id, &ind)?;

                        self.traits.new_trait(symbol);

                        Some(())
                    }
                }
            }

            ItemKind::Impl(it) => {
                spall::trace_scope!("kibi/elab/impl");

                let (ty, val) = self.elab_def_core(item_id,
                    it.levels, it.params, it.ty.some(), it.value)?;

                let trayt = ty.forall_ret().0.app_fun().0;
                let mut is_trait = false;
                if let Some(g) = trayt.try_global() {
                    if self.traits.is_trait(g.id) {
                        is_trait = true;

                        let impls = self.traits.impls(g.id);
                        // @speed: arena.
                        let name = self.strings.insert(&format!("impl_{}", impls.len()));
                        let symbol = self.env.new_symbol(g.id, name, SymbolKind::Def(symbol::Def {
                            num_levels: it.levels.len() as u32,
                            ty,
                            val: Some(val),
                        })).unwrap();
                        self.traits.add_impl(g.id, symbol);
                    }
                }
                if !is_trait {
                    // @todo: better source, type.
                    self.error(item_id, ElabError::ImplTypeIsNotTrait);
                    return None;
                }

                // @todo: better source.
                let _ = self.check_no_unassigned_variables(item_id.into())?;

                Some(())
            }
        }
    }
}

