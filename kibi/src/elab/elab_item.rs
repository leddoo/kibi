use crate::ast::{ItemId, ItemKind, item};

use super::*;

impl<'me, 'c, 'out, 'a> Elaborator<'me, 'c, 'out, 'a> {
    pub fn elab_item(&mut self, item_id: ItemId) -> Option<()> {
        let item = &self.parse.items[item_id];
        match &item.kind {
            ItemKind::Error => None,

            ItemKind::Axiom(it) => self.elab_axiom(it).map(|_| ()),

            ItemKind::Def(it) => self.elab_def(it).map(|_| ()),

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

                let _ = self.elab_inductive(it)?;

                /*
                if printing {
                    println!("inductive {}", &self.elab.strings[ind.name]);
                }
                */
                Some(())
            }

            ItemKind::Trait(it) => {
                match it {
                    item::Trait::Inductive(ind) => {
                        spall::trace_scope!("kibi/elab/trait-ind",
                            &self.strings[ind.name]);

                        let symbol = self.elab_inductive(&ind)?;

                        self.traits.new_trait(symbol);

                        /*
                        if printing {
                            println!("trait inductive {}", &self.elab.strings[ind.name]);
                        }
                        */
                        Some(())
                    }
                }
            }

            ItemKind::Impl(it) => {
                spall::trace_scope!("kibi/elab/impl");

                let (ty, val) = self.elab_def_core(
                    it.levels, it.params, it.ty.some(), it.value)?;

                let trayt = ty.forall_ret().0.app_fun().0;
                if let Some(g) = trayt.try_global() {
                    if self.traits.is_trait(g.id) {
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
                    else {
                        println!("error: must impl a trait");
                        return None;
                    }
                }
                else {
                    println!("error: must impl a trait");
                    return None;
                }

                /*
                if printing {
                    println!("impl");
                }
                */

                let _ = self.check_no_unassigned_variables()?;

                Some(())
            }
        }
    }
}

