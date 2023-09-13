use sti::arena_pool::ArenaPool;

use crate::tt::*;

use super::*;


impl<'me, 'c, 'out, 'a> Elaborator<'me, 'c, 'out, 'a> {
    #[must_use]
    pub fn resolve_impl(&mut self, trayt: SymbolId, ivar: Term<'a>) -> bool {
        let temp = ArenaPool::tls_get_rec();

        let goal = self.infer_type(ivar).unwrap();
        let goal = self.instantiate_term_vars(goal);

        //eprintln!("impl resolution for {}", self.pp(goal, 80));

        if goal.has_ivars() {
            eprintln!("error: impl resolution doesn't support ivars rn, sorry");
            return false;
        }

        // local impls.
        let mut scope = self.lctx.current;
        while let Some(local) = scope.to_option() {
            let entry = self.lctx.lookup(local);
            scope = entry.parent;

            if entry.ty.syntax_eq(goal) {
                let val = self.alloc.mkt_local(local);
                if !self.ensure_def_eq(ivar, val) {
                    eprintln!("error: something went wrong");
                    return false;
                }
                return true;
            }
        }

        let impls = Vec::from_slice_in(&*temp, self.traits.impls(trayt));

        let mut matched = None;
        for impel in impls.iter().copied() {
            let sym = self.env.symbol(impel);
            //let name = sym.name;

            let def = match sym.kind {
                SymbolKind::Def(def) => def,
                _ => unreachable!()
            };

            let Some(def_val) = def.val else {
                continue;
            };

            //println!("found {}", self.pp(def.ty, 80));

            let save = self.save();

            let mut sub_ivars = Vec::new_in(&*temp);
            let mut def_ty  = def.ty;
            let mut def_val = def_val;
            while let Some(pi) = def_ty.try_forall() {
                let ivar = self.new_term_var_of_type(pi.ty);
                sub_ivars.push(ivar);

                def_ty = pi.val.instantiate(ivar, self.alloc);
                def_val = self.alloc.mkt_apply(def_val, ivar);
            }

            if sub_ivars.len() == 0 {
                //println!("simple case");
                if def.ty.syntax_eq(goal) {
                    if matched.is_some() {
                        eprintln!("error: multiple matching impls");
                        return false;
                    }

                    //println!("found match {:?}", &self.strings[name]);
                    matched = Some(def_val);
                }
            }
            else {
                if self.ensure_def_eq(def_ty, goal) {
                    //println!("maybe!");
                    let mut success = true;

                    for sub_ivar in sub_ivars.iter().copied() {
                        let value = self.instantiate_term_vars(sub_ivar);
                        if value.has_ivars() {
                            let sub_goal = self.infer_type(sub_ivar).unwrap();

                            let head = sub_goal.app_fun().0;
                            if let Some(global) = head.try_global() {
                                if self.traits.is_trait(global.id) {
                                    if self.resolve_impl(global.id, sub_ivar) {
                                        continue;
                                    }
                                    else{
                                        success = false;
                                        break;
                                    }
                                }
                            }

                            success = false;
                            break;
                        }
                    }
                    if success {
                        if matched.is_some() {
                            eprintln!("error: multiple matching impls");
                            return false;
                        }

                        //println!("found match {:?}", &self.strings[name]);
                        matched = Some(def_val);
                    }
                    else {
                        //println!("nope");
                        self.restore(save);
                    }
                }
                else {
                    //println!("restore");
                    self.restore(save);
                }
            }
        }

        let Some(matched) = matched else {
            return false;
        };

        if !self.ensure_def_eq(ivar, matched) {
            eprintln!("error: something went wrong");
            return false;
        }

        return true;
    }
}

