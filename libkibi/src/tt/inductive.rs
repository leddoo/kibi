use sti::arena::Arena;
use sti::vec::Vec;

use crate::string_table::Atom;
use crate::env::SymbolKind;
use crate::elab::Elab;

use super::level::*;
use super::term::*;


pub struct MutualSpec<'me, 'a> {
    pub levels: &'me [Atom],
    pub params: &'me [ScopeId],
    pub types: &'me [TypeSpec<'me, 'a>],
}

pub struct TypeSpec<'me, 'a> {
    pub symbol: SymbolId,
    pub local: ScopeId,
    pub ctors: &'me [(Atom, Term<'a>)],
}


pub struct Check<'me, 'temp, 'err, 'a> {
    alloc: &'a Arena,

    // @temp: @inductive_uses_elab.
    elab: &'me mut Elab<'temp, 'err, 'a>,

    spec: MutualSpec<'me, 'a>,

    level_params: &'a [Level<'a>],
    type_globals: Vec<Term<'a>>,
    indices: Vec<Vec<ScopeId>>,
}

impl<'me, 'temp, 'err, 'a> Check<'me, 'temp, 'err, 'a> {
    pub fn check(elab: &mut Elab<'temp, 'err, 'a>, spec: MutualSpec<'_, 'a>) -> Option<()> {
        let num_types = spec.types.len();
        assert!(num_types > 0);

        let mut level_params = Vec::with_cap_in(spec.levels.len(), elab.alloc);
        for (i, name) in spec.levels.iter().copied().enumerate() {
            level_params.push(elab.alloc.mkl_param(name, i as u32));
        }

        let mut this = Check {
            alloc: elab.alloc,
            elab,
            spec,
            level_params: level_params.leak(),
            type_globals: Vec::with_cap(num_types),
            indices: Vec::with_cap(num_types),
        };

        // @complete: check levels params in types.

        // @complete: check params are types.

        // check specs.
        let mut ind_level = None;
        for spec in this.spec.types {
            let mut indices = Vec::new();

            // check type.
            let mut ty = this.elab.lctx.lookup(spec.local).ty;
            while let Some(pi) = this.elab.whnf_forall(ty) {
                // @complete: check indices are types.
                let id = this.elab.lctx.push(pi.kind, pi.name, pi.ty, None);
                indices.push(id);
                ty = pi.val.instantiate(this.alloc.mkt_local(id), this.alloc);
            }

            this.type_globals.push(
                this.alloc.mkt_global(spec.symbol, this.level_params));
            this.indices.push(indices);


            // check level.
            let Some(level) = this.elab.whnf_sort(ty) else {
                unimplemented!()
            };

            if let Some(l) = ind_level {
                if !level.syntax_eq(l) {
                    unimplemented!()
                }
            }
            else {
                ind_level = Some(level);
            }

            // check ctors.
            for (_, ctor_ty) in spec.ctors.iter().copied() {
                // check args.
                let mut ty = ctor_ty;
                while let Some(pi) = this.elab.whnf_forall(ty) {
                    // check level.
                    let Some(_arg_level) = this.elab.infer_type_as_sort(pi.ty) else {
                        println!("this shouldn't have happened...");
                        return None;
                    };
                    // @complete: `ind_level.is_zero() || arg_level.le(ind_level)`.

                    // check recursion.
                    let is_rec = {
                        let mut ret = pi.ty;
                        while let Some(pi) = this.elab.whnf_forall(ret) {
                            // check positivity.
                            if this.has_ind_occ(pi.ty) {
                                println!("invalid recursion");
                                return None;
                            }
                            ret = pi.val;
                        }

                        this.is_valid_inductive_app(ret, spec.local)?
                    };

                    if is_rec {
                        // ensure rec arg not used.
                        ty = pi.val;
                        if !ty.closed() {
                            println!("error: recursive argument used");
                            return None;
                        }
                    }
                    else {
                        let id = this.elab.lctx.push(pi.kind, pi.name, pi.ty, None);
                        ty = pi.val.instantiate(this.alloc.mkt_local(id), this.alloc);
                    }
                }
            }
        }
        let ind_level = ind_level.unwrap();

        // determine elim level.
        let large_elim = {
            // non-prop.
            if ind_level.non_zero() {
                true
            }
            // mutual props aren't LE
            else if this.spec.types.len() > 0 {
                false
            }
            else {
                let ctors = this.spec.types[0].ctors;
                // `False`
                if ctors.len() == 0 {
                    true
                }
                else {
                    // @todo: sub-singleton.
                    false
                }
            }
        };

        println!("ind LE: {}", large_elim);

        Some(())
    }

    fn has_ind_occ(&self, t: Term) -> bool {
        t.find(|at, _| {
            let local = at.try_local()?;
            Some(self.spec.types.iter().find(|spec| local == spec.local).is_some())
        }).is_some()
    }

    fn is_valid_inductive_app(&self, app: Term, ind_local: ScopeId) -> Option<bool> {
        // find app target.
        let mut target = app;
        while let Some(app) = target.try_apply() {
            // check no recursion in arguments.
            if self.has_ind_occ(app.arg) {
                println!("error: invalid recursion");
                return None;
            }

            target = app.fun;
        }

        // check if target is the inductive type.
        if let Some(local) = target.try_local() {
            Some(local == ind_local)
        }
        else { Some(false) }
    }
}

