use sti::vec::Vec;

use crate::string_table::Atom;
use crate::env::{SymbolKind, Env};
use crate::elab::Elab;

use super::level::*;
use super::term::*;


pub struct TypeSpec<'me, 'a> {
    pub symbol: SymbolId,
    pub num_params: usize,
    pub ctors: &'me [(Atom, Term<'a>)],
}


// @temp: @inductive_uses_elab.
pub fn check<'temp, 'err, 'a>(elab: &mut Elab<'temp, 'err, 'a>, specs: &[TypeSpec<'_, 'a>]) -> Option<()> {
    assert!(specs.len() > 0);

    // check levels.
    let _ind_level = {
        fn get_level<'a>(env: &Env<'a>, id: SymbolId) -> Level<'a> {
            let SymbolKind::IndTy(ind) = env.symbol(id).kind else { unreachable!() };
            ind.own_type.try_sort().unwrap()
        }

        let level = get_level(&elab.env, specs[0].symbol);

        for spec in &specs[1..] {
            let l = get_level(&elab.env, spec.symbol);
            if !l.syntax_eq(level) {
                println!("error: all inductive types must live in the same universe");
                return None;
            }
        }

        level
    };


    // check ctors.
    for spec in specs {
        let ind_symbol = spec.symbol;

        let type_former = {
            let SymbolKind::IndTy(ind) = elab.env.symbol(spec.symbol).kind else { unreachable!() };
            ind.type_former
        };

        let lctx_save = elab.lctx.save();

        // collect params & add to lctx.
        let params = {
            let mut result = Vec::with_cap(spec.num_params);
            let mut ty = type_former;
            for _ in 0..spec.num_params {
                let pi = ty.try_forall().unwrap();

                let id = elab.lctx.push(pi.kind, pi.name, pi.ty, None);

                result.push((id, pi.ty));
                ty = pi.val.instantiate(elab.alloc.mkt_local(id), elab.alloc);
            }
            result
        };

        // validate ctors.
        for (_, ctor_ty) in spec.ctors.iter().copied() {
            let lctx_save = elab.lctx.save();

            let mut param_idx = 0;
            let mut ty = ctor_ty;
            while let Some(pi) = elab.whnf_forall(ty) {
                // validate params.
                if param_idx < params.len() {
                    let (id, param_ty) = params[param_idx];

                    if !pi.ty.syntax_eq(param_ty) {
                        println!("um, this shouldn't have happened");
                        return None;
                    }

                    param_idx += 1;
                    ty = pi.val.instantiate(elab.alloc.mkt_local(id), elab.alloc);
                }
                // validate ctor arg.
                else {
                    // check level.
                    let Some(_arg_level) = elab.infer_type_as_sort(pi.ty) else {
                        println!("this shouldn't have happened either...");
                        return None;
                    };
                    // @complete: `ind_level.is_zero() || arg_level.le(ind_level)`.

                    // check recursion.
                    let is_rec = {
                        let mut ret = pi.ty;
                        while let Some(pi) = elab.whnf_forall(ret) {
                            // check positivity.
                            if has_ind_occ(pi.ty, specs) {
                                println!("invalid recursion");
                                return None;
                            }
                            ret = pi.val;
                        }

                        is_valid_inductive_app(ret, ind_symbol, specs)?
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
                        let id = elab.lctx.push(pi.kind, pi.name, pi.ty, None);
                        ty = pi.val.instantiate(elab.alloc.mkt_local(id), elab.alloc);
                    }
                }
            }

            elab.lctx.restore(lctx_save);
        }

        elab.lctx.restore(lctx_save);
    }

    Some(())
}


fn has_ind_occ(t: Term, specs: &[TypeSpec]) -> bool {
    t.find(|at, _| {
        let g = at.try_global()?;
        Some(specs.iter().find(|spec| g.id == spec.symbol).is_some())
    }).is_some()
}

fn is_valid_inductive_app(app: Term, ind_id: SymbolId, specs: &[TypeSpec]) -> Option<bool> {
    // find app target.
    let mut target = app;
    while let Some(app) = target.try_apply() {
        // check no recursion in arguments.
        if has_ind_occ(app.arg, specs) {
            println!("error: invalid recursion");
            return None;
        }

        target = app.fun;
    }

    // check if target is the inductive type.
    if let Some(g) = target.try_global() {
        Some(g.id == ind_id)
    }
    else { Some(false) }
}

