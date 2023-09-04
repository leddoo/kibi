use sti::arena::Arena;
use sti::arena_pool::ArenaPool;
use sti::vec::Vec;

use crate::string_table::Atom;
use crate::elab::Elab;

use super::level::*;
use super::term::*;


// @speed: cache mkt_locals.


pub struct MutualSpec<'me, 'a> {
    pub levels: &'me [Atom],
    pub params: &'me [ScopeId],
    pub types: &'me [TypeSpec<'me, 'a>],
}

pub struct TypeSpec<'me, 'a> {
    pub name: Atom,
    pub symbol: SymbolId,
    pub local: ScopeId,
    pub ctors: &'me [CtorSpec<'a>],
    pub rec_symbol: SymbolId,
}

#[derive(Clone, Copy)]
pub struct CtorSpec<'a> {
    pub name:   Atom,
    pub symbol: SymbolId,
    pub ty:     Term<'a>,
}


pub struct Check<'me, 'temp, 'err, 'a> {
    alloc: &'a Arena,
    temp: &'me Arena,

    // @temp: @inductive_uses_elab.
    elab: &'me mut Elab<'temp, 'err, 'a>,

    spec: MutualSpec<'me, 'a>,

    level_params: &'a [Level<'a>],
    type_globals: Vec<Term<'a>, &'me Arena>,
    type_global_apps: Vec<Term<'a>, &'me Arena>,
    indices: Vec<Vec<ScopeId, &'me Arena>, &'me Arena>,
    ctor_infos: Vec<Vec<CtorInfo<'me, 'a>, &'me Arena>, &'me Arena>,
}

#[derive(Clone, Copy)]
struct CtorInfo<'me, 'a> {
    args:    &'me [(ScopeId, Option<RecArg<'me, 'a>>)],
    indices: &'me [Term<'a>],
}

#[derive(Clone, Copy)]
struct RecArg<'me, 'a> {
    type_idx: usize,
    args:    &'me [ScopeId],
    indices: &'me [Term<'a>],
}

impl<'me, 'temp, 'err, 'a> Check<'me, 'temp, 'err, 'a> {
    pub fn check(elab: &mut Elab<'temp, 'err, 'a>, spec: MutualSpec<'_, 'a>) -> Option<()> {
        let num_types = spec.types.len();
        assert!(num_types > 0);

        let mut level_params = Vec::with_cap_in(spec.levels.len(), elab.alloc);
        for (i, name) in spec.levels.iter().copied().enumerate() {
            level_params.push(elab.alloc.mkl_param(name, i as u32));
        }

        let temp = ArenaPool::tls_get_rec();

        let mut this = Check {
            alloc: elab.alloc,
            temp: &*temp,
            elab,
            spec,
            level_params: level_params.leak(),
            type_globals: Vec::with_cap_in(num_types, &*temp),
            type_global_apps: Vec::with_cap_in(num_types, &*temp),
            indices: Vec::with_cap_in(num_types, &*temp),
            ctor_infos: Vec::new_in(&*temp),
        };

        // @complete: check levels params in types.

        // @complete: check params are types.


        // check specs.
        let mut ind_level = None;
        for (type_idx, spec) in this.spec.types.iter().enumerate() {
            // check type.
            let mut ty = this.elab.lctx.lookup(spec.local).ty;
            let mut indices = Vec::new_in(this.temp);
            while let Some(pi) = this.elab.whnf_forall(ty) {
                // @complete: check indices are types.
                let id = this.elab.lctx.push(pi.kind, pi.name, pi.ty, None);
                indices.push(id);
                ty = pi.val.instantiate(this.alloc.mkt_local(id), this.alloc);
            }

            let global = this.alloc.mkt_global(spec.symbol, this.level_params);

            let mut global_params = global;
            for param in this.spec.params.iter().copied() {
                global_params = this.alloc.mkt_apply(global_params, this.alloc.mkt_local(param));
            }
            let mut global_indices = global_params;
            for index in indices.iter().copied() {
                global_indices = this.alloc.mkt_apply(global_indices, this.alloc.mkt_local(index));
            }

            this.type_globals.push(global);
            this.type_global_apps.push(global_indices);
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
            let mut ty_ctor_infos = Vec::with_cap_in(spec.ctors.len(), this.temp);
            for ctor in spec.ctors.iter().copied() {
                let mut args = Vec::new_in(this.temp);

                // check args.
                let mut ty = ctor.ty;
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
                        let mut args = Vec::new_in(this.temp);
                        while let Some(pi) = this.elab.whnf_forall(ret) {
                            // check positivity.
                            if this.has_ind_occ(pi.ty) {
                                println!("invalid recursion");
                                return None;
                            }
                            ret = pi.val;

                            let id = this.elab.lctx.push(pi.kind, pi.name, pi.ty, None);
                            args.push(id);
                        }
                        let args = args.leak();

                        this.is_valid_inductive_app(ret, None)?
                        .map(|(type_idx, indices)| RecArg { type_idx, args, indices })
                    };

                    if is_rec.is_some() {
                        let rec_ty = pi.ty.replace_app_fun(global_params, this.alloc);
                        let id = this.elab.lctx.push(pi.kind, pi.name, rec_ty, None);
                        args.push((id, is_rec));

                        // ensure rec arg not used.
                        ty = pi.val;
                        if !ty.closed() {
                            println!("error: recursive argument used");
                            return None;
                        }
                    }
                    else {
                        let id = this.elab.lctx.push(pi.kind, pi.name, pi.ty, None);
                        args.push((id, None));

                        ty = pi.val.instantiate(this.alloc.mkt_local(id), this.alloc);
                    }
                }

                // check indices.
                let Some((_, indices)) = this.is_valid_inductive_app(ty, Some((type_idx, spec.local)))? else {
                    println!("error: ctor ret must be the inductive type");
                    return None;
                };

                ty_ctor_infos.push(CtorInfo { args: args.leak(), indices });
            }

            this.ctor_infos.push(ty_ctor_infos);
        }
        let ind_level = ind_level.unwrap();


        // determine elim level.
        let large_elim = {
            // non-prop.
            if ind_level.non_zero() {
                true
            }
            // mutual props aren't LE
            else if this.spec.types.len() > 1 {
                false
            }
            // single inductive type.
            else {
                let ctors = this.spec.types[0].ctors;
                // `False`
                if ctors.len() == 0 {
                    true
                }
                // possibly singleton.
                else if ctors.len() == 1 {
                    let info = &this.ctor_infos[0][0];

                    let mut singleton = true;
                    for (arg, is_rec) in info.args.iter().copied() {
                        // rarg.
                        if is_rec.is_some() {
                            continue;
                        }

                        // narg-direct.
                        for idx in info.indices.iter().copied() {
                            if let Some(local) = idx.try_local() {
                                if local == arg {
                                    continue;
                                }
                            }
                        }

                        // narg-prop.
                        let ty = this.elab.lctx.lookup(arg).ty;
                        let l = this.elab.infer_type_as_sort(ty).unwrap();
                        if l.is_zero() {
                            continue;
                        }

                        singleton = false;
                        break;
                    }
                    singleton
                }
                // too many ctors.
                else {
                    false
                }
            }
        };

        let elim_sort =
            if large_elim {
                this.alloc.mkt_sort(
                    this.alloc.mkl_param(atoms::r, this.level_params.len() as u32))
            }
            else { Term::SORT_0 };


        let mut motives = Vec::with_cap_in(this.spec.types.len(), this.temp);
        for spec_idx in 0..this.spec.types.len() {
            let mp = this.type_global_apps[spec_idx];

            let mut m = elim_sort;
            m = this.alloc.mkt_forall(BinderKind::Explicit, atoms::mp, mp, m);

            for index in this.indices[spec_idx].iter().copied().rev() {
                m = this.elab.lctx.abstract_forall(m, index);
            }

            let name =
                if this.spec.types.len() > 1 {
                    // @temp: sti string stuff.
                    //let name = &this.elab.strings[this.spec.types[spec_idx].name];
                    //this.elab.strings.insert(&format!("M_{}", name))
                    // @todo: shared string table.
                    unimplemented!()
                }
                else { atoms::M };

            let id = this.elab.lctx.push(BinderKind::Explicit, name, m, None);

            motives.push(id);
        }
        let motives = motives;


        // @speed: reserve.
        let mut minors = Vec::new_in(this.temp);
        for spec_idx in 0..this.spec.types.len() {
            let spec = &this.spec.types[spec_idx];
            let m = motives[spec_idx];
            let ctor_infos = &this.ctor_infos[spec_idx];

            for (ctor_idx, ctor) in spec.ctors.iter().copied().enumerate() {
                let info = &ctor_infos[ctor_idx];

                let mut ctor_app = this.alloc.mkt_global(ctor.symbol, this.level_params);
                for (arg, _) in info.args.iter().copied() {
                    ctor_app = this.alloc.mkt_apply(ctor_app, this.alloc.mkt_local(arg));
                }

                let mut ret = this.alloc.mkt_local(m);
                ret = this.alloc.mkt_apps(ret, info.indices);
                ret = this.alloc.mkt_apply(ret, ctor_app);

                let mut minor = ret;
                for (arg, is_rec) in info.args.iter().copied().rev() {
                    if let Some(rec_arg) = is_rec {
                        let mut rec_m = this.alloc.mkt_local(m);
                        rec_m = this.alloc.mkt_apps(rec_m, rec_arg.indices);
                        rec_m = this.alloc.mkt_apply(rec_m, this.alloc.mkt_local(arg));

                        minor = this.alloc.mkt_forall(BinderKind::Explicit, Atom::NULL, rec_m, minor);
                    }
                    // @todo: binder explicit.
                    minor = this.elab.lctx.abstract_forall(minor, arg);
                }

                // @temp: `m_{ctor.name}`.
                let id = this.elab.lctx.push(BinderKind::Explicit, Atom::NULL, minor, None);
                minors.push(id);
            }
        }
        let minors = minors;


        let mut elim_tys = Vec::with_cap_in(this.spec.types.len(), this.temp);
        for spec_idx in 0..this.spec.types.len() {
            let mut ret = this.alloc.mkt_local(motives[spec_idx]);
            for index in this.indices[spec_idx].iter().copied().rev() {
                ret = this.alloc.mkt_apply(ret, this.alloc.mkt_local(index));
            }

            let mut ty =
                this.alloc.mkt_forall(BinderKind::Explicit, atoms::mp,
                    this.type_global_apps[spec_idx],
                    this.alloc.mkt_apply(ret, this.alloc.mkt_bound(BVar { offset: 0 })));

            for index in this.indices[spec_idx].iter().copied().rev() {
                ty = this.elab.lctx.abstract_forall(ty, index);
            }

            for minor in minors.iter().copied().rev() {
                ty = this.elab.lctx.abstract_forall(ty, minor);
            }

            for motive in motives.iter().copied().rev() {
                ty = this.elab.lctx.abstract_forall(ty, motive);
            }

            for param in this.spec.params.iter().copied().rev() {
                ty = this.elab.lctx.abstract_forall(ty, param);
            }

            assert!(ty.closed_no_local_no_ivar());

            println!("{}", this.elab.pp(ty, 80));

            elim_tys.push(ty);
        }


        let mut minors_offset = 0;
        for spec_idx in 0..this.spec.types.len() {
            let ctor_infos = &this.ctor_infos[spec_idx];

            for (i, ctor_info) in ctor_infos.iter().enumerate() {
                // comp_i = λ ps Ms ms as, ms_i as mvs
                let mut comp_ret = this.alloc.mkt_local(minors[minors_offset + i]);

                // (ms_i as mvs)
                for (arg, is_rec) in ctor_info.args.iter().copied() {
                    comp_ret = this.alloc.mkt_apply(comp_ret, this.alloc.mkt_local(arg));

                    // mvs_j  = λ (rs :: Rs), rec_k ps Ms ms rxs (rarg_j rs)
                    if let Some(rec_arg) = is_rec {
                        let rec_k = this.spec.types[rec_arg.type_idx].rec_symbol;

                        // rec_k
                        let mut rec_ret = this.alloc.mkt_global(rec_k, this.level_params);

                        // ps
                        for param in this.spec.params.iter().copied() {
                            rec_ret = this.alloc.mkt_apply(rec_ret, this.alloc.mkt_local(param));
                        }

                        // Ms
                        for motive in motives.iter().copied() {
                            rec_ret = this.alloc.mkt_apply(rec_ret, this.alloc.mkt_local(motive));
                        }

                        // ms
                        for minor in minors.iter().copied() {
                            rec_ret = this.alloc.mkt_apply(rec_ret, this.alloc.mkt_local(minor));
                        }

                        // rxs
                        for index in rec_arg.indices.iter().copied() {
                            rec_ret = this.alloc.mkt_apply(rec_ret, index);
                        }

                        // (rarg_j rs)
                        let mut rec_val = this.alloc.mkt_local(arg);
                        for arg in rec_arg.args.iter().copied() {
                            rec_val = this.alloc.mkt_apply(rec_val, this.alloc.mkt_local(arg));
                        }

                        rec_ret = this.alloc.mkt_apply(rec_ret, rec_val);

                        let mut rec_m = rec_ret;
                        for arg in rec_arg.args.iter().copied().rev() {
                            rec_m = this.elab.lctx.abstract_lambda(rec_m, arg);
                        }

                        comp_ret = this.alloc.mkt_apply(comp_ret, rec_m);
                    }
                }

                let mut comp = comp_ret;

                // as
                for (arg, _) in ctor_info.args.iter().copied().rev() {
                    comp = this.elab.lctx.abstract_lambda(comp, arg);
                }

                // ms
                for minor in minors.iter().copied().rev() {
                    comp = this.elab.lctx.abstract_lambda(comp, minor);
                }

                // Ms
                for motive in motives.iter().copied().rev() {
                    comp = this.elab.lctx.abstract_lambda(comp, motive);
                }

                // ps
                for param in this.spec.params.iter().copied().rev() {
                    comp = this.elab.lctx.abstract_lambda(comp, param);
                }

                assert!(comp.closed_no_local_no_ivar());

                println!("comp_{i} = {}", this.elab.pp(comp, 80));
            }

            minors_offset += ctor_infos.len();
        }

        Some(())
    }

    fn has_ind_occ(&self, t: Term) -> bool {
        t.find(|at, _| {
            let local = at.try_local()?;
            Some(self.spec.types.iter().find(|spec| local == spec.local).is_some())
        }).is_some()
    }

    fn is_valid_inductive_app(&self, app: Term<'a>, ind: Option<(usize, ScopeId)>)
        -> Option<Option<(usize, &'me [Term<'a>])>>
    {
        // find app target.
        let mut target = app;
        let mut args = Vec::new_in(self.temp);
        while let Some(app) = target.try_apply() {
            // check no recursion in arguments.
            if self.has_ind_occ(app.arg) {
                println!("error: invalid recursion");
                return None;
            }

            target = app.fun;
            args.push(app.arg);
        }
        let args = args.leak();

        let Some(local) = target.try_local() else {
            return Some(None);
        };

        // check if target is the inductive type.
        if let Some((type_idx, type_local)) = ind {
            return Some((local == type_local).then_some((type_idx, args)));
        }
        else {
            for (i, spec) in self.spec.types.iter().enumerate() {
                if local == spec.local {
                    return Some(Some((i, args)));
                }
            }
            return Some(None);
        }
    }
}

