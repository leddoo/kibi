use sti::arena::Arena;
use sti::arena_pool::ArenaPool;
use sti::traits::{CopyIt, FromIn};
use sti::vec::Vec;

use crate::string_table::Atom;
use crate::ast::{ItemId, Ident};
use crate::diagnostics::ElabError;
use crate::env::{SymbolKind, symbol::{IndAxiomKind, IndAxiom}};
use crate::elab::Elaborator;

use super::level::*;
use super::term::*;
use super::ScopeKind;


// @speed: cache mkt_locals.


pub struct MutualSpec<'me, 'a> {
    pub levels: &'me [Ident],
    pub params: &'me [ScopeId],
    pub types: &'me [TypeSpec<'me, 'a>],
    // @todo: better sources.
    pub temp_source: ItemId,
}

pub struct TypeSpec<'me, 'a> {
    pub name: Ident,
    pub symbol: SymbolId,
    pub local: ScopeId,
    pub ctors: &'me [CtorSpec<'a>],
    pub rec_symbol: SymbolId,
}

#[derive(Clone, Copy)]
pub struct CtorSpec<'a> {
    pub name:   Ident,
    pub symbol: SymbolId,
    pub ty:     Term<'a>,
}



#[derive(Clone, Copy, Debug, PartialEq)]
pub enum ElimArgKind {
    Motive,
    Target,
    Postpone,
    Extra,
}

#[derive(Clone, Copy, Debug)]
pub struct ElimInfo<'a> {
    #[allow(dead_code)]
    pub motive: usize,
    pub args: &'a [ElimArgKind],
}

#[derive(Clone, Copy, Debug)]
pub struct InductiveInfo<'a> {
    pub type_former: SymbolId,
    pub elim_info: ElimInfo<'a>,

    pub comp_rules: &'a [Term<'a>],
    pub num_params:  u32,
    pub num_indices: u32,
    pub num_motives: u32,
    pub num_minors:  u32,
    pub min_args_for_reduce: u32,
}


pub struct Check<'me, 'temp, 'c, 'out> {
    alloc: &'out Arena,
    temp: &'me Arena,

    // @temp: @inductive_uses_elab.
    elab: &'me mut Elaborator<'temp, 'c, 'out>,

    spec: MutualSpec<'me, 'out>,

    level_params: &'out [Level<'out>],
    elim_levels: &'out [Level<'out>],
    type_globals: Vec<Term<'out>, &'me Arena>,
    type_global_param_apps: Vec<Term<'out>, &'me Arena>,
    type_global_index_apps: Vec<Term<'out>, &'me Arena>,
    indices: Vec<Vec<ScopeId, &'me Arena>, &'me Arena>,
    ctor_infos: Vec<&'me [CtorInfo<'me, 'out>], &'me Arena>,
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

impl<'me, 'temp, 'c, 'out> Check<'me, 'temp, 'c, 'out> {
    pub fn check(elab: &mut Elaborator<'temp, 'c, 'out>, spec: MutualSpec<'_, 'out>) -> Option<()> {
        let num_types = spec.types.len();
        assert!(num_types > 0);

        let level_params =
            Vec::from_in(elab.alloc,
                spec.levels.copy_it().enumerate()
                .map(|(i, name)|
                     elab.alloc.mkl_param(name.value, i as u32))).leak();

        let temp = ArenaPool::tls_get_rec();

        let mut this = Check {
            alloc: elab.alloc,
            temp: &*temp,
            elab,
            spec,
            level_params,
            elim_levels: level_params,
            type_globals: Vec::with_cap_in(&*temp, num_types),
            type_global_param_apps: Vec::with_cap_in(&*temp, num_types),
            type_global_index_apps: Vec::with_cap_in(&*temp, num_types),
            indices: Vec::with_cap_in(&*temp, num_types),
            ctor_infos: Vec::new_in(&*temp),
        };

        // @complete: check levels params in types.

        // @complete: check params are types.


        // check type formers.
        let mut ind_level = None;
        let mut type_formers = Vec::with_cap_in(this.temp, this.spec.types.len());
        for spec in this.spec.types {
            let mut type_former = this.elab.lctx.lookup(spec.local).ty;

            // check type.
            let mut ty = type_former;
            let mut indices = Vec::new_in(this.temp);
            while let Some(pi) = this.elab.whnf_forall(ty) {
                // @complete: check indices are types.
                let id = this.elab.lctx.push(pi.name, pi.ty, ScopeKind::Binder(pi.kind));
                indices.push(id);
                ty = pi.val.instantiate(this.alloc.mkt_local(id, TERM_SOURCE_NONE), this.alloc);
            }

            let global = this.alloc.mkt_global(spec.symbol, this.level_params, TERM_SOURCE_NONE);

            let mut global_params = global;
            for param in this.spec.params.iter().copied() {
                global_params = this.alloc.mkt_apply(global_params, this.alloc.mkt_local(param, TERM_SOURCE_NONE), TERM_SOURCE_NONE);
            }
            let mut global_indices = global_params;
            for index in indices.iter().copied() {
                global_indices = this.alloc.mkt_apply(global_indices, this.alloc.mkt_local(index, TERM_SOURCE_NONE), TERM_SOURCE_NONE);
            }

            for param in this.spec.params.iter().copied().rev() {
                type_former = this.elab.lctx.abstract_forall(type_former, param, TERM_SOURCE_NONE, this.alloc);
            }
            assert!(type_former.closed_no_local_no_ivar());
            type_formers.push(type_former);

            this.type_globals.push(global);
            this.type_global_param_apps.push(global_params);
            this.type_global_index_apps.push(global_indices);
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
        }
        let ind_level = ind_level.unwrap();


        // make params/indices implicit for ctor/rec types.
        for param in this.spec.params.iter().copied() {
            this.elab.lctx.lookup_mut(param).kind = ScopeKind::Binder(BinderKind::Implicit);
        }
        for indices in this.indices.iter() {
            for index in indices.iter().copied() {
                this.elab.lctx.lookup_mut(index).kind = ScopeKind::Binder(BinderKind::Implicit);
            }
        }


        // check ctors.
        let mut ctor_types = Vec::with_cap_in(this.temp, this.spec.types.len());
        for (spec_idx, spec) in this.spec.types.iter().enumerate() {
            // check ctors.
            let mut ty_ctor_infos = Vec::with_cap_in(this.temp, spec.ctors.len());
            let mut ty_ctor_types = Vec::with_cap_in(this.temp, spec.ctors.len());
            for ctor in spec.ctors.iter().copied() {
                let mut args = Vec::new_in(this.temp);

                // check args.
                let mut ty = ctor.ty;
                while let Some(pi) = this.elab.whnf_forall(ty) {
                    // check level.
                    let Some(arg_level) = this.elab.infer_type_as_sort(pi.ty) else {
                        eprintln!("this shouldn't have happened...");
                        return None;
                    };

                    if !ind_level.is_zero() {
                        if let (Some(arg_level), Some(ind_level)) = (arg_level.try_nat(), ind_level.try_nat()) {
                            if arg_level > ind_level {
                                this.elab.error(this.spec.temp_source, ElabError::CtorArgLevelTooLarge);
                                return None;
                            }
                        }
                        else {
                            this.elab.error(this.spec.temp_source, ElabError::TempCtorArgLevelCouldBeTooLarge);
                        }
                    }

                    // check recursion.
                    let is_rec = {
                        let mut ret = pi.ty;
                        let mut args = Vec::new_in(this.temp);
                        while let Some(pi) = this.elab.whnf_forall(ret) {
                            // check positivity.
                            if this.has_ind_occ(pi.ty) {
                                this.elab.error(this.spec.temp_source, ElabError::CtorInvalidRecursion);
                                return None;
                            }
                            ret = pi.val;

                            let id = this.elab.lctx.push(pi.name, pi.ty, ScopeKind::Binder(pi.kind));
                            args.push(id);
                        }
                        let args = args.leak();

                        this.is_valid_inductive_app(ret, None)?
                        .map(|(type_idx, indices)| RecArg { type_idx, args, indices })
                    };

                    if is_rec.is_some() {
                        let ind = this.type_global_param_apps[spec_idx];
                        let rec_ty = pi.ty.replace_app_fun(ind, this.alloc);
                        let id = this.elab.lctx.push(pi.name, rec_ty, ScopeKind::Binder(pi.kind));
                        args.push((id, is_rec));

                        // ensure rec arg not used.
                        ty = pi.val;
                        if !ty.closed() {
                            this.elab.error(this.spec.temp_source, ElabError::CtorRecArgUsed);
                            return None;
                        }
                    }
                    else {
                        let id = this.elab.lctx.push(pi.name, pi.ty, ScopeKind::Binder(pi.kind));
                        args.push((id, None));

                        ty = pi.val.instantiate(this.alloc.mkt_local(id, TERM_SOURCE_NONE), this.alloc);
                    }
                }

                // check indices.
                let Some((_, indices)) = this.is_valid_inductive_app(ty, Some((spec_idx, spec.local)))? else {
                    this.elab.error(this.spec.temp_source, ElabError::CtorNotRetSelf);
                    return None;
                };


                let mut ctor_type = ctor.ty;
                ctor_type = ctor_type.replace(this.alloc, |at, _, _| {
                    let local = at.try_local()?;
                    (local == spec.local).then_some(this.type_global_param_apps[spec_idx])
                });
                for param in this.spec.params.iter().copied().rev() {
                    ctor_type = this.elab.lctx.abstract_forall(ctor_type, param, TERM_SOURCE_NONE, this.alloc);
                }
                assert!(ctor_type.closed_no_local_no_ivar());

                ty_ctor_infos.push(CtorInfo { args: args.leak(), indices });
                ty_ctor_types.push(ctor_type);
            }

            this.ctor_infos.push(ty_ctor_infos.leak());
            ctor_types.push(ty_ctor_types.leak());
        }


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
                let r = this.alloc.mkl_param(atoms::r, this.level_params.len() as u32);

                this.elim_levels =
                    Vec::from_in(this.alloc,
                        this.level_params.copy_it()
                        .chain([r])
                    ).leak();

                this.alloc.mkt_sort(r, TERM_SOURCE_NONE)
            }
            else { Term::SORT_0 };


        let mut motives = Vec::with_cap_in(this.temp, this.spec.types.len());
        for spec_idx in 0..this.spec.types.len() {
            let mp = this.type_global_index_apps[spec_idx];

            let mut m = elim_sort;
            m = this.alloc.mkt_forall(BinderKind::Explicit, atoms::mp, mp, m, TERM_SOURCE_NONE);

            for index in this.indices[spec_idx].iter().copied().rev() {
                m = this.elab.lctx.abstract_forall(m, index, TERM_SOURCE_NONE, this.alloc);
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

            let id = this.elab.lctx.push(name, m, ScopeKind::Binder(BinderKind::Implicit));

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

                let mut ctor_app = this.alloc.mkt_global(ctor.symbol, this.level_params, TERM_SOURCE_NONE);
                for param in this.spec.params.iter().copied() {
                    ctor_app = this.alloc.mkt_apply(ctor_app, this.alloc.mkt_local(param, TERM_SOURCE_NONE), TERM_SOURCE_NONE);
                }
                for (arg, _) in info.args.iter().copied() {
                    ctor_app = this.alloc.mkt_apply(ctor_app, this.alloc.mkt_local(arg, TERM_SOURCE_NONE), TERM_SOURCE_NONE);
                }

                let mut ret = this.alloc.mkt_local(m, TERM_SOURCE_NONE);
                ret = this.alloc.mkt_apps(ret, info.indices, TERM_SOURCE_NONE);
                ret = this.alloc.mkt_apply(ret, ctor_app, TERM_SOURCE_NONE);

                let mut minor = ret;
                for (arg, is_rec) in info.args.iter().copied().rev() {
                    if let Some(rec_arg) = is_rec {
                        let mut rec_m = this.alloc.mkt_local(m, TERM_SOURCE_NONE);
                        rec_m = this.alloc.mkt_apps(rec_m, rec_arg.indices, TERM_SOURCE_NONE);
                        rec_m = this.alloc.mkt_apply(rec_m, this.alloc.mkt_local(arg, TERM_SOURCE_NONE), TERM_SOURCE_NONE);

                        minor = this.alloc.mkt_forall(BinderKind::Explicit, Atom::NULL, rec_m, minor, TERM_SOURCE_NONE);
                    }
                    // @todo: binder explicit.
                    minor = this.elab.lctx.abstract_forall(minor, arg, TERM_SOURCE_NONE, this.alloc);
                }

                // @temp: `m_{ctor.name}`.
                let id = this.elab.lctx.push(Atom::NULL, minor, ScopeKind::Binder(BinderKind::Explicit));
                minors.push(id);
            }
        }
        let minors = minors;


        let mut elim_types = Vec::with_cap_in(this.temp, this.spec.types.len());
        let mut elim_infos = Vec::with_cap_in(this.temp, this.spec.types.len());
        for spec_idx in 0..this.spec.types.len() {
            let mut motive_pos = None;
            let mut elim_arg_kinds = Vec::new_in(this.temp);

            let mut ret = this.alloc.mkt_local(motives[spec_idx], TERM_SOURCE_NONE);
            for index in this.indices[spec_idx].iter().copied().rev() {
                ret = this.alloc.mkt_apply(ret, this.alloc.mkt_local(index, TERM_SOURCE_NONE), TERM_SOURCE_NONE);
            }

            let mut ty =
                this.alloc.mkt_forall(BinderKind::Explicit, atoms::mp,
                    this.type_global_index_apps[spec_idx],
                    this.alloc.mkt_apply(ret, this.alloc.mkt_bound(BVar { offset: 0 }, TERM_SOURCE_NONE), TERM_SOURCE_NONE),
                    TERM_SOURCE_NONE);
            elim_arg_kinds.push(ElimArgKind::Target);

            for index in this.indices[spec_idx].iter().copied().rev() {
                ty = this.elab.lctx.abstract_forall(ty, index, TERM_SOURCE_NONE, this.alloc);
                elim_arg_kinds.push(ElimArgKind::Target);
            }

            for minor in minors.iter().copied().rev() {
                ty = this.elab.lctx.abstract_forall(ty, minor, TERM_SOURCE_NONE, this.alloc);
                elim_arg_kinds.push(ElimArgKind::Postpone);
            }

            for (i, motive) in motives.iter().copied().enumerate().rev() {
                ty = this.elab.lctx.abstract_forall(ty, motive, TERM_SOURCE_NONE, this.alloc);
                if i == spec_idx {
                    motive_pos = Some(elim_arg_kinds.len());
                    elim_arg_kinds.push(ElimArgKind::Motive);
                }
                else {
                    elim_arg_kinds.push(ElimArgKind::Postpone);
                }
            }

            for param in this.spec.params.iter().copied().rev() {
                ty = this.elab.lctx.abstract_forall(ty, param, TERM_SOURCE_NONE, this.alloc);
                elim_arg_kinds.push(ElimArgKind::Postpone);
            }

            assert!(ty.closed_no_local_no_ivar());

            let motive_pos = (elim_arg_kinds.len() - 1) - motive_pos.unwrap();
            elim_arg_kinds.reverse();

            elim_types.push(ty);
            elim_infos.push(ElimInfo {
                motive: motive_pos,
                args: elim_arg_kinds.clone_in(this.alloc).leak(),
            });
        }
        let elim_types = elim_types;
        let elim_infos = elim_infos;


        let mut comp_rules: Vec<&'out [Term<'out>], _> = Vec::with_cap_in(this.alloc, this.spec.types.len());
        let mut minors_offset = 0;
        for spec_idx in 0..this.spec.types.len() {
            let ctor_infos = &this.ctor_infos[spec_idx];

            let mut spec_rules = Vec::with_cap_in(this.alloc, ctor_infos.len());
            for (i, ctor_info) in ctor_infos.iter().enumerate() {
                // comp_i = λ ps Ms ms as, ms_i as mvs
                let mut comp_ret = this.alloc.mkt_local(minors[minors_offset + i], TERM_SOURCE_NONE);

                // (ms_i as mvs)
                for (arg, is_rec) in ctor_info.args.iter().copied() {
                    comp_ret = this.alloc.mkt_apply(comp_ret, this.alloc.mkt_local(arg, TERM_SOURCE_NONE), TERM_SOURCE_NONE);

                    // mvs_j  = λ (rs :: Rs), rec_k ps Ms ms rxs (rarg_j rs)
                    if let Some(rec_arg) = is_rec {
                        let rec_k = this.spec.types[rec_arg.type_idx].rec_symbol;

                        // rec_k
                        let mut rec_ret = this.alloc.mkt_global(rec_k, this.elim_levels, TERM_SOURCE_NONE);

                        // ps
                        for param in this.spec.params.iter().copied() {
                            rec_ret = this.alloc.mkt_apply(rec_ret, this.alloc.mkt_local(param, TERM_SOURCE_NONE), TERM_SOURCE_NONE);
                        }

                        // Ms
                        for motive in motives.iter().copied() {
                            rec_ret = this.alloc.mkt_apply(rec_ret, this.alloc.mkt_local(motive, TERM_SOURCE_NONE), TERM_SOURCE_NONE);
                        }

                        // ms
                        for minor in minors.iter().copied() {
                            rec_ret = this.alloc.mkt_apply(rec_ret, this.alloc.mkt_local(minor, TERM_SOURCE_NONE), TERM_SOURCE_NONE);
                        }

                        // rxs
                        for index in rec_arg.indices.iter().copied() {
                            rec_ret = this.alloc.mkt_apply(rec_ret, index, TERM_SOURCE_NONE);
                        }

                        // (rarg_j rs)
                        let mut rec_val = this.alloc.mkt_local(arg, TERM_SOURCE_NONE);
                        for arg in rec_arg.args.iter().copied() {
                            rec_val = this.alloc.mkt_apply(rec_val, this.alloc.mkt_local(arg, TERM_SOURCE_NONE), TERM_SOURCE_NONE);
                        }

                        rec_ret = this.alloc.mkt_apply(rec_ret, rec_val, TERM_SOURCE_NONE);

                        let mut rec_m = rec_ret;
                        for arg in rec_arg.args.iter().copied().rev() {
                            rec_m = this.elab.lctx.abstract_lambda(rec_m, arg, TERM_SOURCE_NONE, this.alloc);
                        }

                        comp_ret = this.alloc.mkt_apply(comp_ret, rec_m, TERM_SOURCE_NONE);
                    }
                }

                let mut comp = comp_ret;

                // as
                for (arg, _) in ctor_info.args.iter().copied().rev() {
                    comp = this.elab.lctx.abstract_lambda(comp, arg, TERM_SOURCE_NONE, this.alloc);
                }

                // ms
                for minor in minors.iter().copied().rev() {
                    comp = this.elab.lctx.abstract_lambda(comp, minor, TERM_SOURCE_NONE, this.alloc);
                }

                // Ms
                for motive in motives.iter().copied().rev() {
                    comp = this.elab.lctx.abstract_lambda(comp, motive, TERM_SOURCE_NONE, this.alloc);
                }

                // ps
                for param in this.spec.params.iter().copied().rev() {
                    comp = this.elab.lctx.abstract_lambda(comp, param, TERM_SOURCE_NONE, this.alloc);
                }

                assert!(comp.closed_no_local_no_ivar());

                spec_rules.push(comp);
            }

            minors_offset += ctor_infos.len();
            comp_rules.push(spec_rules.leak());
        }


        let mut infos = Vec::with_cap_in(this.alloc, this.spec.types.len());
        for (spec_idx, spec) in this.spec.types.iter().enumerate() {
            let elim_info  = elim_infos[spec_idx];
            let comp_rules = comp_rules[spec_idx];
            infos.push(InductiveInfo {
                type_former: spec.symbol,
                elim_info,
                comp_rules,
                num_params:  this.spec.params.len() as u32,
                num_indices: this.indices[spec_idx].len() as u32,
                num_motives: motives.len() as u32,
                num_minors:  minors.len() as u32,
                min_args_for_reduce: elim_info.args.len() as u32,
            });
        }
        let infos = infos.leak();

        // define symbol.
        for (spec_idx, spec) in this.spec.types.iter().enumerate() {
            let info = &infos[spec_idx];
            let ctor_types = &ctor_types[spec_idx];

            this.elab.env.resolve_pending(spec.symbol, SymbolKind::IndAxiom(IndAxiom {
                kind: IndAxiomKind::TypeFormer,
                info,
                num_levels: this.level_params.len(),
                ty: type_formers[spec_idx],
                mutual_infos: infos,
            }));

            for (ctor_idx, ctor) in spec.ctors.iter().enumerate() {
                this.elab.env.resolve_pending(ctor.symbol, SymbolKind::IndAxiom(IndAxiom {
                    kind: IndAxiomKind::Constructor(ctor_idx as u32),
                    info,
                    num_levels: this.level_params.len(),
                    ty: ctor_types[ctor_idx],
                    mutual_infos: infos,
                }));
            }

            this.elab.env.resolve_pending(spec.rec_symbol, SymbolKind::IndAxiom(IndAxiom {
                kind: IndAxiomKind::Eliminator,
                info,
                num_levels: this.elim_levels.len(),
                ty: elim_types[spec_idx],
                mutual_infos: infos,
            }));
        }

        Some(())
    }

    fn has_ind_occ(&self, t: Term) -> bool {
        t.find(|at, _| {
            let local = at.try_local()?;
            Some(self.spec.types.iter().find(|spec| local == spec.local).is_some())
        }).is_some()
    }

    fn is_valid_inductive_app(&mut self, app: Term<'out>, ind: Option<(usize, ScopeId)>)
        -> Option<Option<(usize, &'me [Term<'out>])>>
    {
        // find app target.
        let mut target = app;
        let mut args = Vec::new_in(self.temp);
        while let Some(app) = target.try_apply() {
            // check no recursion in arguments.
            if self.has_ind_occ(app.arg) {
                self.elab.error(self.spec.temp_source, ElabError::CtorInvalidRecursion);
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

