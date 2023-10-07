
- road map:
    - references.
    - unordered decls & incr.
    - bori.
    - allocation.
    - modules.
    - nat literals.
    - `Of_Nat` and default impls.
    - multi-threading.
    - macros.
    - basic proof inference.
    - crates.


- brck:
    - todo:
        - things to catch:
            - ite.
                - we kinda need to create some locals, huh.
            - error, uninit, etc axioms.
            - ref axioms.
            - jps.
    - generate bbir.
        - next steps:
            - let's start with single jp, no params.
            - let's also not worry about regions during bbir building.
            - but validate that jumps use proper locals.
        - what are we stuck on?
            - well, what needs to be done?
                - fairly simple: convert terms to bbir.
                - the tricky part is that we do kinda need tc, i think.
                - cause we also need to know which values are types.
                - but ig, we only need infer-type and whnf.
                  for infer-type, we can just do an ad-hoc thing in the builder.
                  for whnf, we should be able to abstract that.
                  in fact, whnf is the same across elab, tc, and bc.
                - thing is, we don't really wanna abstract again, like tc does.
            - ok, so:
                - once we need it, move whnf into a separate module.
                - builder will have its own kind of local context.
                  with info about params, mutability, type dependencies, etc.
        - convert ref axioms.
        - def metadata: `is_type`, `is_prop`.
    - during tyck:
        - collect loans.
        - compute region subsets.
            - every reference local has a region.
            - every `Ref::from_*` has a region.
            - `Ref::from_value(Ref::read(r))` is equiv to `Ref::from_ref(r)`.
        - compute cfg.
        - compute liveness.
    - do the thing:
        - thinking compute subsets & liveness.
        - then walk ir. if node "invalidates" loans,
          check that live regions don't require those loans.
    - mutability validation:
        - during tyck. remove from elab-do.
          cause we need to do `&mut x` `x mut` validation in tyck (for simplicity).
          so we might as well validate assignments.
        - `num_local_vars` -> `local_vars(metadata)`.
    - uninit validation.
    - properly handle dependent types.

- todo:
    - address the tech debt.
        - unordered decls, postpone, incr, so we have no excuse to accumulate any more debt.
    - variance.
    - partial functions.
        - we kinda need something to prevent proofs from
          being abused to elide calls to effectful functions.
            - actually, i think that's fine. cause this would only apply
              to tactics or other meta programs.
              as in, the code you write will be executed as written.
            - a function call used in a type isn't executed,
              though we should prevent impure functions from being used
              in types.
            - well, ig the issue would be, if you proved that a variable
              already contains the result of a function call.
              but that would again be covered by disallowing reasoning
              about impure functions.
    - `fn`.


### issues:

- the `Add::R` explosion.
    - aka the associated type blowup.
    - aka this needs fixing.
    - consider `TermKind::Proj`.
        - yeah, seems good.
        - figure out where to reduce projections.
    - we need something that reduces these terms asap.
    - in general, we don't want to reduce asap, cause it can make it harder
      to understand where terms came from.
      here, we may want to record some info (similarly for impl values,
      which are "unfolded" during impl resolution).
    - should be able to do that in `instantiate_ivars`. may still lead to
      pathological cases if the user manually specifies the impl, we'll see.


