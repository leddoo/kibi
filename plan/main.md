
- road map:
    - do.
    - references.
    - bori.
    - allocation.
    - unordered decls.
    - incremental.
    - modules.
    - nat literals.
    - `Of_Nat` and default impls.
    - multi-threading.
    - macros.
    - basic proof inference.
    - crates.


- todo:
    - assignment valiation: make sure the local is actually a `var`.
      not `let` or something different entirely.
        - lctx cleanup binder xor let thing.
    - tyck.
        - no termination checking yet.
        - use for inductive.
    - brck.
        - region inference.
            - how to handle annotations?
            - how to handle join points, do they use region params?
            - or do we infer regions just before brck?
        - check.
            - liveness & stuff.
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

    - uninit dependent vars on assign.
        - track deps using temp arena & vec for each var.
        - also need to remove deps, hmm.
        - don't keep uninit, if not used.
        - hmm, we don't really want to uninit, unless we need to
          cause you should be able to use the old value to derive
          a new proof.
        - maybe also easy to rewrite stuff that uses bool vars?
    - oh ja, `bite`.
    - generate warnings for unreachable code.
    - fix congr-arg let foo := 42 crash.
    - begin test suite.


### issues:

- the `Add::R` explosion.
    - aka the associated type blowup.
    - aka this needs fixing.
    - consider `TermKind::Proj`.
    - we need something that reduces these terms asap.
    - in general, we don't want to reduce asap, cause it can make it harder
      to understand where terms came from.
      here, we may want to record some info (similarly for impl values,
      which are "unfolded" during impl resolution).
    - should be able to do that in `instantiate_ivars`. may still lead to
      pathological cases if the user manually specifies the impl, we'll see.


