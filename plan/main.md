
- road map:
    - references.
    - bori.
    - unordered decls & incr.
    - allocation.
    - modules.
    - nat literals.
    - `Of_Nat` and default impls.
    - multi-threading.
    - macros.
    - basic proof inference.
    - crates.


- todo:
    - brck.
        - summarize baby steps article.
        - plan impl. what data from `elab_do`/`tyck` do we need?
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
    - we need something that reduces these terms asap.
    - in general, we don't want to reduce asap, cause it can make it harder
      to understand where terms came from.
      here, we may want to record some info (similarly for impl values,
      which are "unfolded" during impl resolution).
    - should be able to do that in `instantiate_ivars`. may still lead to
      pathological cases if the user manually specifies the impl, we'll see.


