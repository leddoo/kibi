
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
    - compute region subset relation.
    - compute liveness.
    - do the brck thing.
    - bbir validation.
        - `out` is `in` of successors.
        - `in` of entry is empty, `out` of `ret` block is empty.
        - stack size is 0 on bb entry/exit.
        - stack doesn't underflow.
    - stuff:
        - faster ivar assignment restore: linked list of latest assignment.
          store head, then walk list and clear values until reach old head.
          could combine with "assignment index" for inst cache.
          though that would be linear again, so flush would prob be simpler.
          well, flush is linear too, cause hash map, unless create new empty one.
        - always gen jp for `do`, but only arg if not unit, otherwise return unitmk.
        - incr:
            - env proxy (or just change the env api),
              separate functions for accessing type and value for more granularity.
              add task to hash set on symbol.
                - should prob just change env api. then lsp queries might also "just work".
            - thinking do use generational indices and keep it simple.
              so basically the current data structures but "mutable",
              and custom/simple dependency tracking for state (env/traits/impls).
            - might want some “env scope” object for imports,
              or import set is part of cache key for queries.
    - stmt source info.
    - mutability validation.
    - uninit validation.
    - properly handle dependent types.
    - ite expr: make let binding, so we don't need to mess with vars.
    - def metadata: `is_type`, `is_prop`.
    - sti rev better errors.

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


