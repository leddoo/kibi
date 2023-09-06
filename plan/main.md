
- road map:
    - basic traits.
    - nat literals.
    - unordered decls & compiler rework.
    - codegen.
    - references.
    - multi-threading.
    - modules.
    - macros.
    - basic proof inference.


- todo:
    - basic traits.
        - parse. just do inductives for now.
        - instance binder.
        - trait is special symbol?
            - well, we kinda just want it to be a type.
            - but with a flag that it's a trait.
            - remember, can have params, can be instances.
        - then we need impls.
            - that's just a special kind of def.
            - which is registered with the trait -> vec of instances.
            - make sure it doesn't unify with any other impls.
                - what about something like
                  `impl: Foo(Nat)` and
                  `impl T [bar: Bar T]: Foo(bar.type)`?
                  rust complains that `T` isn't "constrained".
        - then we need impl resolution.
            - just linear search for now.


### backlog:

- stuff:
    - trace debugging.
    - interactivity.
    - very basic tactics.
    - executable code.

- sti:
    - string and formatting stuff, write trait.
    - KVec::truncate, clone.
    - reader `revert(n)`, rename `offset -> position`.
    - vec collect.

- features:
    - mutual inductive:
        - mutual syntax.
        - add existing inductives to def, for non-strict-pos occ.
    - type annotation.
    - let.
    - named args.
    - explicit args.
    - `A -> B` syntax.
    - check/print.
    - dot-idents.
    - method call syntax.
    - error to sorry.

- completeness:
    - `is_type_correct`.
        - lambda type check.
    - kernel type checker.
        - use for inductive.
        - env does type check before insertion.
    - level elab: use `.imax` & friends.
    - constant approx.
    - proper `abstract_def_eq`.
        - "key matching": only call `is_def_eq`, if the head symbol matches.
        - and try `syntax_eq` first, common case.
    - parser eof errors.

- cleanup:
    - `SymbolKind::Axiom`.
    - move `assign` into `def_eq_*`.
    - move `instantiate` into `ivars`.
    - `sep_by_ex` takes vec.
    - document inference.
    - `Compiler` and immutability.

- optimization:
    - metadata.
    - custom memory layout.
    - reset lctx after whnf/defeq?
    - pp caching.

- parser:
    - labels.
    - combined match/if.
    - optional do block.

- pp:
    - binder kinds & merging.
    - dedup local names.
    - `A -> B`.
    - config:
        - indent width.
        - args on separate lines.

- elab:
    - var to let.

- macros:
    - figure out compilation order.

- architecture:
    - error resilience.
    - shared data structures & multi-threading.
        - symbol table & namespaces.
        - error context.
        - consider fork/join around ordering points.
          populating symbol table synchronously.
    - more immutability:
        - for lsp and other queries.
        - but would like to compute ad-hoc, cause seems
          like it could require *a lot* of memory.
        - namespaces - they're kinda immutable by default,
          once we're doing ordering.
        - scopes: the single local + parent id seems nice.

