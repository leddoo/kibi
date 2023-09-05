
- road map:
    - robustness.
    - basic traits.
    - nat literals.
    - unordered decls & compiler rework.
    - codegen.
    - references.
    - multi-threading.
    - modules.
    - macros.
    - basic proof inference.


- todo: robustness.
    - elab-elim:
        - under-applied: `Nat::add`.
        - over-applied: `Array::get`.
    - `is_def_eq`:
        - lambda type check.
        - app expected type propagation.
    - scope approx.
        - use common ancestor.
        - recursively check `other.ty` -> `ty`.
        - create fresh term var of `ty`.
        - assign to `other`.
    - `SymbolKind::Axiom`.
    - kernel type checker.
        - use for inductive.
        - env does type check before insertion.


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
    - level elab: use `.imax` & friends.
    - constant approx.
    - proper `abstract_def_eq`.
    - parser eof errors.

- cleanup:
    - use arena for temp vecs.
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

