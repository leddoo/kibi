
- road map:
    - mutual inductive.
    - traits.
    - interpreter.
    - basic proof inference.
    - unordered decls.
    - modules.
    - macros.


- todo: mutual inductive.
    - check.
    - mutual.



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

- features:
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
    - scope approx.
        - use common ancestor.
        - recursively check `other.ty` -> `ty`.
        - create fresh term var of `ty`.
        - assign to `other`.
    - motive inference.
        - over/under-applied. just use some silly example.
    - lambda type check.
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

