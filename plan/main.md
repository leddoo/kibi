
- road map:
    - lsp.
    - incremental.
    - modules.
    - unordered decls.
    - codegen.
    - nat literals.
    - references.
    - multi-threading.
    - macros.
    - basic proof inference.
    - crates.


- compiler rework.
    - don't expose `ParseId`. instead have opaque `ExprSource`, `TermSource`, etc.
    - query functions either call update (but what about the changes),
      or require compiler to be up-to-date (panic if not).
        - could also keep an internal queue of `Delta`s.
        - hmm, or it could be modal. in incremental mode, you have to
          call update (to get the deltas) before making queries (else panic).
          and otherwise, query functions lazily update the compiler state.

- todo:
    - `parse_datas` to reduce leakage. free prev source parses.
    - lsp document sync.
    - lsp semantic tokens.
    - elab.
    - lsp hover info.
    - incremental parse.
        - each item is a `Parse`.
        - if token range dirty, re-parse, otherwise, keep old result.
        - option for non-incr -> items don't start new `Parse`.
    - incremental elab.
        - track dependencies.
        - re-elab if dependencies or item changed.

    - `vfs::mem`, `vfs::std`.
    - don't `print!`.
        - sti.
        - spall:
            - support non-init (drop everything).
            - counters & drop util w/ callback for debugging.
        - debug tracing.
    - json display: string escapes.
    - vfs directories, create/delete/write.
    - self-reference safety.
    - incremental testing.
        - serialization or hash function.
        - do non-incr compile & compare.
    - compiler: id based functions (alternative to strings).

    - some syntax sugar for fun & profit (arrow, eq, add).

    - cleanup.
        - `SymbolKind::Axiom`.
        - proper errors for elab stuff.

    - ident -> elab as app with no args.
    - arrow functions.
    - dot-idents.
    - methods.
        - lookup in type, needs `self` arg.
    - partial functions.
    - `fn`.
    - codegen.


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

