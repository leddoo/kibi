
- road map:
    - lsp.
    - incremental.
    - modules.
    - unordered decls.
    - codegen.
    - nat literals.
    - `Of_Nat` and default impls.
    - references.
    - multi-threading.
    - macros.
    - basic proof inference.
    - crates.


- todo:
    - hover info.
        - impl for:
            - reduce.
            - token.
            - (innermost) expr ty.
        - `Ident(name, token)` -> lookup does token info.
    - lsp stuff:
        - completions.
        - go to definition.
        - document highlights.
    - error resilient parsing.
        - parser skips comment tokens (add) & error tokens.
        - unterminated `/-` is error token and does not consume input until eof.
        - sep-by until terminator, but not if sync point in between.
        - use indentation for recovery of unmatched parens errors.
        - single line strings. (indented, multi-line later)
        - can we get neovim to draw skipped tokens in italics? maybe w/ modifiers.
    - error resilient elab.
        - error to sorry.
        - type unknown for env -> treat as silent error in uses.
    - proper semantic tokens.
    - incremental parse.
        - each item is a `Parse`.
        - if token range dirty, re-parse, otherwise, keep old result.
        - option for non-incr -> items don't start new `Parse`.
    - incremental elab.
        - track dependencies.
        - re-elab if dependencies or item changed.
        - should be able to keep refs into env,
          cause need to rerun if anything used from env changed.

    - errors use `Term`.
    - query semantic tokens: option to split multi-line tokens.
    - maybe always store elab on elab error -> can use term refs.
    - `validate_string`: `>= 0x20`. do we need simd?
    - `vfs::mem`, `vfs::std`.
    - debug tracing.
    - json display: string escapes.
    - vfs directories, create/delete/write.
    - self-reference safety.
    - incremental testing.
        - serialization or hash function.
        - do non-incr compile & compare.
    - compiler: id based functions (alternative to strings).
    - callgraph for:
        - termination checking.
        - find references.
        - "highlight everything that can allocate."
    - better error sources + tests.

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
    - mutual inductive:
        - mutual syntax.
        - add existing inductives to def, for non-strict-pos occ.
    - type annotation.
    - let.
    - named args.
    - explicit args.
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

- cleanup:
    - `SymbolKind::Axiom`.
    - move `assign` into `def_eq_*`.
    - move `instantiate` into `ivars`.
    - `sep_by_ex` takes vec.
    - document inference.

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

