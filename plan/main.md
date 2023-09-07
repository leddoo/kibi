
- road map:
    - basic traits.
    - codegen.
    - nat literals.
    - unordered decls & compiler rework.
    - references.
    - multi-threading.
    - modules.
    - macros.
    - basic proof inference.


- traits:
    - binders:
        - orthogonal to explicit/implicit.
        - if implicit or `_`, does impl resolution.
        - syntax:
            - `<A>` means `<A: Type>`.
            - `<A is Foo + Bar>` means `<A: Type, _: Foo(A), _: Bar(A)>`.

- todo:
    - higher order impls.
    - local impls.
    - the compiler cleanup.
        - sti vec utils.
        - move parse/elab loop & error formatting into library.
        - the `elab_def` situation.
        - string table shared mutation, but not for tok.
        - `SymbolKind::Axiom`.
    - ident -> elab as app with no args.
    - arrow functions.
    - dot-idents.
    - methods.
        - lookup in type, needs `self` arg.
    - partial functions.
    - `fn`.
    - codegen.


- effects:
    - in particular, panics.
    - `fn foo(): B` means `lam foo(_: ()): Io(B)` or something like that.
    - so if you use `fn` in traits, you expect those to potentially panic
      or have other side-effects.
    - using `Pi`, you can make that explicit (or require totality).
    - the IR is going to get pretty nasty though. oh well.
        - actually, that's pretty bad.
        - cause it also breaks `A -> B -> C`.
        - we could just mark the decl as partial.
        - yeah, that seems better.
        - we could still do explicit effects later on.
          for now, `partial` as a catch-all seems fine.


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

