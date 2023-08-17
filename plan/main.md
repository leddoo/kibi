
- road map:
    - tt elab.
    - interpreter.
    - basic proof inference.
    - unordered decls.
    - modules.
    - user types.
    - macros.


- fp-non-fp:
    - `def`s are math definitions.
        - must not have side effects,
        - must be total (incl WF).
    - for now, just generate code for fp code too.
    - for now, just generate a term for non-fp code too.
        - incl aux defs.
    - actually, we would like to avoid non-fp terms, where possible.
        - but i don't really know how.
        - could do terms for `def`s, and code for `fn`s.
        - issue is just, still need the ability to gen term for `fn` for extended checking.
          and need lctx with locals for type inference/checking.
        - could return (some kind of) `None` for the term.
          and then use `None` as the value in lctx.
        - we pretty much only care about locals, their types, and their (opt) values.


- todo:
    - error messages.
        - elab errors.
            - pp types, store `pp:DocRef<'err>`s.
        - prettier printing.
            - headline, separation.
            - 3 source lines.
            - source line/col.
    - fix kernel bugs: all rules must fail.
    - def levels.
    - def unfold.
    - `fib_iter`.



### backlog:

- sti:
    - Vec::truncate track caller.
    - KVec::truncate, clone.
    - swiss table.

- features:
    - implicit params.
        - new binder syntax.
        - binder info.
    - dot-idents.
    - method call syntax.

- parser:
    - labels.
    - combined match/if.
    - optional do block.

- elab:
    - level inference.
        - ivars.
    - term inference.
    - motive inference.
    - var to let.

- term pretty printer:
    - group binders.
    - binder names.
    - config:
        - indent width.
        - args on separate lines.

- macros:
    - figure out compilation order.

- architecture:
    - error resilience.
        - `ax_sorry`.
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

- optimization:
    - `Term::hash` for faster `syntax_eq`.

