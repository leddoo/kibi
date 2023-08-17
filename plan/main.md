
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
    - better pp:
        - rm vec.
        - generic layout.
    - term pp.
    - error messages.
        - elab errors.
            - 1) we should probably have `'err` and copy all error
                 related data into an error arena.
                - cause `'a` prevents us from having temporary arenas.
                - we may also want a `&ErrorCtx<'err>`.
                - we'd perhaps also want `'env: 'a`.
            - 2) thinking we don't want to clone the lctx & terms.
                - would need to deep clone the entire lctx due to `'e`.
                - annotated `pp::Doc`s seem fine.
                - we'll worry about the whole introspection thing later.
    - fix kernel bugs: all rules must fail.
    - def levels.
    - def unfold.
    - method call syntax.
    - dot-idents.
    - level inference.
        - ivars.
    - term inference.
    - error resilience.
        - `ax_sorry`.
    - implicit params.
        - new binder syntax.
        - binder info.
    - motive inference.
    - var to let.
    - `fib_iter`.


    - stuff:
        - more immutability:
            - for lsp and other queries.
            - but would like to compute ad-hoc, cause seems
              like it could require *a lot* of memory.
            - namespaces - they're kinda immutable by default,
              once we're doing ordering.
            - scopes: the single local + parent id seems nice.


    - sti:
        - Vec::truncate track caller.
        - KVec::truncate, clone.
        - swiss table.


- backlog:
    - `Term::hash` for faster `syntax_eq`.
    - fix number parsing: `1.a` not `"1." "a"`.
    - parser:
        - labels.
        - combined match/if.
        - optional do block.
    - macros:
        - figure out compilation order.

