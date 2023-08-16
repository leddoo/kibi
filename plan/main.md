
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
        - term printing.
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

