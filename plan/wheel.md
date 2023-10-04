
- what:
    - interactive proof assistant.
    - using tactics in a `by` expr.
    - visualize the goals.
    - ability to "just explore":
        - un-/fold definitions.
        - apply theorems and make assumptions without a derivation (aka sorry).
        - apply reductions, but also incrementally, not just whnf & reduce.
    - so mostly lean's pa, but with a focus on interaction in the proof state panel.
    - delab control.


- todo:
    - when/how to abstract locals?
    - info panel.
        - `exists_elim <local>`.
        - inner window size?
            - `vim.api.nvim_call_function("getwininfo", {winid=...})`
    - the `Add::R` issue.
    - `rw` doesn't find `Nat::add_succ` in `Nat::succ((k + a)) = (Nat::succ(k) + b) -> a = b`
    - delab.
        - "source info".
        - don't pp in elab.
        - add & eq.
        - hide implicit params.
            - well, we need infer type...
            - thinking use type checker, but without validation.
            - hmm, but that doesn't support ivars.
            - yikes.
            - well, elab it is. whatever it takes.
              we'll need to figure something out to make that less horrible after the jam.


- backlog:
    - tactics:
        - assumption.
        - exact.
        - print.
        - reduce.
        - unfold.
        - induction.
        - cases.
    - a better delab.
        - configurable, granular level of detail.
        - "source info" for interaction.
        - support for operators.

