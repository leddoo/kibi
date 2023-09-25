
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

- prereqs:
    - tactics & `by`.
    - a better delab.
        - configurable, granular level of detail.
        - "source info" for interaction.
        - support for operators.

- non-prereqs:
    - prelude. we can just use hello.kb.


- plan:
    - mon: tactics.
    - new delab.
    - tue: proof state panel.
    - wed: interactivity.


- todo:
    - tactic info.
        - always include goal.
    - implement tactics.
        - goal.
        - rewrite.


- backlog:
    - tactics:
        - refl.
        - assumption.
        - exact.
        - print.
        - reduce.
        - unfold.
        - induction.
        - cases.

