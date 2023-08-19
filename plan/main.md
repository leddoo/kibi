
- road map:
    - tt elab.
    - interpreter.
    - basic proof inference.
    - mutual inductive.
    - unordered decls.
    - modules.
    - user types.
    - macros.

32 B, rounding:    3.826s,  9,142,401,936 B
32 B, no rounding: 3.882s,  9,142,393,080 B  +1.4%   -0.0% (-8856 B)
40 B, rounding:    4.301s, 13,713,564,032 B
40 B, no rounding: 4.145s, 11,427,974,104 B  -3.6%  -16.7% (-2.3 GB)

- todo:
    - cleanup:
        - closed checks.
        - type correct checks (`infer_type.unwrap(): Sort(l)`)
        - level list = `&'a[LevelRef<'a>]`.
        - `@temp`s.
        - namespace == symbol.
            - so we can always derive a unique name.
            - ig hidden namespaces (symbols in fn bodies) need special names then.
        - consistent lifetime names.
        - consistent param order.
        - `tt::Alloc`.
            - arena extension trait instead?
            - proper allocator abstraction might be better -> tracing.
    - robustness:
        - fix kernel bugs: all rules must fail.
        - kernel type checking.
        - debug mode consistency checks
          (check well types & type is sort).

    - inference:
        - levels.
        - terms in types.
        - motives.
        - implicit params.

    - `fib_iter`.
        - parse it.
        - elab it.
        - interp it.



### backlog:

- better errors:
    - simplify types (cheap reductions).
    - merge binders.
    - binder names.
    - `A -> B` for non-dependent funcs.

- sti:
    - string and formatting stuff, write trait.
    - KVec::truncate, clone.

- features:
    - eq rec.
    - axioms & `ax_sorry`.
    - `A -> B` syntax.
    - print.
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

