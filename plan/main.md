
- road map:
    - tt elab.
    - interpreter.
    - basic proof inference.
    - mutual inductive.
    - unordered decls.
    - modules.
    - user types.
    - macros.


- todo:
    - global pp.
    - eq impl.
    - naive def unfold.
    - some proofs!
    - def levels.
    - fix kernel bugs: all rules must fail.

    - `fib_iter`.
        - parse it.
        - elab it.
        - interp it.



### backlog:

- cleanup:
    - consistent lifetime names.
    - consistent param order.
    - `tt::Alloc`.
        - arena extension trait instead?
        - proper allocator abstraction might be better -> tracing.

- better errors:
    - simplify types (cheap reductions).
    - merge binders.
    - binder names.
    - `A -> B` for non-dependent funcs.

- sti:
    - rename `GrowingArena` -> `Arena`.
    - arena `alloc_str`
    - string and formatting stuff, write trait.
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

