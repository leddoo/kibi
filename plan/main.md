
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
    - robustness:
        - var = term: check locals in term var's lctx.
        - var = var: check lctx is prefix & constrain.
    - infer locals:
        - when popping `x`, `?n -> ?m(x)`.
        - what invariants do we actually care about?
            - we wanna make sure, the popped local can't re-appear.
            - that's kinda it, i think.
            - for the returned term, instantiate it, so the local gets abstracted.
            - then we need to make sure there are no unassigned term vars,
              that have the local in their scope -> `?n -> ?m(x)`.
                - for now, we can just walk the entire ictx.
                - maybe we can be smarter about that somehow.
            - immutable lctx does have the advantage that we can't accidentally
              abstract a local later, cause ids are unique.
              -> docs, cause important. incl "temp locals" in tyctx.

    - implicit params.
        - binder rework.

    - motive inference.

    - inference robustness:
        - do term vars need a lctx?
        - occurs check.

    - document inference.

    - type checking:
        - review tt rules & validate in `infer_type`.
        - run before insert into env.

    - `Compiler`.
        - and immutability.

    - pp opt.

    - `fib_iter`.
        - parse it.
        - elab it.
        - interp it.



### backlog:

- sti:
    - kvec truncate.

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

