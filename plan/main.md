
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
    - everything on elab.
        - put var queries on var id types.
        - general naming cleanup pass.

    - assign term robustness:
        - scope approx.
            - use common ancestor.
            - recursively check `other.ty` -> `ty`.
            - create fresh term var of `ty`.
            - assign to `other`.
        - lambda type check.

    - motive inference.
        - extra args: if their type contains locals that are args to the motive.
        - overapplied.
        - proper `abstract_def_eq`.

    - major gc:
        - consider only returning term from elab.
        - it's not great, what else could be improved?
            - `Compiler`.
            - term pp ergonomics.
            - trace debugging.

    - implicit params.
        - binder rework.

    - more expected type propagation?

    - constant approx.

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

