
- road map:
    - tt elab.
    - interpreter.
    - basic proof inference.
    - mutual inductive.
    - unordered decls.
    - modules.
    - user types.
    - macros.


motive inference:
```

under applied:

def silly: Pi(n: Nat) -> n = n :=
    Nat::rec(_, .refl(0), lam n _ => .refl(n.succ))


elab: Nat::rec(_, .refl(0), lam n _ => .refl(n.succ))

expected = Pi(n: Nat) -> Eq(Nat, n, n)

result    = Nat::rec.{?1}
result_ty = Pi(M: Nat -> Sort(?1), mz: M(0), ms: Pi(n: Nat, ih: M(n)) -> M(n.succ), n: Nat) -> M(n)

arg `_` -> motive ?m: Nat -> Sort(?1)
result    = Nat::rec.{?1}(?m)
result_ty = Pi(mz: ?m(0), ms: Pi(n: Nat, ih: ?m(n)) -> ?m(n.succ), n: Nat) -> ?m(n)

arg `.refl(0)`
-- hmm, don't know expected type, so can't resolve the dot-ident.
-- maybe we should defer elaboration of minor premises, until we know the motive?
-- that appears to be what lean does, too.
-> ?mz: ?m(0)
result    = Nat::rec.{?1}(?m, ?mz)
result_ty = Pi(ms: Pi(n: Nat, ih: ?m(n)) -> ?m(n.succ), n: Nat) -> ?m(n)

arg `lam n _ => .refl(n.succ)`
-> ?ms: Pi(n: Nat, ih: ?m(n)) -> ?m(n.succ)
result    = Nat::rec.{?1}(?m, ?mz, ?ms)
result_ty = Pi(n: Nat) -> ?m(n)

done with args.

expected  = Pi(n: Nat) -> Eq(Nat, n, n)
result_ty = Pi(n: Nat) -> ?m(n)

ig, technically, we could just unify with the expected type in this case.

we'd have `?m(%n) =?= Eq(Nat, %n, %n)`, which lambda inference should be able to figure out.
though it may be harder to generate error messages, idk.
let's see the over applied case.



def Nat::add_comm (a b: Nat): a + b = b + a :=
    Nat::rec(
        lam(a: Nat) => Pi(b: nat) -> a + b = b + a,
        lam(b: Nat) => Nat::zero_add(b),
        lam(a: Nat, ih: Pi(b: Nat) -> a + b = b + a, b: Nat): a.succ + b = b + a.succ =>
            -- rhs is (b + a).succ
            -- lhs can be rewritten with Nat::succ_add
            -- whatever, that's not what matters now.
        a)

def Nat::add_comm (a b: Nat): a + b = b + a :=
    Nat::rec(_, lam b => sorry, lam a ih b => sorry, a, b)

expected = a + b = b + a

result    = Nat::rec.{?1}
result_ty = Pi(M: Nat -> Sort(?1), mz: M(0), ms: Pi(n: Nat, ih: M(n)) -> M(n.succ), n: Nat) -> M(n)

arg `_` -> motive ?m: Nat -> Sort(?1)
result    = Nat::rec.{?1}(?m)
result_ty = Pi(mz: ?m(0), ms: Pi(n: Nat, ih: ?m(n)) -> ?m(n.succ), n: Nat) -> ?m(n)

arg `lam b => sorry`
-> ?mz: ?m(0)
result    = Nat::rec.{?1}(?m, ?mz)
result_ty = Pi(ms: Pi(n: Nat, ih: ?m(n)) -> ?m(n.succ), n: Nat) -> ?m(n)

arg `lam a ih b => sorry`
-> ?ms: Pi(n: Nat, ih: ?m(n)) -> ?m(n.succ)
result    = Nat::rec.{?1}(?m, ?mz, ?ms)
result_ty = Pi(n: Nat) -> ?m(n)

arg `a` -> target ~ elab.
-> %a
result    = Nat::rec.{?1}(?m, ?mz, ?ms, %a)
result_ty = ?m(%a)

stop cause ty isn't a Pi anymore.

args left: `b`

expected  = a + b = b + a
result_ty = ?m(%a)

so here, we need to elab the remaining arg `b`,
and revert it from the expected type.

then we get:

result = Nat::rec.{?1}(?m, ?mz, ?ms, %a, %b)

expected  = Pi(b: Nat) -> a + b = b + a
result_ty = ?m(%a, %b)

and again, it would seem like we could just unify those.



ah, but that would not be the case, if a/b weren't locals, i think.

example: 2+2 = 4 := Nat::rec(_, .refl(0), lam n _ => .refl(n.succ), 4)

expected  = 2+2 = 4
result_ty = ?m(4)

yeah, we definitely need `abstract_eq` here, cause we'll want to match `2+2`.



since i don't really know whether the underapplied case really is as simple as `def_eq`,
we'll just use the generic approach using `abstract_eq` (which we'll specialize for locals).
so if the result_ty is a forall (ie underapplied), we'll introduce locals,
until that's no longer the case, and instantiate the whnf_forall expected_ty with those.

in the overapplied case, we still need to apply the args & then revert them,
cause the expected type is for the entire app.
we just do that by elab_expr'ing them, app'ing them to result, and abstract_eq'ing them from the expected type.
we don't need result_ty anymore, cause it'll just be ?m(...)

now we have the final term `result`.
and the expected_ty for the recursor app.

so we just need to abstract_eq the targets (indices + major premises) out of that expected type, and we have the motive.

we could now assign ?m, but it would probably be cleaner to def_eq it.
i'm not sure there can't be prior assignments.
well, let's just do the simple thing, assigning, and put an assert to catch multiple assignment earlier.


```

- investigate `ih: _` crash.
    - `closed` is broken.
    - assert `closed` in assign.
    - propagate `offset` in `InferCtx::abstracc`
    - need ivar scope approx to prevent infinite recursion.
    - return `BVar`, assign `Local`.
    - instantiate `IVar`s in `def_eq_basic`.
    - else debug assert not in scope.


- todo:
    - fix `ih: _` bugs and create todos. keep ivar elim disabled.
    - implement motive inference.

    - constant approx.

    - implicit params.
        - binder rework.

    - assign term robustness:
        - lambda type check.
        - scope approx.
            - use common ancestor.
            - recursively check `other.ty` -> `ty`.
            - create fresh term var of `ty`.
            - assign to `other`.

    - cleanup:
        - `InferCtx::abstract_*`.

    - inference robustness:
        - do term vars need a lctx?
        - occurs check.

    - more expected type propagation?

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

