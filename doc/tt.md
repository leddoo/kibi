the type theory of lean.
because it works, no need to change it.


meta:
    this document explains lean's type theory,
    which kibi is built on top of.

    "type theory" sounds fancy, and it kind of is,
    but you can think of it like a somewhat esoteric
    programming language.
    below, we'll define its syntax, semantics, and evaluation.

    but before we get into that, let's start with some informal
    background. this is mostly to get us on the same page,
    looking into type theory resources online is highly recommended,
    if you want to understand the `tt` module.


judgments (informal):
    in the following sections, you'll see the pattern `C ⊢ J`.
    we say, "the context `C` derives (⊢) the judgment `J`".

    contexts are explained in the section "context formation".
    judgments can be a variety of things.

    you'll probably be familiar with the typing judgment `a: A`.
    but to judge `a` to be of type `A`, we need to define what
    it means for `A` to be a "type".
    we have another judgment for that: `A type` -
    it just means that we judge `A` to be a type.
    we say, "A is a type".

    in the section on contexts, we'll see the judgment `ctx`.
    it is used to define (semantically) valid contexts.
    normally, we'd pronounce `Γ ⊢ ctx` as "Γ derives ctx",
    but in this case we say, "Γ is a well formed context".


inferences (informal):
    most rules defined below require assumptions.
    for example, we can only judge `a` to be of type `A`,
    if `A` is a type.

    formally, we could try define that like so:
    ```
    Γ ⊢ A type      // assumption "if   Γ derives that A is a type"
    Γ ⊢ a: A        // conclusion "then Γ derives that a is of type A"
    ```

    in papers, you'll usually see it written like so:
    ```
    A1 A2 A3    // a bunch of assumptions (can be empty).
    --------
       C        // the conclusion.
    ```

    but here, it's written like so:
    ```
    A1      // the lines before the last line are assumptions (if any).
    A2
    A3
    C       // the last line is the conclusion.
    ```

    okay, syntax out of the way, let's examine that example from
    above again: "if `Γ ⊢ A type` then `Γ ⊢ a: A`".
    this rule is actually not "sound".
    soundness means, we can't derive nonsense.

    the rule as written means: if `A` is a type, we can derive
    that there is some term `a` of type `A`.
    this would mean that we can find elements of any type.

    this is a problem, because we use types to represent mathematical
    propositions. for example, `Eq(1, 2)` is the type representing
    the proposition that 1 is equal to 2.
    if we can find an element of that type `x: Eq(1, 2)`, then,
    by convention, we have proved that 1 is equal to 2.

    (i say "by convention", because in type theory, we don't really
    "prove" things, or conclude that propositions are "true", we
    merely find that certain propositions are "derivable", and others
    are not. doesn't really matter, but now you know.)

    anyway, according to our rule, we could derive that there is an
    element of type `Eq(1, 2)` (i.e. a proof that 1=2),
    just because `Eq(1, 2)` is a type. that's obviously not good.
    so now let's get into the actual rules of type theory.


syntax:
    we're defining a language,
    let's start with its syntax.

    you can ignore levels and universes for now.
    contexts will be explained shortly.
    terms should seem (remotely) familiar.

    ```tt
    // (universe) levels.
    l ::= u             // variable
        | 0             // zero
        | S(l)          // level + 1
        | max(l, l)     // max of two levels
        | imax(l, l)    // refer to "levels" section

    // terms (aka expressions):
    e ::= x             // variable
        | U(l)          // universe of level `l`
        | (e e)         // function application
        | (λ (x: e) e)  // function definition
        | (Π (x: e) e)  // function type

    // contexts:
    Γ ::= ⋅             // empty context
        | (Γ, (x: e))   // extended context
    ```


context formation:
    contexts hold a sequence of assumptions.
    this is similar to the symbol table in other programming languages.

    eg: when defining a function `fn add(a b: int) = a + b`,
    the "context" of the addition `a + b` contains (at least) two assumptions:
    there's a variable `a` of type `int`, and a variable `b` of `int`.

    here, we define, which contexts are semantically valid.

    we'll use code blocks for the formal definitions.
    initially, there are comments below each rule, explaining how to read it.

    ```
    empty:
        ⋅ ⊢ ctx

        // the empty context is well formed.

    extend:
        Γ ⊢ ctx
        Γ ⊢ A type
        (Γ, a: A) ⊢ ctx

        // here we're reading it bottom up:
        // for a context `Γ` with an assumption `a: A` to be well formed,
        // the context `Γ` needs to be well formed,
        // and `Γ` must derive that `A` is a type.

        // in other words, we clearly can't assume `a: Foo`,
        // if `Foo` is not a type.
        // this is very simple, don't get confused.
    ```


rules in actions (informal):
    reading the rules bottom up is common, cause that's how
    we use them to implement type checking/inference.

    for example, we might find the term `a + b` in the code,
    and we want to type check it.

    first, let's assume `a` and `b` have already been shown
    to be of type `I32`.

    replacing the operator using a function call,
    we have: `I32.add(a, b)`.

    in type theory syntax: `((I32.add a) b)`

    defining `f := (I32.add a)`, we have `(f b)`.

    as you'll see below, we have a rule for function application,
    which has the conclusion `Γ ⊢ (f x): B`.

    matching `(I32.add a)` to `f` and `b` to `x`,
    if we can fulfil the assumptions of that rule,
    we can derive a type for `((I32.add a) b)`, namely that `B`.

    now, we need to work backwards: for each assumption of that rule,
    find other rules, whose conclusions match these assumptions.
    repeat that until all assumptions are derived using rules,
    that don't have any assumptions.

    here's what that derivation may look like:

    ```informal

    for reference, here's the (simplified) rule "pi elim":

        Γ ⊢ f: A -> B       // if `f` is a function from A -> B
        Γ ⊢ x: A            // and `x: A`
        Γ ⊢ (f x): B        // then `(f x): B`


    // we're trying to find a type for this term.
    goal `((I32.add a) b): T1`  // (*1)

        // it is a function application,
        // so we can use "pi elim".
        match rule "pi elim" with `f = (I32.add a)`, `x = b`.

        // the first assumption "f is a function A -> B"
        goal: `(I32.add a): A1 -> B1`  // (*2)

            // still have a function application `(I32.add a)`.
            // so we can use "pi elim" again.
            match rule "pi elim" with `f = I32.add`, `x = a`.

            // first assumption.
            goal: `I32.add: A2 -> B2`

                // this time, we can use the definition of `I32.add`.
                match definition: `I32.add: I32 -> (I32 -> I32)`

                // match that with our type variables `A2` and `B2`
                A2 = I32
                B2 = I32 -> I32

            // second assumption.
            goal: `a: A2`
                  `a: I32`

                // true by assumption (we assumed that above).
                match assumption `a: I32`

            // now we can give a type to the sub-goal `(I32.add a)`
            conclude: `(I32.add a): B2`
                      `(I32.add a): I32 -> I32`

            // this is indeed a function, so we can match the
            // type variables of the first sub-goal (*2):
            A1 = I32
            B1 = I32

        // second assumption.
        goal: `b: A1` ~ `b: I32`

            match assumption `b: I32`

        // we've now satisfied all sub-goals for out initial goal (*1).
        conclude: `((I32.add a) b): B1`
                  `((I32.add a) b): I32`

            T1 = I32

        done.

    ```


basic rules:
    here are a bunch of basic rules for working with contexts.

    ```
    var:
        (Γ, a: A) ⊢ ctx
        (Γ, a: A) ⊢ a: A

        // the judgment `a: A` (`a` is of type `A`) can be derived,
        // if the context contains an assumption `a: A`.

        // technically "ends with an assumption `a: A`,
        // but that's what we have the exchange rule for.

    weaken:
        Γ ⊢ J
        Γ ⊢ A type
        (Γ, a: A) ⊢ J

        // we can add assumptions.

    exchange:
        (Γ1, Γ2) ⊢ J
        (Γ2, Γ1) ⊢ J

        // the assumption order is irrelevant.
        // (provided that these contexts are well formed)

    contract:
        (Γ, a: A, a: A) ⊢ J
        (Γ, a: A) ⊢ J

        // we can remove duplicate assumptions.
    ```


typing:
    these are the typing rules.

    ```
    type:
        Γ ⊢ A: U(l)
        Γ ⊢ A type

        // if `A` is of type `U(l)`, a is a type.

    universe:
        Γ ⊢ U(l): U(S(l))

        // the universe `U(l)` is of type `U(l + 1)`.

    pi formation:
        Γ ⊢ A: U(l1)
        (Γ, a: A) ⊢ B: U(l2)
        Γ ⊢ (Π (a: A) B): U(imax(l1, l2))

        // if `A` is a type,
        // and given `a: A`, `B` is a type,
        // the function type `Π (a: A) B` is a type.

    pi intro:
        (Γ, a: A) ⊢ b: B
        Γ ⊢ (λ (a: A) b): (Π (a: A) B)

        // i think you get the idea.

    pi elim:
        Γ ⊢ f: (Π (a: A) B)
        Γ ⊢ x: A
        Γ ⊢ (f x): B[x/a]

    conversion:
        Γ ⊢ a: A
        Γ ⊢ B ≡ A
        Γ ⊢ a: B
    ```


definitional equality:

    reflexivity:
        Γ ⊢ a: A
        Γ ⊢ a ≡ a

    symmetry:
        Γ ⊢ a ≡ b
        Γ ⊢ b ≡ a

    transitivity:
        Γ ⊢ a ≡ b
        Γ ⊢ b ≡ c
        Γ ⊢ a ≡ c

    universe:
        Γ ⊢ l1 ≡ l2
        Γ ⊢ U(l1) ≡ U(l2)

    pi formation:
        Γ ⊢ A1 ≡ A2
        (Γ, a: A1) ⊢ B1 ≡ B2
        Γ ⊢ (Π (a: A1) B1) ≡ (Π (a: A2) B2)

    pi intro:
        Γ ⊢ A1 ≡ A2
        (Γ, a: A1) ⊢ b1 ≡ b2
        Γ ⊢ (λ (a: A1) b1) ≡ (λ (a: A2) b2)

    pi elim:
        Γ ⊢ f1 ≡ f2: (Π (a: A) B)
        Γ ⊢ x1 ≡ x2: A
        Γ ⊢ (f1 x1) ≡ (f2 x2)

    beta:
        (Γ, a: A) ⊢ b: B
        Γ ⊢ x: A
        Γ ⊢ ((λ (a: A) b) x) ≡ b[x/a]

    eta:
        Γ ⊢ f: (Π (a: A) B)
        Γ ⊢ (λ (x: A) (f x)) ≡ f

    proof irrelevance:
        Γ ⊢ P: U(0)
        Γ ⊢ h1: P
        Γ ⊢ h2: P
        Γ ⊢ h1 ≡ h2


algorithmic equality:
    // denoted by ⇔
    // used by the kernel to approximate the ≡ rules.

    reflexivity: analogous

    symmetry: analogous

    transitivity: absent, something about sub-singleton elimination & decidability & hard to choose middle type.

    universe: analogous

    pi formation: analogous

    pi intro: analogous

    pi elim: analogous

    beta: replaced by head reduction & def/ind rules.

    eta:
        Γ ⊢ f1 f2: (Π (a: A) B)
        (Γ, x: A) ⊢ (f1 x) ⇔ (f2 x)
        Γ ⊢ f1 ⇔ f2

        replaced by extensionality.
        justification:
            (Γ, x: A) ⊢ (f1 x) ≡ (f2 x)
            Γ ⊢ (λ (x: A) (f1 x)) ≡ (λ (x: A) (f2 x)) ; by pi intro
            Γ ⊢ f1 ≡ f2                               ; by eta

    proof irrelevance:
        Γ ⊢ P1 P2: U(0)
        Γ ⊢ h1: P1
        Γ ⊢ h2: P2
        Γ ⊢ P1 ⇔ P2
        Γ ⊢ h1 ⇔ h2

        added conversion, justified by conversion rule.

    head reduction:
        Γ ⊢ a ⇝ a'
        Γ ⊢ a' ⇔ b
        Γ ⊢ a ⇔ b

    conversion: absent, hard to choose target.


head reduction:

    pi elim:
        Γ ⊢ f ⇝ f'
        Γ ⊢ (f x) ⇝ (f' x)

    beta:
        Γ ⊢ ((λ (a: A) b) x) ⇝ b[x/a]


definitions:
    syntax:
        def   c{us}: T = e
        axiom c{us}: T
    where:
        `c` is a name.
        `us` is a list of level variables.
        Γ ⊢ T: U(l)
        Γ ⊢ e: T
        level variables used in `T`, `l`, `e` are from `us`.

    use definition:
        e ::= ... | c{ls}

    type:
        Γ ⊢ c{ls}: T(c)[ls/us]

    levels def-eq:
        Γ ⊢ ls[i] ≡ ls'[i] for i in (1 ..= n)
        Γ ⊢ c{ls} ≡ c{ls'}

    levels algo-eq:
        Γ ⊢ ls[i] ≡ ls'[i] for i in (1 ..= n)
        Γ ⊢ c{ls} ⇔ c{ls'}

    delta-eq:
        Γ ⊢ c{ls} ≡ e(c)[ls/us]

    delta reduction:
        Γ ⊢ c{ls} ⇝ e(c)[ls/us]


levels:
    syntax: l ::= u | 0 | S(l) | max(l l) | imax(l l)

    evaluation (l -> Nat):
        [0]         = 0
        [S(a)]      = [a] + 1
        [max(a b)]  = max([a] [b])
        [imax(a b)] = if ([b] = 0) then 0 else max([a] [b])

    definitional equality:
        l1 ≤ l2
        l2 ≤ l1
        l1 ≡ l2

    ordering: a <= b + n, where n: Nat

        refl:
            n >= 0
            b <= b + n

        zero le:
            n >= 0
            0 <= b + n

        succ le:
            a <= b + (n-1)
            S(a) <= b + n

        le succ:
            a <= b + (n+1)
            a <= S(b) + n

        max le:
            a1 <= b + n
            a2 <= b + n
            max(a1 a2) <= b + n

        le max 1:
            a <= b1 + n
            a <= max(b1 b2) + n

        le max 2:
            a <= b2 + n
            a <= max(b1 b2) + n

        imax le 1:
            0 <= b + n
            imax(a1, 0) <= b + n

        imax le 2:
            max(a1 S(a2)) <= b + n
            imax(a1 S(a2)) <= b + n

        imax le 3:
            max(imax(a1 a2) imax(a1 a3)) <= b + n
            imax(a1 max(a2 a3)) <= b + n

        imax le 4:
            max(imax(a1 a3) imax(a2 a3)) <= b + n
            imax(a1 imax(a2 a3)) <= b + n

        le imax 1-4:
            analogous (because these are just rewrites).

        var:
            a[0   /u] <= b[0   /u] + n
            a[S(u)/u] <= b[S(u)/u] + n
            a <= b + n


inductives:
    examples:
        inductive Nat: Type
        | zero: Nat
        | succ: Nat -> Nat

        inductive Vector {u} (T: Type u): Nat -> Type u
        | nil:  (Vector Nat.zero)
        | cons: (n: Nat) (head: T) (tail: Vector n) -> (Vector (Nat.succ n))

    formation:
        inductive Name {ls}: Π (ps :: Ps) (xs :: Xs) -> (Sort l)

        ls: sequence of level variable names.
        ps: parameters.
        xs: indices.
        l:  a level value that is either zero or non-zero (a plain variable is neither of those).

    introduction:
        | ctor_i: Π (ps :: Ps) (as :: As) -> Name ps cxs

        ps: parameters (same as in formation, implicit in notation of examples).
        as: constructor arguments.
        cxs: index terms (may use the arguments, see below).

        arguments informally:
            - there are two kinds.
            - non-recursive:
                - type does not mention `Name`.
                - value can be used in following types (As and xs above).
            - recursive:
                - type uses `Name`, has the form `Π (rs :: Rs) -> Name ps rxs`.
                - value *may not* be used in later types.

        formal definition of valid constructors:
            where (Γ, Name) means (Γ, Name: Π (ps :: Ps) (xs :: Xs) -> (Sort l))
            and the `Ps` are already in the context.

            env:
                Γ ⊢ (exs :: Xs)
                (Γ, Name) ⊢ (Name ps exs) ctor

            non-recursive argument (narg):
                Γ ⊢ N: Sort ln
                imax(ln, l) <= l
                (Γ, n: N, Name) ⊢ τ ctor
                (Γ, Name) ⊢ (Π (n: N) -> τ) ctor

            recursive argument (rarg):
                Γ ⊢ Rs :: Sort rls
                imax(rl, l) <= l  (for every rl in rls)
                (Γ, rs :: Rs) ⊢ rxs :: Xs
                (Γ, Name) ⊢ τ ctor
                (Γ, Name) ⊢ (Π (Π (rs :: Rs) -> Name ps rxs) -> τ) ctor

        examples of applying the formal definition:
            zero: Nat
                valid by env: Nat has neither parameters nor indices.

            succ: Nat -> Nat
                1) apply rarg.
                    Rs and rxs are empty.
                    the conclusion looks like:
                    (Γ, Name) ⊢ (Π (Nat) -> τ) ctor
                    where τ = Nat.
                2) thus succ is valid because τ is valid by env.

            nil: (Vector Nat.zero)
                valid by env. Nat.zero is a global and Vector takes exactly one Nat index.

            cons: (n: Nat) (head: T) (tail: Vector n) -> (Vector (Nat.succ n))
                1) apply narg.
                    N = Nat: Sort 1. (and 1 <= succ(u) ~ Type u means Sort succ(u))
                    add (n: Nat) to the context.
                    τ = (head: T) (tail: Vector n) -> (Vector (Nat.succ n))
                2) apply narg.
                    N = T: Type u. (and succ(u) <= succ(u))
                    add (head: T) to the context. (for completeness, it's never used)
                    τ = (tail: Vector n) -> (Vector (Nat.succ n))
                3) apply rarg.
                    Rs is emtpy.
                    rxs = [n] (remember, `n` was added to the context in step 1.)
                    context unchanged.
                    τ = (Vector (Nat.succ n))
                4) apply env.
                    exs = [(Nat.succ n)] where `Nat.succ` and `n` are in the context.
                    done.

    elimination:
        Name.rec {ls, lr}:
            Π (ps :: Ps)
              (Motive: Π (mxs :: Xs) (Name ps mxs) -> Sort lr)
              (ms :: Ms)
              (xs :: Xs)
              (v: Name ps xs)
              -> Motive xs v

        where Ms are instances of the motive for every constructor:
            ctor_i: Π (ps :: Ps) (as :: As) -> Name ps cxs

            Ms_i = Π (as :: As) (rms :: RMs) -> (Motive cxs (ctor_i ps as))

            where rms are motives for the recursive arguments:
                rarg_j: Π (rs :: Rs) -> Name ps rxs

                RMs_j = Π (rs :: Rs) -> (Motive rxs (rarg_j rs))

        examples:
            Nat.rec:
                Π (Motive: Π Nat -> Sort lr)
                  (Motive Nat.zero)
                  (Π (n: Nat) (Motive n) -> Motive (Nat.succ n))
                  (v: Nat)
                  -> Motive v

            Vector.rec:
                Π (T: Type u)
                  (Motive: Π (n: Nat) (Vector T n) -> Sort lr)
                  (Motive Nat.zero (Vector.nil T))
                  (Π (n: Nat) (head: T) (tail: Vector T n)
                     (Motive n tail)
                     -> Motive (Nat.succ n) (Vector.cons n head tail)
                  (n: Nat)
                  (v: Vector T n)
                  -> Motive n v

    large elimination:
        the motive in the recursor returns a type of `Sort lr`.
        for "large eliminating" types, `lr` is an unconstrained level variable,
        otherwise `lr = 0`.
        the reason for this constraint is to enforce the Prop discipline.
        eliminating a Prop into a larger universe would allow discerning props,
        which is inconsistent with proof irrelevance.
        there is one exception: sub-singleton elimination.
        props that only have (at most) a single value can safely be eliminated.
        their information isn't compressed in a proof irrelevant system. (they
        only had at most one value to begin with.)

        informal rules for large elimination:
            an inductive type is large eliminating if:
            1) it is a type of sort l >= 1.
            2) it is a prop with at most one constructor where all arguments are
               either propositions or occur directly in the output type.
               the argument constraint is true for all recursive arguments
               because they are props by definition (they return an instance of
               the inductive type, which is a prop, hence they are a prop too).
               these rules ensure that each type of the family has at most one
               inhabitant. (a non-prop non-recursive arg that occurs directly
               in the output type ensures that different values of that arg
               all live in different families of the inductive type.)

        formal rules:
            here [*] is the list of constructors of the inductive type.
            []    is an empty list.
            [τ]   contains exactly one constructor τ.
            [...] is an arbitrary list of constructors.

            type:
                1 <= l
                (Γ, Name) ⊢ [...] LE

            false:
                (Γ, Name) ⊢ [] LE

            singleton:
                (Γ, Name) ⊢ τ LE-ctor
                (Γ, Name) ⊢ [τ] LE

            the following rules for singletons correspond
            roughly to the ctor rules:

            env:
                (Γ, Name) ⊢ (Name ps exs) ctor
                (Γ, Name) ⊢ (Name ps exs) LE-ctor

            narg-prop:
                (Γ, Name) ⊢ N: Prop
                (Γ, n: N, Name) ⊢ τ LE-ctor
                (Γ, Name) ⊢ (Π (n: N) -> τ) LE-ctor

            narg-direct:
                (Γ, n: N, Name) ⊢ (Π (fs :: Fs) -> Name ps cxs) LE-ctor
                cxs = [... n ...] (n is an element of the sequence cxs).
                (Γ, Name) ⊢ (Π (n: N) (fs :: Fs) -> Name ps cxs) LE-ctor

            rarg:
                (Γ, Name) ⊢ τ LE-ctor
                (Γ, Name) ⊢ (Π (Π (rs :: Rs) -> Name ps rxs) τ) LE-ctor

    computation:
        ind-eq:
            one rule for each constructor.
            ctor_i: Π (ps :: Ps) (as :: As) -> Name ps cxs

            (Γ, ps, Motive, ms, as) ⊢ Name.rec ps Motive ms cxs (ctor_i ps as) ≡ ms_i as mvs

            where ms_i: Π (as :: As) (rms :: RMs) -> (Motive cxs (ctor_i ps as))

            where mvs are the motive values for the recursive args:
                rarg_j: Π (rs :: Rs) -> Name ps rxs

                mvs_j : Π (rs :: Rs) -> (Motive rxs (rarg_j rs))
                mvs_j = λ (rs :: Rs), Name.rec ps Motive ms rxs (rarg_j rs)

        reduction:
            ind-reduce:
                Name.rec ps Motive ms cxs (ctor_i ps as) ⇝ ms_i as mvs

            ind-k-reduce (for subsingletons):
                Name.rec ps Motive ms cxs h ⇝ ms_i as mvs

                only difference is that `h` doesn't have to be a constructor term.
                valid by proof irrelevance and ind-eq.
                note that `h` is opaque. we can't extract the `as` from it.
                which is why the non-recursive args must appear directly in `cxs`
                or be propositions (i.e. only have a single value).


