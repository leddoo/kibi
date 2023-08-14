- how do we skip codegen for fp code?
    - i think we may not want to.
    - just for `Prop` stuff, for perf reasons.

- alr, expr vs type context seems useful.
    - `i < n` in an expr is comparison.
    - `i < n` in a  type is `Le(i, n)`.
    - `a = b` in an expr is assignment.
    - `a = b` in a  type is `Eq(a, b)`.
    - kinda weird for `if a + 2 == b` though.
        - well, actually not.
        - `if h: a + 2 == b` is `h: (a + 2).beq(b) = true` (or `.eq`).
        - for `Eq`, you'd `if h: a + 2 = b`.
    - ok, the weird part is that `Eq` would be different from `<=`.
        - cause both have user defined boolean versions.
        - and `<=` would mean `Le` in a type ctx, but `==` would still be `beq`.
        - we could do some compiler magic here:
            - if have proof that `beq = true -> Eq`, `==` means `Eq`.
            - same for other boolean comparisons.
    - actually, it's fine:
        - `=` is `Eq` in type context.
        - `==` is `HasBEq.beq: T -> T -> Bool`.
        - `<=` is `HasLe.le: T -> T -> Prop`.
            - can convert boolean to prop with `ble(a, b) = true`.

- `def` is for math definitions.
    - can still codegen, cause why not.
    - dce can get rid of it.
    - `def`s unfold and need to be acyclic (or well founded).


example:
```
def fib(n: Nat) := match n {
    0 | 1 => n,
    n + 2 => fib(n) + fib(n + 1)
}

fn fib_iter(n: Nat) -> (r: Nat, r === fib(n)) {
    var a = 0
    var b = 1
    var i = 0
    var ha: a = fib(i)     = .rfl
    var hb: b = fib(i + 1) = .rfl
    var hi: i <= n         = .zero_le(n)

    let hnlt: !(i < n) = while hlt: i < n {
        let c = a + b
        let hc: c = fib(i + 2) = ha.rewrite(hb.rewrite(Eq::refl(fib(i + 2))))

        a = b
        b = c
        i += 1

        ha = hb
        hb = hc
        hi = hlt.to_succ_le()
    }

    let heq: i = n = .from_le_not_lt(hi, hnlt)
    return (a, heq.rewrite(ha))
}
```

