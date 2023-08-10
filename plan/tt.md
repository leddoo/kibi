how do we get from TT to kibi?

- well, we mostly analyze the program as usual.
- but we may need to convert to IR for typing.
    - cause mutation and dependent types.
    - not necessarily TT. just something, so we can
      do proper dependent type analysis, and that's
      good for easily compiling to bytecode/wasm.

```
var i = 0
var even: Even i.value = .zero

while i < 10 {
    i += 2
    print(i)
    even = even.add_two()
}

use(even)
```

- we'd like proofs to work a bit like rust references.
  so we need some liveness analysis.
- we don't care about termination for now, just that
  all proofs are constructed correctly & are up-to-date.

- hmm, we might actually not want that.
    - cause `even.add_two()` is a use.
    - instead we want the type to change on assignment.
    - and if the referenced variable is mutated, we create
      a new temporary for that.
- hmm maybe it's easiest to compile to blocks with params.
    - with immutable bindings.
    - ie functions, but like, some specialized repr.
    - is also straight forward to compile to functions for
      kernel validation.
    - perf might be worse, cause we need to explicitly pass
      the state around. but we can improve that, if it becomes
      an issue.
```
locals:
    i: I32
    even: Even i.value
    t0: I32
    t1: Bool
    t2: I32
    t3: Unit
bb0:
    i = 0
    even = Even.zero
    jump bb1
bb1:
    t0 = I32(10)
    t1 = I32.cmp_lt(i, t0)
    switch Bool t1, bb2, bb3
bb2:
    t2 = I32(2)
    i  = I32.add(i, t2)
    t3 = print(i)

```


```
var i = 0
var even: Even(i) = .zero

while i < 10 {
    i += 2
    print(i)
    even = even.add_two()
}


f0: () -> Unit {
    let i: I32 = I32(0)
    let even: Even(I32::value(i)) = Even::zero
    f1(i, even)
}

f1: (i: I32, even: Even(I32::value(i))) -> Unit {
    let t0: Bool = I32::cmp_lt(i, I32(10))
    Bool::rec(t0, f3(i, even), f2(i, even))
}

f2: (i: I32, even: Even(I32::value(i))) -> Unit {
    let i': I32 = I32::add(i, I32(2))
    let _: () = print(i')
    let even' = Even::add_two(I32::value(i), even)
    f1(i', even')
}

f3: (i: I32, even: Even(I32::value(i))) -> Unit {
    let _ = use(even)
    Unit()
}

```

