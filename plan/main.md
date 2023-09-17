
- road map:
    - do.
    - references.
    - codegen.
    - unordered decls.
    - incremental.
    - modules.
    - nat literals.
    - `Of_Nat` and default impls.
    - multi-threading.
    - macros.
    - basic proof inference.
    - crates.


```
def print<T: Type>(value: T): Unit := Unit::mk()

def do_it := do {
    var x := 1;
    (if true { print } else { print })(do {
        if something {
            x := 2;
        }
    });
    x := x + 1;
}

def do_it_0 :=
    let x := 1 in
    ite(true, do_it_1(x), do_it_2(x))

def do_it_1(x: I32) :=
    do_it_3(x, print(I32))

def do_it_2(x: I32) :=
    do_it_3(x, print(I32))

def do_it_3(x: I32, f: I32 -> Unit) :=
    ite(something, do_it_4(x, f), do_it_5(x, f))

def do_it_4(x: I32, f: I32 -> Unit) :=
    let x := 2 in
    do_it_5(x, f)

def do_it_5(x: I32, f: I32 -> Unit) :=
    let a := Unit::mk() in
    let _ := f(x) in
    let x := x + 1 in
    Unit::mk()

```


- todo:
    - do.
        - control flow
            - parse `if` and `loop`.
                - `has_if`, `has_loop`.
                - type: not `has_loop` and not `has_assignment`.
                    - put in `elab_expr_as_type`?
            - join points.
            - `continue`.
            - `break` (`loop` and `do`).
        - assignment valiation: make sure the local is actually a `var`.
          not `let` or something different entirely.
        - uninit dependent vars on assign.
            - track deps using temp arena & vec for each var.
            - also need to remove deps, hmm.
    - brck.
    - partial functions.
        - we kinda need something to prevent proofs from
          being abused to elide calls to effectful functions.
            - actually, i think that's fine. cause this would only apply
              to tactics or other meta programs.
              as in, the code you write will be executed as written.
            - a function call used in a type isn't executed,
              though we should prevent impure functions from being used
              in types.
            - well, ig the issue would be, if you proved that a variable
              already contains the result of a function call.
              but that would again be covered by disallowing reasoning
              about impure functions.
    - `fn`.


### issues:

- the `Add::R` explosion.
    - aka the associated type blowup.
    - aka this needs fixing.
    - consider `TermKind::Proj`.
    - we need something that reduces these terms asap.
    - in general, we don't want to reduce asap, cause it can make it harder
      to understand where terms came from.
      here, we may want to record some info (similarly for impl values,
      which are "unfolded" during impl resolution).
    - should be able to do that in `instantiate_ivars`. may still lead to
      pathological cases if the user manually specifies the impl, we'll see.


