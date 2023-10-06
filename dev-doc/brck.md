

```
-- CFG:
Statement = BBi '/' j
Point = Start(Statement) | Mid(Statement)

.decl cfg_edge(P:point, Q:point)
.input cfg_edge


-- subset relation:

.decl base_subset(R1:region, R2:region)
.input base_subset

.decl subset(R1:region, R2:region)
-- base.
subset(R1, R2) :- base_subset(R1, R2).
-- transitive.
subset(R1, R3) :- subset(R1, R2), subset(R2, R3).


-- region liveness:

.decl create_ref(R:region, L:loan, P:point)
.input create_ref

.decl use_ref(R:region, P:point)
.input use_ref

.decl region_live_at(R:region, P:point)
-- from use.
region_live_at(R, P) :- use_ref(R, P)
-- CFG propagation.
region_live_at(R, Q) :- region_live_at(R, P), cfg_edge(Q, P), !create_ref(R, L, Q)


-- loan liveness:

.decl requires(R:region, L:loan, P:point)
-- from borrow.
requires(R, L, P) :- create_ref(R, L, P).
-- from subset.
requires(R2, L, P) :- requires(R1, L, P), subset(R1, R2).
-- CFG propagation.
requires(R, L, Q) :- requires(R, L, P), cfg_edge(P, Q), region_live_at(R, Q).

.decl loan_live_at(L:loan, P:point)
loan_live_at(L, P) :- requires(R, L, P).


-- loan liveness 2:
-- this one makes more sense, intuitively.
-- should be implied by the other one.
-- and for ssa, could be equivalent, not sure.

.decl requires(R:region, L:loan)
-- from borrow.
requires(R, L) :- create_ref(R, L, P).
-- from subset.
requires(R2, L) :- requires(R1, L), subset(R1, R2).

.decl loan_live_at(L:loan, P:point)
loan_live_at(L, P) :- requires(R, L), region_live_at(R, P).


-- error:

-- accessing a local invalidates any loans derived from that local.
-- this includes `&*foo`.
-- and it should probably be transitive? cause of the stack behavior.
-- but gotta be careful with loops, though liveness might handle that.
.decl invalidates(P:point, L:loan)
.input invalidates

.decl error(P:point)
error(P) :- invalidates(P, L), loan_live_at(L, P).

```



example:
```
p0: var v           := 42;
p1: let r1: &'1 I32 := &'0 mut v;
p2: let r2: &'3 I32 := &'2 mut *r1;
p3: *r1 := 69;
p4: *r2;

inputs:
cfg_edge: (p0, p1), (p1, p2), (p2, p3), (p3, p4)
base_subset: (r0, r1), (r2, r3)
create_ref: (r0, l0, p1), (r2, l1, p2)
use_ref: (r1, p3), (r3, p4)
invalidates: (p3, l1)

computed:
region_live_at: (r1, p2), (r1, p3), (r3, p3), (r3, p4)
requires:
  (r0, l0, p1), (r2, l1, p2),
  (r1, l0, p1), (r3, l1, p2),
  (r1, l0, p2), (r3, l1, p3),
  (r1, l0, p3), (r3, l1, p4),
loan_live_at: (l0, [p1, p2, p3]), (l1, [p2, p3, p4])

error: (p3)


-- actual ir:
def jp_0: Unit :=
  let v(0): Nat := 42 in
  let r1(1): Ref(Region::infer, Ref_Kind::mut, Nat)
    := Ref::from_value(Ref_Kind::mut, Nat, $0) in
  let r2(2): Ref(Region::infer, Ref_Kind::mut, Nat)
    := Ref::from_value(
      Ref_Kind::mut, Nat,
      Ref::read(Ref_Kind::mut, Nat, $0)) in
  let _: Unit := Ref::write(Nat, $1, 69) in
  let _: Nat := Ref::read(Ref_Kind::mut, Nat, $1) in
  Unit::mk


```




examples:

```
def brck_1: Nat := do {
    var a := 42;
    var b := 72;
    var r := &b;
    b := 69;
    r := &a;
    a := 96; -- error.
    return *r;
}

def jp_0: Nat :=
  -- var ids []
  let a(0): Nat := 42 in
  let b(1): Nat := 72 in
  let r(2): Ref(Region::infer, Ref_Kind::shr, Nat)
    := Ref::from_value(Ref_Kind::shr, Nat, $0) in
  let b(1): Nat := 69 in
  let r(2): Ref(Region::infer, Ref_Kind::shr, Nat)
    := Ref::from_value(Ref_Kind::shr, Nat, $3) in
  let a(0): Nat := 96 in
  Ref::read(Ref_Kind::shr, Nat, $1)


stack ir:

bb0:
    const 42
    write local("a")
    const 72
    write local("b")
    ref r0 shr local("b")
    write local("r")
    const 69
    write local("b")
    ref r1 shr local("a")
    write local("r")
    const 96
    write local("a")
    read local("r"), deref
    return

- know `r0`'s live range is empty.
    - cause it's created locally in `bb0`.
    - and not passed to any other bb.
    - and not used (overwritten later).

- know `r1`'s live range is from the `ref` to the `deref`.
    - cause it's created locally in `bb0`.
    - and not passed to any other bb.
    - and its last use is that deref.

- hence there's an error at `write local("a")`.
    - cause `r1` borrows "a" and is live during the write.

- are loans and regions identical in ssa?
    - hmm, i think so, yeah.
    - well, almost, join point params also have regions.
```



```
def brck_4: Nat := do {
    var a := 72;
    var b := 69;
    var r := &b;
    a := 42;
    if Bool::true { r := &a; };
    b := 96; -- error.
    return *r;
}


def jp_0: Nat :=
  -- var ids []
  let a(0): Nat := 72 in
  let b(1): Nat := 69 in
  let r(2): Ref(Region::infer, Ref_Kind::shr, Nat)
    := Ref::from_value(Ref_Kind::shr, Nat, $0) in
  let a(0): Nat := 42 in
  ite(Nat, Bool::true,
    brck_4::jp_2($0, $2, $1),
    brck_4::jp_1($0, $2, $1))

def jp_1: Nat -> Nat -> Ref(Region::infer, Ref_Kind::shr, Nat) -> Nat :=
  -- var ids [0, 1, 2]
  λ(a: Nat, b: Nat, r: Ref(Region::infer, Ref_Kind::shr, Nat)) =>
    let b(1): Nat := 96 in
    Ref::read(Ref_Kind::shr, Nat, $2)

def jp_2: Nat -> Nat -> Ref(Region::infer, Ref_Kind::shr, Nat) -> Nat :=
  -- var ids [0, 1, 2]
  λ(a: Nat, b: Nat, r: Ref(Region::infer, Ref_Kind::shr, Nat)) =>
    let r(2): Ref(Region::infer, Ref_Kind::shr, Nat)
      := Ref::from_value(Ref_Kind::shr, Nat, $2) in
    brck_4::jp_1($3, $2, $0)


bb0:
    const 72
    write local("a")
    const 69
    write local("b")
    ref r0 shr local("b")
    write local("r")
    const 42
    write local("a")
    const true
    ite [bb2, bb1]

bb1 [-, -, r1]:
    const 96
    write local("b")
    read local("r"), deref
    return

bb2 [-, -, r2]:
    ref r3 shr local("a")
    write local("r")
    jump bb1


- `r0` is passed to bb2/bb1, so we need global liveness analysis.

- region subsets: r0:r1, r0:r2, r3:r1

- `write local("b")` errors.
    - cause `r1` is live due to the read.
    - and `r1 := {r0, r3}`.
    - and `r3` borrows "b".
```


