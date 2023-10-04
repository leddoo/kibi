

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


-- error:

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

```


