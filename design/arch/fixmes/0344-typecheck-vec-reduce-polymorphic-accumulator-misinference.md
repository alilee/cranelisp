---
number: 0344
target: /typecheck
filed_by: /stdlib
filed_at: 2026-06-13
sprint_filed: 81
refers_to: stdlib/collections/vec.cl (vec-reduce, vec-reduce-loop ~lines 39-46), crates/cranelisp-typecheck/src/infer.rs
status: open
---

# `vec-reduce` is mis-inferred — the polymorphic accumulator collapses to `(Vec a)` everywhere

## Issue (S81 W-I-5 /stdlib finding)

`stdlib/collections/vec.cl::vec-reduce` (an ordinary Clojure-style reduce over a
Vec) infers a nonsensical scheme:

```
vec-reduce :: (Fn [(Fn [(Vec a) (Vec a)] (Vec a)) (Vec a) (Vec (Vec a))] (Vec a))
```

Every type variable has been over-unified to `(Vec a)`. The correct scheme is
`(Fn [(Fn [b a] b) b (Vec a)] b)` — `b` the accumulator, `a` the element type.
Consequently any call fails, e.g. `(vec-reduce add-i64 0 [1 2 3])` →
`type mismatch: expected (primitives/Vec t1), got Int`.

Source (correct as written):
```clojure
(defn vec-reduce [f init v] (vec-reduce-loop f init v (vec-len v) 0))
(defn- vec-reduce-loop [f acc v :Int len :Int i]
  (if (ge-i64 i len) acc
    (vec-reduce-loop f (f acc (vec-get v i)) v len (add-i64 i 1))))
```

The recursion threads a polymorphic accumulator (`acc`/`init`, type `b`) distinct
from the element type (`a`, via `vec-get`). Inference is collapsing `b`, `a`, and
the Vec type into one variable. By contrast `vec-map` / `vec-filter` (same module,
no separately-typed accumulator threaded through a recursive helper) infer
correctly — so the trigger is the polymorphic-accumulator recursion shape.

**Pre-existing** (vec-reduce predates S81). The S81 test runner avoided it by
writing the tally/report folds as explicit tail-recursive loops over
`vec-len`/`vec-get`; this FIXME is the durable record so the stdlib fold helper
can be restored once inference is fixed.

## Proposed resolution

`/qa` authors a minimal failing repro (no stdlib): a two-defn fold with a
polymorphic accumulator distinct from the element type (the shape above, inlined),
asserting `(reduce add-i64 0 [1 2 3]) == 6`. `// spec:` → spec/05-type-system.md
(let/fn polymorphism + recursive inference). `/typecheck` fixes the
over-unification of the accumulator type variable in the recursive-helper
inference path.

## Operational implication

`vec-reduce` is unusable; downstream stdlib fold helpers must hand-roll loops.
`collections.vec` ships `vec-reduce` in a broken state until resolved.
