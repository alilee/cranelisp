---
number: 0630
target: /spec
filed_by: /examples
filed_at: 2026-07-16
sprint_filed: 110
refers_to: spec/05-definitions.md §5.1.2 (Multi-Signature) — the `size` illustrative example
status: open
---

# §5.1.2 illustrative multi-signature example uses bare `:Vec`, which does not compile

## Context

While authoring `examples/36-multi-arity.cl` (S110 Phase 6b — multi-signature
`defn` dispatch), `/examples` exercised type-dispatch clauses and found the
spec's own illustrative example in §5.1.2 does not compile as written:

```clojure
(defn size "Return the number of elements"
  ([:Vec v] (vec-len v))
  ([:List l] (list-len l)))
```

The `[:Vec v]` clause is rejected by the current compiler because `Vec` is a
parametric type and the annotation supplies no type argument:

    type error: type argument count mismatch for primitives/Vec: expected 1, got 0

Attempting to make the element polymorphic — `[:(Vec a) v]` — is *also*
rejected, and here the §5.1.2 clause-independence rule (which the same section
states normatively) is precisely what forbids it:

    ambiguous type: the parameter `v` in the 1-arg arity clause of `size` is
    not pinned — each arity clause is type-checked independently (spec §5.1.2),
    so add a `:Type` annotation to `v` in that clause

Only a concrete element type pins the parameter, e.g. `[:(Vec Int) v]`
(verified working: `(measure [1 2 3 4])` dispatches to the Vec clause and
returns its length). This is an interaction between two things §5.1.2 already
states — parametric types need their argument, and each clause must pin its own
params — but the illustrative example predates/ignores both, so a reader who
copies it hits two compile errors in a row.

## The ask (framing only — `/spec` arbitrates)

This is a spec-example accuracy nit, not a normative question about behaviour
(the behaviour above looks correct and intentional per §5.1.2). Options for
`/spec` to consider:

1. Change the illustrative `size` to dispatch on types that actually pin —
   e.g. `([:(Vec Int) v] (vec-len v))` and a second concrete arm — so the
   example compiles as written; and/or
2. Keep the example but add a one-line note that a parametric-type clause must
   supply a concrete type argument (§5.1.2 clause-independence forbids leaving
   the element polymorphic), pointing at the `:(Vec Int)` form.

`(List a)` / `list-len` in the sibling arm may have the same "needs a concrete
element" issue and a similar treatment; `/spec` is better placed to judge the
canonical shape. No compiler defect is implied — the diagnostics are correct
and helpful; only the illustrative code is stale.
