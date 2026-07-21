---
number: 0797
target: /qa
filed_by: /testing
filed_at: 2026-07-21
sprint_filed: 115
refers_to: spec/04-expressions.md §4.6.3 Auto-Currying (the `[Tested+Neg …]` row);
  tests/spec_04_expressions.rs::auto_curry_* ; design/arch/fixmes/0779-qa-autocurry-drain-seam-detection-gap.md
status: open
---

# Auto-curry REJECTS partial application of a function with an unconstrained generic parameter — adjudication + a matrix cell needed

## Severity

Minor-to-Important, pending adjudication: either a `wrong-reject` on a
spec-conforming program, or a spec gap. Either way it is an uncovered cell of
the §4.6.3 matrix — the row is `[Tested+Neg]` on twelve tests and none of them
has a free type variable in a parameter position.

## Issue

Full application of a function with an unconstrained (unused, therefore fully
generic) parameter works. Partial application of the SAME function is rejected
at typecheck. Measured at HEAD `99bd23a8`, `PrimitivesOnly`, `--run`:

```clojure
(defn g [x y] (add-i64 y 0))     ; g : forall a. (Fn [a Int] Int)

(defn main [] (Pure (g 5 3)))       ; => exit 3   OK
(defn main [] (Pure ((g 5) 3)))     ; => exit 1
;; error: type mismatch: expected (Fn [primitives/Int] primitives/Int),
;;        got primitives/Int
```

The discriminator is the free type variable, not the arity, not the Vec, and not
the shape of the call:

| program | partial application |
|---|---|
| `(defn g [x y] (add-i64 y 0))` — `x` unconstrained | **rejected** |
| `(defn g [:Int x :Int y] (add-i64 y 0))` — same body, `x` annotated | accepted |
| `(defn g [:(Vec Int) x :Int y] (add-i64 (vec-len x) y))` | accepted |
| `(defn g [x y] (add-i64 (str-len x) y))` — `x` pinned to String by use | accepted |

So a parameter whose type is a free variable at the point of currying defeats
the curry, while any parameter with a determined type does not.

## Why this needs `/qa` and not a repro straight to `/dev`

§4.6.3 states auto-currying applies "at any depth" and explicitly extends it to
**constrained** polymorphic functions (trait-dispatched operators, the
`(fn [:Num a a] a)` shape), with the closure "monomorphised at the call site
where concrete types become known". It says nothing about an **unconstrained**
type variable. Two readings, and choosing between them is a semantics call, not
a test call:

- **`wrong-reject`** — the curried closure should carry the free variable exactly
  as the constrained case carries its constraint, and monomorphise at the site
  that supplies the second argument. Then this is a defect and wants a failing
  repro naming an owner.
- **Deliberate** — currying is only defined where the residual closure's type is
  determinable, and an unconstrained parameter is out of scope. Then §4.6.3 wants
  a sentence saying so (`/spec`, via the user) and the matrix wants a NEGATIVE
  cell pinning the rejection with a diagnostic that says what is wrong. The
  present message ("expected `(Fn [Int] Int)`, got `Int`") describes the failure
  of the *application*, not the reason the curry did not form — it would send a
  user looking at the wrong line.

## Proposed resolution

`/qa`: adjudicate (with the user if it is a semantics fork), then either route a
repro to the owning `/dev` or add the negative cell + a `/spec` FIXME. Either
way, add the free-type-variable column to the §4.6.3 matrix — it is a variant of
"coverage by definition variants" (`tests/CLAUDE.md`): the twelve existing
auto-curry tests all happen to curry over a determined type.

## Context

Found by `/testing` at S115 W7 while making the generative flow harness
(`tests/gen_ownership_flows.rs`) well-typed BY CONSTRUCTION: the first draft of
the `curried_partial_application` position left the owning-type parameter
unannotated and three of five owning types failed to compile. Annotating the
parameter — which the harness now does everywhere, since a generated program must
never depend on inference finding a type nobody wrote — made them all pass, which
is what isolated the discriminator. No memory-safety consequence; the harness
covers the curried position with annotated parameters.
