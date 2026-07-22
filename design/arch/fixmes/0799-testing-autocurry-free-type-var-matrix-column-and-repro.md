---
number: 0799
target: /testing
filed_by: /qa
filed_at: 2026-07-21
sprint_filed: 115
refers_to: spec/04-expressions.md §4.6.3 Auto-Currying (the `[Tested+Neg …]` row);
  tests/spec_04_expressions.rs::auto_curry_* ;
  design/arch/fixmes/0779-qa-autocurry-drain-seam-detection-gap.md ;
  tests/plan/s115-test-plan.md §10.4 (the adjudication + the probe table)
status: deferred
---

# Auto-curry over a free-var parameter: the failing repro at the SHARPENED axis + the §4.6.3 free-type-variable column

## Adjudication (already made — this FIXME is the work, not the question)

Supersedes FIXME 0797 (retired). `/qa` ruled at S115 W7: this is a
**`wrong-reject` defect**, not a spec fork, and **no user ruling is needed** for
the case as filed. Full reasoning and the probe table: `tests/plan/s115-test-plan.md`
§10.4. The two load-bearing findings:

1. **The rejection has no semantic content.** `(defn g [x :Int y] …)` and
   `(defn g [:Int x :Int y] …)` have identical bodies and an identical residual
   closure type `(Fn [Int] Int)` — fully determined, no type variable — and one
   is rejected while the other is accepted. A boundary invisible in the residual
   type is an implementation artifact.
2. **0797's characterisation is superseded, and this is what changes the repro.**
   It is NOT "partial application is rejected". The curry **forms correctly**
   over the same unconstrained parameter when its result flows to a
   **non-application** use — `(add-i64 (g 5) 1)` reports
   `got (Fn [Int] Int)`, which is right. It fails only when the curried result is
   subsequently **applied**, immediately or via a let binder; there `(g 5)` types
   as `Int`, i.e. the inner node was accepted as a *full* application of a
   2-parameter function to 1 argument.

That inconsistency is what settles the adjudication: the implementation
observably crosses the boundary in the adjacent cell, so the boundary is not
deliberate.

## The measured axis (HEAD `9088c82e`, `--run`, `PrimitivesOnly`)

| # | Program (`x` unannotated ⇒ free type var) | Result |
|---|---|---|
| a | `(defn g [x y] (add-i64 y 0))` → `((g 5) 3)` | **rejected**: `expected (Fn [Int] Int), got Int` |
| b | same `g`, full application `(g 5 3)` | exit 3 ✓ |
| c | `(defn g [:Int x :Int y] …)` → `((g 5) 3)` — annotated twin | exit 3 ✓ |
| e | `(defn g2 [:Int x y] (add-i64 x 0))` → `((g2 5) 3)` — free var in the **residual** | rejected by the **§3.11 ambiguity gate** — a *different, principled* rejection (see "normative residue") |
| f | `(defn g3 [x :Int y] …)` → `((g3 5) 3)` — free var in the **supplied** position only | **rejected**, same message as (a) |
| h | `(defn g4 [x :Int y :Int z] …)` → `((g4 5 3) 4)` — 3-arity | **rejected**, same message — not arity-specific |
| **j** | same `g` as (a), non-callee use `(add-i64 (g 5) 1)` | rejected with `got (Fn [Int] Int)` — **the curry DID form** |
| m | same `g`, let-bound then applied `(let [h (g 5)] (h 3))` | **rejected**, same message as (a) |
| n | annotated twin of (m) | exit 3 ✓ |

**(j) vs (a)/(f)/(h)/(m) is the discriminating control.** Same function, same
free parameter; the only variable is whether the curried result is applied.

## Ask

1. **Commit the failing repro at the sharpened axis**, failing-not-ignored, with
   `// spec: spec/04-expressions.md §4.6.3` and `// defect: class=wrong-reject`.
   The minimal pair is **(a) RED beside (j) GREEN** — one function, two uses.
   That pair is worth more than (a) alone: it pins that the curry *can* form,
   so a future "fix" that simply rejects both cannot pass.
   Cell (c) is the born-green annotated twin control.
2. **Author the free-type-variable column of the §4.6.3 matrix.** All twelve
   existing `auto_curry_*` tests curry over a **determined** type — a
   coverage-by-definition-variants hole. Rows owed, each with its annotated
   twin: free var in the supplied position; free var in the residual position
   (expect the §3.11 gate — see below); free var in both; ≥3 arity with the free
   var in a middle position; curried result used as a value (the (j) shape) vs
   applied (the (a) shape) vs let-bound-then-applied (the (m) shape).
3. **Diagnostic quality is part of the fix's acceptance, not a nicety.** The
   present message describes the failure of the *application*
   (`expected (Fn [Int] Int), got Int`) rather than the reason the curry did not
   form — it sends a reader to the wrong line. Whatever lands must say something
   a user can act on; pin that text.

## For the owning `/dev`: the seam is a HYPOTHESIS, observe it first

`infer.rs::try_auto_curry:1040` guards on
`Type::Fn(params, ret) if arg_types.len() < params.len()`, with a **silent**
`_ => return Ok(None)` fallthrough for any other callee shape; deferred
settlement is `mono_collect.rs::resolve_auto_curry` + `AutoCurryDrain`. A callee
type not yet resolved to `Fn` at that guard would fall through silently, after
which an ordinary-apply unification against a bare type variable cannot enforce
arity — which fits every observation, including why the error surfaces at the
*outer* node. **This has a discriminating control and NO seam observation.** Per
METHOD §2.2 the first act is to observe which arm is taken. Do not fix from the
table.

**Adjacency worth checking in the same breath:** FIXME 0779 records that **five
of six** `resolve_auto_curry` drain seams have no cell that reddens on a flip.
If the seam observation lands in that machinery, 0779 and this are one finding —
and 0779's detection gap is why this was invisible.

## Normative residue — NOT part of this FIXME

Cell (e) — currying where the **residual** carries a free type variable — is
rejected by the §3.11 ambiguity gate. Whether that is the intended interaction
between §4.6.3 (auto-currying "at any depth", extended to *constrained*
polymorphism with monomorphisation at the supplying call site) and §3.11 ("pin
the type") is a question the spec does not answer. **That one is the user's**,
via `/spec`; `/qa` routed it to `/sprint` for an S116 slot. It blocks nothing
here — do not pin a polarity for (e) until it is ruled.

## Context

**S116 disposition:** Deferred outside Sprint 116 Tracks A--C. The sharpened
wrong-reject and missing free-type-variable column remain live; this is not a
closure verdict. `/sprint` must schedule the repro/matrix with the next
auto-curry/type-inference wave.

Found by `/testing` at S115 W7 while making `tests/gen_ownership_flows.rs`
well-typed by construction (an unannotated owning-type parameter in the
`curried_partial_application` position failed to compile for three of five
owning types). Adjudicated and sharpened by `/qa` the same wave. No
memory-safety consequence; the harness annotates every parameter, which is
correct independently — a generated program must never depend on inference
finding a type nobody wrote.
