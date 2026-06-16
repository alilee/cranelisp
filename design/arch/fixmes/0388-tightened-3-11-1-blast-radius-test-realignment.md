---
number: 0388
target: /qa
filed_by: /dev
filed_at: 2026-06-16
sprint_filed: 84
refers_to: tests/spec_04_expressions.rs::vec_literal_empty, tests/spec_11_stdlib.rs::result_ok_constructs, tests/spec_11_stdlib.rs::result_err_constructs, tests/spec_12_runtime.rs::empty_vec_let_bound_freed, tests/spec_12_runtime.rs::closure_capturing_closure_balanced, tests/build_confidence.rs::mode_equiv_pattern_match_nested, spec/03-types.md §3.11.1
status: open
---

# Tightened §3.11.1 (full concreteness) rejects 6 previously-green e2e programs — realign

## Issue

S84 FIXME 0386 flipped the §3.11.1 codegen-reaching ambiguity verdict from the
representation-determinacy predicate (`is_representation_undetermined()` + the
`adt_type_is_mixed_shape` gate) to **full concreteness** (`!ty.is_concrete()`),
per the tightened spec (commit `2290aa9`) and `design/arch/concrete-boundary-type.md`
§3.1. The verdict now rejects ANY residual free `Type::Var` at a codegen-reaching
value position — no representation exemption, no `Mixed`-shape gate.

This is the intended verdict, and the 5 acceptance guards /qa committed in `3fedb6b`
flip green on it (4 directly; the 5th is blocked by a *separate* frontend parse bug,
FIXME 0389). But the tightening's blast radius extends to **6 pre-existing e2e tests**
that encoded the OLD lenient behaviour. All 6 now produce the clean
`"ambiguous type; add an annotation to pin the type of the polymorphic value bound
in \`…\`"` error. They were GREEN at baseline (159f544), RED after 0386:

| Test | Program | Unpinned var |
|---|---|---|
| `spec_04_expressions::vec_literal_empty` | `(vec-len [])` | `[]` : `(Vec a)` |
| `spec_12_runtime::empty_vec_let_bound_freed` | `(let [xs []] (vec-len xs))` | `xs` : `(Vec a)` |
| `spec_12_runtime::closure_capturing_closure_balanced` | `(let [f (fn [x] x)] (let [g (fn [] f)] 42))` | `f` : `(Fn [a] a)` captured |
| `spec_11_stdlib::result_ok_constructs` | `(match (Ok 42) [(Ok x) (= x 42) (Err _) false])` | `(Ok 42)` : `(Result Int b)` (phantom `b`) |
| `spec_11_stdlib::result_err_constructs` | `(match (Err "oops") [(Ok _) false (Err _) true])` | `(Err "oops")` : `(Result a String)` (phantom `a`) |
| `build_confidence::mode_equiv_pattern_match_nested` | `(defn main [] (Pure (match (Ok 42) [(Ok x) x (Err _) -1])))` | `(Ok 42)` : `(Result Int b)` (phantom `b`) |

## Proposed resolution

These are spec-correct rejections under the literal tightened §3.11.1 verdict
(`!is_concrete()`). Realign each test the way the 5 acceptance guards were realigned:
either (a) add the disambiguating `:Type form` annotation that pins the var and
assert the now-correct concrete result, or (b) invert the test to assert the
ambiguity error (the worked-example rejection). The `(Vec a)`/`(Fn a)` cases use
the `:(Vec Int)`/`:(Fn …)` escapes (the `Vec` annotation now resolves — 0385 landed
in the same change-set); the `(Result …)`/`(Ok)`/`(Err)` cases pin via
`:(Result Int String)`.

## Operational implication / Context — PHANTOM-VAR ADJUDICATION (escalate to /arch + /spec)

The `(Result …)` cases (`result_ok_constructs`, `result_err_constructs`,
`mode_equiv_pattern_match_nested`) reject on a **phantom type-arg var** — `(Ok 42)`
is a fully-determined value (the `Ok` ctor carrying an `Int`); the rejected `b` (the
`Err` payload type) never materialises a runtime value. The strict verdict
`!is_concrete()` rejects it regardless ("no machine representation is the point",
§3.11.1) and the `ConcreteType` boundary agrees by construction (the design's
"agree by construction" invariant — narrowing the typecheck check to exempt phantom
positions would re-open the gap the arc closed). But the blast radius is broad: every
`(Ok x)`/`(Err y)` whose sibling arm is wildcarded now needs an annotation.

**This is a /spec interpretation question the /dev verdict cannot decide:** does the
tightened §3.11.1 intend to reject a phantom type-arg var (a var in an unused ctor
position that has no runtime representation in the constructed value), or only a var
that is *structurally part of the value's representation* (`None`/`[]`/`(Fn a)`)?
The /arch design (`concrete-boundary-type.md` §3.1) says `!is_concrete()` rejects ANY
var; if /spec intends a phantom-position exemption, both the typecheck verdict AND the
`ConcreteType` boundary type must carve it out together (to preserve agree-by-
construction). /dev implemented the design as written; /sprint should route the
phantom-var breadth question to /arch + /spec before /qa mass-realigns the `(Result)`
tests — the realignment shape (annotate vs invert) depends on the answer.
