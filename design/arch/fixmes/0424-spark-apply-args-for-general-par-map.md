---
number: 0424
target: /arch
filed_by: /examples
filed_at: 2026-06-21
sprint_filed: 87
refers_to: examples/30-parallel-map-reduce.cl, crates/cranelisp-backend/src/compiler/control_flow/sparkability.rs, design/backend/lenient-eval.md, design/arch/effect-concurrency.md §7
status: open
---

> **/arch verdict (S93, CORRECTED by user S93 Phase-3 review) — no PRIMITIVE (declined, stands); `par-map` IS a /stdlib function; status stays open for (i)'s generalization.**
> A dedicated `par-map`/`par-reduce` **compiler primitive** is **not** sanctioned: an explicit
> parallel-map *primitive*/syntax cuts directly against the ratified effect-concurrency thesis
> (`design/arch/effect-concurrency.md` §1/§3 — the programmer writes ZERO concurrency
> primitives; parallelism is extracted from dataflow). **The (ii)-as-primitive sub-question
> is closed (declined).** BUT `par-map` / `par-reduce` / `par-map-reduce` **ARE legitimate
> /stdlib functions** — ordinary `.cl` library definitions over the inferred apply-arg
> sparking substrate, NOT compiler primitives, adding NO language surface. **`/stdlib` owns
> them** (this REVERSES the earlier "`/stdlib` holds / names merely reserved" disposition; the
> user keeps "no primitive" but rules stdlib provides the functions). What makes them parallel
> is exactly (i)'s apply-arg sparking — a stdlib `par-map` is an ordinary `map`/`fmap` whose
> per-element applications spark when independent + expensive, NOT a magic primitive. (i)'s
> divide-and-conquer apply-arg shape **shipped S92**; this FIXME stays **OPEN** for the
> full-independence generalization of (i) (+ limit #2, dependent-binding sparks), which is
> the substrate the stdlib `par-*` functions build on — a rayon-side increment (§7 de-risking)
> that can land anytime. **Companion FIXME 0445 (the stdlib D&C interim-or-reserve question) is
> resolved the STDLIB-PROVIDES way** (not "hold"): `/stdlib` provides the `par-*` functions and
> owns their sprint placement. See `design/arch/effect-concurrency.md` §7 "Verdict on
> `par-map`/`par-reduce` — no PRIMITIVE, but they ARE stdlib functions".

# Spark independent apply-arguments (and/or a par-map primitive) to enable a general parallel map over a Functor

## Issue

Lenient evaluation today sparks parallelism over `let` bindings ONLY. The
sparkability pass (`crates/cranelisp-backend/src/compiler/control_flow/sparkability.rs`,
`find_sparkable_bindings`) is invoked solely from `let_if.rs` for `let`
blocks. Two consequences limit how far parallelism generalises:

1. **Apply-arguments are never sparked.** `(f a b)` does not evaluate `a` and
   `b` in parallel, even when they are independent and individually expensive.
   Concretely, `(Pair (fib a) (fib b))` runs the two `fib`s serially because
   they are arguments to a constructor apply, not `let` bindings.

2. **Dependent let bindings are left serial.** A binding whose RHS references
   an earlier binding in the same block is excluded by the free-var check
   (`depends_on_earlier`), so it never sparks. This is a *conservative-analysis*
   limit, not a hard semantic one — the IVar machinery (`cranelisp-intrinsics/src/ivar.rs`)
   could spark the dependent binding and force the dependency on demand. Noted
   here as context; the primary ask is #1.

The user-visible gap (surfaced while reworking `examples/30-parallel-map-reduce.cl`
toward a general parallel map): a fully general **`par-map`** — map a function
over a Functor with every application running in parallel — is NOT expressible.
The natural implementation, `fmap` of an expensive function over a container,
compiles correctly but runs SERIALLY, because each per-element application is
an apply-argument (limit #1).

The example demonstrates the honest current state: a self-parallelising
divide-and-conquer map-reduce over a `Vec` (which works, by lifting each half
into an independent `let` binding), plus a **manual, per-shape** `par-fmap-pair`
that recovers parallelism for a known-arity container by hand-lifting each
element-application into an independent `let`. The manual workaround does not
generalise to arbitrary collections — which is exactly the gap a real
`par-map` would close.

## Proposed resolution

Pick one (or both) of:

- **(i) Spark independent apply-arguments.** Extend the sparkability analysis
  beyond `let` bindings to independent, non-trivial arguments of an apply, so
  `(Pair (fib a) (fib b))` sparks both `fib`s. This is the most general fix and
  directly enables `fmap fib` to be parallel with no new surface syntax. Cost
  heuristic, the ≥2-candidate gate, and the cheap-builtin/constructor exclusions
  carry over; the new question is per-call-site analysis of argument
  independence and the barrier placement at the apply.

- **(ii) A dedicated `par-map` / parallel-`fmap` primitive** the runtime sparks
  element-wise over a collection. Narrower than (i); does not help arbitrary
  apply sites, but gives users a direct, intention-revealing parallel map.

Either lets `examples/30-parallel-map-reduce.cl` replace its manual per-shape
workaround with a single general `par-map`, and lets the divide-and-conquer
trick retire in favour of the obvious recursive form.

## Operational implication / Context

- No defect, no failing test: this is a *capability gap*, not a spec violation
  or crash. Per `memory/feedback_no_fixme_with_failing_test.md`, a design FIXME
  (not a test) is the right record for a missing capability.
- `examples/30-parallel-map-reduce.cl` is the live demonstrator and will be
  simplified once this lands. The example currently labels both limits inline
  and shows the manual workaround, so the teaching stays accurate in the
  meantime.
- Reference: `design/backend/lenient-eval.md` §2 (the decision pass);
  `sparkability.rs` (the `let`-only scope); `ivar.rs` (the IVar machinery that
  already supports forcing on demand, relevant to limit #2).
