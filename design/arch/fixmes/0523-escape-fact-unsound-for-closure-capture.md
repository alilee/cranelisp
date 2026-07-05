---
number: 0523
target: /typecheck  # cranelisp-typecheck — ownership escape analysis
filed_by: /dev  # cranelisp-backend, B3.4 (first hard consumer of the escape fact)
filed_at: 2026-07-05
sprint_filed: 102
refers_to: crates/cranelisp-typecheck/src/ownership/transfer.rs (escapes computation); crates/cranelisp-typecheck/src/ownership/sites.rs (fact annotation); design/backend/ownership-codegen.md §4.1/§4.3; design/arch/ownership-inference.md §R6 (suspension-points-as-escape-edges)
status: open
---

# Escape fact is UNSOUND for closure capture — a captured value is marked `escapes = Some(false)` even when its closure escapes (hard UAF)

## Issue

B3.4 (stack slots for `NoEscape` scalar-payload aggregates) is the FIRST hard
consumer of the `escapes` site fact — it is the first place `escapes = Some(false)`
drives a decision (stack-allocate) that DANGLES if wrong (a stack aggregate whose
pointer outlives its frame is a use-after-free the RC-balance guards cannot catch;
`memory/feedback_verify_fix_not_symptom_absence`). Consuming it surfaced a
soundness gap in the ownership escape analysis, exactly parallel to how B3.2 was
`param_modes`' first hard consumer and surfaced the 0520 result-mode gap.

**A value captured by a closure is marked `escapes = Some(false)` even when the
closure escapes the frame.** Two shapes, both proven to produce a hard UAF:

1. **Intra-procedural** — `(defn f [n] (let [p (Rect n n)] (fn [] … p …)))`.
   The `(Rect n n)` Apply is annotated `escapes = Some(false)`, but `p` is
   captured by the returned closure, so it escapes `f`'s frame. Verified: the
   value stack-allocates, and once the popped frame is reused, reading the
   captured pointer yields garbage → `runtime panic: match failed` (the tag word
   is clobbered). Without frame reuse it returns the correct value — a
   textbook false-green UAF.

2. **Inter-procedural** — `(defn make-clo [x] (fn [] … x …)) (defn f [n] (make-clo (Rect n n)))`.
   `f`'s `(Rect n n)` is annotated `escapes = Some(false)` even though `f` has NO
   closure form in its own body — the capture happens in the callee `make-clo`,
   whose summary does not propagate "param captured into a returned closure" as an
   escape to the caller's argument.

The analysis IS sound for the other escape edges — all verified `escapes = Some(true)`:
returned directly (`(defn mk [n] (Rect n n))`), stored into a heap ADT
(`(Wrap (Rect n n))` returned), passed through a callee that returns it
(`(id (Rect n n))`), pushed into a returned vec (`(vec-push [] (Rect n n))`).
**Only closure capture (and, by the same R6 mechanism, spark/`ParBind`/
`LaunchContinue` suspension capture) is unsound.**

## Why the backend cannot gate around it

The inter-procedural case (2) has NO closure form in the constructing function's
own body, so no backend-local syntactic scan can detect it. Re-deriving
inter-procedural escape in the backend would violate the narrowness counterweight
(`ownership-inference.md` — the backend performs no escape/strand reasoning of its
own; it consumes verdicts). The escape fact must be a sound hard-UAF decision AT
THE PRODUCER before B3.4 can consume it.

## Proposed resolution

Treat closure capture (and spark/suspension capture, R6) as an escape edge in the
ownership escape analysis, both intra- and inter-procedurally:

- **Intra:** a value captured by a `Lambda` whose closure value can escape the
  frame (returned, stored, passed-on) is `Escapes`. A closure that is created and
  fully consumed in-frame (invoked and dropped locally) does not force escape —
  but conservative widening (any captured value escapes) is sound and is the safe
  first cut.
- **Inter:** a callable that captures a param into a closure value it returns/leaks
  must report that param as escaping in its `ModeSummary` (`param_flow` /
  the escape summary the fixpoint propagates), so a caller's argument at that
  position is marked `escapes = Some(true)`.

`design/arch/ownership-inference.md` §R6 already commits to "suspension points as
escape edges"; this is the same commitment for ordinary closure capture. Until it
lands, B3.4 stays gated at the conservative all-heap point.

## Operational implication / Context

**B3.4 is landed but HELD OFF** at the conservative point behind a single
compile-time flag — `STACK_ALLOC_ESCAPE_FACT_SOUND = false`
(`crates/cranelisp-backend/src/compiler/fn_compiler.rs`). The complete mechanism
(the four eligibility gates + `heap::emit_stack_alloc` with the immortal-RC
sentinel header + the stack-slot-hit counter) is implemented and unit-tested;
`false` makes it byte-identical to pre-B3.4 (no site stack-allocates). When this
FIXME resolves (the analysis treats closure/spark capture as an escape edge), flip
the flag to `true` and the mechanism activates unchanged — no backend re-work.

A narrow failing e2e repro of both UAF shapes is owed from `/qa` (per the defect
protocol) so the flip is guarded: a `capture-escape` / interprocedural-capture
program whose stack-allocated captured value dangles when the popped frame is
reused (`MALLOC_PERTURB_` + a frame-clobbering non-tail recursion between capture
and call surfaces it deterministically as `match failed`).
