---
number: 0445
target: /arch
filed_by: /sprint
filed_at: 2026-06-27
sprint_filed: 92
refers_to: stdlib/collections/vec.cl, design/backend/lenient-eval.md §2.5, design/arch/fixmes/0424-spark-apply-args-for-general-par-map.md
status: open
---

# Sanction a stdlib divide-and-conquer `par-reduce`/`par-map` as interim — or reserve the names for the 0424(ii) primitive

## Issue

Sprint 92 slice 1 shipped apply-argument sparking: a **divide-and-conquer** shape
(a node whose two recursive calls are independent expensive apply-args) now
auto-parallelizes. The `/stdlib` Phase-6a assessment found this is cleanly
expressible as a stdlib `par-reduce`/`par-map-reduce` over an index range with an
associative combiner — but it has **no consumer yet** (the exemplar Sudoku reshape
inlines its own D&C search; it does not call a stdlib par helper), so `/stdlib`
correctly **held** rather than build speculative surface.

Two coupled questions for `/arch` before `/stdlib` builds anything:

1. **Interim vs primitive.** A `.cl` D&C `par-reduce` is the *expressible-today*
   form, but the general "parallel map over an arbitrary collection with no
   author-side D&C restructuring" is **FIXME 0424(ii)** — a dedicated primitive,
   deferred. Is a hand-written `.cl` D&C helper the intended interim surface, or
   would it be throwaway against an imminent primitive (Principle 8 —
   build-subsumable-not-discardable)?
2. **Name reservation.** If a future primitive will claim `par-map`/`par-reduce`,
   reserve those names now (consistent with the §11.4a collection-verb
   reservation) so the interim `.cl` helper and the future primitive don't
   collide.

## Proposed resolution

`/arch` rules: (a) green-light a stdlib D&C `par-reduce` as the sanctioned interim
surface (shaped to be subsumed by 0424(ii)), with the honest constraints documented
(associative combiner; only wins for expensive per-element work; NOT a drop-in for
`vec-map`); OR (b) reserve the names and direct `/stdlib` to hold until the 0424(ii)
primitive lands. Either way, record the decision so `/stdlib` and the eventual
primitive author share one plan.

## Operational implication / Context

- **No defect, no failing test** — a capability/surface-shaping question, the
  correct use of a design FIXME (per `memory/feedback_no_fixme_with_failing_test.md`).
- Cross-ref **0424** (the spark-apply-args FIXME; option (i) shipped S92, option
  (ii) the deferred primitive). The D&C-not-vec-map limitation is the load-bearing
  honest constraint surfaced repeatedly in the S92 Phase-6a assessments.
