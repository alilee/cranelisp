---
number: 0459
target: /backend
filed_by: /arch
filed_at: 2026-06-28
sprint_filed: 94
refers_to: design/backend/lenient-eval.md §2.6.2, design/backend/lenient-eval.md §3.6.3 (and the acceptance-test floor language §3.6.3 Residual 1 / line ~668/696)
status: open
---

# Scope the lenient-eval floor claim to spark-machinery overhead — it does not cover per-branch user contention

## Issue

`design/backend/lenient-eval.md` §2.6.2 ("The parallelism this actually extracts (and the
floor)") and §3.6.3 ("Floor-restoration argument") state that the spark-budget create-gate
restores the never-slower-than-serial floor and "collapses the measured ≈140× back toward
≈1×." That argument is **correct within its scope** — the create-gate bounds spark *count*,
so the *spark-machinery* overhead (IVar/thunk allocation per node) is `O(cap)`, which is the
`fib` explosion it was built for.

But the prose implies a **broader floor** than the gate delivers. /port measured (Sprint 94,
Phase 6) that the floor is **violated up to ~10×** for allocation-/RC-heavy parallel
workloads (Sudoku copy-per-guess: 81-elem Vec of RC-managed `Cell` ADTs per branch, parallel
~20s vs serial ~1.9s). Root cause: the **per-branch user-level** heap allocation + atomic-RC
traffic (global allocator lock + atomic-RC cache-line bouncing across workers, Decision 13)
that each of the (bounded) `cap` live branches generates concurrently. The create-gate's
count-only signal cannot see this — count is the wrong signal for contention.

The arch-thesis floor has been scoped accordingly in
`design/arch/effect-concurrency.md` §3 + new §3.1 (S94 /arch ruling, verdict = BOTH: scope
the claim now + specify a contention-aware gate as the in-track path back; Phase H is the
structural cure and the sequencing edge is *reinforced*, not pulled forward). The backend
design doc should be brought into line.

## Proposed resolution

In `design/backend/lenient-eval.md`:

1. **§2.6.2 / §3.6.3** — add a scope note: the create-gate restores the floor against
   *spark-machinery* overhead (IVar/thunk allocation, bounded `O(cap)`); it does **not**
   bound *per-branch user-level* allocation + atomic-RC contention. Cross-reference
   `effect-concurrency.md` §3.1 for the contention-aware-gate plan and the Phase-H structural
   cure. Qualify the "collapses ≈140× toward ≈1×" / acceptance-test (`ON < 1.3·OFF`) floor
   language as holding for allocation-/RC-light branches.

2. **The contention-aware gate (design, not implement now).** Sketch the two-layer extension
   per `effect-concurrency.md` §3.1:
   - **Static (first):** extend the sparkability cost heuristic (§2.2) from a compute-cost
     axis to also carry an **allocation/RC-density** axis — an allocation-/RC-dominated branch
     stays sequential even when its compute cost clears the "expensive Apply" bar.
   - **Dynamic (later):** gate the runtime create-gate on a shared-substrate contention
     signal (allocator / atomic-RC hotness) in addition to in-flight spark count — same family
     as §3.6.4 / FIXME 0442 (unified CPU+IO budget); rides with that, not ahead of it.

   Both layers are **rayon-side CPU-spark increments** (independent of the reactor work,
   §7 de-risking). Sequence as a create-gate refinement in the backpressure-family slice
   (slice 3/4), or earlier if the Sudoku exemplar (FIXME 0408) forces it.

## Operational implication / Context

This is a **doc-scope correction + future-slice design sketch**, not an implementation ask.
/qa is pinning a failing-not-ignored guard for the floor violation in parallel (the durable
regression record); this FIXME is the backend-side design alignment that complements the
arch ruling. The structural cure (atomic-RC contention removal: thread-local RC,
escape→stack/region, Perceus reuse) is **Phase H**, after the concurrency track — the
finding reinforces that sequencing edge (the non-atomic-where-thread-local opt is *defined
by* which values cross threads, which the concurrency model must settle first — Principle 8).
