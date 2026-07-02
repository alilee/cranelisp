---
number: 0462
target: /design
filed_by: /dev
filed_at: 2026-07-02
sprint_filed: 99
refers_to: design/backend/ring2-rc.md §5.5.2.6, design/backend/lenient-eval.md §4.4.1, design/arch/effect-concurrency.md §3.1, tests/plan/s99-measurement.md §8
status: open
---

# Capture-by-borrow's §5.5.2.6 volume prediction is empirically refuted — the (b) prize is the leaf vec-COW RC, not spark captures

## Issue

Wave 1b implemented capture-by-borrow across structured fork-join **exactly within
the FIXME 0461 boundary** (structural-join gate; coarse borrow of all joined-spark
captures; return-value-only retain; `LaunchContinue` excluded; §4.5 keepalive
carve-out). It is correct and byte-identical-off (canonical suite 1807/1/0; the
mandatory `LaunchContinue`-exclusion, parallel≡serial, heap-balance, and inc-drop
guards are green).

The **ablation** (`s99-measurement.md` §8, release/system, N-worker, 5-rep medians)
shows the toggle recovers **~0% of the (b) atomic-RC contention** it was funded to
remove:

- **F2 (the clean low-variance contention probe): user-time FLAT** (17.86 → 18.16 s),
  wall flat. `rc_inc` drops only **897 of 170,000,000 (0.0005%)**.
- F1/F3 drops: −1,003 / −577. F4-hard drop: −23,144 of 52.6M.
- The F4-hard wall "1.9×" in the first median pass is a **false green** — verified
  search-path variance (OFF single-reps span 4.99–16.66 s, ON 3.38–18.41 s, fully
  overlapping); `rc_inc` moved 0.04%, so the wall delta is not attributable to the
  borrow (`memory/feedback_verify_fix_not_symptom_absence.md`).

The borrow *does* work — with it on, parallel `rc_inc` == serial `rc_inc` exactly,
proving it elides precisely the spark-capture incs. There are just **hundreds** of
them, not the millions §5.5.2.6 predicted.

## Root cause of the mis-prediction

§5.5.2.6 predicted `rc_inc` drops by `≈ captures-per-spark × spark-count ≈ leaf-count
× per-leaf shared-capture arity`. Two errors:

1. **Spark count is create-gate-budget-bounded (`O(cap)`, §3.6), NOT leaf-count.**
   The budget caps concurrent sparks far below the leaf count, so the number of
   spark captures elided is small and size-insensitive.
2. **The dominant (b) traffic is the LEAF copy-work, not captures.** Each
   `(vec-set g …)` in `copy-work` COW-copies the 81-cell grid Vec and **bumps every
   retained `Cell`'s refcount** (~81 incs × COPIES × leaves ≈ the 170M on F2). These
   are inside the computation — not spark captures — so capture-by-borrow (correctly,
   by its scope) never touches them.

## Proposed resolution (`/design`)

1. **Correct `ring2-rc.md` §5.5.2.6** — replace the volume prediction with the
   measured result (capture-borrow removes hundreds of incs, budget-bounded, not
   leaf-scaled) and record that on F1–F4 it recovers no measurable (b) contention.
   The correctness/soundness content (§5.5.2.1–.5) and the mandatory guards
   (§5.5.2.6 test list) STAND — only the "inc-count reduction witness" *magnitude
   claim* is wrong.
2. **Re-point the (b)-cure funding** (`effect-concurrency.md` §3.1, the §6 decision
   table's "FUND — capture-by-borrow (b-cure)" bullet). On this evidence the (b)
   prize is the **vec-COW leaf refcount traffic**, addressable by (i) owned-copy
   mutate-in-place / last-use on the freshly-COW'd grid (a §5.5 last-use extension,
   not a capture rule) and/or (ii) the saturation gate (FIXME 0459) throttling the
   number of branches concurrently bouncing those cell cache-lines. Capture-by-borrow
   should be re-scoped as a *correct, zero-cost-off, Phase-H-durable substrate*
   (§5.5.2.5) — landable — but **not** as the funded (b) performance cure.

## Operational implication / Context

- **Close-time default-on decision (`/sprint` + `/review`):** on this ablation, do
  NOT flip `CRANELISP_CAPTURE_BORROW` default-on for a performance reason — there is
  no measured (b) recovery to justify perturbing the canonical path. Keep it opt-in
  until a real (b)-cure lands (or land it default-off as a correctness substrate).
- The implementation confines to `cranelisp-backend` (no `cranelisp-types` /
  public-API impact; `public-api.txt` unchanged). This FIXME is about the design
  *prediction* and *funding*, not the mechanism, which is within the 0461 boundary.
