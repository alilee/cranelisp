---
number: 0442
target: /arch
filed_by: /design
filed_at: 2026-06-26
sprint_filed: 92
refers_to: design/backend/lenient-eval.md §3.6, design/arch/effect-concurrency.md §5 (concurrency descriptor — "global budget"), §14 (build sequencing, step 3 backpressure)
status: open
---

# One unified in-flight budget (CPU + I/O), or two?

## Issue

Sprint 92 slice 1 adds a **global in-flight-spark budget** to `ivar_spark`
(`cranelisp-intrinsics`, design home `design/backend/lenient-eval.md` §3.6): a
module-static `AtomicIsize` counter + `CRANELISP_SPARK_BUDGET` cap that bounds how
many pure CPU sparks are in flight on rayon. Over budget, a spark runs **inline on the
calling thread** instead of spawning.

This is deliberately shaped as the **CPU-side seed of the slice-4 I/O backpressure
budget** — the §5 concurrency-descriptor's "global budget" field ("optional cap on
total in-flight effects of this kind = the backpressure threshold," mapped to a bounded
channel / `Semaphore`; §14 step 3). Both bound total in-flight work of a kind. Principle 8
(no interim implementations) says the slice-1 counter must be subsumable by the slice-4
mechanism, not thrown away and not duplicated into a second unrelated throttle.

The open question is a cross-cutting interface decision that is **not slice 1's to make
unilaterally**: when slice 4 designs the descriptor→runtime-primitive mapping, should the
CPU spark budget and the I/O backpressure budget be **one unified budget abstraction**, or
two mechanisms that merely share a shape?

The non-trivial tension: the **over-budget actions differ fundamentally**.
- CPU spark over budget → **run inline on the caller** (a pure spark is cheap to fold back into the calling thread).
- I/O effect over budget → **admission-park / backpressure** (you cannot cheaply "run an I/O effect inline"; the descriptor's action is to block admission until a slot frees).

That difference may justify two distinct mechanisms sharing only the counter shape, rather
than one abstraction with a polymorphic over-budget action.

## Proposed resolution

`/arch` decides, when slice 4 (backpressure) is designed, whether:
- (a) a single budget abstraction (e.g. a per-kind budget table; over-budget action is a
  per-kind strategy: inline-fold for CPU, admission-park for I/O), subsuming the slice-1
  counter; or
- (b) two separate mechanisms (the CPU counter stays a standalone `ivar.rs` throttle; the
  I/O budget is a distinct `Semaphore`/bounded-channel admission gate), sharing only the
  conceptual "bound in-flight work of a kind" shape.

Either way, the slice-1 counter must be **subsumable, not orphaned** — keep it a plain
atomic counter + a cap + a single decision site (`ivar_spark`) so slice 4 can replace or
generalize it without reworking codegen.

## Operational implication / Context

- **Not blocking slice 1.** The standalone CPU counter is the correct, sufficient choice
  for slice 1 (Phase-2 verdict: slice 1 is rayon-only, independent of the async substrate).
  This FIXME records the unification decision for the slice-4 design sprint.
- **Trigger:** slice 4 (backpressure) design. Until then this idles correctly; per the
  "close FIXMEs each sprint" discipline, the unmet trigger (slice-4 not yet open) is the
  legitimate defer reason.
- No public-API impact on slice 1 (counter is module-private; the env knob is not public
  API; `cranelisp_ivar_spark` signature unchanged).
