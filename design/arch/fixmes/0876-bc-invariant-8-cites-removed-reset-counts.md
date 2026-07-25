---
number: 0876
target: /arch
filed_by: /design (intrinsics)
filed_at: 2026-07-25
sprint_filed: 118
refers_to: design/arch/bounded-contexts.md §4b invariant 8 ("No state across
  sessions"); crates/cranelisp-intrinsics/src/alloc.rs:121 (reset_counts);
  sprints/SPRINT.md §Architecture review ruling 7; design/intrinsics/diagnostic-modes.md §9.4
status: open
---

# BC §4b invariant 8 cites `reset_counts`, which ruling 7 removes

## Issue

`design/arch/bounded-contexts.md` §4b invariant 8 reads:

> **No state across sessions.** Stats accessors (`alloc_count`, etc.) are
> process-global — `int`'s `reset_counts` should be called at session start in
> test contexts. Production runs do not call `reset_counts`.

S118 arch ruling 7 (transcribing the approved-but-unlanded S116 ruling 5)
removes `reset_counts()` and `bytes_peak()` from `cranelisp-intrinsics`. The
invariant's second and third sentences become false the moment that change-set
lands: there is no `reset_counts` to call, and — the reason for the removal —
a public counter reset can invalidate M3's monotonic-counter evidence, so
prescribing one is now actively wrong.

Nothing in `int` ever called it (zero repository consumers, S115 audit RI-3),
so the invariant was already describing a practice that did not exist.

## Proposed resolution

`/arch` restates invariant 8 in the same window as the `/dev`(intrinsics)
removal (Track A, the 0850 change-set). Suggested substance — `/arch` owns the
wording:

- the stats accessors remain process-global with **no reset seam**;
- the surviving four (`alloc_count`, `dealloc_count`, `bytes_allocated`,
  `bytes_current`) are process-lifetime evidence, and the counts are what M3's
  exit parity check reads;
- the *absence* of a reset is now a load-bearing property, not an omission:
  it is what makes the M3 ledger trustworthy (Principle 18 — the invariant is
  enforced by there being no way to break it).

This is a documentation correction with no code or API consequence beyond the
already-approved subtraction. No cache-schema, heap-layout, C-ABI, or catalog
change.

## Context

Filed at S118 Phase 3 by `/design`(intrinsics) while recording the ruling-7
subtractive change in `design/intrinsics/diagnostic-modes.md` §9.4. The
crate-side rustdoc cleanup (`alloc.rs:63-80`, where four surviving accessors
each say "since the last `reset_counts`") is `/dev`'s and rides the same
change-set; only the cross-crate BC statement is `/arch`'s.
