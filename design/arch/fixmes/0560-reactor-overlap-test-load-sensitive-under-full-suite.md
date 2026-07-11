---
number: 0560
target: /dev
filed_by: /sprint
filed_at: 2026-07-11
sprint_filed: 108
refers_to: crates/cranelisp-intrinsics/src/reactor (test `two_async_reads_overlap_max_not_sum_one_thread`); tests/CLAUDE.md §"Failing-test discipline" (no "timing-sensitive")
status: open
---

# `reactor::tests::two_async_reads_overlap_max_not_sum_one_thread` is load-sensitive — passes in isolation, fails under full-suite contention

## Issue

Surfaced during S108 Wave-3 verification. The `#[cfg(test)]` test
`cranelisp-intrinsics::reactor::tests::two_async_reads_overlap_max_not_sum_one_thread`
**failed in a full `cargo nextest run --no-fail-fast`** (parallel, contended) but
**passes deterministically in isolation**
(`cargo nextest run -p cranelisp-intrinsics -E 'test(two_async_reads_overlap_max_not_sum_one_thread)'`
→ PASS, ~0.2s). It was GREEN in the S108 Wave-1 full run and RED in the Wave-3
full run — i.e. intermittent, gated on scheduling contention, NOT on any S108
change (S108 touched only `src/` REPL display + agent; this test is a different
crate/binary entirely). It is not an S108 regression.

The test asserts real-time OVERLAP of two async reads on one thread (max-not-sum
wall-clock), so under a loaded parallel test pool the reads are starved and the
overlap window the assertion expects does not materialise.

Per `tests/CLAUDE.md` §"Failing-test discipline" (migrated from the retired
ledger, S108 M1): "timing-sensitive" is not an acceptable disposition — a test
that assumes a scheduling/timing property is either testing something real (name
it and pin it deterministically) or is incorrectly written (fix it). This one is
testing something real (overlap != sum), so it must be **pinned deterministically**.

## Proposed resolution

`/dev` (cranelisp-intrinsics), owner of the test: make the overlap assertion
independent of real-wall-clock contention — options for /dev to weigh:
- drive the reactor against a mocked/virtual clock so the overlap is asserted on
  logical time, not measured wall-clock;
- or assert the structural fact (both reads were in-flight concurrently — e.g. a
  concurrency counter/high-water mark) rather than a wall-clock ratio;
- or, if a real-time assertion is genuinely required, segregate the test from the
  contended parallel pool (its own serial group) AND widen the tolerance so pool
  scheduling cannot starve it — least preferred (masks rather than pins).
`/qa` may want to confirm the real-vs-mis-written classification, but the isolation
PASS indicates the assertion is real and the wall-clock coupling is the defect.

## Operational implication / Context

- Intermittent full-suite REDs erode the "any RED not tracing to a known open
  defect is a regression" triage convention — a load-flaky test poses as a
  regression on a bad-luck run. Fixing it protects the triage signal the S108
  ledger retirement now leans on.
- Not a blocker for S108 close (pre-existing, unrelated crate, passes in
  isolation) — carried as a next-sprint /dev item.
- Delete when the test is pinned deterministically and survives repeated full-suite
  runs.
