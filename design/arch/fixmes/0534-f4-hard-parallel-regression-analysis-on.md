---
number: 0534
target: /backend
filed_by: /qa
filed_at: 2026-07-06
sprint_filed: 103
refers_to: tests/plan/s100-ownership-verification.md §2.3 (II-G3), design/arch/effect-concurrency.md §3.1, design/backend/ownership-codegen.md §13.4 (B4 density-admission axis)
status: open
---

# F4-hard N-worker regresses ~20× under analysis-ON (II-G3 fails 121×; increment-II-introduced)

## Issue

The increment-II acceptance gate **II-G3** (F4-hard median N-worker wall ≤ 2×
serial) FAILS catastrophically, and the cause is an increment-II-introduced
parallel regression that the analysis-off differential isolates cleanly.

**Measured (release binary, S103 HEAD, settled load, 2026-07-06):**

| Config | analysis-ON | analysis-OFF (`CRANELISP_NO_OWNERSHIP=1`) |
|---|---|---|
| F4-hard **serial** | 0.91s | ~0.90s |
| F4-hard **N-worker** | **108.8s** (median; 3 reps 108.4 / 108.8 / 111.3 — tight) | **5.46s** (median; 5.1 / 5.46 / 17.18) |

- II-G3: N-worker/serial = 108.8 / 0.91 = **121×** (bar ≤ 2×).
- The ON-vs-OFF differential on the SAME binary, same fixture, settled load,
  is the attribution: **analysis-ON N-worker is ~20× slower than analysis-OFF**
  (108.8s vs 5.46s), while serial is unaffected (ON ≈ OFF ≈ 0.9s). The
  slowdown is parallel-only and analysis-on-only.
- **This is a regression vs increment I.** At S102 close the I-G4/F4 report
  recorded F4-hard N-worker ON=[8.38, 9.81, 14.54, 30.28, 33.0] vs
  OFF=[6.6, 12.16, 15.15, 15.6, 19.18] — ON ≈ OFF, max ~33s
  (`tests/plan/s100-ownership-verification.md` §2.2.1). Increment II opened a
  ~20× ON-vs-OFF divergence that did not exist at increment I.
- `f4_sudoku.cl` is unchanged since S102 Wave A (`c09c0a2`); the regression is
  purely compiler-side (the S103 Wave 3a/3b/3c increment-II change-sets:
  R5 value-flattening + reuse tokens + Wave-3c function registration).

## Probable mechanism

This is the known contention class (`effect-concurrency.md` §3.1 — the
Sudoku copy-per-guess workload that violates the "never slower than sequential"
floor for allocation-/RC-heavy parallel work; former FIXME 0459). The
hypothesis, for `/backend` to confirm:

- Increment II's borrow-elision + reuse-token check-elision **reduce the
  measured static allocation/RC density** that the **B4 density-admission axis**
  (`ownership-codegen.md` §13.4) reads to decide whether to spark a
  heap-returning branch or decline it to the serial arm.
- With the density reduced, B4 now **under-declines** on F4-hard: sparks it
  previously kept serial (the whole point of B4 — kill the over-sparking
  contention) are now admitted, re-exposing the parallel over-sparking
  thrashing. Net: 108s of redundant speculative work where OFF stays at 5.5s.

I.e. increment II's density reduction defeats B4's density-based decline on this
workload. The fix likely lives in the B4 admission heuristic (it must not
mistake ownership-reduced RC/alloc density for genuine low contention), not in
R5 or the reuse tokens themselves (both are correct — output is byte-identical
under the differential oracle; only the wall regressed).

## Repro

```
SYS_BIN=target/release/cranelisp python3 tests/perf/ig_gates.py --gates iig3 --reps 7
```
or the direct ON-vs-OFF differential in `tests/perf/s99_measure.py` (F4-hard,
Nworker, toggle both polarities). The `ig_gates.py` II-G runner (S103 /qa
extension) grades II-G3 and prints the distribution.

## Operational implication / Context

- Perf-lane finding (not canonical nextest); this FIXME is the durable
  record + trigger (per `memory/feedback_no_fixme_with_failing_test.md` — a
  perf-gate result is a script, not a suite guard, so the FIXME is the
  appropriate durable trigger).
- II-G1's parallel-must-pay half is a **separate, benign** non-pass (R5 made
  F2v serial 0.12s and F2v N-worker 10× faster than OFF; parallelism can't beat
  the now-super-cheap serial — not a regression). II-G4's wall is the documented
  §5-limit-1 F2-not-cured case (F2 N-worker ON ≈ OFF; system-allocator
  contention, cured only at the III-G composed end-state). **0534 is the one
  gate failure that is a genuine regression**, not a designed limit.
- Does not block correctness: the differential oracle is byte-identical-off
  throughout; the suite is green modulo the intentional 0528 RED.
