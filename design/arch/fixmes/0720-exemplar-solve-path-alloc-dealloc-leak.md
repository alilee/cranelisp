---
number: 0720
target: /qa
filed_by: /port
filed_at: 2026-07-20
sprint_filed: 114
refers_to: exemplar/solver.cl (solve/set-cell/eliminate COW path) +
  design/arch/backlog/performance.md §"0408 — Sudoku exemplar copy-per-guess" +
  SPRINT.md Track B MS-P8 (0408 never-freed face, drained W4)
status: open
---

# Exemplar full solve leaks ~11.8k objects/solve (allocs≠deallocs) after the W4 MS-P8 fix

## Severity
Important (memory leak in the showcase's hot path; the S114 dispatch item-2 explicitly
asked /port to corroborate the MS-P8 conj-loop fix from the exemplar — "the exemplar is
the real program")

## Measurement (`CRANELISP_RC_STATS=1`, this VM, consistent build)

| Program | allocs | deallocs | residue | notes |
|---|---|---|---|---|
| `hello.cl` (baseline) | 5 | 4 | **1** | the one live "hello" string; establishes the counter does NOT count at-exit teardown |
| `solver.cl` (1 solve, parallel) | 26457 | 14634 | **11823** | easy puzzle |
| `solver.cl` (1 solve, `CRANELISP_NO_LENIENT=1` serial) | 26457 | 14634 | **11823** | byte-identical to parallel |
| `user.cl` (1 solve + HTML render) | 30007 | 18120 | **11887** | |
| `tests.cl` (2 full solves + 38 small tests) | 60413 | 36049 | **24364** | ≈ 2× per-solve + small-test residue |

## Why this is a genuine leak, not benign at-exit residue

1. **The counter does not count teardown.** `hello.cl` shows residue = 1 = its single
   live-at-exit string. So residue = live-at-exit + genuine leaks.
2. **`main` returns a scalar.** `solver/main` and `user/main` return `(IO Int)` (the exit
   code); the solution grid is consumed by `format-board`, nothing large is live at exit.
   Live-at-exit should be ~O(1), yet residue is ~11.8k.
3. **Identical serial and parallel.** `NO_LENIENT=1` gives the exact same 11823 — this is
   NOT speculative-thunk retention or a concurrency-specific leak; it is a plain RC leak
   in the copy path (serial has no sparked branches).
4. **Scales linearly per solve.** 1 solve ≈ 11.8k; 2 solves ≈ 24.4k. Structural, per-solve.

## Relationship to 0408 and MS-P8 — the reconciliation asked for

`design/arch/backlog/performance.md` §0408 frames the copy-per-guess as a **performance**
finding ("copies the whole 81-cell Vec per guess … allocation-dominated") and
`exemplar/CLAUDE.md` explicitly says "This is a performance finding, **not a correctness
defect**." That framing is about copy *cost*. The RC evidence here is a distinct claim:
the copied/discarded intermediate grids are **never freed** (allocs≠deallocs), which is the
MS-P8 "0408 never-freed face" that SPRINT.md Track B says was **drained in W4** ("MS-P8 =
missing release of the superseded heap loop-param at the TCO tail-jump … 1 leak/iter …
allocs==deallocs at N=20"). W4's `allocs==deallocs` was verified on a **small controlled
loop** (N=20 param-flush); the exemplar's full solve — the first-real-program contact the
sprint named — still shows an ~11.8k/solve imbalance.

## Ask

Attribute: is the ~11.8k/solve residue (a) the inherent 0408 copy-per-guess churn that is
genuinely freed and the RC_STATS gap is an accounting artifact I've misread; (b) a
**residual never-freed face** the W4 MS-P8 fix did not cover (the exemplar's
`set-cell`/`assoc` COW + `eliminate`/`propagate`/backtrack discard path, not the N=20
tail-jump loop the fix targeted); or (c) a distinct COW-drop leak. If (b)/(c), it wants a
narrow scaling repro (per-solve residue grows with backtracking depth) and an owner
(backend RC, likely). The discriminators to hand: identical serial/parallel, per-solve
linear scaling, 1-object baseline floor. RC_TRACE on a reduced puzzle will name the
first freed-while-reachable / never-freed cell.

## /port disposition

The showcase is **correct** end-to-end regardless (right solution, exit 0, both modes).
This is memory hygiene, not a crash — but it is the exact thing item-2 asked me to check,
and the answer is "no, they do not balance." `test-hard-puzzle` stays excluded from the
runner (the 0408 carry). No exemplar source change proposed; this is a compiler-side
attribution request.
