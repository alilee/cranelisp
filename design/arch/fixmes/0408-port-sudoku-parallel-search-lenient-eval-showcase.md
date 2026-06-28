---
number: 0408
target: /port
filed_by: /sprint
filed_at: 2026-06-18
sprint_filed: 86
narrowed_at: 2026-06-27
sprint_narrowed: 92
refers_to: exemplar/solver.cl, exemplar/grid.cl, exemplar/plan-exemplar.md §"Wave 4 Parallelism Opportunities Assessment", exemplar/CLAUDE.md §"Known Issues", exemplar/tests.cl
status: open
---

# Sudoku exemplar — make the showcase fast (the perf carry)

> **NARROWED — S92 (Phase 6b), `/port`. The parallel-search EXPRESSION half is
> DONE; this FIXME now tracks the PERF half only.** Do not re-add the
> parallel-search work below — see "## Done (S92)". The Issue / Proposed
> resolution sections have been rewritten to the perf-half scope.

## Done (S92) — parallel-search expression (the contained half)

The backtracking search in `exemplar/solver.cl` was reshaped from the
sequential `try-digits` early-exit digit loop into a **divide-and-conquer**
search over the candidate digits (~40 lines, `solver.cl` only; `grid.cl`
untouched):

- `mask-to-digits` — enumerate the set digits (1-9) of a candidate mask → `(Vec Int)`;
- `first-success a b` — `(match a (Success s) (Success s) _ b)`: take `a` if it
  solved, else `b` (correct even when `b` was computed speculatively — pure
  branches, the loser's work is discarded);
- `solve-range g idx digits lo hi` — copy-free index-range D&C: base `hi-lo==1`
  commits the digit and `solve`s; else split at `mid` and combine the two
  **independent expensive recursive solves** with `first-success`.

The two `solve-range` calls are the independent expensive **apply-arguments** of
`first-success`, which **slice-1 lenient eval (S92) auto-sparks** — the search
parallelises with zero `spark`/`par` in the source, and the spark-budget
create-gate bounds over-sparking (over budget → serial arm). See
`design/backend/lenient-eval.md` §2.5.

Validated: easy 9×9 solves end-to-end; exemplar suite **40/40 green under both
default (parallel) and `CRANELISP_NO_LENIENT=1` (serial)** — the parallel ≡
serial equivalence guard (`solver/test-solve-parallel-equiv`, full solution
pinned). The Wave-4 "inherently sequential / counterexample" verdict in
`plan-exemplar.md` was superseded (constraint *propagation* is sequential;
backtracking *search* is embarrassingly parallel — Sudoku is a showcase of
**budget-bounded speculative parallel search**). The web-side per-request
concurrency moved to the **effect-concurrency track**
(`design/arch/effect-concurrency.md`), distinct from this inferred-parallelism
axis.

## Issue (perf half — carried)

The reshape parallelises the search *structurally*, but parallel is currently
**~10× SLOWER than serial** — a never-slower-than-serial **floor VIOLATION**,
not merely "no speedup" (S94 measurement, /port). Debug-backend A/B of the
exemplar suite: **~20 s parallel vs ~1.9 s serial**, **sys-time dominated**
(~21 s sys parallel vs ~0.05 s serial; user ~43 s = many cores busy spinning).
This is **shape-independent** — the retired S92 `solve-range` apply-arg shape
and the S94 stdlib-`par-map-reduce` shape measure identically (~19.5 s / ~1.7 s).

**Mechanism (S94, isolated with a free-standing repro ladder).** The
**immutable copy-per-edit grid** dominates — `eliminate`/`set-cell`/`assoc`
copy the full 81-cell Vec on every modification (quadratic), and the Vec holds
**heap-allocated RC-managed `Cell` ADTs**, so each copy also atomically bumps
81 element RCs and each guess allocates fresh `Cell`s. Under the spark
substrate this generates **allocator-lock + atomic-RC contention** across the
worker threads, and that contention — not the create-gate's spark *count*,
which it does bound — is what blows up `sys` time and breaks the floor. A repro
ladder confirms the penalty scales with allocation/RC, not compute:

| Workload | parallel real | serial real | parallel user | parallel sys |
|---|---|---|---|---|
| pure compute (examples/30) | 1.3 s | 0.9 s | 1.9 s | 0.04 s |
| int-Vec copy (D&C) | 3.1 s | 2.85 s | 16.4 s | 0.87 s |
| ADT-Vec copy (D&C) | 6.9 s | 5.0 s | 45.8 s | 2.3 s |
| Sudoku suite | ~20 s | ~1.9 s | ~43 s | ~21 s |

Pure-compute parallel ≈ serial with sys≈0 (floor holds); adding per-node Vec
copy then heap-ADT copy walks the penalty up to the Sudoku's 10×. Repro `.cl`
ladder handed to `/qa` for a narrow guard (S94). Genuinely-hard puzzles still
run for minutes, so `solver/test-hard-puzzle` stays excluded from the runner.

Two compounding causes, unchanged from the original filing:
- **Copy-per-guess representation** (the dominant, fixable cause) — now
  understood as allocator/atomic-RC contention under parallelism, which is
  *why* parallel is actively slower, not just flat.
- **Unoptimized debug backend** (no release/Tier-2 backend until Phase H).

**Cross-skill note (`/backend`):** the create-gate's never-slower-than-serial
floor (`design/backend/lenient-eval.md` §3.6.3) holds for compute-bound sparks
but is violated by allocation-bound sparks, because the gate bounds spark
*count* but not the global-allocator / shared-value-atomic-RC contention each
sparked branch generates. Worth assessing whether the floor claim should be
scoped, or whether a contention-aware / per-arena gate is warranted.

## Proposed resolution (perf half)

1. **Fix the copy-per-guess representation** so each guess is not a full
   81-cell Vec copy — a persistent / structural-share Vec, or an in-place
   candidate-mask scheme. This is the change that lets the already-present
   parallel search *show* a speedup. (DEF-2's curated-`conj` RC bug was fixed
   in S86; the curated Vec verbs are usable here.)
2. **Phase-H benchmark.** Once the quadratic copy is gone, measure the parallel
   search under a release/Tier-2 backend and record the speedup number against
   the ~3.3 s / ~8.5 s baselines. Coordinate timing with Phase H — a release
   build is the right moment to land the perf numbers.
3. **Re-include `test-hard-puzzle`** in `exemplar/tests.cl` once a hard puzzle
   solves in fast-test time, and refresh the `/repl` `sudoku.demo` showcase to
   highlight a *measured* parallel speedup.

## Operational implication / Context

- **Demo / showcase-quality** perf improvement, deliberately carried. The
  parallel-search *expression* (S92) makes the centerpiece *show* the language's
  inferred parallelism; this carry makes it *fast*.
- Depends on: a non-copying grid representation (the actionable trigger now) +
  the Phase-H release/Tier-2 backend (for the headline numbers).
- The equivalence guard (`test-solve-parallel-equiv`) and the 40/40 two-mode
  green run are the regression guards that protect the reshape while the perf
  carry is open.
