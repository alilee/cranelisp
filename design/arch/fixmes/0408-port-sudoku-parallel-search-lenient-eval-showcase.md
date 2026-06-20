---
number: 0408
target: /port
filed_by: /sprint
filed_at: 2026-06-18
sprint_filed: 86
refers_to: exemplar/plan-exemplar.md §"Wave 4 Parallelism Opportunities Assessment", exemplar/solver.cl, exemplar/CLAUDE.md §"Known Issues"
status: open
---

# Sudoku exemplar — make the showcase actually demonstrate lenient-eval parallel search (and be fast)

## Issue

The Sudoku exemplar is now THE showcase centerpiece (S86) and is meant to
*demonstrate the language*. But as measured during S86 UAT it:

1. **Does not exercise the language's flagship lenient-eval / auto-IO
   parallelism at all** — zero `spark`/`par`/`Par`/commutative constructs; the
   solve is strictly sequential and the web serve loop handles one request at a
   time.
2. **Is slow**: `POST /solve` for an *easy* 9×9 measures **~3.3 s** (standalone
   stripped exe, live HTTP); hard puzzles "run for minutes" (`test-hard-puzzle`
   is excluded from the test runner for this reason).

The exemplar's own Wave-4 assessment (`plan-exemplar.md §29`) dismissed
parallelism as inapplicable and framed Sudoku as a "useful counterexample."
That conclusion is **only valid for constraint *propagation*** (each
propagation step depends on the prior grid state). It **misses that the
backtracking *search* is embarrassingly parallel**: at each guess point the
candidate-digit branches are fully independent (each tries a different digit on
its own grid), so they are exactly the independent-`let`-binding /
sparkable-IO shape lenient eval was built for. The "counterexample" framing was
acceptable when Sudoku was *an* exemplar; it is at odds with Sudoku being *the*
language showcase.

The slowness has two compounding causes:
- **Immutable copy-per-edit grid**: `eliminate`/`set-cell`/`assoc` copy the full
  81-cell Vec on every modification (quadratic; documented in
  `exemplar/CLAUDE.md §"Known Issues"`).
- **Unoptimized debug backend** (no release/Tier-2 backend until Phase H).

## Proposed resolution

A demo-quality rework of the solver (and the plan-doc verdict):

1. **Parallel backtracking search (the lenient-eval showcase).** At each guess
   point, evaluate the recursive solve for each candidate digit as **independent
   `let` bindings** (sparkable → lenient-eval parallel), then take the first
   `Success`. This genuinely exercises the flagship feature and speeds up hard
   puzzles. (Speculative branches do work pruning would skip, but with
   work-stealing this is a net win on deep search and — crucially — it makes the
   centerpiece *show* parallelism.) Consider also a parallel-propagation pass
   over independent units where the data-flow allows.
2. **Fix the copy-per-guess representation** so each guess is not a full 81-cell
   Vec copy — an in-place candidate-mask scheme or a persistent/structural-share
   Vec. (DEF-2's curated-`conj` RC bug is fixed as of S86, so the curated Vec
   verbs are usable in the rework.)
3. **Supersede the Wave-4 verdict**: update `plan-exemplar.md §"Wave 4
   Parallelism Opportunities Assessment"` — the "inherently sequential /
   counterexample" conclusion is wrong for the search dimension; record the
   parallel-search opportunity and the measured baseline (~3.3 s easy 9×9).

## Operational implication / Context

- This is a **demo / showcase-quality** improvement, deliberately deferred out
  of S86 (the user's call: "a fixme for demo"). S86 delivered the *working* web
  front-end (`--run` + standalone `--link`, DEF-4/5/6 fixed); this makes the
  centerpiece a *good* showcase of the language's parallelism and performance.
- Depends on: lenient eval (live since S25) + auto-IO scheduling (S85). Raw
  speed also benefits from the Phase-H release/Tier-2 backend — coordinate
  timing (a release build may be the better moment to land the perf numbers).
- Downstream: the `/repl` `sudoku.demo` showcase demo should be refreshed to
  highlight the parallel search once it lands; the `tests.cl` runner can then
  re-include a (now-fast) hard-puzzle test.
- Web-side concurrency (serving requests in parallel) is a *separate* axis,
  tracked by FIXME 0407 (Model B closure-callback) — not this FIXME.
