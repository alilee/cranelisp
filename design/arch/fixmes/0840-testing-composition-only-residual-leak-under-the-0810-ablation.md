---
number: 0840
target: /testing
filed_by: /port
filed_at: 2026-07-21
sprint_filed: 115
refers_to: design/arch/fixmes/0810-*.md (the 88.9% face, pinned by
  tests/match_owned_temporary_scrutinee_0810.rs) + design/arch/fixmes/0837-*.md
  (the depth-≥2 class this is a candidate sixth instance of) +
  exemplar/CLAUDE.md §"Solve-path never-freed leak"
status: open
---

# The 11% the 0810 ablation leaves behind: a work-scaling leak that only appears in COMPOSITION

## Severity

**Important**, not Blocker — it leaks, it does not corrupt. Its value is that it
is the **acceptance-criterion residual** for 0810: without it, "the leak should
improve" replaces "the number must reach ≈1,300", and a partial 0810 fix would
be indistinguishable from a complete one.

## Issue

Ablating FIXME 0810's wrapper mechanism out of the Sudoku exemplar's propagation
path accounts for 10,508 of the 11,820 objects a serial solve leaks (88.9%).
**1,312 objects remain**, and they are not a constant — they scale with work:

| Ablated (no `Option` wrapper anywhere on the propagation path) | `eliminate-from-peers` calls | `set-cell` calls | residue |
|---|---|---|---|
| Already-solved grid (propagation is a no-op sweep) | 81 | 0 | **83** |
| Easy puzzle solved by propagation alone | 556 | 392 | **1,256** |
| Full `--run exemplar/solver.cl` (adds board formatting + print) | 556 | 392 | **1,312** |

Fit: ≈**1.0 object per `eliminate-from-peers` call** plus ≈**1.8 per
`set-cell`**. All numbers `CRANELISP_NO_LENIENT=1 CRANELISP_RC_STATS=1`, **warm
cache** — a cold cache adds a constant ~1,042 compile-session objects, so cold
and warm runs must never be compared to each other.

## What it is NOT — four measured negative controls

Each component is **exact on its own**. That is what makes this interesting, and
what a reduction has to get past:

| # | Shape | Result |
|---|---|---|
| N1 | `set-cell` (`(match g [(Grid cells) (Grid (assoc cells idx c))])`) in a tail loop superseding the grid param | N=100 → 1278/1277, N=1100 → 4278/4277 — residue 1, **slope 0** |
| N2 | `peers` (a 20-element Vec built by a `conj` accumulator) called N times, result consumed immediately | N=1100 → 23101/23101 — **exact** |
| N3 | A Vec **literal** returned by a callee, then carried as a loop parameter through a tail-recursive helper that also supersedes an ADT param | N=100 → 103/101, N=1100 → 1103/1101 — residue 2, **non-scaling** |
| N4 | N3 with the Vec built by a `vec-push` accumulator loop instead of a literal | N=100 → 103/101, N=1100 → 1103/1101 — residue 2, **non-scaling** |

So the leak needs the **composition**: a `Gr` box that owns a cells `Vec`, being
COW-superseded through a tail loop, *while* a separately-owned peer-list `Vec`
is carried as a loop parameter of the same loop. N3/N4 have the loop-carried Vec
but a payload-free ADT; N1 has the heap-owning ADT but no second Vec.

That shape — heap that owns heap, wrong only once two levels compose — is
exactly **FIXME 0837**'s hypothesised class. If `/arch` rules 0837 one class,
this is a candidate sixth instance and probably should not be reduced in
isolation first.

## What /testing is asked for

1. **A reduction.** The recipe is deterministic and cheap: copy `exemplar/*.cl`
   to a scratch dir, apply the de-`Option` ablation (`eliminate`,
   `eliminate-from-peers-helper`, `propagate-pass-helper`, `propagate`, and
   `solve`'s match over `propagate` all return a `Grid` directly — the easy
   puzzle still solves, exit 0, so the ablation is behaviour-preserving on this
   input), then shrink from there. N1–N4 above are the controls already
   eliminated; do not re-derive them. Counting call sites is easy with an
   alloc-counter probe: add `(let [probe [x]] (if (= (count probe) 99) <alt>
   <body>))` to the function of interest and read the ALLOCS delta — the probe
   Vec is always freed, so it perturbs deallocs identically.
2. **A cell either way.** If it reduces, a failing-not-ignored exact-balance
   cell with two Ns (this is a slope property). If it resists reduction after a
   reasonable attempt, an **application-scale** cell is still worth having: a
   test that runs the exemplar's serial solve and asserts the residue is
   ≤ ~1,400, which today is RED at 11,820, flips to a narrow GREEN when 0810
   lands, and would catch a regression that no small cell sees.

Either way the number is the point: **after the 0810/0782 fix the warm-cache
serial-solve residue must read ≈1,300.** Materially above ~2,000 means the fix
is partial; ~0 would mean this residual was 0810 after all and the ablation
over-attributed — both outcomes are informative, which is why the number is
worth pinning rather than the direction.

Deletes when the cell lands (or when 0837's ruling folds it into a class-level
record).
