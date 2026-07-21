---
number: 0810
target: /testing
filed_by: /port
filed_at: 2026-07-21
sprint_filed: 115
refers_to: crates/cranelisp-backend/src/compiler/match_codegen.rs — release of an
  OWNED temporary scrutinee under CONSTRUCTOR patterns (sibling of 0782, which is
  the same seam under a VAR pattern)
status: open
---

# `match` over an owned ADT temporary: inline scrutinee LEAKS the wrapper, let-bound scrutinee OVER-RELEASES it (SIGBUS)

## Severity

**Blocker** on the over-release face (memory corruption, `--run` AND `--link`).
**Important** on the leak face — but it is the *entire* residue the exemplar has
been carrying since S114 (see §"Exemplar attribution").

**Pre-existing**: measured identically at `4d20cea1` (pre-S115-RC-wave) and at
`87bb383a` (HEAD). Not introduced by the S115 RC wave; not fixed by it either.

## Issue

Two polarities of one seam. Both faces are `PrimitivesOnly` (no stdlib, no
closures, no Vec required), both are mode-independent (`--run` and `--link`
agree), both are deterministic and scale exactly 1 object per iteration.

### Face A — inline scrutinee: the wrapper box is never released (leak)

```lisp
(platform stdio)
(import [primitives [add-i64 eq-i64 Pure]])
(deftype B (Mk [v]))
(defn mk [n] (Mk n))
(defn go [i n acc]
  (if (eq-i64 i n) acc
    (match (mk i)
      [(Mk v) (go (add-i64 i 1) n (add-i64 acc v))])))
(defn main [] (Pure (go 0 N 0)))
```

`CRANELISP_NO_LENIENT=1 CRANELISP_RC_STATS=1`:
N=100 → allocs 101 / deallocs **1**; N=1100 → allocs 1101 / deallocs **1**.
Slope **1 leaked object per iteration** (the `Mk` box).

With a **heap payload** (`(Mk [n n n])`) the slope is **2 per iteration** — the
box AND its Vec field strand together (allocs 2N+1, deallocs 1).

The same leak occurs when the scrutinee is an inline *constructor* expression
with no call at all (`(match (Mk i) …)`), so it is not a post-call-seam artifact.

The exemplar's own shape — a wrapper returned by a called function whose payload
supersedes a tail-recursive loop parameter — leaks at the same 1/iteration rate:

```lisp
(deftype G (Gr [cells]))
(deftype O (Non) (Jus [g]))
(defn step [g i] (Jus g))
(defn go [g i n]
  (if (eq-i64 i n) g
    (match (step g i)
      [Non g
       (Jus g2) (go g2 (add-i64 i 1) n)])))
(defn main [] (Pure (match (go (Gr [1 2 3]) 0 N) [(Gr c) 7])))
```

N=100 → 103/3; N=1100 → 1103/3 (exit 7, correct). `--link`: identical (1103/3).

### Face B — the SAME program with the scrutinee let-bound: over-release

```lisp
(defn go [g i n]
  (if (eq-i64 i n) g
    (let [r (step g i)]
      (match r
        [Non g
         (Jus g2) (go g2 (add-i64 i 1) n)]))))
(defn main [] (let [x (go (Gr [1 2 3]) 0 100)] (Pure 7)))
```

→ **SIGBUS (exit 135, core dumped)** in `--run` and in `--link`. RC now balances
(allocs 102 / deallocs 102) — the wrapper IS released, but the extracted payload
goes with it, so the loop reads freed memory. A variant of the same program
(outer `match` on the result instead of a `let`) reports **`runtime panic: match
failed`** at exit 1 with the same balanced 102/102 — a wrong-tag read off the
freed box rather than a fault.

So the seam has no correct cell for this shape: spelling the scrutinee inline
leaks it, spelling it as a binding frees it too early.

### Discriminating controls (METHOD §2.2) — these are GREEN, keep them as cells

| # | Shape | Result |
|---|---|---|
| C1 | Face A with an **Int** payload and the scrutinee **let-bound** (`(let [b (mk i)] (match b [(Mk v) …]))`) | **exact balance** 101/101, 1101/1101 |
| C2 | `match` performed **inside a callee** on a `Borrowed` parameter (`(defn peek [b] (match b [(Mk v) v]))`, called as `(peek (mk i))`) | **exact balance** 101/101, 1101/1101 |

C1 vs Face B is the sharp pair: identical spelling change, opposite outcome —
the difference is whether the extracted payload outlives the match (Face B feeds
a tail-call loop parameter; C1 consumes an Int).

## Exemplar attribution (why this matters at scale)

The Sudoku exemplar's `~11.8k-objects-per-solve` residue (FIXME 0720, S114) is
**this defect and essentially nothing else**:

- HEAD serial solve (`--run exemplar/solver.cl`, `CRANELISP_NO_LENIENT=1`,
  `CRANELISP_RC_STATS=1`): allocs **26457** / deallocs **14637** → residue
  **11,820**.
- Propagation-only probe (same puzzle; the easy puzzle is solved by constraint
  propagation alone, so **no closure, no `par-map-reduce`, no guessing** runs):
  allocs 25517 / deallocs 13750 → residue **11,767** = 99.6% of the total.
  The residue is therefore NOT capture stranding (0760) and NOT curry (0796).
- Inside propagation, the leaking call is `solver/eliminate`, which returns
  `(Some g)`: a loop of N `eliminate` calls leaks exactly N objects (N=100 →
  1082/980; N=1100 → 2082/980), with or without a let-bound scrutinee — Face A.
- Order of magnitude agrees: ~500 `eliminate-from-peers` calls × 20 peers ≈ 10^4
  `Some` wrappers per solve.

`exemplar/set-cell` — the shape S114 blamed — now **balances exactly** (N=100 and
N=1100 both residue 2, no scaling), so the 0720 fix landed on its own repro.

## Pin directive (what /testing is asked for)

Failing-not-ignored REDs, `CRANELISP_NO_LENIENT=1`, both toggles, `--run` and
`--link`, asserting exact balance and non-scaling at two N:

1. Face A, Int payload (slope 1) — RED.
2. Face A, heap payload (slope 2 — box + field) — RED.
3. Face A, wrapper-from-call with payload superseding a tail loop param — RED.
4. Face B, let-bound scrutinee — RED, asserting **exit code / no fault** (this
   one is a correctness cell, not a balance cell).
5. C1 and C2 as GREEN controls.

`// defect: class=rc-miscount locus=crates/cranelisp-backend match_codegen —
owned temporary scrutinee under constructor patterns (0782 is the var-pattern
sibling) found=S115 owner=/dev`.

Deletes when the cells land. The exemplar record correction
(`exemplar/CLAUDE.md`, `plan-exemplar.md`) is /port's own 6b work — no FIXME.
