---
id: ACT-1081
title: One module graph that returns to a parent through its declared child is accepted or refused as a cycle according to which module loads first
status: open
priority: required
from: qa
to: qa
sprint: 124
filed_at: 2026-11-18
refers_to:
  - spec/08-modules.md
  - design/int/int.md
  - src/scheduler.rs
  - tests/plan/s124-evidence-delta.md
---

## Observation

`qa`, on the debug build of `2d3a5b3e`, 2026-11-18, no prelude, cold
unless stated. Four files:

| File | Content |
|---|---|
| `P.cl` | `(mod c)` and `(defn x [] 1)` |
| `P/c.cl` | `(import [z [zf]])` and `(defn cf [] (zf))` |
| `z.cl` | `(import [P [x]])` and `(defn zf [] (primitives/add-i64 (x) 10))` |
| entry | one of the three below |

`P` reaches `c` only by declaring it. `c` depends on `z`, and `z` depends on
`P`.

| Route | Outcome | Runs |
|---|---|---|
| `--run`, the entry imports `P` | refused: `circular dependency detected: z -> P -> P.c -> z` | 6 of 6 |
| `--run`, the entry imports `z` | refused: `circular dependency detected: P.c -> z -> P -> P.c` | 4 of 4 |
| `--run` and `--link`, the entry imports `P.c` | runs and exits 11 | 9 of 9 cold under `--run`, 2 warm, 1 linked |
| REPL, `(P/x)` first | 1; `(P.c/cf)` and `(z/zf)` then fail with the cycle | 1 |
| REPL, `(z/zf)` first | the cycle error; `(P.c/cf)` in the next turn evaluates to 11 | 1 |
| REPL, `(z/zf)` first, on the cache an accepting session left | 11 | 1 |
| REPL, `(P.c/cf)` first | 11, and `(P/x)` is 1 | 2 |
| A session whose `user.cl` imports `P.c`, where a save of `z.cl` adds the import of `P` | `[updated: z.cl]`, `[updated: c.cl]`, `[updated: user.cl]`; 11. A restart on the saved files gives 11 | 1 |

**Control.** With `z.cl` reduced to `(defn zf [] 10)`, no edge returns to
`P`, and the session's first turn gives 10.

## Classification

- **A defect under either reading of the specification.** The outcome of
  one program depends on which of its modules is reached first, and a REPL
  session evaluates a module in the turn after reporting it failed. One of
  the two outcomes is wrong whichever way the question below is ruled.
  Class: `mode-divergence` is the nearest existing class; the face is a
  route dependence within one mode, so the class is provisional.
- **Which outcome is correct is not decided.** Spec §8.10.1 lists `mod` in
  the dependency graph, which makes `P -> c -> z -> P` a cycle. §8.3.8
  accepts a child's own import of its parent, which is the same shape with
  one module fewer. The specification does not say whether §8.3.8 covers
  only that direct case or means a `mod` declaration never closes a cycle.
  [Int §6.11](../../design/int/int.md#611-module-cycles-at-publication),
  *Undecided by the spec*, frames it; the user has been asked.
- **The design's expectation is not met.** Int §6.11 keeps "accepted",
  because declared children are no edge in its graphs. The scheduler
  reports an edge `P -> P.c` in two of the three batch routes.

## Attribution: provisional

- **Owner:** `src/`, the scheduler's wait graph. Not observed at its seam.
- **Hypothesis.** A parent that is still driving its declared children is
  held as waiting on them, so a module that waits on the parent closes a
  wait cycle through the child. When the child is reached first, the parent
  has published before the child's dependency asks for it.
- **Refuted if** `CRANELISP_SCHEDULER_TRACE` shows no wait edge from `P` to
  `P.c` in a refused run.
- **Entered:** not established. The release build of the W2 tree was not
  run on this fixture.

## Evidence allocation

- **Now, independent of the ruling (`test`).** REPRO-1081: the three batch
  entries above over one module tree, under `--run`; and the two REPL
  orders. Assert that the routes agree: either every route refuses with a
  circular-dependency error, or every route produces 11. Assert in the REPL
  legs that a module reported failed for a cycle does not evaluate in a
  later turn of the same session without a save. The control is the tree
  without `z`'s import of `P`, which gives 10 from every route.
  `// spec: spec/08-modules.md §8.10.2`; `class=mode-divergence`,
  `locus=src/scheduler.rs` wait graph (provisional), `found=S124`,
  `owner=/dev`. Expected RED: the routes disagree.
- **Held for the ruling.** Which of the two outcomes the cell requires, and
  the session-save and restart legs.
- **`design`(int)** states, once ruled, where the declared-child edge is or
  is not an edge; `dev`(`src/`) adds the scheduler row.

## Completion evidence

REPRO-1081 fails on the disagreement, then passes with every route giving
the ruled outcome; the session-save leg and a restart agree with it; `qa`
judges adequacy and deletes this action.
