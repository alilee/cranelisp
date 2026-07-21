---
number: 0777
target: /design
filed_by: /review
filed_at: 2026-07-21
sprint_filed: 115
refers_to: design/typecheck/ownership-inference.md §17.3 (the no-5th-arm
  argument) + §17.4 (face-3 probe-first) + §17.2 row 4 — the probe has been run
  and the row-4 groundwork does NOT cover face 3 in one arm order
status: open
---

# §17.3's family-grain claim and §17.4's face-3 prediction need correcting against the probe result

## Severity

**Important** (design-of-record accuracy; the behavioural defect is FIXME 0772).

## Issue

Two claims in §17 are now measurably wrong as written:

**§17.3** — *"the single pre-existing projection-out arm (row 6) discharges every
link of every chain shape … New chain shapes (longer nests, more `let` hops, the
face-3 `If`/`Match` container once probed) are covered by the composition rules
(rows 8/2/4) that already run on every walk."*

**§17.4** — *"Row 4's join-UNION of cow-alloc span-sets is the groundwork that
WOULD cover it … No design change beyond rows 4/6 is anticipated."*

`/review` ran the face-3 probe §17.4 called for. Result: the `If`-joined
container is covered when the may-alias arm is written **first** and aborts
(`--link`, exit 134) when it is written **second** — the two programs execute
the same runtime path. A `let`-mediated variant aborts in **both** orders. Full
probe table in FIXME 0772.

The mechanism gap is that row 4's stated condition — union "*when the join is
`Conditional`*" — leaves the join's own variant choice free to be
`Unconditional`, and the as-built `join_origin` then discards the union it just
computed. So the composition is not in fact closed over the chain: the value
does **not** always carry its own allocation history, which is the single
premise §17.3's whole argument rests on.

Structurally the wave delivered what §17.3 asked for — `/review` verified by
grep that **no new consumer arm was added**: the `if let MonoExpr::Apply` reach
was deleted and replaced by a loop over the carried spans, and the
`Origin::Conditional` arms at `transfer.rs:752` and `:1054` are pre-existing arms
that gained a `cow` field, not new ones. The arm-count discipline held. It is the
*sufficiency* claim that failed.

## Proposed resolution

1. Amend §17.2 row 4 to state the invariant the composition actually needs: a
   join whose operands carry may-alias links produces a value carrying their
   union — **independent of which operand contributed them and of the joined
   variant**. Order-independence is the property (P24); "when the join is
   Conditional" is a description of one code path.
2. Retire §17.4's prediction and replace it with the probe result: face 3 is RED
   in one arm order and its `let`-mediated form is RED in both; the cure is the
   row-4 correction above, not a new arm. Record the probe (per the §3.8
   precedent §17.4 itself cites).
3. Soften §17.3's claim to what is provable: the arm *count* is fixed and the
   composition covers every shape **for which the composition is closed** — and
   name order-independence at every join as the closure obligation, so the next
   composition rule added is checked against it.
4. Extend §17.7's `/qa`/`/testing` rider: the behavioural matrix axis list
   (chain length × {nested, let} × {in-place, shared} × {REPL, `--link`}) should
   gain an **arm-order** axis. Order symmetry is the property that failed, and no
   cell in the lane tests it.

## Context

- Behavioural fix + repros: FIXME 0772 (`target: /dev`), FIXME 0773
  (`target: /testing`).
- What the design got right and `/review` confirmed: the obligation genuinely
  belongs on the value (P25), the fix is walk-internal so §17.6's tripwire
  correctly did not fire (zero `cranelisp-types` edits, no schema bump), the
  escape-force is monotone with no measured over-forcing
  (`CRANELISP_RC_STATS` `allocs == deallocs` on chained and control shapes), and
  the mechanism generalizes well past the two pinned faces — a three-link nested
  chain, a cross-function chain and a nested-`let` chain are all RED-to-GREEN or
  clean at `d4efdf08` versus `d4efdf08~1`.
