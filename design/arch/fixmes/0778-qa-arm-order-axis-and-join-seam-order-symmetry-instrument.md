---
number: 0778
target: /qa
filed_by: /testing
filed_at: 2026-07-21
sprint_filed: 115
refers_to: tests/plan/ — the MS-P7 may-alias variant matrix (chain-length axis)
  and the plan rows for the six 0772 face-3 cells landed in
  tests/safety_oracle_lane.rs
status: open
---

# The may-alias variant matrix needs an ARM-ORDER axis, and the join seam needs a standing order-symmetry instrument

## Severity

**Important** — a coverage-process gap, not a defect. The defect it failed to
catch (FIXME 0772) is Blocker-class.

## Issue

Two items, both downstream of the 0772 face-3 probe.

**1. Plan rows for the six new cells.** `/testing` landed the FIXME-0773 cells
in `tests/safety_oracle_lane.rs` (3 RED + 3 GREEN, listed below); they need
`tests/plan/PLAN.md` rows.

| cell | colour at `bd5628a8` |
|---|---|
| `safety_lane_if_joined_cow_arm_second_returns_set_value_abort_free_red` | RED (`--link` 134) |
| `safety_lane_if_joined_cow_arm_first_order_symmetry_twin_green` | GREEN (masks 0772) |
| `safety_lane_let_bound_if_joined_cow_arm_second_returns_set_value_abort_free_red` | RED |
| `safety_lane_let_bound_if_joined_cow_arm_first_returns_set_value_abort_free_red` | RED |
| `safety_lane_if_joined_whole_value_transfer_clean_green` | GREEN (over-force fence) |
| `safety_lane_chained_cow_generalization_shapes_clean_green` | GREEN (W4 generalization fence) |

**2. The matrix axis.** `design/typecheck/ownership-inference.md` §17.7's
`/qa`+`/testing` rider names a **chain-length** axis. 0772 was not a
chain-length miss — it was an **arm-order** miss: the same runtime path is safe
or corrupting depending on which `If` arm the COW producer is written in, and
the whole family fix passed review-by-suite because every existing cell (e2e
and unit) happened to use the surviving order. Per the standing
"coverage by definition variants" lens (`tests/CLAUDE.md`), **operand/arm order
is a variant axis** for any join/merge/fold operation, and its cells must be
twin cells (same contract, orders swapped, SAME assertion).

Requested: add an **arm-order** axis to the §17.7 rider's matrix (and to any
successor plan doc), covering `If` arms, `Match` arm sequence, and the
`VecLit`/element-fold accumulation order — each as an order-swapped twin pair.

## Instrumentation answer (METHOD §2.2), for the record

The instrument that would have caught 0772 at its seam **does not exist**:
`crates/cranelisp-typecheck/src/ownership/transfer/tests.rs` has **zero**
`join_origin` cells (`grep join_origin` on that file returns nothing). The two
§17 cells that do exist
(`msp7_chained_nested_cow_projection_forces_escape_at_every_link`,
`msp7_chained_let_bound_cow_projection_forces_escape_at_every_link`) are
program-SHAPE cells: they assert an escape fact for one hand-built `MonoExpr`
tree, so they can only ever exercise the operand order that tree happens to
produce. Shape cells cannot fail on an order asymmetry — the shape fixes the
order.

The shape that would have caught it is a **seam-level algebraic-property cell
over the `Origin` lattice**, independent of any program:

- **commutativity** — for every pair `(a, b)` drawn from a representative
  `Origin` set (`Fresh`, `AliasOf(i)`, `ProjectionOf(i)`, `Conditional` with a
  non-empty cow set, same index and different index), assert
  `join_origin(a, b) == join_origin(b, a)`;
- **union preservation** — assert
  `cow_spans(join_origin(a, b)) ⊇ cow_spans(a) ∪ cow_spans(b)` for every pair
  (the row-4 contract stated as a property, not as one example).

Either property fails on the as-built `other => other` arm immediately, with no
program, no `--link`, and no allocator to notice the double-dec. This is the
generalisable lesson: **a join/merge/fold seam takes property cells over its
operand lattice, not example cells over one syntax tree** — and the property
cells are cheap enough to be exhaustive over the representative set.

`/dev` owns the cell itself (it lives in the crate; 0772's "Proposed
resolution" already names an order-symmetry unit cell as part of the fix). This
FIXME records the shape and asks `/qa` to make it a standing matrix
obligation for join-shaped seams, so the next such seam is instrumented at
birth rather than after a Blocker.

## Context

- FIXME 0772 (`target: /dev`) — the defect and its mechanism.
- FIXME 0777 (`target: /design`) — the §17.3 family-grain claim correction.
- `tests/CLAUDE.md` §"Coverage by definition variants" — the twin-fixture rule
  this axis instantiates ("one invariant satisfied two ways, SAME assertion").
