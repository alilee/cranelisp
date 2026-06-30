---
number: 0474
target: /backend
filed_by: /sprint
filed_at: 2026-06-29
sprint_filed: 96
refers_to: crates/cranelisp-intrinsics/src/io.rs (feed_continuation / dec_shallow_io), design/backend/io-trampoline.md §16, design/backend/ring2-rc.md §3.5
status: open
---

# Title — a continuation-produced (fresh) `IO_TAG_SELECT` / `IO_TAG_PAR` node leaks its branch children

## Issue

Surfaced by the C3 adversarial review (S96 Chunk C). When a `select`/`race`
(or `par`) node is produced **fresh by a bind continuation** — e.g.
`(bind X (fn [_] (select [a b])))` or the `par` analogue — the trampoline
shallow-dec's the fresh node via `feed_continuation` → `dec_shallow_io`. A
shallow dec frees the node header but does **not** walk its fields, so the
node's branch `Vec` (and the branch IO sub-trees it owns) **leak**.

This is **not C3-introduced**: it is identical to the established
`IO_TAG_PAR` model (`io.rs` — Par branches are likewise "left for
`consume_io_tree`", and a fresh Par node is also shallow-dec'd). C3's
`IO_TAG_SELECT` inherits the exact same shape. Both are currently
**untested** for the fresh-continuation-produced case.

The non-fresh (caller-tree) path is correct — `consume_io_tree`'s
`IO_TAG_SELECT` / `IO_TAG_PAR` arms walk the branch Vec and free every
branch exactly once (C3 unit `consume_io_select_frees_branch_vec_and_all_branches`
proves the select arm RED-on-revert). Only the **fresh** path leaks.

## Proposed resolution

Decide the correct shallow-dec contract for fresh multi-child IO nodes:
either (a) `dec_shallow_io` (or `feed_continuation`'s fresh-node release)
recognizes `IO_TAG_SELECT` / `IO_TAG_PAR` and deep-frees the branch Vec for
fresh nodes, or (b) the trampoline routes fresh select/par nodes through
`consume_io_tree` instead of the shallow path. Apply to BOTH tags together
(they share the model). Per the cross-skill defect protocol, ask `/qa` for a
narrow **heap-balance** repro (a `(bind X (fn [_] (select […])))` and a `par`
analogue that asserts no leak under `CRANELISP_RC_TRACE` / sustained
repetition) — failing-not-ignored — to co-land with the fix.

## Operational implication / Context

Low severity, pre-existing (inherited from Par), not a regression: it
requires a select/par node *constructed inside* a continuation, which the
current cancellation/fan-out programs do not do (they build select/race at
the top of the bind). It becomes observable for user code that returns a
`select`/`par` from a `bind` continuation. Routed forward (A3 precedent:
forward + fixme, not fold) rather than blocking the C3 wave.
