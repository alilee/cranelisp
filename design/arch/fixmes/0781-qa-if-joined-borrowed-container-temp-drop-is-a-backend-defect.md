---
number: 0781
target: /qa
filed_by: /dev
filed_at: 2026-07-21
sprint_filed: 115
refers_to: tests/safety_oracle_lane.rs::safety_lane_let_bound_if_joined_cow_arm_{first,second}_returns_set_value_abort_free_red
  — their `defect:` notation attributes the locus to
  `cranelisp-typecheck/src/ownership/transfer.rs::join_origin`; the reduction
  below shows the locus is
  `cranelisp-backend/src/compiler/vec_codegen.rs::emit_vec_drop_if_temporary`
status: open
---

# The two `let`-mediated 0772 cells are a BACKEND defect, not `join_origin` — re-attribution + a 1-line repro

## Severity

**Blocker** (memory-safety UAF, `--link` exit 134) — but a *re-attribution*, not a
new defect: both cells are already committed failing-not-ignored at `94dd3319`,
so they remain their own record and trigger (no new numbered FIXME is owed for
the defect itself). This FIXME exists for the attribution correction and the
reduction, per root `CLAUDE.md` §"Cross-skill defect handoff requires a minimal
repro".

## Issue

The 0772 `join_origin` fix landed (S115 W4b) and flipped
`safety_lane_if_joined_cow_arm_second_returns_set_value_abort_free_red` GREEN.
The two `let`-mediated cells stayed RED — as FIXME 0772 itself predicted ("a 0772
fix that only stops `join_origin` discarding the union will flip the bare-`If`
cell and leave this one RED"). The prediction was right; the *reason* recorded
alongside it ("the may-alias link travels through the LET BINDING env, and the
join is over {param `v`, binding `w`}") is not.

The ownership walk is CORRECT on these shapes. With the 0772 fix,
`CRANELISP_OWNERSHIP_TRACE=1` on
`(defn f [v b] (let [w (vec-set v 0 1)] (vec-get (if b v w) 0)))` shows the join
producing a `Conditional` that carries the link, the row-6 projection-out force
firing, and the `vec-set` span's `escapes` fact `true` — everything §17.2 asks
for. It still aborts.

### The reduction

Neither `let` nor COW is necessary. On `PrimitivesOnly`, `--link`:

| # | program (`(defn main [] (Pure (f [9 9 9] false)))` in each case) | `--link` |
|---|---|---|
| Q3 | `(defn f [v b] (vec-get (if b v v) 0))` | **134 `corrupted double-linked list`** |
| Q1 | `(defn f [v b] (let [w [1 1 1]] (vec-get (if b w w) 0)))` | **134 `free(): chunks in smallbin corrupted`** |
| Q2 | `(defn f [v b] (vec-get v 0))` | 9 (clean) |
| Q4 | `(defn f [v b] (let [w [1 1 1]] (vec-get w 0)))` | 1 (clean) |

Q3 is the whole defect in one line: **no `let`, no COW, no may-alias, both `If`
arms identical**. Q1 is the same with a FRESH vector — no param reach at all, so
the ownership walk's `Origin` for the container is plain `Fresh` and no §17
machinery is involved on either side. Both abort at `94dd3319` AND at the pre-0772
arm (verified by revert), so neither is a regression from this wave.

Typecheck's facts for Q3 are right:
`f: modes=[Borrowed, Copy] result=ProjectionOf(0)` — `v` is borrowed, the result
is a projection of it. Nothing here licenses a release.

### Mechanism

`crates/cranelisp-backend/src/compiler/vec_codegen.rs::emit_vec_drop_if_temporary`
decides "is this container an owned temporary?" **syntactically**:

```rust
// Named variables are handled by scope cleanup — skip.
if matches!(vec_expr, MonoExpr::Var { .. }) {
    return Ok(());
}
```

An `If` (or `Match`, or `Let`) node that merely *yields* a borrowed param or a
let binding is not a `Var`, so it takes the release path and the rc-checked dec
frees a box the enclosing scope still owns and will dec again. Q2/Q4 are clean
only because their container happens to be spelled as a bare `Var`. This is the
same shape as the S115 W3 "one predicate, not per-site syntax" family
(`crates/cranelisp-backend/CLAUDE.md` §"RC-emission gates"): the sibling
predicate `fn_compiler::is_fresh_construction` already answers the right
question — freshness, forwarding through `let` AND through control-flow joins
("fresh iff EVERY arm is fresh"). `emit_vec_drop_if_temporary`'s `Var` test is
the un-converted member of that family.

## Proposed resolution

For `/qa`:

1. **Re-attribute** the two cells' `defect:` notation (`/testing` edits) —
   `locus=crates/cranelisp-backend/src/compiler/vec_codegen.rs::emit_vec_drop_if_temporary`,
   `owner=/dev` (backend). Their current locus points at `join_origin`, which is
   now fixed and pinned; leaving the notation would send the next reader to the
   wrong crate.
2. **Land Q3 and Q1 as cells** — Q3 especially. It is a one-line, COW-free,
   `let`-free repro of a `--link` double-free, and it is a far better trigger for
   the backend fix than the two `let`+COW faces. Q2/Q4 are its ready-made
   negative controls (same shape, container spelled as a `Var`).
3. Note for the backend fix: the release must be keyed on whether the container
   VALUE is freshly constructed, not on the container EXPRESSION's node kind —
   i.e. route it through the existing `is_fresh_construction` family rather than
   adding a second `matches!` list (which is the duplication that produced this).

## Context

- FIXME 0772 (`target: /dev`, resolved S115 W4b) — the `join_origin` arm-order
  half, now fixed and pinned by the `join_lattice_*` property cells.
- FIXME 0777 (`target: /design`) — the §17.3/§17.4 correction; its §17.4 entry
  should note that face 3's `let`-mediated form was NOT a row-4 gap at all.
- `crates/cranelisp-backend/CLAUDE.md` §"RC-emission gates that are ONE
  predicate, not per-site syntax" — the family this belongs to.
