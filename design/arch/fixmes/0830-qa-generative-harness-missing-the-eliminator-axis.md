---
number: 0830
target: /qa
filed_by: /testing
filed_at: 2026-07-21
sprint_filed: 115
refers_to: tests/gen_ownership_flows.rs — the v1 generation space
  `{owning type} x {position} x {toggle} x {iters}` has no ELIMINATOR axis, so no
  generated cell ever puts an owned temporary in match-scrutinee position; plus
  the PLAN.md rows owed for the 0810/0782 pin batch
  (`tests/match_owned_temporary_scrutinee_0810.rs`)
status: open
---

# The generative harness is ONE ROW short of catching 0810 — it has no eliminator axis

## Two actions

1. **PLAN.md rows** for the 14 cells of `tests/match_owned_temporary_scrutinee_0810.rs`
   (the S115 Phase-6b pin batch for FIXME 0810, plus the 0782 var-pattern sibling
   cells). 10 RED / 4 GREEN as landed; both trace to open `/dev`-owned defects.
2. **The harness row proposal below** — the substantive half.

## The coverage finding

`tests/gen_ownership_flows.rs` enumerates

    {owning type, nesting 1..3} x {position} x {ownership toggle} x {iters}

with nine positions: `applied_in_place`, `let_bound`, `borrowed_argument`,
`returned`, `returned_through_1_let`, `returned_through_2_lets`,
`curried_partial_application`, `captured_in_escaping_closure`, `loop_carried`.
All 45 cells are GREEN, while a 1-object-per-iteration leak and a SIGBUS
over-release sit in `match` over an owned temporary.

**Why it cannot see them.** Every cell reads its owned value through a fixed
per-type reader function — `str-len`, `vec-len`, `bxlen`. The reader is always a
**callee taking the value as a parameter**, so the value is `Borrowed` at every
elimination site the harness ever generates. Notably `bxlen` IS a `match`:

```lisp
(defn bxlen [:Bx b] (match b [(MkBx s) (str-len s)]))
```

That is *exactly* FIXME 0810's GREEN control C2 — "match inside a callee on a
`Borrowed` parameter" — reproduced verbatim by the generator, in all 45 cells.
The harness generates the one match shape that works and no other.

So the missing axis is **not an owning type and not (quite) a position**: it is
**how the owned value is CONSUMED at its use site**. The `position` axis varies
where the value comes FROM; nothing varies what eliminates it. `applied_in_place`
and `let_bound` are indeed present — but they are `applied_in_place`/`let_bound`
*into a borrowing call*, never into a match.

## Proposed rows (the one-row-short answer)

Add an **eliminator** dimension, orthogonal to `position`, with three values:

| eliminator | form | covers |
|---|---|---|
| `borrowing_call` (today's behaviour) | `(read v)` | the current 45 cells, unchanged |
| `match_var_pattern` | `(match v [x (read x)])` | **FIXME 0782** across all 5 owning types |
| `match_ctor_pattern` (ADT owning types only) | `(match v [(MkBx s) (str-len s)])` | **FIXME 0810** |

Crossed with the existing 9 positions this is 9x(1 + 1 + ADT-only) cells per
owning type. If the full cross is too wide for the always-on budget, the
**minimum** that would have caught both defects is two new `Position` rows,
which is a strictly smaller change and needs no new generator concept:

```rust
Position { name: "matched_in_place",       // (match <mk> [pat ...])      → 0810 Face A
Position { name: "let_bound_then_matched", // (let [v <mk>] (match v ...)) → 0810 Face B / control C1
```

Both compose with the existing `ITERS` repeater, so the SCALING face reports the
slope (1/iteration for the Int-payload face, 2/iteration for the heap-payload
face) with no other change.

**This axis was in the strategy and got dropped in v1.**
`tests/plan/memory-safety-coverage.md` §2.1 lists the flow operators explicitly:
*"project out (`vec-get` / field accessor / **`match` ctor-pattern bind**);
**`match` var-pattern bind**"*. The v1 implementation replaced the operator
algebra with fixed per-type reader functions, and the two match operators went
with it. The gap is v1-vs-its-own-design, not an unforeseen axis — which is the
strongest possible argument for adding it now.

## Instrument caveat for whichever rows land

The 0782 face is **invisible to the harness's own instrument as configured**: a
var-pattern arm double-releasing an owned temporary exits 8 with `allocs=2
deallocs=2` under `--run` in BOTH toggles, and is a deterministic signal only
under `--link` (exit 134). `gen_ownership_flows.rs` v1 is `--run` x toggle only
(a documented v1 scope exclusion). So a `match_var_pattern` row added without the
`--link` face would generate the 0782 cell and still report GREEN. Either the
new rows route through `assert_safety_matrix` (the v2 plan), or the row lands
with an explicit note that it covers the 0810 polarity only.

Also relevant: every cell of the 0810 batch is **toggle-independent** (identical
exits and identical counts ON vs OFF). The differential RC face is structurally
blind to this whole class — the same FIXME-0761 blindness that already drove the
harness to assert exact balance rather than a differential. Exact balance is what
catches it; keep that property in any new rows.

## /qa S118 Phase-3 disposition (2026-07-25) — action 1 DONE; action 2 RIDES Track B

Action 1 (PLAN rows for the 0810/0782 pin batch): landed in
`tests/plan/PLAN.md` §"Sprint 118" (the pin-batch table, 10 RED + 4 GREEN
controls). Action 2 (the eliminator axis): planned in
`tests/plan/s118-test-plan.md` §4.2 — `/testing` W1 adds the two minimum
`Position` rows (`matched_in_place`, `let_bound_then_matched`) with the
instrument caveat binding (absolute exact balance, `--link` face or explicit
0810-polarity-only note). This FIXME closes when the harness rows land.

## Context

- `tests/match_owned_temporary_scrutinee_0810.rs` — the committed pins.
- FIXME 0810 (`/testing`, the record; stays open until the fix lands),
  FIXME 0782 (`/dev`, the var-pattern polarity of the same seam).
- FIXME 0831 (`/qa`) — the risk-register half of the same finding.
