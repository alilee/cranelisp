---
number: 0745
target: /design
filed_by: /dev (cranelisp-backend, S115 W3)
filed_at: 2026-07-21
sprint_filed: 115
refers_to: design/backend/s115-carrier-and-rc-sweep.md §2.1 (faces 1+2); crates/cranelisp-backend/src/compiler/rc_emission.rs::protect_return_value; tests/adt_drop_glue_underkey.rs::entry_main_ioresult_heap_payload_toggle_off_leak_r2
status: open
---

# The entry-`main` heap-PAYLOAD leak is not fixable at `protect_return_value` — both §2.1 mechanisms are falsified, and the true seam is cross-crate

## Severity
Important (a scoped carry RED cannot flip at the attributed seam; the design's
two admissible mechanisms are both unsound as stated).

## Issue

`s115-carrier-and-rc-sweep.md` §2.1 attributes the entry-`main` IO-result
heap-payload leak to `rc_emission.rs::protect_return_value` and offers two
admissible mechanisms. The W3 `/dev` measurements falsify **both**, and the
attribution with them.

### Evidence 1 — the leak reproduces with NO scope binding at all

§2.1's discriminator is `(defn main [] (let [s "hi"] (Pure s)))` (2 allocs / 1
free), and mechanism (a) is "suppress the box protect but let the `let`-scope dec
of the moved-in binding stand". Measured at HEAD (`--run --no-cache`,
`CRANELISP_RC_STATS=1`, `PrimitivesOnly`):

```
(defn main [] (let [s "hi"] (Pure s)))   allocs=2 deallocs=1   ← leaks 1
(defn main [] (Pure "hi"))               allocs=2 deallocs=1   ← leaks 1, NO let
(defn main [] (let [s "hi"] (Pure 9)))   allocs=2 deallocs=2   ← balanced
```

The `let` is irrelevant: the bare `(Pure "hi")` form has no scope binding, so
there is no "`let`-scope dec of the moved-in binding" to let stand. Mechanism (a)
has no referent. (The CLIF confirms the `let` form's scope dec IS already
emitted: `atomic_rmw.i64 sub` on the payload before the return.)

### Evidence 2 — the residual reference is CORRECTLY held, and its owner is the driver

The accounting is coherent end-to-end and there is no backend over-inc:

1. `main` builds the payload (rc=1), stores it into the fresh `Pure` box with the
   ordinary consuming inc (rc=2), and the `let`-scope dec returns it to rc=1 —
   the box owns exactly one reference. Correct.
2. `intrinsics::panic::cranelisp_run_program:289` calls `io::drive_io(main_result)`,
   which for a `Pure` node RETURNS `field0` — the payload — without inc'ing it.
3. `:291` calls `drop::consume_io_tree(main_result)`, whose `IO_TAG_PURE` arm
   deliberately does nothing with the payload ("Pure's payload is opaque — the
   trampoline returns it to the caller as the final value"). The box is freed;
   the payload's one reference **transfers to the returned value**.
4. `ProgramOutcome.exit_code` carries that value out. **Nobody releases it.**

So the leaked reference is the program RESULT VALUE's, and its owner is whoever
consumes the outcome — `cranelisp-intrinsics` (the driver) or `src/` (which is
the only party that knows `main`'s return type and hence whether the `i64` is a
heap pointer). It is not `protect_return_value`'s.

### Why mechanism (b) as stated is unsound

§2.1(b) is "make the entry teardown's box drop-glue recursively release the heap
payload". Decing the payload inside `consume_io_tree`'s `Pure` arm would free it
while `drive_io`'s `inner` still holds the pointer — harmless for `--run` (the
value is truncated to an exit code, never dereferenced) but a **UAF on the REPL
path**, where `src/repl/format.rs:598` drives the same tree through
`cranelisp_run_io` and then DISPLAYS `inner_value`.

Symmetrically, any backend-side "dec the payload before returning" would free the
program's own result value before it is observed.

## Proposed resolution

`/design`(backend) re-attributes the face and re-scopes §2.1: the backend half of
the RC sweep is faces 3 (0720) only, and the entry-payload face routes to the
owner of the program-result value. Two shapes for the owning skill to weigh
(stated as inputs, not as a `/dev` design):

- **int-side**: `src/` releases the outcome value after converting it, gated on
  `main`'s return type (`IO a` with `a` heap-typed) — the only place the type is
  known.
- **intrinsics-side**: the driver takes a "result is heap" flag alongside
  `main_returns_io` and releases after the outcome is consumed.

Either way it is a CROSS-CRATE attribution, so `/qa` triage (or `/arch`) should
place it before a wave is scheduled. The pin
`adt_drop_glue_underkey::entry_main_ioresult_heap_payload_toggle_off_leak_r2`
stays RED as the record and the trigger; the plan §1.4/§7 toggle-ON pin should be
authored by `/testing` alongside the re-attributed fix, not now (it would add a
second RED for the same unfixed defect).

## Context

Found while executing S115 W3 change-set 2. Note that
`binding-indirection-consume.md` §6.1 already recorded the same suspicion
("the IO trampoline and the result-tree teardown live in `cranelisp-intrinsics`,
not backend … attribution is unsettled") and named the discriminator; these
measurements run it and settle it against the backend seam.
