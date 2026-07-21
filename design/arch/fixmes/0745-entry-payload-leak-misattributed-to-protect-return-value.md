---
number: 0745
target: /design (int) — /qa re-attributed 2026-07-21 (was /design backend); /arch consult REQUIRED on the release mechanism
filed_by: /dev (cranelisp-backend, S115 W3)
filed_at: 2026-07-21
sprint_filed: 115
refers_to: tests/plan/s115-test-plan.md §8.1 (the /qa attribution brief); tests/adt_drop_glue_underkey.rs::entry_main_ioresult_heap_payload_toggle_off_leak_r2; src/pipeline.rs::program_outcome_to_result + src/main.rs:331 + src/repl display consumer (the result-value lifetime seam); crates/cranelisp-intrinsics/src/{panic.rs::cranelisp_run_program, io.rs:236, drop.rs:303} (verified coherent — NOT the seam); design/backend/s115-carrier-and-rc-sweep.md §2.1 (re-scoped to face 3 / 0720)
scheduled: S116 (needs a /design(int) pass + an /arch mechanism ruling; carries out of S115 as an attributed carry)
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

## /qa ATTRIBUTION (2026-07-21, S115 mid-Phase-5 disposition batch)

**Re-attribution ACCEPTED; both §2.1 mechanisms verified falsified against
source.** Full brief + fix constraints: `tests/plan/s115-test-plan.md` §8.1
(the durable record — read it before opening any wave on this).

**Owner: `/design`(int) → `/dev`(src), with a REQUIRED `/arch` consult on the
release mechanism.** `target:` re-pointed accordingly. Not backend, not
intrinsics-alone.

Summary of the placement:

- The residual reference is the **program RESULT VALUE's**, and **nobody
  releases it in any mode** — verified by absence (`src/` contains no
  rc-dec/value-release call site at all). `--run`/`--link`:
  `ProgramOutcome.exit_code` → `src/main.rs:331` truncation. REPL:
  `src/pipeline.rs:148-151` → `program_outcome_to_result` →
  `ExprOutcome::Value` → `display::result_value_doc`.
- **Only int knows the result TYPE** (the driver has only
  `main_returns_io: bool`; `main.rs:331` already branches on `ty`), so the
  heap-vs-immediate judgment and glue selection can only live there. This is
  Decision 24's consuming convention at the ONE call boundary whose caller is
  Rust host code rather than generated code.
- **Citation correction to §"Why mechanism (b) is unsound":** the UAF is on
  the LIVE REPL path, not only the defensive one — `src/repl/format.rs:598`
  is documented-unreachable for current callers; the live dereference is
  `pipeline.rs:149` → `ExprOutcome::Value` → `display::result_value_doc`.
  The conclusion is unchanged and stronger.
- **No type-erased release exists today**: `HeapHeader`
  (`crates/cranelisp-types/src/heap.rs:18-24`) is `{alloc_size, rc}` — no
  drop-glue pointer. Choosing between a type-directed release entry (trivial
  in JIT, not free under `--link`) and a scoped mechanism is the `/arch` half.
- Defect class: **`rc-miscount`**. Scope question (IO-specific vs general
  result-value ownership) is OPEN and decides fix size, not owner; the
  confirming one-liner is named in plan §8.1.

**Sprint routing: this RED does not flip in S115** (needs a design pass +
an /arch mechanism ruling; no wave carries that). §1.4's three-face sweep
row is re-scoped to the two 0720 faces (both flipped); the entry-payload
face leaves it and enters certification as an **attributed carry with a NEW
owner**. Do NOT author the toggle-ON sibling pin (a second RED for one
unfixed defect). `/testing` rider: re-locus the pin's `// defect:` off
`protect_return_value` onto the int result-value lifetime seam.
