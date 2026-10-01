---
id: ACT-1042
title: A runtime panic in a callee whose result is a scalar lets the caller resume with 0, so a loop can hang and a later panic replaces the first message
status: open
priority: required
from: qa
to: qa
sprint: 122
filed_at: 2026-10-01
refers_to:
  - spec/12-runtime.md §12.7.2
  - spec/12-runtime.md §12.7.4
  - spec/12-runtime.md §12.7.8
  - design/backend/s122-closure.md §10
  - crates/cranelisp-intrinsics/src/panic.rs::runtime_panic
  - crates/cranelisp-intrinsics/src/panic.rs::set_runtime_error
  - tests/spec_12_runtime.rs
---

## Observation

`design`(backend) measured both faces on 2026-10-01 while costing
[ACT-1040](ACT-1040-panic-sentinel-reaches-heap-consumer-intake.md)
([s122-closure §10.1](../../design/backend/s122-closure.md#101-mechanism-read-at-source)),
with a copy of the debug binary built after `88bbbd12` and the primitives-only
prelude. QA did not re-probe them: running the binary was not available in
its dispatch. `lookup` is `(defn lookup [v i] (vec-get v i))`.

| Face | Form | Observed | Required |
|---|---|---|---|
| Q1 | `(defn scan [v i] (if (lt-i64 (lookup v i) 100) (scan v (add-i64 i 1)) i))`, then `(scan [1 2] 0)` | the REPL never returns: each call from `i = 2` panics, and `scan` continues with `0` | the index panic is reported and the session continues (§12.7.2, §12.7.4.1) |
| Q2 | `(div-i64 10 (lookup [1 2] 9))` | reports `division by zero` | reports the index panic, which is the first (§12.7.4.1 item 1, §12.7.8 item 5) |

- Neither face is memory-unsafe: a scalar consumer reads `0` as a value, and
  a `Mixed` consumer tests the nullary threshold before any dereference.
- Violations: §12.7.2 ("cannot resume"), §12.7.4.1 items 1 and 3, and
  §12.7.8 items 2 and 5 (a panic converted to an arbitrary value).

## Attribution

- **Status: confirmed in source; the executed discriminator is ACT-1040's.**
  The mechanism is ACT-1040's, reached through a result category whose `0`
  is an ordinary value: the faulting frame returns `0`, and no emitted code
  reads the panic slot after a call.
- **Q2's second step, read at source:** `runtime_panic` overwrites
  `RUNTIME_ERROR` on every raise, while the fork-join ferry's
  `set_runtime_error` keeps the first error. So the caller's own later panic
  replaces the callee's message.
- **Discriminator (for `test` to reproduce):** each face against a sibling
  that raises the same panic in the consumer's own frame, for example
  `(div-i64 10 (vec-get [1 2] 9))`. The in-frame panic returns before the
  division, so it reports the index message. Refuted if the in-frame sibling
  misbehaves too, or if some caller path consults the slot after a call.
- **Class:** `unpropagated-panic`, the same propagation protocol as ACT-1040.
- **Coverage gap:** as for ACT-1040. No cell continues a computation past a
  callee's panic and then observes it.
- **Not covered by ACT-1040's option A0.** A0 tests only `AlwaysHeap`
  results. Option A, the slot query on any other zero result, closes both
  faces; it needs a new intrinsic and so the inter-crate public-API user gate.
  First-error-wins in `runtime_panic` would close Q2 alone and is
  `design`(intrinsics)'s choice, with `arch` confirming that it is not a
  panic-ABI change.

## Evidence allocation

- **`test` (allocated now):** failing, un-ignored cells in
  `tests/spec_12_runtime.rs` citing `// spec: spec/12-runtime.md §12.7.2`,
  with
  `class=unpropagated-panic locus=design/backend/backend.md §7 panic shape found=S122 owner=/dev`.
  - Q1 in the REPL, with a bounded timeout: the index panic is reported and
    the next form evaluates. Use a fallible capture, so the timeout reads as
    a failed assertion with its diagnostic, not a harness error. Choose the
    smallest bound that separates termination from a hang; the RED costs that
    bound on every suite run until the correction lands.
  - Q2 in every mode through `catch-runtime-error`: the `Err` message names
    the index panic, not division by zero.
  - Controls, passing: Q1 with every index in range terminates with its
    value; Q2's in-frame sibling reports the index message.
- **`dev`:** the unit row at the chosen seam, with the correction.

## Disposition

- Fix or carry is the user's decision (METHOD §2.4), taken with ACT-1040's
  option. Under A0 alone this filing carries; under A it closes with
  ACT-1040's correction.
- QA retains this intake.

## Completion evidence

The Q1 and Q2 cells go RED for the intended reason, then GREEN after the
correction in every mode they cover, with the controls still passing. QA
restores the §12.7.2 and §12.7.8 item 5 bands.
