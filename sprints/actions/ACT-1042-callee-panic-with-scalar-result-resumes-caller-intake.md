---
id: ACT-1042
title: A runtime panic in a callee whose result is a scalar lets the caller resume with 0, so a loop can hang and a later panic replaces the first message
status: resolved
priority: required
from: qa
to: qa
sprint: 122
filed_at: 2026-10-01
refers_to:
  - spec/12-runtime.md §12.7.2
  - crates/cranelisp-backend/src/raise.rs::emit_raise
  - crates/cranelisp-intrinsics/src/panic.rs::terminate
  - tests/spec_12_runtime.rs
---

## Resolution (qa, 2026-11-15, S123 W1)

Resolved with [ACT-1040](ACT-1040-panic-sentinel-reaches-heap-consumer-intake.md):
no raise returns, so no caller resumes with `0`, and the first panic is the
only one reported.

- **Source opened.** `crates/cranelisp-backend/src/raise.rs::emit_raise` and
  `crates/cranelisp-intrinsics/src/panic.rs::terminate`, as for ACT-1040; the
  overwritable error slot no longer exists.
- **Evidence.** Q1 (`callee_panic_with_scalar_result_stops_the_calling_loop`)
  and Q2 (`callee_panic_message_is_not_replaced_by_callers_later_panic_in_every_mode`)
  were assertion-RED on the W1 test checkpoint and pass in the full suite of
  2026-11-15, with their in-range and in-frame controls passing.
- **Owed.** `test` stamps `fixed=S123/<W1 commit>` on both cells when W1 is
  committed.
- Delete this action once `design/backend/backend.md`, `sprints/archive/sprint-123.md`,
  `tests/plan/s122-evidence-delta.md` and ACT-1040 no longer link it.
