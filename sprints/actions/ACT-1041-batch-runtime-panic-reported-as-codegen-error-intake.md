---
id: ACT-1041
title: Under --run an uncaught runtime panic is reported as a codegen error at 0..0 with a doubled prefix, and the three modes disagree on the panic prefix
status: resolved
priority: required
from: qa
to: qa
sprint: 122
filed_at: 2026-09-30
refers_to:
  - spec/12-runtime.md §12.7.5
  - src/session_v4/lifecycle.rs::trampoline
  - crates/cranelisp-intrinsics/src/panic.rs::terminate
  - tests/spec_12_runtime.rs
---

## Resolution (qa, 2026-11-15, S123 W1)

The `--run` report is the single §12.7.5 line in every mode.

- **Source opened.** The runtime-error slot and its two readers are gone:
  `crates/cranelisp-intrinsics/src/panic.rs::terminate` writes the one report
  before the process exits, so `src/session_v4/lifecycle.rs::trampoline`
  never sees a panic to wrap. The prefix question was settled by the user's
  2026-11-15 ruling in §12.7.5.
- **Evidence.** `tests/spec_12_runtime.rs::uncaught_panic_report_is_not_a_codegen_error_run`
  was RED on the W1 test checkpoint and passes in the full suite of
  2026-11-15; its `--link` control passes. The shared exit checker asserts the
  anchored prefix in every mode and has its own detection proof
  (`panic_exit_checker_rejects_wrong_reports_and_resumption`).
- **Owed.** `test` stamps `fixed=S123/<W1 commit>` on the cell when W1 is
  committed.
- Delete this action once `tests/plan/s122-evidence-delta.md` no longer links
  it.
