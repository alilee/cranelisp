---
id: ACT-1040
title: A runtime panic in a callee returns a null sentinel that the caller dereferences, so the process dies with SIGSEGV instead of reporting the panic
status: resolved
priority: blocking
from: qa
to: qa
sprint: 122
filed_at: 2026-09-30
refers_to:
  - spec/12-runtime.md §12.7.8
  - crates/cranelisp-backend/src/raise.rs::emit_raise
  - crates/cranelisp-intrinsics/src/panic.rs::terminate
  - tests/spec_12_runtime.rs
---

## Resolution (qa, 2026-11-15, S123 W1)

A callee's panic no longer returns a sentinel: the user's 2026-11-15 ruling
makes every runtime panic end the process (`spec/12-runtime.md` §12.7.2,
§12.7.8), and W1 built it.

- **Source opened.** Every backend raise site emits through
  `crates/cranelisp-backend/src/raise.rs::emit_raise`, a call to the
  diverging `runtime/panic` followed by a trap; no raise returns a value.
  `crates/cranelisp-intrinsics/src/panic.rs::terminate` claims termination
  once, flushes, reports and exits.
- **Evidence.** The R1–R4 and R6 cells, re-pointed to process exit (C-3 of
  the [S123 evidence delta](../../tests/plan/s123-evidence-delta.md#32-panics-end-the-process)),
  were assertion-RED on the W1 test checkpoint and pass in the full suite of
  2026-11-15, with the C1–C4 controls passing. R5 tested
  `catch-runtime-error`, which is removed; P-9 evidences the removal.
- **Owed.** `test` stamps `fixed=S123/<W1 commit>` on the cells' `// defect:`
  lines when W1 is committed.
- Delete this action once `design/backend/backend.md`,
  `design/backend/s122-closure.md`, `sprints/SPRINT.md`, `sprints/ROADMAP.md`
  and `tests/CLAUDE.md` no longer link it. Git holds the intake record.
