---
id: ACT-1004
title: Verify missing-entry filename diagnostics in normal batch modes
status: open
priority: advisory
from: sprint
to: qa
sprint: 122
filed_at: 2026-09-28
refers_to:
  - repl/spec/00-cli-invocation.md
  - src/exe.rs
  - src/session_v4/lifecycle.rs
  - tests/link.rs
---

## Request

Reproduce the reported missing-entry diagnostic gap in `--run` and `--link`.
CLI §0.5.5 requires the error to name the missing source file. The existing
link test checks exit status only. The shared-runner work covers the `--test`
leg; it does not establish conformance of the other two modes.

## Evidence and limits

S122 dev and independent review report that entry registration leaves an empty
module and normal batch execution reaches `validate_main`, which emits
`entry module has no 'main' function`. Sprint reopened `src/exe.rs` and
verified that diagnostic, and read the owning CLI requirement. QA classifies
this as a pre-existing conformance lead; no independent reproduction has yet
been recorded. The mechanism attribution remains provisional.

## Completion

Establish a narrow unignored regression for both modes and the filename on
stderr before assigning a fix. If confirmed, design the missing-source check
once for batch callers rather than adding a separate check to each mode.
Retain the `--test` behavior and the REPL's ability to start an empty module.
This intake does not authorize changing the shared runner or expanding its
current correction basket.
