---
number: 0126
target: /int
filed_by: /qa
filed_at: 2026-05-03
sprint_filed: 64
refers_to: tests/legacy/v4_repl_eval.rs
status: open
---

# (Optional) Harvest tests/legacy/v4_repl_eval.rs — already e2e-shaped, carry-forward complete

## Issue

The Sprint 64 test-port quarantined `tests/legacy/v4_repl_eval.rs`
(567 LOC, 14 tests). Unlike the other Wave 3 quarantines, this file
was already e2e-shaped — it spawns the `cranelisp` binary as a
subprocess, pipes stdin, and asserts on stdout/stderr/exit. The
quarantine is for **provenance only**; the carry-forward is complete:

- Bespoke `run_repl(input, label)` helper retired in favour of
  `tests/helpers/e2e::Cranelisp::new().repl().stdin(...)`.
- Bespoke `result_lines(o)` parser retired in favour of
  `out.assert_stdout_contains(":Type value")`.
- Each test's spec content is absorbed by `tests/repl_lifecycle.rs`
  (eval persistence, error recovery, defn-then-call, error cascade)
  and `tests/repl_introspection.rs` (defn display, type display).

## Proposed resolution

This is an **optional** harvest. The 14 tests' spec coverage is fully
present in the e2e files. Two paths:

1. **Delete `tests/legacy/v4_repl_eval.rs` outright** at S65 cleanup.
   Git history preserves provenance.
2. **Translate the bespoke helpers into a `tests/helpers/v4_eval.rs`
   module** if `/int` discovers a residual concern about the
   subprocess `result_lines` parser shape that the new harness's
   `assert_stdout_contains` does not preserve. (Unlikely — the new
   harness is strictly more capable.)

Recommend path 1.

## Operational implication / Context

The file was retained as a quarantine rather than deleted at port
time so that any concern about the carry-forward fidelity has a
reference point during S64 close + S65 review. After S65 close, if
no concern surfaces, this FIXME resolves by deleting the file.

When complete, delete `tests/legacy/v4_repl_eval.rs` and remove its
row from `tests/legacy/README.md`. Git history preserves provenance.
