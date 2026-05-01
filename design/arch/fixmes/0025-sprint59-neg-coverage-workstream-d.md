---
number: 0025
target: /int
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/sprint59_neg.rs (lines 66, 103, 132, 182), spec/08-modules.md §8.3.1, §8.3.7, §8.3.9
status: open
migrated_from_inline: true
---

# 0025 — Sprint 59 Workstream D module-boundary negative coverage

## Issue

Sprint 59 Workstream D filed four `/int` negative-coverage tests for module-boundary spec rules:

- `tests/sprint59_neg.rs:66` `import_nonexistent_name_errors_neg` — §8.3.1: import of a non-existent name MUST error. Distinct from `import_private_name_errors` (which covers §8.7.3 private-name exclusion); this test exercises the case where the name simply does not exist at all in the target module.
- `:103` `super_import_at_repl_prompt_rejected_neg` — §8.3.7: using `super` in a top-level module MUST produce a compile-time error. Cross-checks the existing batch-mode neg test (`tests/modules.rs::super_import_at_root_is_rejected_neg`) from the REPL-eval surface. A REPL session is inherently in the top-level `user` module.
- `:132` `import_inside_let_rejected_neg` — §8.3.9: `(import …)` MUST appear as top-level forms. Currently unguarded in the test suite. Implementation shortcuts (e.g., scanning for import at ANY depth) would silently admit the invalid program.
- `:182` `import_before_definition_compiles_neg` — §8.3.9 imports-before-definitions positive-of-negative check: the program MUST compile and run, proving that imports are extracted before compilation.

## Source location

`tests/sprint59_neg.rs` (4 FIXMEs at lines 66, 103, 132, 182).

## Context

Workstream D is the negative-coverage track for Sprint 59. These tests pin what the module-boundary spec rules MUST reject (or accept) at the REPL surface. Owning skill is `/int` because the dispatch lives in REPL session orchestration.

## Proposed resolution

`/int` ensures the four tests pass against the implementation; if any reject-shape test passes when it should fail (or vice versa), file a focused defect repro and resolve.
