---
id: ACT-1010
title: Keep /mod definition turns from overwriting a module file this session never compiled
status: open
priority: required
from: qa
to: qa
sprint: 122
filed_at: 2026-09-29
refers_to:
  - repl/spec/14-file-watching.md
  - repl/spec/15-session-persistence.md
  - repl/spec/03-slash-commands.md
  - design/int/session-persistence.md
  - src/repl/commands.rs
---

## State

- **M1, a dependency that failed at startup: realized.**
  - `recover_startup_failure` locks each non-entry module the failed start
    left `Failed` (`design/int/repl-lifecycle.md` §1.3.1).
  - `persist_mod_definition_keeps_dependency_source_failed_at_startup` went
    RED (`lib.cl` became `(defn z [] 1)`), then GREEN, with its in-session
    control. The module unit went RED first too.
  - Record:
    [correction adequacy](../../tests/plan/s122-evidence-delta.md#failed-reload-lock-and-removed-definitions--correction-adequacy-2026-09-29).
  - A fixed startup-failed dependency does not recompile its dependents.
    That is a separate defect, filed as
    [ACT-1011](ACT-1011-startup-failed-dependency-fix-does-not-cascade-intake.md).
- **M2, a module never loaded: open.** This is a `spec` question.

## M2 observation (2026-09-29)

Probes: `.local/s122-reload-cleanup-final-qa-scratch/p-mod*`.

- `lib.cl` holds `(defn keep-me [] 42)` and nothing imports it.
- `/mod lib` gives a blank table, so `(keep-me)` is `undefined variable`.
- Then `(defn z [] 1)` rewrites `lib.cl` without `keep-me`.
- Control: the same turns with `lib` imported keep `keep-me` in the file.
- REPL §15.1 regenerates only the entry module's file, and §8 invites
  `/mod <name>` to create a module. The spec does not settle whether `/mod`
  to an existing unloaded file must load it, refuse, or may replace it.
- `design/int/session-persistence.md` §2.4.5 records the as-built behaviour
  as open and undecided.

## Attribution (M2)

- **Mechanism, seen in source.** `handle_mod` → `set_current_module` →
  `ensure_module_exists` creates a blank table.
- **Class.** None until `spec` rules.

## Next evidence

1. `spec` frames M2, and the user decides it.
2. If the ruling forbids the rewrite, `test` commits a failing, unignored
   cell, then `design`(int) and `dev` realize it.

## Completion

M2 has a spec disposition. If that disposition forbids the rewrite, its cell
passes.
