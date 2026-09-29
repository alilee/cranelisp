---
id: ACT-1011
title: Recompile the dependents of a module fixed after a startup failure
status: open
priority: required
from: qa
to: qa
sprint: 122
filed_at: 2026-09-29
refers_to:
  - repl/spec/14-file-watching.md
  - src/session_v4/lifecycle.rs
  - src/process_form/dependency.rs
---

## Requirement

- REPL [§14.2](../../repl/spec/14-file-watching.md#142-eager-recompilation)
  step 4: the dependents of a changed module MUST also be recompiled.
- [§14.6](../../repl/spec/14-file-watching.md#146-clearing-errors): the
  error clears when the offending file is fixed and saved.

## Observation (2026-09-29, binary `2408e889…b510`)

Probes: `.local/s122-reload-cleanup-correction-qa-scratch/p-cascade*` and
their `run-*` outputs.

- **Fixture.**
  - `base.cl`: `(defn b [] (undefined-name 1))`.
  - `lib.cl`: `(import [base [b]])` and `(defn f [] (b))`.
  - `user.cl`: `(import [lib [f]])` and `(defn g [] 1)`.
- **Startup.** Only `[errors: user.cl]` is reported, with
  `'f' not found in module 'lib'`. The report omits `base`'s own
  `undefined-name` error. QA has not assessed whether §15.2.3 requires it.
- **Save a fix.** `base.cl` becomes `(defn b [] 7)`. Only
  `[updated: base.cl]` is reported; `lib` and `user` are not recompiled.
  - `(f)` is refused because `lib` and `user` have errors.
  - `/mod lib` plus `(defn z [] 1)` is refused by the ACT-1010 M1 lock, so
    `lib.cl` is kept.
- **A changed save of `lib.cl`** releases `lib`, but `user` stays blocked.
  A content-identical save is ignored (§14.2 content hash).
- **In-session control.** The same files, with `base.cl` compiling at
  startup, then failing through a save and fixed through a save. The fix
  reports `[updated:]` for `base.cl`, `lib.cl` and `user.cl`, and `(f)` gives
  7. A definition in `lib` is accepted.
- **Before the M1 correction** (binary `b6f373e9…04b6`), the dependents were
  not recompiled either. `lib` was not blocked, so `/mod lib` plus a
  definition rewrote `lib.cl` as `(defn z [] 1)` and lost `f`. The M1 lock
  turns that loss into a refusal. The missing cascade predates it.

## Impact

- After a startup failure in an imported module, fixing that module does
  not restore the session.
- Evaluation stays blocked until each dependent file receives a changed
  save, or the REPL restarts.
- No authored source is lost.

## Attribution (mechanism observed at the scheduler seam)

`CRANELISP_SCHEDULER_TRACE=1` on the startup probe shows:

- `ResetAllFailed count=3`, after which only `user` re-registers;
- `IsTypecheckedHit module=lib`: the degraded re-drive's import treats the
  untracked `lib` as typechecked (the `handle_import` fast path);
- on the save, `RecompileModule module=base` with no dependent recompiled.

The in-session control, which differs only in when the failure arose,
cascades. `recover_startup_failure`'s reset leaves no scheduler record of the
dependents of `base`.

- **Refuter.** A trace in which `lib` is registered with its dependency on
  `base`, while the reload of `base` still recompiles nothing else.
- **Class.** `enumeration-miss`, provisional until `design`(int) places the
  writer.
- **Entry.** The startup recovery reset
  (`src/session_v4/lifecycle.rs::recover_startup_failure`) and the fast path
  that reports an untracked module as typechecked
  (`src/process_form/dependency.rs::handle_import`). `design`(int) recorded that fast path as an unverified
  lead in the ACT-1010 correction; this trace observes it.

## Next evidence

This is a next-basket item. It does not block the M1 correction, which is
fail-closed here.

1. The user decides fix or carry.
2. `test` commits the smallest failing, unignored cell, with this
   in-session control.
3. `design`(int) places the mechanism, then `dev` implements it.

## Completion

The cell passes: a fixed startup-failed dependency recompiles its dependents,
which are released, and the in-session control stays GREEN.
