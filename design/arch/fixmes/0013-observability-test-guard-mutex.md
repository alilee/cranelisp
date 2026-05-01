---
number: 0013
target: /int
filed_by: /review
filed_at: 2026-05-01
sprint_filed: 64
refers_to: src/observability.rs:692, design/review/sprint-61-wave-1-slice-0.md §Importants I-1
status: open
migrated_from_inline: true
---

# 0013 — Add test serialisation lock to `reset_panic_hook_installed_for_tests` (observability)

## Issue

Sprint 61 Wave 1 `/review` raised Important I-1: `reset_panic_hook_installed_for_tests` in `src/observability.rs` mutates process-global state (`PANIC_HOOK_INSTALLED` + `std::panic::set_hook`) without a serialisation lock. Safe under `cargo nextest run` (subprocess-per-test) but fragile under `cargo test` where tests share a process. Sister concern to FIXME 0012 in `crates/cranelisp-runtime/src/io_trace.rs`.

Recommended fix: add `static TEST_GUARD: Mutex<()> = Mutex::new(())` and take the lock at the top of every test that calls this + `install_panic_hook`. Deferred once under the one-deferral-permitted policy — ship by Wave 5 or next sprint, else escalate.

## Source location

`src/observability.rs:692-700` (FIXME comment block above the `#[cfg(test)] fn reset_panic_hook_installed_for_tests`).

## Context

Test-only reset hook for the idempotent-install guard. Allows a single test to reinstall the hook to observe the install path twice. Not part of the stable API.

## Proposed resolution

Same shape as FIXME 0012 — `~10 LOC` `once_cell::sync::Lazy<Mutex<()>>`. Apply in the same wave so the two sister sites share the convention.
