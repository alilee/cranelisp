---
number: 0012
target: /backend
filed_by: /review
filed_at: 2026-05-01
sprint_filed: 64
refers_to: crates/cranelisp-runtime/src/io_trace.rs:547, design/review/sprint-61-wave-1-slice-0.md §Importants I-1
status: open
migrated_from_inline: true
---

# 0012 — Add test serialisation lock to `reset_panic_hook_installed_for_tests` (io_trace)

## Issue

Sprint 61 Wave 1 `/review` raised Important I-1: `reset_panic_hook_installed_for_tests` in `crates/cranelisp-runtime/src/io_trace.rs` mutates process-global state (`PANIC_HOOK_INSTALLED` + `std::panic::set_hook`) without a serialisation lock. Safe under `cargo nextest run` (subprocess-per-test) but fragile under `cargo test` where tests share a process. Mirrors the same concern as `src/observability.rs::reset_panic_hook_installed_for_tests` (see FIXME 0013).

Recommended fix: add a `static TEST_GUARD: Mutex<()>` and take the lock in every test that calls this + `install_panic_hook`. Deferred once under the one-deferral-permitted policy — ship by Wave 5 or next sprint, else escalate.

## Source location

`crates/cranelisp-runtime/src/io_trace.rs:547-554` (FIXME comment block above the `#[cfg(test)] fn reset_panic_hook_installed_for_tests`).

## Context

The reset hook is part of the idempotent-install guard for the IO trace panic hook. It allows a single test to reinstall the hook to observe the install path twice. Not part of the stable API.

## Proposed resolution

Add `once_cell::sync::Lazy<Mutex<()>>` (~10 LOC), grab at test entry in every site that calls `reset_panic_hook_installed_for_tests` or `install_panic_hook`. Apply the same fix in `src/observability.rs` (FIXME 0013).
