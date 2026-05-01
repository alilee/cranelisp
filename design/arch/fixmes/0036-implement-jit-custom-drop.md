---
number: 0036
target: /backend
filed_by: /int
filed_at: 2026-05-01
sprint_filed: 64
refers_to: design/int/concurrent-workers.md:231, crates/cranelisp-backend/src/jit.rs
status: open
migrated_from_inline: true
---

# 0036 — Implement custom `Drop` on `Jit` that calls `JITModule::free_memory()`

## Issue

Implement the custom `Drop` on `Jit` (in `crates/cranelisp-backend/src/jit.rs`) that calls `unsafe JITModule::free_memory()`. The safety proof is the Arc-refcount-zero + symbol-table-and-GOT-discipline invariant from Decision 31. The previously-filed `FIXME(/backend)` about adding a `Jit::finish()` wrapper is re-aimed at this target.

## Source location

`design/int/concurrent-workers.md:231` (FIXME after §5 "Per-worker JIT lifecycle").

## Context

Per Decision 31, the canonical reclaim path is custom `Drop` calling `free_memory()`. The earlier `kept_jits`/`drain_to_shared` design (in `concurrent-workers.md` below the FIXME) is superseded — it was a correct workaround given a misunderstanding of Cranelift's drop semantics; the real behaviour is the opposite (default drop leaks; explicit `free_memory` is required).

Safety contract: (a) every code pointer either lives on a `ModuleEntry::Def.code` (refcount > 0) or is ephemeral; (b) GOT slots are atomically swapped to new code before the old Arc can drop; (c) user-returned `fn` values are heap closures calling through the GOT, not raw code pointers.

## Proposed resolution

`/backend` implements `impl Drop for Jit` calling `unsafe JITModule::free_memory()`. Add the safety proof comment referencing Decision 31. Verify against `tests/v4_jit_reclaim.rs` (Decision 31 Scenario 1 + 2).
