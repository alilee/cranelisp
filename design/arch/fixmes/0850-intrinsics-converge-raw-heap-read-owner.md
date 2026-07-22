---
number: 0850
target: /dev
filed_by: /sprint
filed_at: 2026-07-22
sprint_filed: 116
refers_to: audits/cranelisp-intrinsics-s115.md §6 R-3; crates/cranelisp-intrinsics/src/heap_access.rs; crates/cranelisp-intrinsics/src/drop.rs; crates/cranelisp-intrinsics/src/vec_runtime.rs
status: open
---

# Converge intrinsics raw heap reads on their declared owner

## Issue

Accepted audit recommendation R-3. `CLAUDE.md` declares `heap_access` the sole raw heap-access owner, but `drop.rs` open-codes a read and duplicates Vec layout offsets already owned by `vec_runtime.rs`. This is the third-sprint recurrence of S87 F3.

## Proposed resolution

Make `drop.rs` delegate raw reads to `heap_access` and reuse `vec_runtime`'s layout authority, with unit coverage demonstrating behaviour is unchanged. Prefer making the correct single-owner guidance true over weakening it.
