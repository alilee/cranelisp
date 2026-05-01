---
number: 0037
target: /backend
filed_by: /int
filed_at: 2026-05-01
sprint_filed: 64
refers_to: design/int/symbol-table-cache.md:230, crates/cranelisp-backend/src/lib.rs:200-260
status: open
migrated_from_inline: true
---

# 0037 — `define_module_got_data` for ObjectModule: macOS S_ZEROFILL relocation segfault

## Issue

`define_module_got_data` for `ObjectModule` (in `crates/cranelisp-backend/src/lib.rs:200-260`) uses `desc.define_zeroinit(slot_count * 8)` followed by `desc.write_function_addr(offset, func_ref)`. Cranelift composes these as a `__DATA,__bss` section (Mach-O `S_ZEROFILL`) carrying relocations. macOS `ld` segfaults on `.o` files containing relocations in a `S_ZEROFILL` section because BSS has no file content for the linker to patch (verified via `nm` / `otool -lv` / direct `ld` invocation reproducing exit 139 with empty stderr).

Filed Sprint 58 Wave 2c by `/int`.

## Source location

`design/int/symbol-table-cache.md:230` (HTML-comment FIXME below the GOT discussion).

## Context

The cross-module call mechanism on the `ObjectModule` path requires per-module `__cranelisp_got_M` data with relocations into function addresses. The `S_ZEROFILL` placement is the issue — relocations require a section with file content.

## Proposed resolution

`/backend` switches `define_module_got_data` from `define_zeroinit` to a backed allocation (e.g., `define` with an explicit zero-byte buffer) so relocations land in a regular `__DATA` section. Verify with `--link` integration tests on macOS.
