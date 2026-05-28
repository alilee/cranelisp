---
number: 0229
target: /int
filed_by: /dev (platform)
filed_at: 2026-05-28
sprint_filed: 71
refers_to: design/platform/sprint71-redesign.md §9, design/arch/bounded-contexts.md §5, crates/cranelisp-platform/src/lib.rs (HostCallbacks)
status: open
---

# Wire host-side ADT marshaling callbacks

## Issue

Sprint 71 Wave 2 introduced `HostCallbacks::alloc_with_tag` and
`HostCallbacks::validate_schema` as named-null callback fields (per
A6 ruling / design §5.2). The fields are currently populated with
`cranelisp_platform::null_alloc_with_tag` (panics with R1 gate
message naming this FIXME) and `cranelisp_platform::null_validate_schema`
(no-op, returns 0).

The host (`src/platform.rs:182` + `crates/cranelisp-exe-bundle/src/lib.rs:97`)
currently passes the null callbacks. CLAdt construction
(`CLAdt::<T>::construct(...)`) therefore panics at runtime under the
R1 gate. Schema validation against the host's actual deftype data is
deferred until this FIXME is resolved.

## Proposed resolution

In the host-wiring sprint:

1. **`alloc_with_tag`**: implement `cranelisp_intrinsics::cranelisp_alloc_with_tag`
   following the contract in `crates/cranelisp-platform/src/lib.rs` on
   `HostCallbacks::alloc_with_tag` rustdoc. Specifically:
   - Allocate `total_size = 16 (header) + 8 (tag+pad) + 8*field_count` bytes
     via the runtime allocator.
   - Write `[total_size: i64][rc: i64=1]` header.
   - Write `[tag: u32][pad: u32]` at payload+0.
   - Copy `field_count` i64s from `fields_ptr` at payload+8 onwards.
   - Return the alloc base pointer (matching CLString's convention).

2. **`validate_schema`**: implement a host-side validator that:
   - Re-parses the schema (via `cranelisp_platform::Schema::parse`).
   - Cross-references each declared type-name against the active
     typecheck symbol-table for matching `ModuleEntry::Type` shapes
     (variant arity, field types).
   - On mismatch, writes a diagnostic message into the provided
     `err_msg` buffer and returns non-zero.

3. **Replace the null-callback pointers in both HostCallbacks
   construction sites** with the wired implementations:
   - `src/platform.rs:182` — `load_platform_dll`
   - `crates/cranelisp-exe-bundle/src/lib.rs:97` — `cranelisp_init_platform`

4. **Delete `cranelisp_platform::null_alloc_with_tag` and
   `cranelisp_platform::null_validate_schema`** once the host wires
   real callbacks — the R1 gate is structural, not runtime, and the
   named-null functions are the gate itself.

## Operational implication / Context

Per design §9 the R1 gate's removal is "two lines in one file" (the
HostCallbacks initializer at the host's load site). The wired callbacks
unlock the full ADT-marshaling surface end-to-end, allowing platform
DLLs to construct and pass typed heap-ADT values across the FFI boundary
without runtime panic.

This FIXME also pairs with FIXMEs 0230–0233 (parse_type_sig removal +
platform-as-module migration) — coordinated landing in the host-wiring
sprint allows the platform-DLL surface to consume the cranelisp
typecheck symbol-table for schema validation.
