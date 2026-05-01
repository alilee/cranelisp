---
number: 0001
target: /arch
filed_by: /arch
filed_at: 2026-04-25
sprint_filed: 63
refers_to: design/arch/facades/platform.md (Sealed traits + non_exhaustive section); design/arch/facades/runtime.md
status: open
---

# `#[non_exhaustive]` interaction with `#[repr(C)]` for C-ABI types

## Issue

The facade convention (`/arch` skill def §Facade convention, item 3) requires `#[non_exhaustive]` on every public DTO. Several types in `cranelisp-runtime` and `cranelisp-platform` carry `#[repr(C)]` because they cross the C ABI boundary (intrinsic helper signatures, platform DLL contracts, IO trampoline structs).

`#[non_exhaustive]` and `#[repr(C)]` together are well-defined in Rust syntactically, but the *intent* differs:

- `#[non_exhaustive]`: external consumers cannot construct, exhaustively pattern-match, or destructure — protects API evolution.
- `#[repr(C)]`: layout is fixed and consumed by external code (Cranelift JIT relocations, platform DLLs).

Adding a field to a `#[non_exhaustive] #[repr(C)]` DTO is *source-non-breaking* in Rust but *binary-breaking* against the JIT/DLL surface — anyone who hard-coded a layout or offset will read garbage. The protection `#[non_exhaustive]` offers is illusory at the C-ABI boundary.

## Proposed resolution

`/arch` decides one of:

(a) **Exempt `#[repr(C)]` DTOs from the `#[non_exhaustive]` rule.** Layout drift is the real concern at that boundary; explicit version-bumping or a `_reserved` padding field replaces `#[non_exhaustive]` semantically.

(b) **Apply both.** Accept that `#[non_exhaustive]` only guards source-level breakage; layout drift is governed by an additional `cargo-public-api` rule once M4 lands (or by a separate FFI-stability discipline).

(c) **Split DTOs.** Internal struct = `#[non_exhaustive]`; FFI-export struct = bare `#[repr(C)]` with explicit field order, version bumped on any change. The internal-FFI conversion happens at the platform/runtime boundary.

Option (c) is the most robust but adds layer cost. (a) is simplest and matches FFI conventions.

## Context

Surfaced during S63 W2 facade-spec authoring. The facades `platform.md` and `runtime.md` both list types where this tension applies (e.g., `IoTrampolineFrame`, `CLHeap` header layout, intrinsic argument structs). M6 (facade refactor, S67) will mechanically apply `#[non_exhaustive]`; this decision must precede M6 to avoid retrofit.
