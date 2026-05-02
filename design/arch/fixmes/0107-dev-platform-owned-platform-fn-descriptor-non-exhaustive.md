---
number: 0107
target: /dev
filed_by: /arch
filed_at: 2026-05-02
sprint_filed: 64
refers_to: design/arch/facades/platform.md §"#[non_exhaustive] DTOs", design/arch/principles/14-ffi-layout-discipline.md, crates/cranelisp-platform/src/lib.rs (OwnedPlatformFnDescriptor)
status: open
---

# Add `#[non_exhaustive]` to `OwnedPlatformFnDescriptor`

## Issue

Per `/arch`'s resolution of FIXME 0105 (Option A — extend Principle 14 to cover both `#[repr(C)]` and `#[repr(transparent)]`), the per-facade `#[non_exhaustive]` rule applies to plain Rust DTOs that do NOT carry an FFI repr annotation. `OwnedPlatformFnDescriptor` is the post-load owned form of a platform fn descriptor — pure Rust, no `#[repr]` annotation, never crosses the DLL ABI directly. It SHOULD carry `#[non_exhaustive]` per the standard facade convention.

The current implementation in `crates/cranelisp-platform/src/lib.rs` does not.

## Proposed resolution

Add `#[non_exhaustive]` to the `OwnedPlatformFnDescriptor` struct definition. Update any internal construction sites (within `cranelisp-platform`) — `#[non_exhaustive]` only restricts external construction, so internal builders continue to work. External consumers (`int`'s session) should already be using the public construction path (`manifest_to_descriptors`); verify no `int`-side direct struct-literal construction exists.

Half a sprint hour. Bundle naturally with FIXME 0104 (the larger PlatformError adoption pass) since both touch `cranelisp-platform/src/lib.rs`.

## Context

The `#[repr(C)]` and `#[repr(transparent)]` types in the platform facade (CLInt/CLString/etc., PlatformManifest/PlatformFn/HostCallbacks) remain exempt per Principle 14. This FIXME catches the one remaining type that should carry the annotation but doesn't. Closes the inventory mismatch flagged in `design/platform/platform.md` §3.
