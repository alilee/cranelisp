---
number: 0042
target: /arch
filed_by: /platform
filed_at: 2026-05-01
sprint_filed: 64
refers_to: design/platform/platform.md:272-275, design/arch/facades/platform.md §"Host context"
status: open
migrated_from_inline: true
---

# 0042 — Define `HostContext::dispatch` (or formally retire from facade)

## Issue

`facades/platform.md §"Host context"` specifies `HostContext::dispatch(platform_fn_id, args) -> Result<CLValue, PlatformError>` as a surfaced facade entry. The implementation does not have it — today the IO trampoline reaches platform fns directly via the JIT linker (via `platform_fn_ptr` on `ModuleEntry::Def`).

Either (a) `dispatch` is a future centralised path that should land, or (b) the facade should record that direct JIT-linker resolution is the canonical path and `dispatch` was an early sketch.

`/arch` arbitrates. If (a), file an implementation FIXME(/dev) on this crate. If (b), update facade text to remove `dispatch` from the public surface.

## Source location

`design/platform/platform.md:272-275` (FIXME section "FIXME — define `HostContext::dispatch` (or formally retire from facade)").

## Context

The `cranelisp-platform` crate's documentation includes a list of FIXMEs for `/arch` arbitration on the public surface. This is one of them.

## Proposed resolution

`/arch` reads the facade and the implementation, picks (a) or (b), and either files the implementation FIXME or updates `facades/platform.md` text.
