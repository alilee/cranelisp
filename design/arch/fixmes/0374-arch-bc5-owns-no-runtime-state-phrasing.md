---
number: 0374
target: /arch
filed_by: /design
filed_at: 2026-06-16
sprint_filed: 84
refers_to: design/arch/bounded-contexts.md §5 ("owns no runtime state"), audits/platform-2026-06-14.md (LOW-1), crates/cranelisp-platform/src/lib.rs:884-891, crates/cranelisp-platform/src/adt.rs:90
status: open
---

# platform BC §5: correct "owns no runtime state" to name the three per-DLL write-once globals

## Issue
`design/arch/bounded-contexts.md` §5 states the platform crate "owns no runtime state and no cadence." Per `audits/platform-2026-06-14.md` LOW-1 this is literally inaccurate: the crate holds **three** process-global statics — two `AtomicPtr` allocator slots (`GLOBAL_ALLOC`, `GLOBAL_ALLOC_WITH_TAG`, `lib.rs:884-891`) and one `OnceLock<Schema>` (`GLOBAL_SCHEMA`, `adt.rs:90`). These are sound and intentional (per-DLL, write-once at `HostContext::init` / `set_global_schema`, bounded by invariant 6's no-unload rule), but a future reader reconciling the BC statement against source will trip on the literal claim.

## Proposed resolution
`/arch` refines the BC §5 phrasing to: "owns **no session-coordinated state** and no cadence; the only state is three per-DLL write-once globals (`GLOBAL_ALLOC`, `GLOBAL_ALLOC_WITH_TAG`, `GLOBAL_SCHEMA`) set at DLL load and bounded by invariant 6." (`GLOBAL_SCHEMA` is a `OnceLock`, not an `AtomicPtr` — the count is 3, not 2.)

## Context / Operational implication
LOW-severity doc-accuracy, no behaviour change. The platform master design doc `design/platform/platform.md` §1 was already corrected to the "no session-coordinated state" phrasing in the S84 §3-refresh pass (FIXME 0372); this FIXME propagates the same correction to the `/arch`-owned BC §5 (the canonical source `platform.md` §1 cites). Filed alongside the 0372 §3 refresh.
