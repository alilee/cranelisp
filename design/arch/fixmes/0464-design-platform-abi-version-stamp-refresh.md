---
number: 0464
target: /design
filed_by: /sprint
filed_at: 2026-07-02
sprint_filed: 99
refers_to: design/platform/platform.md, design/platform/poll-support.md, crates/cranelisp-platform/src/lib.rs:281 (ABI_VERSION)
status: open
---

# Platform design docs still stamp `ABI_VERSION = 7`; live source is `9`

## Issue

Surfaced during the Sprint-99 close-out stale-`declare_concurrent_platform!`
doc sweep (`/design`, platform surface): `design/platform/platform.md` and
`design/platform/poll-support.md` still print `ABI_VERSION = 7` as the *current*
stamp, but live source is `ABI_VERSION = 9` (`crates/cranelisp-platform/src/lib.rs:281`,
set by the S97 v9 ctx-vtable handle-model cutover).

This is **separate from** the stale-macro sweep (which corrected the deleted
`declare_concurrent_platform!` / `ConcurrentPlatformFn` references — done S99)
and was deliberately left untouched as out-of-scope for that focused sweep.

## Proposed resolution

Refresh the ABI-version stamp in both docs from 7 → 9, checking the surrounding
prose for any v7/v8-specific claims that the v9 cutover changed (the version
number rarely travels alone). Verify against `lib.rs` + the S97/S98 concurrency
docs (`bounded-contexts.md §4b`, `effect-concurrency.md §12.1`) for what v9
actually is (the ctx-vtable handle model: tramp-owned `acquire`/`register_*`/
`retire`, opaque ADT handles).

## Operational implication / Context

- Pure doc-accuracy refresh, no behaviour change; a platform author reading a
  `= 7` stamp against a `= 9` binary would be misled about the current ABI.
- Cheap; drain opportunistically. Not gating anything.
