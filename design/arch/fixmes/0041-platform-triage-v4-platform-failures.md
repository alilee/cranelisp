---
number: 0041
target: /platform
filed_by: /int
filed_at: 2026-05-01
sprint_filed: 64
refers_to: design/int/platform-registry-removal.md:293
status: open
migrated_from_inline: true
---

# 0041 — Triage 5 v4_platform failures: cache-restore dependency check

## Issue

Triage the 5 `v4_platform` failures — do any exercise cache restore of a platform-loaded module? If yes, glue option (b) (temporarily retain `(platform "name")` form re-execution path inside the cache-hit codepath) is required this sprint; if no, option (a) (Phase 5 closes the gap) is sufficient and the cache-restore gap moves to Phase 5.

## Source location

`design/int/platform-registry-removal.md:293` (HTML-comment FIXME below §8).

## Context

`platform_fn_ptr` is `#[serde(skip)]`; on cache-hit load, every cached `PlatformEffect` entry deserialises with `platform_fn_ptr: None`. The mechanism for re-resolution is via `SymbolTable.platforms: Vec<PlatformDecl>` (Phase 5 work).

## Proposed resolution

`/platform` triages the 5 v4_platform failures and reports back: are any cache-restore-dependent? If yes, scope (b) glue into the current Phase 4 G8 wave; if no, defer to Phase 5.
