---
number: 0482
target: /dev
filed_by: /arch
filed_at: 2026-07-03
sprint_filed: 101
refers_to: crates/cranelisp-backend/src/cache/manifest.rs:202 (CacheInvalidReason), crates/cranelisp-backend/public-api.txt, .claude/commands/arch.md §"Facade convention" item 3
status: open
---

# `CacheInvalidReason` gains `#[non_exhaustive]` — S101 Wave-3 finding ruled by /arch Wave 5

## Severity

Minor (convention alignment; no behavioural change).

## Issue

The S101 Wave-3 `/dev`(backend) finding: `CacheInvalidReason` (public enum,
`cache/manifest.rs:202`) is not `#[non_exhaustive]`, so the Wave-3
`OwnershipToggle` variant addition was technically breaking for any external
exhaustive matcher. `/arch` Wave-5 ruling: the facade convention
(`.claude/commands/arch.md` §"Facade convention — lib.rs mechanics" item 3)
mandates `#[non_exhaustive]` on every public DTO, with the sole exemption
being `#[repr(C)]`/`#[repr(transparent)]` layout contracts — which this enum
is not. It is a produced-by-backend, matched-by-consumers reason enum: the
textbook `#[non_exhaustive]` case. Survey at ruling time: no exhaustive
matcher exists in-workspace (`src/` names the type only in a doc comment;
backend's own `Display` impl is unaffected — same-crate matches stay
exhaustive), so the attribute costs nothing today.

## Proposed resolution

On `cranelisp-backend` (deployed with the next backend change-set; no
dedicated sprint slot needed):

1. Add `#[non_exhaustive]` to `CacheInvalidReason`.
2. Regenerate `crates/cranelisp-backend/public-api.txt` in the same
   change-set (baseline-diff discipline, `design/arch/CLAUDE.md`
   §"Baseline-diff discipline") — the attribute appears in the baseline, so
   the diff is the `/arch`-approval artifact.
3. While there, audit the sibling public cache DTOs (`CacheManifest`,
   `CachedModuleRef`) for the same convention. Note `CacheManifest` is
   constructed via `new_for_host()` (no external struct-literal
   construction), so `#[non_exhaustive]` is compatible; if any DTO is
   constructed by struct literal outside the crate, flag back to /arch
   rather than adding the attribute.

## Operational implication / Context

The S101 public-api delta itself (5 lines: `OwnershipToggle` + `CacheManifest::
ownership_disabled` + `compile_trap_stub`) is CONFIRMED by /arch as-is; this
FIXME is the forward-looking guard so the *next* variant addition is
non-breaking by construction (Principle 18).
