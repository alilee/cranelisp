---
number: 0042
title: `PlatformError` is a `cranelisp-types`-hosted enum with `ErrorLocation` carriers per variant; surfaces via `CranelispError::Platform`
status: operative
---

# 0042 — `PlatformError` is a `cranelisp-types`-hosted enum with `ErrorLocation` carriers per variant; surfaces via `CranelispError::Platform`

`PlatformError` is a `cranelisp-types`-hosted enum carrying `ErrorLocation` per variant. Platform-origin failures (DLL load, manifest parse, ABI mismatch, dispatch error) construct it and surface via `CranelispError::Platform(PlatformError)`. Int's `Sess::format_error` consumes it through Decision 39's mode-conditional resolution path. Closes the gap where `manifest_to_descriptors` returned `Result<…, String>` and threw away every coordinate the parser had — a user typing `(platform "stdio")` with a missing DLL gets `lib/main.cl:42:7: error: platform "stdio" not found in search path` rather than a free-floating string.

## Shape

```rust
// cranelisp-types/src/error.rs
#[non_exhaustive]
pub enum PlatformError {
    LoadFailed { dll: PathBuf, cause: String, location: ErrorLocation },
    ManifestNotFound { dll: PathBuf, location: ErrorLocation },
    AbiVersionMismatch { dll: PathBuf, expected: u32, found: u32, location: ErrorLocation },
    DispatchError { fn_name: Symbol, cause: String, location: ErrorLocation },
}

pub enum CranelispError {
    // …existing variants…
    Platform(PlatformError),
}
```

Each variant's `location` field points back at the offending source — the `(platform "name")` form's span; the file path when known; FQ context per Decision 39. `cranelisp-platform`'s `manifest_to_descriptors` and DLL load paths refactor to construct `PlatformError` rather than `String`. Int's `Sess::format_error` (from Decision 39) gains a `PlatformError` arm following the same mode-conditional source-resolution path the other Decision-39 errors already use.

## Why this shape

The `cranelisp-types`-as-home choice is non-negotiable per Principle 3 (boundary types live in `cranelisp-types`; cannot live downstream and be wrapped from upstream). The variant set is minimal per Principle 2 — four variants covering the load/manifest/ABI/dispatch failure modes the platform crate actually surfaces today; future failure modes extend the enum (it's `#[non_exhaustive]`). Single source of truth per Principle 7 — one enum, one home, every platform-origin failure flows through it.

Decision 39 is the binding cross-crate rule: errors carry `ErrorLocation`. Platform was the holdout — `facades/platform.md` specified `PlatformError` as the public surface, but the implementation never built it. This Decision aligns implementation with facade and with Decision 39's coordinates-as-data discipline.

## Scope clarification (vs §2.10)

§2.10 was originally bundled with this Decision as a parallel Decision-39 application: enrich `runtime_panic` with structured location data. Per §2.10's revised disposition (runtime panics are being driven to zero, not enriched — investment is in eliminating call sites, not making panics richer), Decision 42 narrows to platform-only. `runtime_panic` stays flat-String; §2.11 separately corrects the runtime facade to truth-tell that signature.

## Consequences

- `cranelisp-types/src/error.rs` gains `PlatformError` enum with `ErrorLocation` carriers per variant; marked `#[non_exhaustive]`.
- `CranelispError::Platform(PlatformError)` variant added.
- `crates/cranelisp-platform/` refactors `manifest_to_descriptors` and DLL load paths to construct `PlatformError` rather than `String`.
- `facades/platform.md` `PlatformError` reference moves from "specified, unimplemented" to "spec + implementation aligned" (facade subsequently retired S71 W4; canonical surface is now `crates/cranelisp-platform/src/lib.rs` rustdoc on the `PlatformError` re-export + `bounded-contexts.md` §5).
- `facades/types.md` gains the `PlatformError` enum in §"Errors and warnings".
- `Sess::format_error` (per Decision 39) gains the `PlatformError` arm.

## Cross-references

- Decision 39 (errors carry `ErrorLocation`) — binding cross-crate rule that this Decision applies to platform.
- §2.11 — runtime facade signature alignment for `runtime_panic` (sibling work; intentionally NOT enriched per §2.10).
- Sprint 63 substance-scoping resolution §1.3.

## Rationale

- Principle 2 (narrow interfaces) — minimal four-variant enum; `#[non_exhaustive]` for future extension.
- Principle 3 (dependency direction) — boundary type lives in `cranelisp-types`, not in `cranelisp-platform`.
- Principle 7 (single source of truth) — one enum for all platform-origin failures.

## Canonical location

`crates/cranelisp-types/src/error.rs` (`PlatformError` enum + `CranelispError::Platform` variant). Owner: `/arch` files Decision, authors `PlatformError` in `cranelisp-types`, updates `crates/cranelisp-platform/src/lib.rs` rustdoc on the `PlatformError` re-export (post-S71 W4 facade retirement) and `facades/types.md`. `/dev` (platform) refactors load and dispatch paths to construct the enum. `/dev` (int) extends `Sess::format_error` with the `PlatformError` arm.
