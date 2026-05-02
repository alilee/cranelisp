---
number: 0104
target: /dev
filed_by: /design (platform)
filed_at: 2026-05-02
sprint_filed: 64
refers_to: design/arch/decisions/0042-platform-error-adopts-error-location.md, design/arch/facades/platform.md §"Errors", design/arch/facades/types.md §"Errors and warnings", crates/cranelisp-platform/src/lib.rs (manifest_to_descriptors), src/platform.rs (load_platform_dll), design/platform/platform.md §3 divergence #2
status: open
---

# Adopt structured `PlatformError` per Decision 42

## Issue

`crates/cranelisp-platform/src/lib.rs::manifest_to_descriptors` returns `Result<…, String>`. `src/platform.rs::load_platform_dll` surfaces failures through `CranelispError::ModuleError` with stringified causes. The `(platform "name")` form's coordinates are dropped at the boundary — a user typing `(platform "stdio")` with a missing DLL gets a free-floating string, not `lib/main.cl:42:7: error: platform "stdio" not found in search path`.

Decision 42 pins `PlatformError` as a `cranelisp-types`-hosted enum with `ErrorLocation` per variant, surfaced via `CranelispError::Platform(PlatformError)`. The facade (`design/arch/facades/platform.md`) re-exports `pub use cranelisp_types::PlatformError` per the Principle 15 external-audience exception. Implementation has not yet caught up.

## Proposed resolution

Three-crate `/dev` change, sequenced:

**Phase 1 — `cranelisp-types`** (define enum):
1. Add `PlatformError` enum to `crates/cranelisp-types/src/error.rs` per Decision 42's shape:
   ```rust
   #[non_exhaustive]
   pub enum PlatformError {
       LoadFailed { dll: PathBuf, cause: String, location: ErrorLocation },
       ManifestNotFound { dll: PathBuf, location: ErrorLocation },
       AbiVersionMismatch { dll: PathBuf, expected: u32, found: u32, location: ErrorLocation },
       DispatchError { fn_name: Symbol, cause: String, location: ErrorLocation },
   }
   ```
2. Add `CranelispError::Platform(PlatformError)` variant.
3. Add `Display` impl matching the `Sess::format_error` mode-conditional path (per Decision 39).

**Phase 2 — `cranelisp-platform`** (refactor surface):
1. Re-export `pub use cranelisp_types::PlatformError;` (parallel to existing `pub use cranelisp_types::SchedulingClass;`).
2. Refactor `manifest_to_descriptors` to return `Result<(String, String, Vec<OwnedPlatformFnDescriptor>), PlatformError>`. UTF-8 validation failures construct `LoadFailed` with `cause` carrying the underlying `Utf8Error` message and `location: ErrorLocation::unknown()` (caller threads in real location at the call site).
3. Update inline tests if any depend on `String` error type.

**Phase 3 — `int`** (refactor load + format):
1. Refactor `src/platform.rs::load_platform_dll` to construct `PlatformError` variants:
   - `libloading::Library::new(path)` failure → `LoadFailed { dll: path, cause, location: <span of (platform "name") form> }`
   - Missing `cranelisp_platform_manifest` symbol → `ManifestNotFound { dll: path, location }`
   - `manifest.abi_version != ABI_VERSION` → `AbiVersionMismatch { dll: path, expected: ABI_VERSION, found: manifest.abi_version, location }`
   - `manifest_to_descriptors` error → propagate, threading `location` in (the platform crate constructed with `unknown()`; int rewrites to the form's span).
2. Replace `CranelispError::ModuleError` constructions in the platform load path with `CranelispError::Platform(PlatformError::…)`.
3. Add `PlatformError` arm to `Sess::format_error` (per Decision 39 mode-conditional source-resolution path).

## Sequencing notes

- Phase 1 is prerequisite for Phases 2 and 3.
- Phases 2 and 3 land together (the public API change in Phase 2 cannot land without Phase 3 updating call sites).
- Independent of FIXMEs 0098, 0099, 0100, 0103.
- Bundles naturally with the `platform-dlls.md` refresh (the subordinate doc references the stringly-typed surface in §"Error Conditions").

## Operational implication / Context

User-visible win: a missing or ABI-mismatched DLL produces a located error with the `(platform "name")` form's coordinates rather than a free-floating string. Aligns the platform load path with the rest of the workspace's Decision-39 coordinates-as-data discipline. Closes the last hole in the per-surface error-location story.

Cost estimate: 1–2 sprint days. Most of the work is Phase 3 (rewriting call sites in `int::load_platform_dll`); Phase 1 is mechanical; Phase 2 is local to one function.
