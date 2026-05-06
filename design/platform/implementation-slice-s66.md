# Sprint 66 implementation slice — `cranelisp-platform`

**Status.** draft
**Author.** /design (platform), 2026-05-06
**Reads.** `design/arch/facades/platform.md` (post-S65 final-state target — D42 PlatformError + ErrorLocation, OwnedPlatformFnDescriptor `#[non_exhaustive]` per FIXME 0107, IO_TAG_* in public consts per W1 25fa73a, CLString wraps `cranelisp_intrinsics::HeapString`); `design/platform/platform.md` (master design); `design/arch/facades/types.md` §"Errors and warnings" + §"FQTypeName" — PlatformError canonical shape; `design/arch/facades/intrinsics.md` §"String primitives" + §"Heap allocator" — HeapString home post-D43; `design/arch/decisions/0042-platform-error-adopts-error-location.md`; `design/arch/decisions/0043-runtime-split-into-primitives-intrinsics.md`; `design/arch/fixmes/0104-dev-types-platform-int-platformerror-adoption.md`; `design/arch/fixmes/0107-dev-platform-owned-platform-fn-descriptor-non-exhaustive.md`; `design/arch/fixmes/0150-runtime-split-primitives-intrinsics.md`; `sprints/SPRINT.md` Wave Phase 4 W4a; `design/arch/sprint-65-reshape-phase-2-review.md` §3 (slice template).

This slice enumerates the concrete delta between the post-S65 final-state `facades/platform.md` and the current `crates/cranelisp-platform/src/lib.rs` source. It is consumed by `/sprint` as input to S66's wave plan; it is not itself a wave allocation.

---

## 1. Scope from facade — delta table

Each row names one facade item, its current state in source, the target state, and the action class. Action classes:

- **rename** — symbol exists; signature/name changes
- **signature-change** — symbol exists with the right name but parameters/return type need adjustment
- **new** — symbol does not yet exist in this crate; must be authored
- **migrate-in** — symbol exists in another crate and must be moved into this crate
- **delete** — symbol exists and must be removed
- **attribute-add** — public type exists, gains a Rust attribute (e.g., `#[non_exhaustive]`)
- **dep-update** — Cargo.toml dependency edge changes (e.g., `cranelisp-runtime` → `cranelisp-intrinsics`)
- **verify** — facade and source already align; an `/arch`-level cross-check confirms the alignment; no source change

| # | Facade item | Source location(s) | FIXME closed | Action | Acceptance |
|---|---|---|---|---|---|
| 1 | `pub use cranelisp_types::PlatformError;` (re-export per Principle 15 external-audience exception) | not present; `manifest_to_descriptors` returns `Result<…, String>` | 0104 Phase 2 | new (re-export) | Single-line `pub use` in `lib.rs`; rustdoc cites Principle 15 inline justification (out-of-tree DLL author crates depend ONLY on `cranelisp-platform`); compiles against `cranelisp-types` Phase 1 landing |
| 2 | `manifest_to_descriptors(manifest) -> Result<(String, String, Vec<OwnedPlatformFnDescriptor>), PlatformError>` | `lib.rs:598` returns `Result<…, String>` | 0104 Phase 2 | signature-change | UTF-8 validation failures construct `PlatformError::LoadFailed { dll: PathBuf::new(), cause, location: ErrorLocation::unknown() }` — caller (`int::load_platform_dll`) rewrites `dll` and `location` at the call site. Existing inline tests retargeted to the typed error; one new unit test asserting `LoadFailed` returned on UTF-8-invalid name field |
| 3 | `#[non_exhaustive] pub struct OwnedPlatformFnDescriptor { name, jit_name, ptr, param_count, type_sig, docstring, scheduling_class }` | `lib.rs:583` defines struct without `#[non_exhaustive]`; carries `param_names: Vec<String>` not in facade reference shape (acknowledged §3 divergence #6) | 0107 | attribute-add (+ facade-text correction note) | `#[non_exhaustive]` annotation lands; internal builders inside `cranelisp-platform` continue to construct via struct literal (the attribute only restricts external construction); verify `int`-side never struct-literals (it consumes through `manifest_to_descriptors`'s return value); facade text update for `param_names` field is `/arch`-narrow editorial (slice records as known divergence; no source action) |
| 4 | `pub struct CLString(pub i64)` — `i64` is base ptr to `cranelisp_intrinsics::HeapString` (D43 — string layout owned by intrinsics); `CLString::as_str()` reads the intrinsics-allocated bytes | `lib.rs:341–418` reads `[len][bytes]` at `payload = base + HEAP_HEADER_SIZE` directly via raw pointer arithmetic; layout constants come from `cranelisp_types::HeapHeader::SIZE` (lib.rs:47); does NOT reach into `cranelisp-intrinsics` (no dep edge) | 0150 (D43 split) | verify (no source change) | The current implementation already conforms to the post-D43 contract: platform reads bytes by hard-coded offset against the layout governed by `ABI_VERSION` per Principle 14; intrinsics owns the canonical `HeapString` definition + writers (`alloc_string`, `read_string_as_str`); platform's accessor is a layout-compatible reader. **No `cranelisp-intrinsics` dep edge added** — platform stays free of all workspace crates except `cranelisp-types` per BC §5 invariant. Slice records this as deliberate: cross-DLL boundary code reads via documented byte offsets (the `HEAP_HEADER_SIZE` + `STRING_HEADER_BYTES` constants), not through the intrinsics function ABI |
| 5 | `pub const IO_TAG_PURE: i64; IO_TAG_EFFECT; IO_TAG_BIND; IO_TAG_PAR; IO_EFFECT_RESOURCE_OFFSET: i64; ABI_VERSION: u32` (R9 truth-telling — public consts) | `lib.rs:1–52` — already public consts (commit `25fa73a`, S65 W1) | (R9 platform truth-telling) | verify | Source matches facade exactly post-`25fa73a`; one cross-check pass during slice review confirming no rename or visibility regression |
| 6 | `HostContext::dispatch` — formally retired (facade §"Host context"; direct GOT lookup via `platform_fn_ptr` on `ModuleEntry::Def` is the canonical path per Decision 26) | `lib.rs:535–576` defines `HostContext` with `init()` only; no `dispatch` method ever existed | (S64 W3 sub-batch B; substance §2.13) | verify | Source has never carried `dispatch`; facade truth-telling landed S64 W3 sub-batch B; one cross-check confirms no `pub fn dispatch` reappears via accidental re-introduction during the FIXME 0104 refactor |
| 7 | `HostCallbacks { alloc, dec, rc_inc, invoke_closure }` — facade-target shape | `lib.rs:53–120` ships only `alloc` (the three callback fields tied to Decision 31 `Fn a b` callback row, currently future work) | (Decision 31 forward-commitment; NOT in S66 scope) | verify (no-op for S66) | Facade-target shape lands when spec §10.10.1 adds the `Fn a b` row and the ABI version bumps to 2; out of S66 scope per master §3 divergence #1 + §9 forward-commitment. Slice records as known forward-commitment; no source change this sprint |
| 8 | `pub fn parse_type_sig(sig: &str) -> Result<Vec<Type>, PlatformError>` (facade §"Type signature parser") | NOT in `cranelisp-platform`; lives in `src/platform.rs` per BC §5 (DLL lifecycle is `int`'s, including type-vocabulary parsing that needs `cranelisp-typecheck`) | (master §3 divergence #4) | verify (no source change in `cranelisp-platform`) | Facade text divergence acknowledged: facade names `parse_type_sig` as a platform-crate entry; implementation places it in `int` (correct per BC §5 — typecheck-vocabulary access is `int`'s side). Slice records as known editorial divergence resolvable by `/arch` facade text correction. **No source action in `cranelisp-platform` this slice.** The `int` slice's mirror item refactors `int::parse_type_sig` to return `Result<…, PlatformError>` per FIXME 0104 Phase 3 |
| 9 | `pub fn load_manifest(dll_path: &Path) -> Result<Vec<OwnedPlatformFnDescriptor>, PlatformError>` (facade §"Host-side descriptors") | NOT in `cranelisp-platform`; `dlopen` orchestration lives in `src/platform.rs::load_platform_dll` per BC §5 (DLL lifecycle is `int`'s) | (master §3 divergence #4) | verify (no source change in `cranelisp-platform`) | Same disposition as row 8: facade names `load_manifest` as platform-crate; implementation correctly places lifecycle orchestration in `int` (the `libloading::Library` retention lives in `SharedState.kept_dlls` per Decision 38). Slice records as known editorial divergence; no source action in `cranelisp-platform`. **The `int` slice carries the `load_platform_dll` refactor to construct `PlatformError`** — see "Cross-crate dependencies" below |
| 10 | `Cargo.toml` workspace deps — depend on `cranelisp-types` only (Decision 43 — platform does NOT name `cranelisp-runtime` and does NOT name `cranelisp-intrinsics`); see facade §"Consumed surface" + master §1 + BC §5 | currently `Cargo.toml` deps: `cranelisp-types` (workspace), `libloading` (external) — already correct | 0150 (D43 split) | verify | The pre-D43 source never depended on `cranelisp-runtime`; the platform-runtime pairing has always been **runtime depends on platform** (for `HostContext` access at IO trampoline dispatch), not the reverse. Post-D43, **`cranelisp-intrinsics` depends on platform** for the same reason. Platform's dep set is unchanged by D43. Slice confirms by cross-check; no `Cargo.toml` edit |
| 11 | `pub use cranelisp_types::SchedulingClass;` re-export (Principle 15 external-audience exception; already landed) | `lib.rs:41` | — | verify | Already aligned; cross-check during slice review confirms no regression |
| 12 | Inline `#[cfg(test)] mod tests` — `into_owned_consuming` no-inc semantics, `own()` vs `into_owned_consuming` contrast, capture-Effect RC balance | `lib.rs:818–940` | — | verify-then-extend | Existing tests stay; one new test added per row 2 acceptance (UTF-8-invalid name → `LoadFailed`). Capture-Effect tests are layout-sensitive — confirm they pass against the unchanged HEAP_HEADER_SIZE/STRING_HEADER_BYTES constants post-D43 |
| 13 | `declare_platform!` macro — three-phase capture / JIT-name derive / leaked manifest static | `lib.rs:678–816` | — | verify | Macro shape unchanged by D42 + FIXME 0107; the macro emits the `cranelisp_platform_manifest` extern that the host reads; no signature interaction with `PlatformError` (the manifest extern signature is `extern "C" fn(host_callbacks: *const HostCallbacks) -> *const PlatformManifest` — failure surfaces via host-side validation, not through this extern). Slice records the macro as untouched |

**Total rows: 13.** By action class:

- **verify**: 8 rows (5, 6, 7, 8, 9, 10, 11, 13)
- **verify-then-extend** (existing tests stay; one new test added): 1 row (12)
- **signature-change**: 1 row (2)
- **attribute-add**: 1 row (3)
- **new** (re-export): 1 row (1)
- **dep-update**: 0 rows (D43 changes the upstream-of-platform graph but leaves platform's own dep set unchanged — important Decision-43 finding)
- **migrate-in / migrate-out / delete / rename**: 0 rows

Single-action distribution by primary verb: verify 9, signature-change 1, attribute-add 1, new 1, verify-extend 1.

The slice is **small**. The crate is the most stable in the workspace by design (it is the binding contract DLL authors compile against; ABI churn is rare). The two substantive deltas are PlatformError adoption (rows 1, 2) and the `#[non_exhaustive]` cleanup (row 3).

---

## 2. Ordering within the slice

The slice has internal ordering driven by FIXME 0104's three-phase sequence (types → platform + int) plus a small `#[non_exhaustive]` housekeeping item:

1. **Prerequisite (NOT in this slice; lives in `cranelisp-types`)**: Phase 1 of FIXME 0104 — `PlatformError` enum lands in `crates/cranelisp-types/src/error.rs` with `LoadFailed`/`ManifestNotFound`/`AbiVersionMismatch`/`DispatchError` variants per Decision 42; `CranelispError::Platform(PlatformError)` variant added; `#[non_exhaustive]` on the enum. **This slice is blocked on the types slice for rows 1, 2.**

2. **`pub use cranelisp_types::PlatformError;` (row 1)** — single-line re-export. Lands once Phase 1 is in.

3. **`manifest_to_descriptors` signature-change (row 2)** — refactor return type from `Result<…, String>` to `Result<…, PlatformError>`; UTF-8 validation failure constructs `PlatformError::LoadFailed { dll: PathBuf::new(), cause, location: ErrorLocation::unknown() }`; caller (`int::load_platform_dll`) rewrites `dll` and `location` at the call site per Phase 3 of FIXME 0104. Inline tests retargeted; one new test asserting LoadFailed-return.

4. **`#[non_exhaustive]` on `OwnedPlatformFnDescriptor` (row 3)** — independent of rows 1 + 2; can land in same commit or separately. Single-attribute touch; mechanical.

5. **Verify-class rows (5, 6, 7, 8, 9, 10, 11, 12, 13)** — no source changes in `cranelisp-platform`; one cross-check pass during slice review confirms alignment. Rows 8 + 9 are facade-text editorial concerns surfaced for `/arch` (master-design §3 divergences #4 — `load_manifest`/`parse_type_sig` placement); slice records but does not action.

Items 2 and 3 are independent and may land in a single commit. The slice is small enough to fit in **half a wave** for `/dev` (platform), with most of that time in the test refresh + the `int`-side-pairing work that lives in the int slice.

---

## 3. Estimated effort

**Half an S66 wave for `/dev` (platform)** — the platform crate is the smallest and most stable surface in the workspace by design, and S66's platform delta is intentionally narrow:

- Row 2 (`manifest_to_descriptors` signature-change) is ~50 LOC of refactor (return-type change + 4–6 construction sites for `PlatformError::LoadFailed`); 4–5 inline tests retargeted.
- Row 1 (re-export) is single-line.
- Row 3 (`#[non_exhaustive]`) is single-attribute touch; trivial.
- One new unit test for row 2 acceptance (~20 LOC).
- Verify-class rows consume one cross-check pass; ~30 minutes.

Sized as **~1 day** of `/dev`-platform time. Pairs **sequentially** with the `int` slice — the `int` slice's `load_platform_dll` refactor consumes the new `PlatformError` return type and rewrites the location-bearing fields at call sites. Decoupled from frontend, typecheck, backend, primitives, intrinsics slices (platform has no edges to those).

If S66's wave envelope is generous, the platform slice can complete in the same wave as the types slice's Phase 1 landing (with ~15 min of synchronisation). Tighter envelope: platform slice lands in the wave immediately after types Phase 1 concludes, paired with int's Phase 3 in the same wave.

---

## 4. Dependencies on other crates' slices

| This slice's item | Depends on | In the other crate's slice |
|---|---|---|
| Row 1 (`pub use cranelisp_types::PlatformError`) | `PlatformError` enum exists in `cranelisp-types` per Decision 42 shape (`#[non_exhaustive]` enum with `LoadFailed`/`ManifestNotFound`/`AbiVersionMismatch`/`DispatchError`, each carrying `ErrorLocation`); `CranelispError::Platform(PlatformError)` variant present; serde derives applied per types-crate convention | **types slice** (FIXME 0104 Phase 1): land `PlatformError` in `crates/cranelisp-types/src/error.rs`; add `CranelispError::Platform(PlatformError)` variant per `facades/types.md` §"Errors and warnings" lines 537–620; verify `Display` impl supports the `Sess::format_error` mode-conditional resolution path per Decision 39 |
| Row 2 (`manifest_to_descriptors` returns `Result<…, PlatformError>`) | The `int` slice rewrites `src/platform.rs::load_platform_dll` to call `manifest_to_descriptors` and rewrite `dll`/`location` on the returned `PlatformError` | **int slice** (FIXME 0104 Phase 3): replace `CranelispError::ModuleError` constructions in `load_platform_dll` with `CranelispError::Platform(PlatformError::…)`; add `PlatformError` arm to `Sess::format_error` (per Decision 39 mode-conditional source-resolution path); rewrite `(platform "name")`-form span into the location field at the call site |
| Row 4 (`CLString` reads layout-compatible `HeapString` bytes) | `cranelisp-intrinsics` owns canonical `HeapString` definition + writers; layout governed by `ABI_VERSION` (Principle 14); platform reads via documented `HEAP_HEADER_SIZE` + `STRING_HEADER_BYTES` byte offsets | **intrinsics slice** (FIXME 0150): confirm `HeapString` layout (`[i64 len][u8 bytes...]` at `payload = base + HEAP_HEADER_SIZE`) is the canonical post-D43 shape; `cranelisp-intrinsics::alloc_string` writes the layout platform's `CLString::from(&str)` reads back; any future layout change requires an `ABI_VERSION` bump per Principle 14 + a coordinated platform-crate refresh. **No code edge added** — the layout-compatibility contract is documented + enforced by `ABI_VERSION`, not by a Rust dep edge |
| Row 8 (facade names `parse_type_sig` in platform; implementation correctly places it in `int`) | `int` slice's `parse_type_sig` refactor returns `Result<…, PlatformError>` per FIXME 0104 Phase 3; `/arch` may correct facade text to reflect BC §5 placement (editorial only, no source change) | **int slice** (FIXME 0104 Phase 3): refactor `parse_type_sig` to return `Result<…, PlatformError>` constructing `LoadFailed` or a new variant for malformed type signatures (slice files question if needed — see §6); facade text correction is `/arch`-narrow editorial |
| Row 9 (facade names `load_manifest` in platform; implementation correctly places it in `int::load_platform_dll`) | `int` slice carries the load-orchestration refactor | **int slice** (FIXME 0104 Phase 3): see row 2 entry above — `load_platform_dll` is the integration-side enactment of the contract this crate publishes |

**Cross-crate count: 5 distinct dependency rows naming 2 other slices** — types slice (1 row, prerequisite) and int slice (4 rows, mostly downstream consumer of platform's signature change). The intrinsics slice is referenced (row 4) but the dependency is **layout-governance-by-`ABI_VERSION`**, not a Rust dep edge — no Cargo.toml change. All bilateral: each row identifies the corresponding entry in the other crate's slice.

The dependency graph is **shallow and forward-only**: types → platform → int. No cycle; no triad-cycle hazard. Per Principle 3 (dependency direction), platform stays at its post-D43 position — depends only on `cranelisp-types`, with `cranelisp-intrinsics` being **downstream** of platform via the IO trampoline's per-entry `platform_fn_ptr` dispatch (per facade §"Host context" + BC §5).

**Platform's dep set is unchanged by Decision 43.** This is a notable finding: the runtime split affects the *upstream-of-platform* graph (via the runtime → primitives + intrinsics rebrand) but leaves platform's own `Cargo.toml` untouched. The platform-runtime pairing has always been runtime-depends-on-platform (host callbacks installed at session init); under D43 the same structural relationship holds with `cranelisp-intrinsics` taking runtime's place at the trampoline dispatch site. Confirmation lives in row 10 verify-class disposition.

---

## 5. Test surface impact

### Existing platform unit tests touched

The 3-test inline `#[cfg(test)] mod tests` block at `lib.rs:818–940` covers:
- `into_owned_consuming` no-inc semantics (Decision 24)
- `own()` vs `into_owned_consuming` contrast
- The capture-Effect pattern's RC balance

The slice's source changes touch:

- **`manifest_to_descriptors` tests** (if any inline depend on `String` error type) — retarget to `PlatformError::LoadFailed { cause, .. }` pattern-match. Audit during slice authoring shows current inline tests do NOT exercise the error path, so no existing-test bodies change for row 2.
- **`OwnedPlatformFnDescriptor` construction** — internal struct-literal sites continue to compile with `#[non_exhaustive]` (the attribute only restricts external construction); no test changes for row 3.
- **Layout-sensitive RC tests** (capture-Effect, `into_owned_consuming`) — verify pass against unchanged `HEAP_HEADER_SIZE` and `STRING_HEADER_BYTES` post-D43; the constants don't move under D43 (they remain derived from `cranelisp_types::HeapHeader::SIZE`).

### New unit tests authored

- **`manifest_to_descriptors` UTF-8-invalid name returns `LoadFailed`** (acceptance for row 2): construct a `PlatformManifest` with an invalid-UTF-8 byte sequence in the `name` field; assert `Err(PlatformError::LoadFailed { dll: PathBuf::new(), cause, location: ErrorLocation::unknown() })` with `cause` containing the underlying UTF-8 error message. This is structural — does not require a live DLL or any cross-crate scheduler.
- **(optional, if useful)** — `OwnedPlatformFnDescriptor` external-construction-rejected test in a downstream crate. Out of scope here (the attribute's behaviour is a Rust language guarantee; no per-crate test needed).

**~1 new unit test authored inside `cranelisp-platform`** per the project test strategy (memory: unit tests with /dev). E2E coverage of the PlatformError surfacing path — a missing DLL produces `lib/main.cl:42:7: error: platform "stdio" not found in search path` — is `/qa`'s domain in `tests/`. This slice files a FIXME against `/qa` if the S66 test plan slice doesn't enumerate an end-to-end test exercising the Decision-39 mode-conditional source-resolution path through `Sess::format_error`'s new `PlatformError` arm.

### Existing e2e tests touched

The E2E suite in `tests/` exercises platform DLL loading via the binary; the migration is internal-shape (typed errors replace stringly-typed ones), so e2e behaviour SHOULD be invariant for the success path. **Negative-path e2e tests** (missing DLL, ABI mismatch, malformed manifest) become more useful post-adoption: they can assert on the structured location field, not just the stringified cause. Sprint `/qa` slice owns the negative-path uplift.

---

## 6. Open questions

The facade is unambiguous on the migration's shape. The slice surfaces three narrow questions where authoring met an edge:

1. **Should `parse_type_sig` (in `int`) construct `PlatformError::LoadFailed`, `PlatformError::DispatchError`, or warrant a new `PlatformError::TypeSigParseError` variant?** The facade lists four variants (`LoadFailed`, `ManifestNotFound`, `AbiVersionMismatch`, `DispatchError`) plus the `#[non_exhaustive]` ellipsis. A malformed type signature surfaces during the `manifest_to_descriptors` → `parse_type_sig` chain in `int`'s `load_platform_dll`, NOT as a runtime dispatch failure. Treating it as `LoadFailed { cause: "type signature parse error: ..." }` is cheapest; a dedicated variant is more honest and aligns with Decision 42's per-failure-mode discipline. **Slice's tentative choice: `LoadFailed`.** If `/arch` prefers a dedicated variant, file as a same-sprint `/arch` revision. Not blocking platform-slice authoring; the choice lives in the `int` slice's Phase 3 work (`int::parse_type_sig`).

2. **Facade text mentions `load_manifest` and `parse_type_sig` as platform-crate entries; the implementation correctly places both in `int` per BC §5. Should `/arch` correct the facade text to reflect placement, or leave the facade abstract (naming the contract surface, not the crate-level placement)?** The master-design §3 divergence #4 notes this. Slice's tentative read: facade text should be tightened to acknowledge that the contract surface (returning `Result<…, PlatformError>`) is published by `cranelisp-platform` (via `manifest_to_descriptors`'s Phase 2 refactor) but the orchestration entry-points (`load_manifest`, `parse_type_sig`) are integration-side per BC §5. This is editorial, not substantive. **Filed tentatively as a question for `/arch`** — pending whether `/arch` regards the facade text as already implicit in the BC §5 placement or as a substantive interpretation that warrants facade tightening. If substantive: file `design/arch/fixmes/0152-name.md` (or next sequential) targeting `/arch`.

3. **The S66 wave plan should sequence the platform slice BETWEEN the types slice (Phase 1 lands `PlatformError`) and the int slice (Phase 3 consumes the new return type). Is half-a-wave allocation appropriate, or should `/sprint` collapse types-Phase-1 + platform-Phase-2 + int-Phase-3 into a single coordinated wave?** Slice's tentative read: the three phases are sequential (Phase 1 prerequisite for Phases 2+3; Phase 3 consumes Phase 2's signature change), so a single coordinated wave with explicit sub-batch ordering (`/dev`(types) → `/dev`(platform) → `/dev`(int)) is cleaner than three separate waves. **Slice records the question for `/sprint`** — the wave allocation is `/sprint`'s output, not the slice's.

If `/arch` regards any of these as substantive (i.e., not editorial or wave-allocation), the slice files as `design/arch/fixmes/0152-name.md` (or 0153, 0154 — sequential allocation) targeting `/arch`. **Tentative count: 0–2 FIXMEs may be filed during S66 implementation depending on `/arch`'s read.** Per Principle 4 (uninvented answers), the slice does not unilaterally resolve; surfaces the question.

---

## 7. Cross-references

- `design/arch/facades/platform.md` — public-API contract (this slice's target)
- `design/arch/facades/types.md` §"Errors and warnings" lines 537–620 — `PlatformError` enum canonical home + `CranelispError::Platform` variant
- `design/arch/facades/intrinsics.md` §"String primitives" + §"Heap allocator" — post-D43 `HeapString` home + layout governance
- `design/arch/decisions/0042-platform-error-adopts-error-location.md` — Decision 42 (PlatformError + ErrorLocation per variant)
- `design/arch/decisions/0043-runtime-split-into-primitives-intrinsics.md` — Decision 43 (the split that puts `HeapString` in intrinsics; reframes 15)
- `design/arch/fixmes/0104-dev-types-platform-int-platformerror-adoption.md` — multi-crate migration; this slice executes Phase 2
- `design/arch/fixmes/0107-dev-platform-owned-platform-fn-descriptor-non-exhaustive.md` — `#[non_exhaustive]` housekeeping; this slice executes
- `design/arch/fixmes/0150-runtime-split-primitives-intrinsics.md` — D43 multi-crate work; platform's row 4 + 10 verify-class confirms platform's dep set is untouched
- `design/platform/platform.md` §3 divergence list, §5 ABI architecture, §9 callback forward-commitment, §11 Decision register — master design
- `sprints/SPRINT.md` Wave Phase 4 W4a — slice-authoring wave
- `design/arch/sprint-65-reshape-phase-2-review.md` §3 — slice template authority
- `crates/cranelisp-platform/src/lib.rs` (940 lines) — current source under reshape
- `src/platform.rs` — `int`'s platform load + path resolution + type signature parser (the integration-side enactment of this crate's contract; refactored per FIXME 0104 Phase 3 in the int slice)
