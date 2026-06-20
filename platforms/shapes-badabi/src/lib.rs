//! `shapes-badabi` — a hand-rolled platform cdylib that declares a **stale
//! `abi_version`**, so the host refuses it at load with
//! `PlatformError::AbiVersionMismatch { expected, found }`.
//!
//! Sprint 80 Phase 5 Wave 1 (FIXME 0289 item 4 — the perturbed-ABI e2e
//! fixture). It feeds `tests/platform_errors.rs::platform_abi_version_mismatch_e2e`.
//!
//! ## Why hand-rolled
//!
//! The [`cranelisp_platform::declare_platform!`] macro hard-codes
//! `abi_version: $crate::ABI_VERSION` in its emitted
//! `cranelisp_platform_manifest` (see `crates/cranelisp-platform/src/lib.rs`
//! `__declare_platform_body!`), so it has **no override arm** for baking a
//! stale version (FIXME 0238 notes this gap). To produce a DLL whose declared
//! ABI deliberately differs from the host's, this fixture hand-writes the
//! per-platform-namespaced `cranelisp_platform_manifest_shapes-badabi` C-ABI
//! entry point (via `#[unsafe(export_name = ...)]`, matching the name the host
//! computes through `cranelisp_platform::platform_manifest_symbol`) with a stale
//! version literal ([`STALE_ABI_VERSION`]) rather than
//! `cranelisp_platform::ABI_VERSION`.
//!
//! ## Distinct artifact name
//!
//! The crate is named `cranelisp-shapes-badabi` so the compiled cdylib is
//! `libcranelisp_shapes_badabi` — a DISTINCT output from the real `shapes`
//! platform's `libcranelisp_shapes`. Each cdylib exports its own per-platform-
//! namespaced `cranelisp_platform_manifest_<name>`; distinct artifacts AND
//! distinct symbol names keep the two manifests apart, so there is no symbol
//! collision. The
//! host resolves `(platform shapes-badabi)` to this artifact via
//! `resolve_platform_path` (`libcranelisp_{name}.{ext}`, `-`→`_`).
//!
//! ## Surface mirrors `shapes` up to the ABI check
//!
//! This DLL declares the same single `area` function over `shapes/Rectangle`
//! as the real `shapes` platform, so it is structurally a valid platform DLL —
//! but the host's load path validates `abi_version` (`src/platform.rs`
//! `check_abi_version`, Step 4) BEFORE it reads descriptors, dlsyms the GOT,
//! or forces any effect. So the stale version short-circuits the load with
//! `AbiVersionMismatch` and the `area` body is never reached. The body is
//! present only to make the manifest a faithful mirror; it is dead at runtime.

use cranelisp_platform::{
    CLAdt, CLAdtType, CLHeap, CLInt, CLIO, HostCallbacks, HostContext, PlatformFn,
    PlatformManifest, SchedulingClass,
};

/// The deliberately-stale ABI version baked into this DLL's manifest.
///
/// The host's `ABI_VERSION` is currently `6` (DEF-5 bump, §5.5.5); baking `2`
/// here (a prior ABI) guarantees `found (2) != expected (6)` at the
/// `check_abi_version` gate, triggering
/// `PlatformError::AbiVersionMismatch { expected: 6, found: 2 }`. This literal
/// is intentionally NOT derived from `cranelisp_platform::ABI_VERSION` — it
/// stays stale across every host ABI bump, so the mismatch holds regardless of
/// the current real ABI.
const STALE_ABI_VERSION: u32 = 2;

static HOST: HostContext = HostContext::new();

/// Marker type for the `shapes/Rectangle` ADT parameter (mirrors `shapes`).
pub struct Rectangle;

impl CLAdtType for Rectangle {
    const TYPE_NAME: &'static str = "shapes/Rectangle";
}

/// Mirror of `shapes::rectangle_area`. Never reached at runtime — the host
/// refuses this DLL at load on the stale `abi_version` before any dispatch.
pub extern "C" fn rectangle_area(r: CLAdt<Rectangle>) -> CLIO<CLInt> {
    let owned = <CLAdt<Rectangle> as CLHeap>::into_owned_consuming(r);
    CLIO::effect(move || {
        let w: CLInt = owned.read_field("w");
        let h: CLInt = owned.read_field("h");
        CLInt::from(i64::from(w) * i64::from(h))
    })
}

// -- Hand-rolled manifest (the override `declare_platform!` cannot produce —
//    FIXME 0238). Mirrors the macro's emitted body but bakes
//    `STALE_ABI_VERSION` instead of `cranelisp_platform::ABI_VERSION`. --

const PLATFORM_NAME: &str = "shapes-badabi";
const PLATFORM_VERSION: &str = "0.1.0";
const AREA_CL_NAME: &str = "area";
const AREA_SIG: &str = "(Fn [shapes/Rectangle] (primitives/IO primitives/Int))";
const AREA_DOC: &str = "Stale-ABI mirror of shapes/area; never dispatched (load refused on ABI mismatch)";
const AREA_PARAM_R: &str = "r";

/// Hand-rolled C-ABI manifest entry point.
///
/// Mirrors `__declare_platform_body!`'s emitted manifest entry point
/// (init the host context, build a single `PlatformFn` descriptor, return the
/// `PlatformManifest`) — but with `abi_version: STALE_ABI_VERSION` (= 2) in
/// place of the macro's `abi_version: ABI_VERSION` (= 6, DEF-5). The host reads
/// `abi_version` first (`src/platform.rs` Step 4) and refuses with
/// `AbiVersionMismatch { expected, found }`, so the descriptor/GOT/schema
/// machinery the real macro emits is unnecessary here.
///
/// # Safety
/// Matches the macro-emitted entry point's contract: `callbacks` must point to
/// a valid `HostCallbacks` for the duration of the call (the host passes a
/// stack reference). `#[unsafe(export_name = "cranelisp_platform_manifest_shapes-badabi")]`
/// exports the per-platform-namespaced symbol the host dlsyms, exactly matching
/// `cranelisp_platform::platform_manifest_symbol("shapes-badabi")` (§5.5.5
/// invariant: every per-platform C-ABI export is name-suffixed). The macro
/// emits the same string via `concat!("cranelisp_platform_manifest_", $name)`;
/// this fixture hand-rolls the identical export name because it bypasses the
/// macro to bake a stale ABI literal.
#[unsafe(export_name = "cranelisp_platform_manifest_shapes-badabi")]
pub unsafe extern "C" fn cranelisp_platform_manifest(
    callbacks: *const HostCallbacks,
) -> PlatformManifest {
    // Initialise the host context exactly as the macro does (stores callbacks,
    // sets the global allocator). Harmless even though load will be refused.
    unsafe {
        HOST.init(callbacks);
    }

    // One parameter name (`r`), as parallel (ptrs, lens) arrays — the same
    // shape `__declare_platform_body!` builds, leaked to `'static`.
    let name_ptrs: Vec<*const u8> = vec![AREA_PARAM_R.as_ptr()];
    let name_lens: Vec<usize> = vec![AREA_PARAM_R.len()];
    let name_ptrs_ptr = Box::leak(name_ptrs.into_boxed_slice()).as_ptr();
    let name_lens_ptr = Box::leak(name_lens.into_boxed_slice()).as_ptr();

    let functions: &'static [PlatformFn] = Box::leak(
        vec![PlatformFn {
            name: AREA_CL_NAME.as_ptr(),
            name_len: AREA_CL_NAME.len(),
            ptr: rectangle_area as *const u8,
            param_count: 1,
            type_sig: AREA_SIG.as_ptr(),
            type_sig_len: AREA_SIG.len(),
            docstring: AREA_DOC.as_ptr(),
            docstring_len: AREA_DOC.len(),
            param_names: name_ptrs_ptr,
            param_name_lens: name_lens_ptr,
            param_name_count: 1,
            scheduling_class: SchedulingClass::Commutative as u32,
        }]
        .into_boxed_slice(),
    );

    PlatformManifest {
        // THE DELIBERATE DEFECT: stale ABI literal, not `ABI_VERSION`.
        abi_version: STALE_ABI_VERSION,
        name: PLATFORM_NAME.as_ptr(),
        name_len: PLATFORM_NAME.len(),
        version: PLATFORM_VERSION.as_ptr(),
        version_len: PLATFORM_VERSION.len(),
        functions: functions.as_ptr(),
        function_count: functions.len(),
    }
}
