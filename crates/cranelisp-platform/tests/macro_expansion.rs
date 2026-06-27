//! Crate-integration tests for the reworked `declare_platform!` macro
//! (FIXME 0286 / platform-interface.md §6.1) — the three-exports model:
//! the exported GOT (`__cranelisp_got_platform_<name>`), the manifest
//! (`cranelisp_platform_manifest`), and the embedded generated schema +
//! layout-hash (`__cranelisp_layout_hash_<name>`).
//!
//! These assert the *behaviour* of the macro's emitted exports; the
//! *compilation contract* of the arm surface is in `macro_full_arm_compile.rs`.

use cranelisp_platform::{
    set_global_schema, CLAdt, CLAdtType, CLInt, HostContext, Schema, SchedulingClass,
};
use std::sync::atomic::Ordering;

// Static HOST required by declare_platform!.
static HOST: HostContext = HostContext::new();

// An author-defined marker type keyed by FQ name (the macro no longer emits
// these; the author declares them — a few lines).
struct Rectangle;
impl CLAdtType for Rectangle {
    const TYPE_NAME: &'static str = "shapes/Rectangle";
}

// Two trivial extern fns the macro references. We do not call them through the
// language; we only need them to populate the GOT + manifest.
#[allow(unsafe_op_in_unsafe_fn)]
pub extern "C" fn noop_fn() -> cranelisp_platform::CLIO<CLInt> {
    cranelisp_platform::CLIO::pure(CLInt::from(0i64))
}

#[allow(unsafe_op_in_unsafe_fn)]
pub extern "C" fn second_fn() -> cranelisp_platform::CLIO<CLInt> {
    cranelisp_platform::CLIO::pure(CLInt::from(1i64))
}

cranelisp_platform::declare_platform! {
    name: "macro-test",
    version: "0.1.0",
    host: HOST,
    schema: "\
;; layout-hash: macrotesthash
(schema
  (shapes/Rectangle
    (Rectangle 0 ((w primitives/Int) (h primitives/Int)))))",
    functions: [
        noop_fn {
            cl_name: "noop",
            sig: "(Fn [] (IO primitives/Int))",
            doc: "noop",
            params: [],
            scheduling: SchedulingClass::Commutative,
        },
        second_fn {
            cl_name: "second",
            sig: "(Fn [] (IO primitives/Int))",
            doc: "second",
            params: [],
            scheduling: SchedulingClass::Sequential,
        },
    ]
}

// The macro emits these `pub` items at this module's root (the GOT static + the
// manifest entry fn). The GOT carries `export_name`/`no_mangle` link names for
// the host; the Rust identifiers `__CRANELISP_PLATFORM_GOT` /
// `cranelisp_platform_manifest` are reachable in-crate directly.

extern "C" fn test_alloc(_size: i64) -> i64 {
    0
}

/// Call the macro-emitted manifest entry point exactly as the host would, so
/// the GOT-populate + schema-install side effects run.
fn invoke_manifest() -> cranelisp_platform::PlatformManifest {
    let callbacks = cranelisp_platform::HostCallbacks {
        alloc: test_alloc,
        alloc_with_tag: cranelisp_platform::null_alloc_with_tag,
    };
    unsafe { cranelisp_platform_manifest(&callbacks) }
}

// spec: design/arch/platform-interface.md §5.1 — the macro exports the GOT
// `__cranelisp_got_platform_<name>` and populates slot i with functions[i]'s
// pointer (manifest order IS GOT slot order). ABI v7.
#[test]
fn macro_exports_got_in_manifest_order() {
    let manifest = invoke_manifest();
    assert_eq!(
        manifest.abi_version, 7,
        "ABI v7 (Sprint 93 — the ABI-v4 cascade recorded numerically 6→7: \
         poll-shape async-leaf effect fns + ConcurrencyDescriptor in the \
         manifest + the host-reactor C-ABI; v7 layout types landed-and-dormant \
         behind the `concurrency` feature, the macro still emits the v6 \
         PlatformFn shape until the reactor wires them. Was v6 at DEF-5 — the \
         manifest export is namespaced per platform name; v5 at FIXME 0327 \
         Option A; v4 at the step-1 node-widen; v3 at FIXME 0286)"
    );
    assert_eq!(manifest.function_count, 2);

    // GOT slot i must equal manifest functions[i].ptr — one declared order.
    let functions = unsafe {
        std::slice::from_raw_parts(manifest.functions, manifest.function_count)
    };
    for (i, f) in functions.iter().enumerate() {
        let got_ptr = __CRANELISP_PLATFORM_GOT[i].load(Ordering::Acquire) as *const u8;
        assert_eq!(
            got_ptr, f.ptr,
            "GOT slot {i} must hold the fn pointer of manifest functions[{i}]"
        );
    }
    // Slot 0 is noop_fn, slot 1 is second_fn — distinct, non-null.
    let s0 = __CRANELISP_PLATFORM_GOT[0].load(Ordering::Acquire);
    let s1 = __CRANELISP_PLATFORM_GOT[1].load(Ordering::Acquire);
    assert!(!s0.is_null() && !s1.is_null());
    assert_ne!(s0, s1, "the two functions occupy distinct GOT slots");
}

// spec: design/arch/platform-interface.md §5.5.4 — the macro exports the
// layout hash `__cranelisp_layout_hash_<name>`, extracted from the embedded
// artifact's `;; layout-hash:` header.
#[test]
fn macro_exports_layout_hash_from_header() {
    assert_eq!(__CRANELISP_LAYOUT_HASH, "macrotesthash");
}

// spec: design/arch/platform-interface.md §5.5 — the macro installs the
// embedded generated schema so CLAdt::read_field resolves fields by name.
#[test]
fn macro_installs_schema_for_name_based_read() {
    invoke_manifest(); // installs the global schema
    // Allocate a synthetic Rectangle and read its fields by name.
    let base = {
        let total = 16 + 8 + 2 * 8; // header + tag-slot + 2 fields
        unsafe {
            let layout = std::alloc::Layout::from_size_align_unchecked(total, 8);
            let p = std::alloc::alloc_zeroed(layout);
            *(p as *mut i64) = total as i64;
            *((p as *mut i64).add(1)) = 1;
            let payload = p.add(16);
            *(payload as *mut u32) = 0; // tag
            *((payload.add(8)) as *mut i64) = 11; // w
            *((payload.add(16)) as *mut i64) = 22; // h
            p as i64
        }
    };
    let r: CLAdt<Rectangle> = CLAdt::from_raw(base);
    assert_eq!(i64::from(r.read_field::<CLInt>("w")), 11);
    assert_eq!(i64::from(r.read_field::<CLInt>("h")), 22);
    unsafe {
        let total = 16 + 8 + 2 * 8;
        let layout = std::alloc::Layout::from_size_align_unchecked(total, 8);
        std::alloc::dealloc(base as *mut u8, layout);
    }
    // Belt-and-braces: a freshly parsed copy of the same artifact agrees.
    let _ = set_global_schema; // surface witness — the installer is public
    let schema = Schema::parse(
        ";; layout-hash: x\n(schema (shapes/Rectangle (Rectangle 0 ((w primitives/Int)))))",
    )
    .unwrap();
    assert!(schema.lookup_type("shapes/Rectangle").is_some());
}
