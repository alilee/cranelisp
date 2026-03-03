//! Static library bundle for standalone cranelisp executables.
//!
//! This crate produces a single `.a` file that bundles the cranelisp runtime
//! (intrinsics, primitives, marshal) with the Rust standard library.
//! Platform functions are linked separately as rlibs via rustc.

// Force the linker to include all runtime symbols by referencing them.
pub use cranelisp_runtime::intrinsics;
pub use cranelisp_runtime::marshal;
pub use cranelisp_runtime::primitives;

extern crate cranelisp_platform;

/// Initialize a platform by calling its manifest function with host callbacks.
///
/// Called from the startup stub of standalone executables. Takes the manifest
/// function pointer as i64 (obtained via `func_addr` in Cranelift IR),
/// constructs `HostCallbacks` with the runtime allocator, and calls the
/// manifest function — which triggers `HostContext::init()` and sets GLOBAL_ALLOC.
#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_init_platform(manifest_fn_ptr: i64) {
    type ManifestFn =
        extern "C" fn(*const cranelisp_platform::HostCallbacks) -> cranelisp_platform::PlatformManifest;
    let manifest_fn: ManifestFn = unsafe { std::mem::transmute(manifest_fn_ptr) };
    let callbacks = cranelisp_platform::HostCallbacks {
        alloc: cranelisp_runtime::intrinsics::alloc,
    };
    manifest_fn(&callbacks);
}
