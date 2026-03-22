//! Static library bundle for standalone Cranelisp executables.
//!
//! This crate produces a single `.a` file (`libcranelisp_exe_bundle.a`) that
//! bundles the Cranelisp runtime (allocator, RC, string ops, IO trampoline,
//! primitives, marshal) with the Rust standard library. Platform functions
//! are linked separately as rlibs via the system linker.
//!
//! Build with: `cargo build -p cranelisp-exe-bundle`
//!
//! The resulting `.a` appears in `target/debug/` or `target/release/`.

// Force the linker to include all runtime modules by referencing them.
// Without these re-exports, the staticlib would contain only the symbols
// defined in this crate, and the linker would strip unreferenced runtime
// functions.
pub use cranelisp_runtime::alloc;
pub use cranelisp_runtime::io;
pub use cranelisp_runtime::marshal;
pub use cranelisp_runtime::panic;
pub use cranelisp_runtime::primitives;
pub use cranelisp_runtime::rc;
pub use cranelisp_runtime::string;
pub use cranelisp_runtime::trace;
pub use cranelisp_runtime::vec;

extern crate cranelisp_platform;

/// Initialize a platform by calling its manifest function with host callbacks.
///
/// Called from the startup stub of standalone executables. Takes the manifest
/// function pointer as i64 (obtained via `func_addr` in Cranelift IR),
/// constructs `HostCallbacks` with the runtime allocator, and calls the
/// manifest function — which triggers `HostContext::init()` and sets GLOBAL_ALLOC.
#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_init_platform(manifest_fn_ptr: i64) {
    type ManifestFn = extern "C" fn(
        *const cranelisp_platform::HostCallbacks,
    ) -> cranelisp_platform::PlatformManifest;
    let manifest_fn: ManifestFn = unsafe { std::mem::transmute(manifest_fn_ptr) };
    let callbacks = cranelisp_platform::HostCallbacks {
        alloc: cranelisp_runtime::alloc::heap_alloc,
    };
    manifest_fn(&callbacks);
}
