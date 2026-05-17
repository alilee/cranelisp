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
//!
//! ## Force-link incantation
//!
//! The `pub use` re-exports below exist to force the linker to include all
//! runtime symbols in the produced staticlib. Without these references, the
//! `.a` would contain only symbols defined in this crate, and the linker
//! would strip the `#[no_mangle]` / `#[export_name]` runtime functions from
//! `cranelisp-intrinsics` and `cranelisp-primitives` as unreferenced.
//!
//! Wave 4a.pre.exe-bundle (Sprint 66) migrated these re-exports from the
//! soon-to-be-retired `cranelisp-runtime` shim crate to the two terminal
//! crates directly:
//!
//! - `cranelisp-intrinsics` — backend-emitted-call targets (alloc, drop,
//!   io, ivar, ops, panic, rc, string-internal, trace, vec-internal).
//! - `cranelisp-primitives` — user-callable / symbol-table-addressable
//!   functions (string user APIs, vec_len, marshal sconcat/quote_sexp,
//!   int/float/bool to_string, parse_int).

// Force-link intrinsics submodules (backend-emitted calls).
pub use cranelisp_intrinsics::alloc;
pub use cranelisp_intrinsics::drop;
pub use cranelisp_intrinsics::io;
pub use cranelisp_intrinsics::ivar;
pub use cranelisp_intrinsics::panic;
pub use cranelisp_intrinsics::rc;
// `cranelisp_intrinsics::trace` re-export DELETED per Decision 40 / Path B1
// (S67 W4, FIXME 0202): `--link` mode rejects `(trace ...)` at compile time
// (FIXME 0199), so the static archive `libcranelisp_exe_bundle.a` does not
// need trace symbols.
pub use cranelisp_intrinsics::heap_string as intrinsics_string;
pub use cranelisp_intrinsics::vec_runtime as intrinsics_vec;

// Force-link primitives submodules (user-callable APIs + Ring 0 ops).
pub use cranelisp_primitives::bool;
pub use cranelisp_primitives::float;
pub use cranelisp_primitives::int;
pub use cranelisp_primitives::marshal;
pub use cranelisp_primitives::ring0;
pub use cranelisp_primitives::string as primitives_string;
pub use cranelisp_primitives::vec as primitives_vec;

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
        alloc: cranelisp_intrinsics::alloc::heap_alloc,
    };
    manifest_fn(&callbacks);
}
