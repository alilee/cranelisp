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
//! ## Force-link incantation — intrinsics
//!
//! The `pub use` re-exports below exist to force the linker to include
//! intrinsics symbols in the produced staticlib. Without these references,
//! the `.a` would contain only symbols defined in this crate, and the linker
//! would strip the `#[no_mangle]` / `#[export_name]` runtime functions from
//! `cranelisp-intrinsics` as unreferenced.
//!
//! Wave 4a.pre.exe-bundle (Sprint 66) migrated these re-exports from the
//! soon-to-be-retired `cranelisp-runtime` shim crate to the terminal
//! `cranelisp-intrinsics` crate directly — backend-emitted-call targets
//! (alloc, drop, io, ivar, ops, panic, rc, string-internal, vec-internal).
//!
//! ## Startup-hook discipline — primitives
//!
//! `cranelisp-primitives`' force-link `pub use` re-exports were retired in
//! Sprint 68 Wave 3 per `design/arch/decisions/0048-primitives-static-symboltable-and-got-in-crate.md`
//! §Cascade. The replacement is the explicit `cranelisp_init_primitives()`
//! startup hook (below) — the standalone binary's startup stub calls it
//! before user code runs; the hook forces `LazyLock::force(&PRIMITIVES_TABLE)`,
//! which references every primitive's fn ptr via the static-init body, so
//! the linker preserves them as transitive dependencies of the static.
//! See `design/arch/facades/int.md` §"Exe-bundle startup contract —
//! `cranelisp_init_primitives()`" for the full rationale.

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

// Primitives force-link `pub use` lines RETIRED in S68 Wave 3 per
// Decision 0048 §Cascade. The replacement is the explicit
// `cranelisp_init_primitives()` startup hook below — see crate-level docs.

extern crate cranelisp_platform;

/// Force population of `cranelisp-primitives`' static `SymbolTable` + `GotTable`
/// before any compiled code runs.
///
/// Per `design/arch/decisions/0048-primitives-static-symboltable-and-got-in-crate.md`
/// §Cascade and `design/arch/facades/int.md` §"Exe-bundle startup contract —
/// `cranelisp_init_primitives()`", this hook replaces the pre-S68 force-link
/// `pub use cranelisp_primitives::*` re-exports. The standalone binary's
/// startup stub calls it (alongside `cranelisp_init_platform`) before user
/// code runs.
///
/// `LazyLock::force(&PRIMITIVES_TABLE)` triggers the static-init body, which
/// references every primitive's `extern "C"` fn ptr via `extern_shims()`.
/// The linker preserves those symbols in `libcranelisp_exe_bundle.a` as
/// transitive dependencies of the static-init body — making the dependency
/// legible at the site that needs it (Principle 7, single source of truth),
/// rather than relying on implicit `pub use` force-link discipline.
#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_init_primitives() {
    std::sync::LazyLock::force(&cranelisp_primitives::PRIMITIVES_TABLE);
}

/// Initialize a platform by calling its manifest function with host callbacks.
///
/// Called from the startup stub of standalone executables. Takes the manifest
/// function pointer as i64 (obtained via `func_addr` in Cranelift IR),
/// constructs `HostCallbacks` with the runtime allocator, and calls the
/// manifest function — which triggers `HostContext::init()` and sets GLOBAL_ALLOC.
///
/// Also forces `cranelisp_init_primitives()` so the primitives `LazyLock`
/// runs before any compiled code dispatches through `__cranelisp_got_primitives`.
#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_init_platform(manifest_fn_ptr: i64) {
    // Force the primitives table's `LazyLock` so __cranelisp_got_primitives
    // is populated before any backend-emitted import resolves through it.
    cranelisp_init_primitives();

    type ManifestFn = extern "C" fn(
        *const cranelisp_platform::HostCallbacks,
    ) -> cranelisp_platform::PlatformManifest;
    let manifest_fn: ManifestFn = unsafe { std::mem::transmute(manifest_fn_ptr) };
    let callbacks = cranelisp_platform::HostCallbacks {
        alloc: cranelisp_intrinsics::alloc::heap_alloc,
    };
    manifest_fn(&callbacks);
}
