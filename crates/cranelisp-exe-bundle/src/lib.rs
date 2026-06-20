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
//! (alloc, drop, io, ivar, panic, rc, trace, string-internal, vec-internal).
//!
//! `trace` rejoined the force-linked set in Sprint 76 (FIXME 0255). The
//! 2026-06-04 trace ruling (`design/arch/tracing.md` TARGET STATE) retracted
//! D40's REPL/`--run`-only restriction: `(trace ...)` now works in ALL modes
//! including `--link`, the 12 trace bodies are ordinary intrinsics published by
//! `intrinsics_table()`, and backend bakes self-contained display descriptors
//! that survive `.o` caching. The trace symbols must therefore be present in
//! `libcranelisp_exe_bundle.a` like every other intrinsic.
//!
//! ## Startup-hook discipline — primitives
//!
//! `cranelisp-primitives`' force-link `pub use` re-exports were retired in
//! Sprint 68 Wave 3 per `design/arch/decisions/0048-primitives-static-symboltable-and-got-in-crate.md`
//! §Cascade. The replacement is the explicit `cranelisp_init_primitives()`
//! startup hook (below) — the standalone binary's startup stub calls it
//! UNCONDITIONALLY before user code runs (FIXME 0280 made the call
//! unconditional; pre-0280 it rode on `cranelisp_init_platform`, so a
//! no-platform program calling an extern primitive reached user code with an
//! unpopulated GOT); the hook forces `LazyLock::force(&PRIMITIVES_TABLE)`,
//! which references every primitive's fn ptr via the static-init body, so
//! the linker preserves them as transitive dependencies of the static.
//!
//! Since FIXME 0280 (S76 Wave 3) the force ALSO populates the exported writable
//! static slab `cranelisp_primitives::PRIMITIVES_GOT_SLAB`
//! (`#[unsafe(export_name = "__cranelisp_got_primitives")]`), over which
//! `PRIMITIVES_TABLE`'s `GotTable` is constructed. That export is what makes
//! `__cranelisp_got_primitives` a link-time symbol — `--link`-mode
//! extern-primitive dispatch (`(str-len (str-concat …))`) now resolves at `ld`
//! time instead of failing with "symbol not found: ___cranelisp_got_primitives".
//! The startup hook populates the slab's slots before the first GOT-indirect
//! dispatch reads them (null slots → SIGSEGV).
//! See `design/arch/facades/int.md` §"Exe-bundle startup contract —
//! `cranelisp_init_primitives()`" for the full rationale.

// Force-link intrinsics submodules (backend-emitted calls).
pub use cranelisp_intrinsics::alloc;
pub use cranelisp_intrinsics::drop;
pub use cranelisp_intrinsics::io;
pub use cranelisp_intrinsics::ivar;
// `cranelisp_check_layout_hash` — the `--link` platform layout-hash gate
// (platform-interface.md §5.5.4 / FIXME 0287 seam). Backend declares it
// `Linkage::Import` in the startup stub and never names the Rust symbol, so it
// is force-linked here like every other startup intrinsic.
pub use cranelisp_intrinsics::layout;
pub use cranelisp_intrinsics::panic;
pub use cranelisp_intrinsics::rc;
// `cranelisp_intrinsics::trace` re-export RESTORED in S76 (FIXME 0255). The
// 2026-06-04 trace ruling retracted D40's trace half: `(trace ...)` now works
// in all modes incl. `--link`, so `libcranelisp_exe_bundle.a` must carry the
// trace symbols (the 12 `cranelisp_trace_*` bodies + the descriptor formatter).
pub use cranelisp_intrinsics::trace;
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
    // `alloc_with_tag` is wired to the real intrinsic (S76 W3, FIXME 0229
    // step 1): `cranelisp_alloc_with_tag` allocates a tagged heap ADT and
    // returns the alloc base, removing the R1 gate in `--link` mode too. The
    // `validate_schema` callback channel is gone (FIXME 0288): schema validation
    // is superseded by the `--link` layout-hash gate (platform-interface.md
    // §5.5.4), baked into the startup object as a `cranelisp_check_layout_hash`
    // compare-and-abort.
    let callbacks = cranelisp_platform::HostCallbacks {
        // DEF-6 (Sprint 86): `HostCallbacks::alloc` MUST return a PAYLOAD pointer
        // (alloc base + HEAP_HEADER_SIZE) — the platform's heap-node constructors
        // (`CLIO::pure`/`effect`, `CLString::from`) subtract HEAP_HEADER_SIZE to
        // recover the base. `heap_alloc` returns the BASE, so wiring it here drove
        // every platform-built node's stored base 16 bytes too low, clobbering the
        // RC header and overrunning adjacent heap metadata one node per host↔DLL
        // crossing (glibc "double free or corruption" after ~40 crossings). The
        // JIT path (`src/platform.rs`) already wires `heap_alloc_payload`; this
        // makes the `--link` path match. See the platform-side layout-invariant
        // guards `def6_*` in cranelisp-platform/src/lib.rs.
        alloc: cranelisp_intrinsics::alloc::heap_alloc_payload,
        alloc_with_tag: cranelisp_intrinsics::alloc::cranelisp_alloc_with_tag,
    };
    manifest_fn(&callbacks);
}
