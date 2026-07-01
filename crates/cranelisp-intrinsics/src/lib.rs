//! Cranelisp intrinsics — backend-emitted-call targets.
//!
//! Runtime support code with stable ABI contracts called by JIT-emitted code
//! or by the IO trampoline. **NOT callable from user code**; the ABI is tightly
//! coupled to the backend's codegen choices. This crate is one of the two
//! produced by the `cranelisp-runtime` split (Decision 43); the sibling is
//! `cranelisp-primitives` (user-callable conversions / operators-as-values).
//! Bounded context: `design/arch/bounded-contexts.md` §4b — Intrinsics.
//!
//! ## How the surface is reached (two consumer categories)
//!
//! 1. **Backend-emitted call (the dominant category).** The backend emits
//!    Cranelift IR that calls these by *string name*: the `#[export_name = "…"]`
//!    / `#[no_mangle]` linker symbol (e.g. `runtime/alloc`, `vec-push-copy`,
//!    `cranelisp_ivar_force`). `int`'s session init resolves each name to a fn
//!    pointer and registers it with the JIT via `JITBuilder::symbol`; in
//!    `--link` mode the system linker resolves the same symbol against the
//!    archive. Nothing here is in any symbol table or GOT.
//!
//!    The `#[export_name]` / `#[no_mangle]` attribute emits the linker symbol
//!    into the object/staticlib **independent of Rust visibility** — so the
//!    emitted-call ABI is keyed on that string, not on the Rust path. The
//!    per-module `pub` Rust paths are additionally fn-ptr-harvested by the
//!    backend at `crates/cranelisp-backend/src/jit.rs` (a real Rust-path
//!    dependency), so every per-module extern stays `pub`.
//!
//! 2. **Rust-path consumers.** A second category reaches intrinsics by Rust
//!    path, not by emitted-call relocation:
//!    - `cranelisp-primitives` Rust-calls the allocator (`alloc_string`,
//!      `alloc_with_rc`, `vec_new`), the drop/RC/panic helpers (`consume_sexp`,
//!      `consume_slist`, `consume_shallow`, `runtime_panic`), and reads the
//!      **heap-layout-ABI consts** ([`heap_string::HeapString::LEN_OFFSET`] /
//!      [`heap_string::HeapString::DATA_OFFSET`], [`vec_runtime::LEN_OFFSET`] /
//!      [`vec_runtime::CAP_OFFSET`] / [`vec_runtime::DATA_PTR_OFFSET`]).
//!    - `cranelisp-platform`'s `CLString::as_str` reaches string bytes through
//!      [`heap_string::read_string_as_str`].
//!    - `int` reads the allocation stats ([`alloc::alloc_count`],
//!      [`alloc::dealloc_count`], [`alloc::bytes_current`]), drives the IO
//!      trampoline via [`io::run_io_trampoline`], registers the IO observer via
//!      [`io_observer::register_io_observer`] / [`io_observer::trace_anchor`],
//!      and polls [`panic::take_runtime_error`].
//!
//!    Because `cranelisp-primitives` is a named Rust consumer, the heap-object
//!    layout consts are intrinsics' **blessed, stable public ABI** — governed
//!    by the baseline-diff discipline and by Principle 14 (FFI layout
//!    discipline: evolution via explicit version bump, not source-level guards).
//!    These consts are a settled contract; primitives holds no duplicate copies
//!    (Principle 7). See FIXME 0245.
//!
//! ## `JITBuilder::symbol` narrows to intrinsics only (Decision 0048)
//!
//! Post-S68, the `JITBuilder::symbol(name, ptr)` direct-registration path is
//! reserved **exclusively for intrinsics**: there is no `intrinsics` module,
//! no symbol-table entry, no GOT slot for any of these. **Primitives** flow
//! through the standard cross-module GOT-indirect dispatch path against
//! `cranelisp_primitives::PRIMITIVES_TABLE` — byte-identical to any user-module
//! dispatch. This asymmetry is load-bearing (intrinsics are genuinely
//! runtime-special; primitives are a synthetic module), not residual; forcing
//! intrinsics through a synthetic GOT would introduce a categorical fiction for
//! no semantic gain. Adding a primitive to `JITBuilder::symbol` registration is
//! a regression of the post-S68 categorical line.
//!
//! ## Symbol survival under dead-code elimination (FIXME 0247)
//!
//! `#[used]` is **not** applicable to `extern fn` (rustc accepts it on statics
//! only). The intrinsic externs survive DCE by the same mechanism the sibling
//! `cranelisp-primitives` shims use: the `#[export_name]` / `#[no_mangle]`
//! attribute emits the symbol into the object/staticlib, and `int`'s
//! `JITBuilder::symbol` registration harvest takes each fn address at session
//! init. No redundant `#[used] static` anchor is needed (minimum mechanism,
//! Principle 2).
//!
//! ## Forbidden patterns (load-bearing prohibitions)
//!
//! 1. **No conditional registration of intrinsics.** Every intrinsic MUST be
//!    registered with the JIT unconditionally at session setup. Per-program
//!    syntactic scans gating which intrinsic to register are forbidden — they
//!    have repeatedly drifted (Sprint 59 Defect 8; S66 Wave 3a-β regression).
//!    The cost of registering an unused intrinsic is one `HashMap` entry; the
//!    cost of missing one is a JIT-finalize panic. (FIXME 0178.) Only intrinsics
//!    enumerated on this crate's surface are eligible for `JITBuilder::symbol`;
//!    primitives use GOT-indirect dispatch (above).
//! 2. **No trait-knowledge keys in inline-substitution tables** (Decision 43):
//!    the backend's `primitives_inline.rs` table is keyed on `Symbol` only
//!    (`add-i64 → iadd`), never on `(TraitName, Symbol, TypeName)` triples.
//! 3. **No backend-emitted-call functions exposed as user-callable.** Primitives
//!    Rust-consume a defined subset of this surface but do NOT re-export the
//!    externs as user-callable; user code never references an intrinsic name.
//!
//! ## Int-owned intrinsics (inventory note)
//!
//! The two test-runner intrinsics `discover-tests` and `run-test` physically
//! live in `src/` (int), registered unconditionally — see `src/CLAUDE.md`
//! §"Int-owned JIT intrinsics". They are NOT in this crate and NOT in the
//! catalog (parked — out of scope per the 2026-06-04 ruling).
//!
//! The `(trace ...)` runtime is **hosted HERE** (the [`trace`] module — S76
//! user ruling 2026-06-04 retracting D40's trace-relocation-to-int; BC §4b
//! invariant 12): the 12 `cranelisp_trace_*` bodies (incl. the pure
//! descriptor-driven `cranelisp_trace_format`), the `TRACE_STACK` GOT-swap
//! call-frame stack, `TRACE_THREAD_ID`, the `consume_trace_call` ADT walker,
//! the `DisplayDescriptor` layout-ABI, and the same-thread nested-trace runtime
//! guard. They publish through [`intrinsics_table`] like every other intrinsic
//! and resolve in all modes (REPL / `--run` / `--link`). The unrelated
//! `io_trace` ring buffer (IO observation) STAYS in int via the [`io_observer`]
//! callback contract; this crate keeps only the extension-point API.
//!
//! ## Consumed surface (the verified real set)
//!
//! Intrinsics imports only:
//! - **`cranelisp-types`** — `HeapHeader`, `NULLARY_TAG_THRESHOLD`, and the
//!   marshaling tags `TAG_SCONS` / `TAG_SEXP_INT` / `TAG_SEXP_STR` /
//!   `TAG_SEXP_SYM` / `TAG_SEXP_LIST` / `TAG_SEXP_BRACKET` (used by the Sexp
//!   drop walk). No types-crate trait implementations; no `FQTypeName`/`TypeName`
//!   at the surface.
//! - **`cranelisp-platform`** — the IO node tags `IO_TAG_PURE` / `IO_TAG_EFFECT`
//!   / `IO_TAG_BIND` / `IO_TAG_PAR` and `call_effect_thunk` for the IO
//!   trampoline's `Effect` dispatch. Effect dispatch is GOT-slot-mediated
//!   (Decision 26), **not** a Rust-path `HostContext` call — no `HostContext`,
//!   `Symbol`, `ErrorLocation`, `Span`, `CranelispError`, or `SchedulingClass`
//!   is imported.
//!
//! No re-exports of dependency-crate items (Principle 15).
//!
//! ## The published Import-catalog (`intrinsics_table()`, BC §4b invariant 11)
//!
//! [`intrinsics_table`] returns the published flat `name → (signature, ptr)`
//! catalog of this crate's backend-emitted-call targets — 16 core + the 12
//! `cranelisp_trace_*` family (S76 trace ruling) + `catch-runtime-error` (the
//! protected-call combinator). The authoritative entry count is the catalog's
//! own test constant ([`catalog`]'s `EXPECTED_NAMES` /
//! `name_set_is_exactly_the_expected_29`), not a literal restated here — cite
//! that single owner when the catalog grows. This is the
//! Decision-0048-for-intrinsics self-publication (the `PRIMITIVES_TABLE`
//! precedent applied to intrinsics). Each [`IntrinsicEntry`] carries the
//! emitted-call ABI `name`, the in-crate fn `ptr`, and the `(param_count,
//! has_return)` scalar signature — NO `cranelisp-types` type is named
//! (invariant 10; the value-passing C-ABI is uniformly `i64`-in /
//! `i64`-or-void-out, so arity + return-ness fully determine the Cranelift
//! signature).
//!
//! **Flat catalog, NOT a mounted GOT-module** (contrast
//! `cranelisp_primitives::PRIMITIVES_TABLE`): intrinsics are Import-dispatched
//! (invariant 9 / the §"`JITBuilder::symbol`" narrowing) — not a module, no
//! `SymbolTable`, no GOT slots. The table is consumed at **three resolution
//! points, never at codegen**: (a) JIT construct — `JITBuilder::symbol(name,
//! ptr)`; (b) cache-hit load — `Linker::register_symbol(name, ptr)`; (c)
//! `--link` — names resolved against this crate's archive. It is exposed as a
//! `pub fn` returning a `'static` slice (not a `pub static`) to sidestep the
//! `unsafe impl Sync` a raw-pointer-bearing static would need (S76 seam-3
//! ruling; Principle 6 — no `unsafe` where a fn suffices).
//!
//! Relation to the **retired** `cranelisp_backend::jit::intrinsic_symbols()`:
//! the data relocated here verbatim (same names/ptrs/arities/`is_runtime`);
//! backend becomes a *reader* of this catalog, not the owner. The §"Symbol
//! survival" / per-module `#[export_name]` ABI is UNCHANGED — the table
//! republishes the established names, it does not redefine them.
//!
//! ## Module inventory
//!
//! | Module | Role |
//! |---|---|
//! | [`catalog`]          | Published Import-catalog — `intrinsics_table()` + `IntrinsicEntry` (BC §4b inv 11) |
//! | [`alloc`]            | Heap allocator + RC header layout (Decision 11 base-pointer) |
//! | [`drop`](mod@drop)   | `consume_*` drop-glue helpers (Sexp/SList/Vec/IO/closure) |
//! | [`heap_string`]      | `HeapString` layout-ABI + alloc/read helpers (opaque to backend, Decision 12) |
//! | [`io`]               | `cranelisp_run_io` IO trampoline (Decision 29) |
//! | [`io_observer`]      | IO observation extension point — registration + `IoEvent`/`IoEventTag` + `trace_anchor` (Decision 40) |
//! | [`ivar`]             | IVar primitives for lenient evaluation (spec §12.4.3) + fork-join error-slot ferry |
//! | [`layout`]           | `cranelisp_check_layout_hash` — `--link` platform layout-hash gate (platform-interface.md §5.5.4) |
//! | [`panic`](mod@panic) | `runtime/panic` sentinel + `catch-runtime-error` combinator + error-slot mechanism |
//! | [`rc`]               | RC trace + underflow check + `consume_shallow` (Decision 13/24) |
//! | [`trace`]            | `(trace ...)` runtime — 12 `cranelisp_trace_*` bodies + `TRACE_STACK` + nested-trace guard + `DisplayDescriptor` (BC §4b inv 12) |
//! | [`vec_runtime`]      | Vec layout-ABI + COW ops + drop |

pub mod alloc;
pub mod catalog;
pub mod drop;
/// Single-source heap-cell `i64` read/write accessors over a base+offset (MED-1,
/// FIXME 0370). `pub(crate)` — an internal layout-access helper, not a public
/// surface item.
pub(crate) mod heap_access;
pub mod heap_string;
pub mod io;
/// Fault guard for the platform-Effect force site (FIXME 0327). `pub(crate)` —
/// not a public-surface item; the trampoline (`io`) is its only consumer.
pub(crate) mod io_guard;
pub mod io_observer;
pub mod ivar;
pub mod layout;
pub mod panic;
pub mod rc;
pub mod trace;
/// The pure `(trace ...)` value formatter — the `DisplayDescriptor` ABI + the
/// `cranelisp_trace_format` intrinsic. Split out of `trace` (HIGH-3, FIXME 0370);
/// its public types are re-exported under the `trace::` path for cross-crate
/// path stability.
pub mod trace_format;
pub mod vec_runtime;

// Strand identity + the trampoline observability event stream
// (effect-concurrency track — observability §11). UNCONDITIONAL under the
// single-trampoline cutover (`design/arch/platform-interface.md` §6.8.0a) — the
// feature gate is retired. **`pub(crate)`** (A4c #2): the whole strand surface
// (the `StrandId`/`StrandEvent` types + the recording sink) has **no cross-crate
// consumer** today — the dev-facing `/strand` dump (int `src/`) that will re-`pub`
// it is deferred (§3). Reached in-crate by `io`/`reactor`; downgrade until a
// consumer lands.
pub(crate) mod strand;

// The host reactor IMPLEMENTATION — the mio `HostCtx` reactor + the C-ABI waker +
// the `block_on` executor + the `EffectPoll` await boundary + the supervisor +
// the token/global admission pools + the hand-written demo leaves
// (`design/arch/effect-concurrency.md` App. B). UNCONDITIONAL under the
// single-trampoline cutover (§6.8.0a): the reactor IS the runtime, always linked.
// A pure-blocking program constructs no mio `Poll` at runtime (lazy init).
// **`pub(crate)`** (A4c #2): the entire reactor surface is host-internal — reached
// only through `io::cranelisp_run_io` / the trampoline, with no cross-crate Rust
// consumer (verified: zero `reactor::`/`EffectPoll`/`Reactor`/`join_io_leaves`
// path uses outside this crate).
pub(crate) mod reactor;

// Root re-exports — only the names with a verified root-form Rust consumer.
//
// Every per-module `pub fn`/`pub extern`/`pub const`/`pub mod` stays public on
// its module path (backend harvests every per-module extern by fn-ptr at
// `backend/jit.rs`; primitives/int/platform reach the rest by per-module path).
// These root aliases exist ONLY where a consumer reaches the bare-root form;
// the per-module path is the canonical reference for everything else (S74 W1
// narrowing — 17 unused root-duplicate re-exports removed; per-module surface
// unchanged).
pub use catalog::{intrinsics_table, IntrinsicEntry}; // backend Jit::new + int worker.rs cache-hit (S76 W1b readers)
pub use io_observer::{register_io_observer, trace_anchor}; // src/io_trace.rs, src/got_trace.rs
pub use alloc::{alloc_count, alloc_with_rc, bytes_current, dealloc_count, heap_alloc_payload}; // src/{session_v4,pipeline,platform}.rs
pub use io::run_io_trampoline; // src/{session_v4,pipeline}.rs

/// The canonical host-callbacks table handed to every platform manifest call.
///
/// This is the **single, divergence-proof construction site** for the
/// `HostCallbacks` a platform DLL receives — DEF-6 divergence-proofing. Every
/// mode (`--run`/REPL JIT via `src/platform.rs`, the `--link` startup stub in
/// `cranelisp-exe-bundle`, and the test mirror) calls this one builder, so the
/// `alloc` = payload-returning (`heap_alloc_payload`) vs base-returning
/// (`heap_alloc`) mismatch that corrupted the heap in DEF-6 cannot recur by
/// hand-mirroring three separate literals.
///
/// This is the lowest crate that can name both `cranelisp_platform::HostCallbacks`
/// (its dependency) and both intrinsic function pointers it owns
/// (`heap_alloc_payload`, `cranelisp_alloc_with_tag`) without inverting the crate
/// DAG (Principle 3) — see FIXME 0419 for the home ruling.
pub fn host_callbacks() -> cranelisp_platform::HostCallbacks {
    cranelisp_platform::HostCallbacks {
        // DEF-6 (Sprint 86): `HostCallbacks::alloc` MUST return a PAYLOAD pointer
        // (alloc base + HEAP_HEADER_SIZE). `heap_alloc` returns the BASE and wiring
        // it here clobbers the RC header one node per host↔DLL crossing.
        alloc: alloc::heap_alloc_payload,
        alloc_with_tag: alloc::cranelisp_alloc_with_tag,
    }
}

#[cfg(test)]
mod host_callbacks_tests {
    // spec: design/arch/fixmes/0419 — DEF-6 divergence-proofing. The one shared
    // builder MUST wire `alloc` to the PAYLOAD-returning `heap_alloc_payload`,
    // never the base-returning `heap_alloc`. Pinning the function-pointer identity
    // makes the builder divergence-proof by construction.
    #[test]
    fn host_callbacks_alloc_is_payload_returning() {
        let cb = super::host_callbacks();
        // Function-pointer identity: `alloc` is exactly `heap_alloc_payload`.
        assert_eq!(
            cb.alloc as *const () as usize,
            super::alloc::heap_alloc_payload as *const () as usize,
            "DEF-6: host_callbacks().alloc must be the payload-returning heap_alloc_payload"
        );
        // And it must NOT be the base-returning `heap_alloc` (the DEF-6 defect).
        assert_ne!(
            cb.alloc as *const () as usize,
            super::alloc::heap_alloc as *const () as usize,
            "DEF-6: host_callbacks().alloc must NOT be the base-returning heap_alloc"
        );
        assert_eq!(
            cb.alloc_with_tag as *const () as usize,
            super::alloc::cranelisp_alloc_with_tag as *const () as usize,
            "host_callbacks().alloc_with_tag must be the tagged-ADT intrinsic"
        );
    }
}
