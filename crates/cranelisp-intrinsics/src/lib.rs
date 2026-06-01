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
//! `discover-tests`, `run-test`, and `cranelisp_trace_format` physically live in
//! `src/` (int), registered unconditionally — see `src/CLAUDE.md`
//! §"Int-owned JIT intrinsics". They are NOT in this crate. The `(trace ...)`
//! machinery (12 `cranelisp_trace_*` fns, the GOT-swap stack, the io_trace ring
//! buffer + dump + panic-hook, and the `consume_trace_call` ADT walker) relocated
//! to int's `src/trace.rs` + `src/io_trace.rs` at S67 Wave 4 (Decision 40, Path
//! B1). The surviving observation surface here is the [`io_observer`]
//! extension-point API.
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
//! ## Module inventory
//!
//! | Module | Role |
//! |---|---|
//! | [`alloc`]            | Heap allocator + RC header layout (Decision 11 base-pointer) |
//! | [`drop`](mod@drop)   | `consume_*` drop-glue helpers (Sexp/SList/Vec/IO/closure) |
//! | [`heap_string`]      | `HeapString` layout-ABI + alloc/read helpers (opaque to backend, Decision 12) |
//! | [`io`]               | `cranelisp_run_io` IO trampoline (Decision 29) |
//! | [`io_observer`]      | IO observation extension point — registration + `IoEvent`/`IoEventTag` + `trace_anchor` (Decision 40) |
//! | [`ivar`]             | IVar primitives for lenient evaluation (spec §12.4.3) |
//! | [`panic`](mod@panic) | `runtime/panic` sentinel for match-exhaustiveness failures |
//! | [`rc`]               | RC trace + underflow check + `consume_shallow` (Decision 13/24) |
//! | [`vec_runtime`]      | Vec layout-ABI + COW ops + drop |

pub mod alloc;
pub mod drop;
pub mod heap_string;
pub mod io;
pub mod io_observer;
pub mod ivar;
pub mod panic;
pub mod rc;
pub mod vec_runtime;

// Root re-exports — only the names with a verified root-form Rust consumer.
//
// Every per-module `pub fn`/`pub extern`/`pub const`/`pub mod` stays public on
// its module path (backend harvests every per-module extern by fn-ptr at
// `backend/jit.rs`; primitives/int/platform reach the rest by per-module path).
// These root aliases exist ONLY where a consumer reaches the bare-root form;
// the per-module path is the canonical reference for everything else (S74 W1
// narrowing — 17 unused root-duplicate re-exports removed; per-module surface
// unchanged).
pub use io_observer::{register_io_observer, trace_anchor}; // src/io_trace.rs, src/got_trace.rs
pub use alloc::{alloc_count, alloc_with_rc, bytes_current, dealloc_count, heap_alloc_payload}; // src/{session_v4,pipeline,platform}.rs
pub use io::run_io_trampoline; // src/{session_v4,pipeline}.rs
