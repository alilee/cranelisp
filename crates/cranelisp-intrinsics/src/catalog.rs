//! The published flat Import-catalog of this crate's backend-emitted-call
//! targets — `intrinsics_table()` + [`IntrinsicEntry`].
//!
//! BC §4b invariant 11 (Decision-0048-for-intrinsics): intrinsics self-publishes
//! its catalog, a flat `name → (signature, ptr)` table of the backend-emitted-call
//! targets this crate owns. The data previously lived in
//! `cranelisp_backend::jit::intrinsic_symbols()` (enumerated by Rust path inside
//! backend); it relocates here verbatim — same names, same fn pointers, same
//! `(param_count, has_return)` arities, same `is_runtime` classification — with
//! the `ptr` expressions now naming in-crate Rust paths. Backend becomes a reader
//! of this table, not the owner (S76 W1b switches its readers).
//!
//! # `signature` is `(param_count, has_return)`, not a `cranelisp-types` type
//!
//! The BC's `(signature, ptr)` "signature" half is the `(param_count, has_return)`
//! scalar pair, NOT a `Type`/`Scheme`. Invariant 10 forbids `FQTypeName`/`TypeName`
//! at this surface, and the value-passing C-ABI is uniformly `i64`-in /
//! `i64`-or-void-out — so arity + return-ness fully determine the Cranelift
//! signature `declare_intrinsics_generic` builds. No `cranelisp-types` type is
//! named here (minimum mechanism, Principle 6 / narrow interface, Principle 2).
//!
//! Each row derives the pair from its function's pointer type (`signature`),
//! so a row cannot disagree with its function and still compile.
//!
//! # `pub fn` not `pub static` (S76 seam-3 ruling)
//!
//! Exposed as `intrinsics_table() -> &'static [IntrinsicEntry]`, not a bare
//! `pub static`. `IntrinsicEntry` holds a `*const u8` (`!Sync`), so a `pub static`
//! of `&[IntrinsicEntry]` would not auto-derive `Sync` and would require an
//! `unsafe impl Sync` newtype wrapper. The fn form hands out a per-call shared
//! `&'static` borrow of the slice literal — no shared static of a `!Sync` type
//! exists — sidestepping the `unsafe impl` entirely (Principle 6, no `unsafe`
//! where a fn suffices) and matching today's `intrinsic_symbols() -> Vec<…>`
//! reader shape.
//!
//! # ABI guardrail (BC §6)
//!
//! Each entry's `name` is the emitted-call ABI string — the per-module extern's
//! `#[export_name]` / `#[no_mangle]` linker symbol. This table *republishes* those
//! established names; it does NOT touch the per-module attributes or `pub` paths
//! and does NOT redefine the ABI. Three things MUST agree per name: the extern's
//! export name, this table's `name`, and the name backend emits the `Import`
//! against. A typo in a `name` is an unresolved-symbol crash at JIT-finalize or
//! `--link`, not a compile error — see the unit tests below (the durable guard).
//!
//! # Three resolution points, never codegen
//!
//! The table is consumed at three points (BC §4b invariant 11): (a) JIT construct
//! — `JITBuilder::symbol(name, ptr)` at `Jit::new(symbol_tables)` setup; (b)
//! cache-hit load — `Linker::register_symbol(name, ptr)`; (c) `--link` — names
//! resolved against the `cranelisp-intrinsics` archive (no code reads the table
//! here; the name agreement is the contract). All three register *every* entry
//! unconditionally (no conditional registration — crate-root `//!` forbidden
//! pattern 1). NEVER consumed at codegen.
//!
//! # Asymmetry vs `PRIMITIVES_TABLE`
//!
//! `cranelisp_primitives::PRIMITIVES_TABLE` is a `SymbolTable` + `Arc<GotTable>`
//! mounted into the session (primitives ride the GOT-indirect path). This catalog
//! is a flat slice, Import-dispatched, never mounted, never GOT-slotted — because
//! intrinsics are not a module (invariant 9).
//!
//! # Scope — what is NOT here
//!
//! The two int-owned **test** intrinsics (`discover-tests`, `run-test`) and the
//! GOT-dispatched primitives (`add-i64`, `str-concat`, `vec-len`, …) are
//! deliberately absent. This catalog is the `cranelisp-intrinsics` crate's
//! contribution only, not the complete JIT symbol universe — int concatenates
//! its own test intrinsics at JIT setup.
//!
//! # Trace family present (S76 trace ruling 2026-06-04)
//!
//! The 12 `cranelisp_trace_*` entries (incl. the pure descriptor-driven
//! `cranelisp_trace_format`) ARE in this catalog — the 2026-06-04 user ruling
//! retracted D40's trace-relocation-to-int and hosts the bodies here (BC §4b
//! invariant 12; `design/arch/tracing.md`). The table holds the core entries
//! (incl. `cranelisp_spark_budget_try_reserve`,
//! the create-gate reservation primitive, lenient-eval.md §3.6.1, S92; the
//! 2 S99 `runtime/rc_stat_{inc,dec}` measurement tally helpers; and the 3
//! increment-II `runtime/{reuse_hit,reuse_miss,extern_adapt_str_len}` tally
//! helpers, §6.5/§9.2; and `runtime/free_io_node`, the post-dec IO teardown
//! tail) + the 12 `cranelisp_trace_*` family. The exact name set, and so the
//! entry count, is owned by this module's test list `EXPECTED_NAMES`, pinned by
//! `name_set_is_exactly_the_expected_names`; it is not restated here. The
//! catalog + its tests are the single owner of the trace name-agreement
//! contract (closing the prior no-owner gap).

mod signature;
use cranelisp_platform::PollFn;
use signature::{catalog_row, poll_leaf_row};

/// One backend-emitted-call target in the published intrinsics catalog.
///
/// The `signature` half of BC §4b invariant 11's `name → (signature, ptr)` is
/// the `(param_count, has_return)` pair — every intrinsic param and return is
/// `i64` at the ABI (heap pointers cross as integers, invariant 10 / the
/// value-passing C-ABI), so the Cranelift signature is fully determined by the
/// arity + return-ness. No `cranelisp-types` type is named (invariant 10).
pub struct IntrinsicEntry {
    /// Emitted-call ABI string (the `#[export_name]` / `#[no_mangle]` linker
    /// symbol the backend emits `Linkage::Import` against). LOAD-BEARING — this
    /// MUST equal the per-module extern's export name (BC §6 guardrail).
    pub name: &'static str,
    /// Function pointer to the Rust implementation in this crate.
    pub ptr: *const u8,
    /// Count of `i64` parameters (Cranelift signature param loop).
    pub param_count: usize,
    /// Whether the fn returns an `i64` (false = void).
    pub has_return: bool,
    /// `runtime/`-prefixed infrastructure (true) vs user-visible-named
    /// backend-emitted target (false). Classificatory metadata only — no
    /// dispatch consumer today; retained because the catalog design needs the
    /// runtime-vs-primitive split it encodes (BC §4b invariant 11).
    pub is_runtime: bool,
}

/// The published flat Import-catalog of this crate's backend-emitted-call
/// targets (BC §4b invariant 11 — Decision-0048-for-intrinsics).
///
/// Returns a `'static` slice of the core entries (the set relocated
/// from the retired `cranelisp_backend::jit::intrinsic_symbols()`, plus
/// `cranelisp_ivar_dealloc`, the IVar-aware drop path;
/// `cranelisp_spark_budget_try_reserve`, the create-gate primitive;
/// the 2 S99 `runtime/rc_stat_{inc,dec}` tally helpers; and the 3 increment-II
/// `runtime/{reuse_hit,reuse_miss,extern_adapt_str_len}` tally helpers,
/// §6.5/§9.2) plus the 12
/// `cranelisp_trace_*` family (S76 trace ruling, BC §4b invariant 12). The
/// exact name set and entry count are the module tests' `EXPECTED_NAMES`, not
/// restated here. See this module's `//!` for the consumer contract, the ABI
/// guardrail, and the scope boundary.
pub fn intrinsics_table() -> &'static [IntrinsicEntry] {
    &[
        // Runtime infrastructure (internal, not user-callable).
        catalog_row!(
            "runtime/alloc",
            crate::alloc::heap_alloc,
            extern "C" fn(i64) -> i64,
            runtime: true
        ),
        catalog_row!(
            "runtime/dealloc",
            crate::alloc::heap_dealloc,
            extern "C" fn(i64) -> i64,
            runtime: true
        ),
        catalog_row!(
            "runtime/panic",
            crate::panic::runtime_panic,
            extern "C" fn(*const u8, usize) -> !,
            runtime: true
        ),
        catalog_row!(
            "runtime/rc_underflow_check",
            crate::rc::rc_underflow_check,
            extern "C-unwind" fn(i64, i64) -> i64,
            runtime: true
        ),
        // Emitted before each inline dec only under the codegen-time
        // `CRANELISP_RC_DEC_CHECK` gate; registered unconditionally so the symbol
        // resolves when the gate is on (FIXME 0494).
        catalog_row!(
            "runtime/rc_dec_check",
            crate::rc::rc_dec_check,
            extern "C" fn(i64) -> i64,
            runtime: true
        ),
        // RC-stats tally helpers, emitted only under the backend's codegen-time
        // `CRANELISP_RC_STATS` gate (inert off); registered unconditionally.
        catalog_row!(
            "runtime/rc_stat_inc",
            crate::rc::rc_stat_inc,
            extern "C" fn() -> i64,
            runtime: true
        ),
        catalog_row!(
            "runtime/rc_stat_dec",
            crate::rc::rc_stat_dec,
            extern "C" fn() -> i64,
            runtime: true
        ),
        catalog_row!(
            "runtime/reuse_hit",
            crate::rc::reuse_hit_stat,
            extern "C" fn() -> i64,
            runtime: true
        ),
        catalog_row!(
            "runtime/reuse_miss",
            crate::rc::reuse_miss_stat,
            extern "C" fn() -> i64,
            runtime: true
        ),
        catalog_row!(
            "runtime/extern_adapt_str_len",
            crate::rc::extern_adapt_str_len_stat,
            extern "C" fn() -> i64,
            runtime: true
        ),
        catalog_row!(
            "runtime/alloc_string",
            crate::heap_string::heap_alloc_string,
            extern "C" fn(*const u8, i64) -> i64,
            runtime: true
        ),
        catalog_row!(
            "runtime/string_read",
            crate::heap_string::string_read,
            extern "C" fn(i64, *mut *const u8, *mut i64),
            runtime: true
        ),
        catalog_row!(
            "runtime/vec_new",
            crate::vec_runtime::vec_new,
            extern "C" fn(i64) -> i64,
            runtime: true
        ),
        catalog_row!(
            "runtime/vec_drop",
            crate::vec_runtime::vec_drop,
            extern "C" fn(i64, i64),
            runtime: true
        ),
        catalog_row!(
            "runtime/free_io_node",
            crate::drop::free_io_node,
            extern "C" fn(i64),
            runtime: true
        ),
        catalog_row!(
            "runtime/run_io",
            crate::io::cranelisp_run_io,
            extern "C" fn(i64) -> i64,
            runtime: true
        ),
        // `sleep`'s timer poll-fn: an address-only row whose pointer the backend
        // bakes as a poll-node `code_ptr` (`intrinsics-table.md` §2.2).
        poll_leaf_row!("runtime/sleep_pollfn", crate::reactor::sleep_pollfn),
        // IVar intrinsics for lenient evaluation (spec §12.4.3).
        catalog_row!(
            "cranelisp_ivar_create",
            crate::ivar::ivar_create,
            extern "C" fn(i64) -> i64,
            runtime: true
        ),
        catalog_row!(
            "cranelisp_ivar_spark",
            crate::ivar::ivar_spark,
            extern "C" fn(i64) -> i64,
            runtime: true
        ),
        catalog_row!(
            "cranelisp_ivar_force",
            crate::ivar::ivar_force,
            extern "C" fn(i64) -> i64,
            runtime: true
        ),
        catalog_row!(
            "cranelisp_ivar_dealloc",
            crate::ivar::ivar_dealloc,
            extern "C" fn(i64) -> i64,
            runtime: true
        ),
        // The backend create-gate's reservation primitive (lenient-eval.md §3.6.1):
        // returns 1 (granted) or 0 (over budget).
        catalog_row!(
            "cranelisp_spark_budget_try_reserve",
            crate::ivar::spark_budget_try_reserve,
            extern "C" fn(i64) -> i64,
            runtime: true
        ),
        // Vec COW targets the backend emits; not user-callable.
        catalog_row!(
            "vec-set-copy",
            crate::vec_runtime::vec_set_copy,
            extern "C" fn(i64, i64, i64, i64) -> i64,
            runtime: false
        ),
        catalog_row!(
            "vec-push-copy",
            crate::vec_runtime::vec_push_copy,
            extern "C" fn(i64, i64, i64) -> i64,
            runtime: false
        ),
        catalog_row!(
            "vec-push-grow",
            crate::vec_runtime::vec_push_grow,
            extern "C" fn(i64, i64) -> i64,
            runtime: false
        ),
        // The `(trace ...)` runtime family (BC §4b invariant 12; `design/arch/tracing.md`).
        catalog_row!(
            "cranelisp_trace_enter",
            crate::trace::cranelisp_trace_enter,
            extern "C" fn(i64, i64, i64, i64),
            runtime: true
        ),
        catalog_row!(
            "cranelisp_trace_exit",
            crate::trace::cranelisp_trace_exit,
            extern "C" fn(i64, i64) -> i64,
            runtime: true
        ),
        catalog_row!(
            "cranelisp_trace_swap_got",
            crate::trace::cranelisp_trace_swap_got,
            extern "C" fn(i64, i64, i64, i64) -> i64,
            runtime: true
        ),
        catalog_row!(
            "cranelisp_trace_restore_got",
            crate::trace::cranelisp_trace_restore_got,
            extern "C" fn(i64, i64),
            runtime: true
        ),
        catalog_row!(
            "cranelisp_collect_trace",
            crate::trace::cranelisp_collect_trace,
            extern "C" fn() -> i64,
            runtime: true
        ),
        catalog_row!(
            "cranelisp_trace_first_child_nanos",
            crate::trace::cranelisp_trace_first_child_nanos,
            extern "C" fn(i64) -> i64,
            runtime: true
        ),
        catalog_row!(
            "cranelisp_trace_name",
            crate::trace::cranelisp_trace_name,
            extern "C" fn(i64) -> i64,
            runtime: true
        ),
        catalog_row!(
            "cranelisp_trace_params",
            crate::trace::cranelisp_trace_params,
            extern "C" fn(i64) -> i64,
            runtime: true
        ),
        catalog_row!(
            "cranelisp_trace_result",
            crate::trace::cranelisp_trace_result,
            extern "C" fn(i64) -> i64,
            runtime: true
        ),
        catalog_row!(
            "cranelisp_trace_children",
            crate::trace::cranelisp_trace_children,
            extern "C" fn(i64) -> i64,
            runtime: true
        ),
        catalog_row!(
            "cranelisp_trace_nanos",
            crate::trace::cranelisp_trace_nanos,
            extern "C" fn(i64) -> i64,
            runtime: true
        ),
        catalog_row!(
            "cranelisp_trace_format",
            crate::trace::cranelisp_trace_format,
            extern "C" fn(i64, i64) -> i64,
            runtime: true
        ),
    ]
}

#[cfg(test)]
mod tests;
