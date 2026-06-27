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
//! invariant 12; `design/arch/tracing.md`). The table is 30 entries (17 core +
//! 12 trace + `catch-runtime-error`, the protected-call combinator,
//! `design/arch/test-discovery.md` §6). The 17th core entry is
//! `cranelisp_spark_budget_try_reserve` (the create-gate reservation primitive,
//! lenient-eval.md §3.6.1, S92). The catalog + its tests are the single owner of
//! the trace name-agreement contract (closing the prior no-owner gap).

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
/// Returns a `'static` slice of the 30 entries — 17 core (relocated verbatim
/// from the retired `cranelisp_backend::jit::intrinsic_symbols()`, plus
/// `cranelisp_ivar_dealloc`, the IVar-aware drop path, and
/// `cranelisp_spark_budget_try_reserve`, the create-gate primitive) plus the 12
/// `cranelisp_trace_*` family (S76 trace ruling, BC §4b invariant 12) plus
/// `catch-runtime-error` (the protected-call combinator, test-discovery.md §6).
/// See this module's `//!` for the consumer contract, the ABI guardrail, and the
/// scope boundary.
pub fn intrinsics_table() -> &'static [IntrinsicEntry] {
    &[
        // Runtime infrastructure (internal, not user-callable).
        IntrinsicEntry { name: "runtime/alloc", ptr: crate::alloc::heap_alloc as *const u8, param_count: 1, has_return: true, is_runtime: true },
        IntrinsicEntry { name: "runtime/dealloc", ptr: crate::alloc::heap_dealloc as *const u8, param_count: 1, has_return: true, is_runtime: true },
        IntrinsicEntry { name: "runtime/panic", ptr: crate::panic::runtime_panic as *const u8, param_count: 2, has_return: true, is_runtime: true },
        // `catch-runtime-error` — the language-level protected-call combinator
        // (test-discovery.md §6). Self-contained intrinsic (calls the thunk,
        // reads/clears the slot, marshals a heap `Result`); works in ALL modes
        // incl. `--link`. User-visible name, so `is_runtime: false`.
        IntrinsicEntry { name: "catch-runtime-error", ptr: crate::panic::catch_runtime_error as *const u8, param_count: 1, has_return: true, is_runtime: false },
        IntrinsicEntry { name: "runtime/rc_underflow_check", ptr: crate::rc::rc_underflow_check as *const u8, param_count: 1, has_return: true, is_runtime: true },
        IntrinsicEntry { name: "runtime/alloc_string", ptr: crate::heap_string::heap_alloc_string as *const u8, param_count: 2, has_return: true, is_runtime: true },
        IntrinsicEntry { name: "runtime/string_read", ptr: crate::heap_string::string_read as *const u8, param_count: 1, has_return: true, is_runtime: true },
        IntrinsicEntry { name: "runtime/vec_new", ptr: crate::vec_runtime::vec_new as *const u8, param_count: 1, has_return: true, is_runtime: true },
        IntrinsicEntry { name: "runtime/vec_drop", ptr: crate::vec_runtime::vec_drop as *const u8, param_count: 2, has_return: false, is_runtime: true },
        IntrinsicEntry { name: "runtime/run_io", ptr: crate::io::cranelisp_run_io as *const u8, param_count: 1, has_return: true, is_runtime: true },
        // IVar intrinsics for lenient evaluation (spec §12.4.3).
        IntrinsicEntry { name: "cranelisp_ivar_create", ptr: crate::ivar::ivar_create as *const u8, param_count: 1, has_return: true, is_runtime: true },
        IntrinsicEntry { name: "cranelisp_ivar_spark", ptr: crate::ivar::ivar_spark as *const u8, param_count: 1, has_return: true, is_runtime: true },
        IntrinsicEntry { name: "cranelisp_ivar_force", ptr: crate::ivar::ivar_force as *const u8, param_count: 1, has_return: true, is_runtime: true },
        IntrinsicEntry { name: "cranelisp_ivar_dealloc", ptr: crate::ivar::ivar_dealloc as *const u8, param_count: 1, has_return: true, is_runtime: true },
        // The backend create-gate's reservation primitive (lenient-eval.md §3.6.1,
        // S92). Emitted at each spark site BEFORE any IVar/thunk allocation:
        // returns 1 (granted ⇒ lenient arm) or 0 (over budget ⇒ direct arm).
        IntrinsicEntry { name: "cranelisp_spark_budget_try_reserve", ptr: crate::ivar::spark_budget_try_reserve as *const u8, param_count: 1, has_return: true, is_runtime: true },
        // Vec COW backend-emitted-call targets (internal, not user-callable via
        // the primitives module — `vec-len` is user-callable and rides the GOT
        // via PRIMITIVES_TABLE, not this catalog).
        IntrinsicEntry { name: "vec-set-copy", ptr: crate::vec_runtime::vec_set_copy as *const u8, param_count: 4, has_return: true, is_runtime: false },
        IntrinsicEntry { name: "vec-push-copy", ptr: crate::vec_runtime::vec_push_copy as *const u8, param_count: 3, has_return: true, is_runtime: false },
        IntrinsicEntry { name: "vec-push-grow", ptr: crate::vec_runtime::vec_push_grow as *const u8, param_count: 2, has_return: true, is_runtime: false },
        // The `(trace ...)` runtime family (S76 trace ruling 2026-06-04 — BC §4b
        // invariant 12; `design/arch/tracing.md`). Backend emits these as
        // `Linkage::Import`; this catalog single-sources the name-agreement
        // contract. `cranelisp_trace_format` is the pure descriptor-driven
        // formatter (arity `(2, true)` — unchanged from the prior int shim).
        IntrinsicEntry { name: "cranelisp_trace_enter", ptr: crate::trace::cranelisp_trace_enter as *const u8, param_count: 4, has_return: false, is_runtime: true },
        IntrinsicEntry { name: "cranelisp_trace_exit", ptr: crate::trace::cranelisp_trace_exit as *const u8, param_count: 2, has_return: true, is_runtime: true },
        IntrinsicEntry { name: "cranelisp_trace_swap_got", ptr: crate::trace::cranelisp_trace_swap_got as *const u8, param_count: 4, has_return: true, is_runtime: true },
        IntrinsicEntry { name: "cranelisp_trace_restore_got", ptr: crate::trace::cranelisp_trace_restore_got as *const u8, param_count: 2, has_return: false, is_runtime: true },
        IntrinsicEntry { name: "cranelisp_collect_trace", ptr: crate::trace::cranelisp_collect_trace as *const u8, param_count: 0, has_return: true, is_runtime: true },
        IntrinsicEntry { name: "cranelisp_trace_first_child_nanos", ptr: crate::trace::cranelisp_trace_first_child_nanos as *const u8, param_count: 1, has_return: true, is_runtime: true },
        IntrinsicEntry { name: "cranelisp_trace_name", ptr: crate::trace::cranelisp_trace_name as *const u8, param_count: 1, has_return: true, is_runtime: true },
        IntrinsicEntry { name: "cranelisp_trace_params", ptr: crate::trace::cranelisp_trace_params as *const u8, param_count: 1, has_return: true, is_runtime: true },
        IntrinsicEntry { name: "cranelisp_trace_result", ptr: crate::trace::cranelisp_trace_result as *const u8, param_count: 1, has_return: true, is_runtime: true },
        IntrinsicEntry { name: "cranelisp_trace_children", ptr: crate::trace::cranelisp_trace_children as *const u8, param_count: 1, has_return: true, is_runtime: true },
        IntrinsicEntry { name: "cranelisp_trace_nanos", ptr: crate::trace::cranelisp_trace_nanos as *const u8, param_count: 1, has_return: true, is_runtime: true },
        IntrinsicEntry { name: "cranelisp_trace_format", ptr: crate::trace::cranelisp_trace_format as *const u8, param_count: 2, has_return: true, is_runtime: true },
    ]
}

#[cfg(test)]
mod tests;
