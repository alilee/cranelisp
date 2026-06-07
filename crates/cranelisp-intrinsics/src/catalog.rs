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
//! invariant 12; `design/arch/tracing.md`). The table is 28 entries (15 core +
//! 12 trace + `catch-runtime-error`, the protected-call combinator,
//! `design/arch/test-discovery.md` §6). The catalog + its tests are the single
//! owner of the trace name-agreement contract (closing the prior no-owner gap).

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
/// Returns a `'static` slice of the 28 entries — 15 core (relocated verbatim
/// from the retired `cranelisp_backend::jit::intrinsic_symbols()`) plus the 12
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
mod tests {
    use super::*;

    /// The complete, expected name-set — the ABI contract. A name added or
    /// dropped here without a corresponding extern is an unresolved-symbol
    /// crash at JIT-finalize / `--link`, so the set is pinned explicitly.
    const EXPECTED_NAMES: &[&str] = &[
        "runtime/alloc",
        "runtime/dealloc",
        "runtime/panic",
        "catch-runtime-error",
        "runtime/rc_underflow_check",
        "runtime/alloc_string",
        "runtime/string_read",
        "runtime/vec_new",
        "runtime/vec_drop",
        "runtime/run_io",
        "cranelisp_ivar_create",
        "cranelisp_ivar_spark",
        "cranelisp_ivar_force",
        "vec-set-copy",
        "vec-push-copy",
        "vec-push-grow",
        // The `(trace ...)` runtime family (S76 trace ruling — BC §4b inv 12).
        "cranelisp_trace_enter",
        "cranelisp_trace_exit",
        "cranelisp_trace_swap_got",
        "cranelisp_trace_restore_got",
        "cranelisp_collect_trace",
        "cranelisp_trace_first_child_nanos",
        "cranelisp_trace_name",
        "cranelisp_trace_params",
        "cranelisp_trace_result",
        "cranelisp_trace_children",
        "cranelisp_trace_nanos",
        "cranelisp_trace_format",
    ];

    /// Name-set completeness + uniqueness: the table contains exactly the 27
    /// expected names — no more, no fewer — and no name repeats (BC §6
    /// guardrail; positive + negative coverage).
    #[test]
    fn name_set_is_exactly_the_expected_28() {
        let names: Vec<&str> = intrinsics_table().iter().map(|e| e.name).collect();
        assert_eq!(names.len(), 28, "table must hold exactly 28 entries");
        assert_eq!(names.len(), EXPECTED_NAMES.len());

        // Every expected name present (no drop).
        for want in EXPECTED_NAMES {
            assert!(names.contains(want), "missing intrinsic name: {want}");
        }
        // No unexpected name present (no accidental add).
        for got in &names {
            assert!(
                EXPECTED_NAMES.contains(got),
                "unexpected intrinsic name in table: {got}"
            );
        }
        // Uniqueness — each name registers once (no conditional/duplicate).
        let mut sorted = names.clone();
        sorted.sort_unstable();
        sorted.dedup();
        assert_eq!(sorted.len(), names.len(), "duplicate intrinsic name in table");
    }

    /// Non-null ptrs: a mis-pathed fn reference would const-eval to a bad
    /// address; assert every `ptr` is non-null.
    #[test]
    fn every_ptr_is_non_null() {
        for e in intrinsics_table() {
            assert!(!e.ptr.is_null(), "null ptr for intrinsic {}", e.name);
        }
    }

    /// Arity sanity: the `(param_count, has_return)` for each name matches the
    /// historical `declare_intrinsics_generic` expectation. A wrong arity is a
    /// JIT signature mismatch (silent miscompile / trap), so it is guarded.
    #[test]
    fn arity_matches_historical_signature() {
        // (name, param_count, has_return) — the verbatim backend set.
        let expected: &[(&str, usize, bool)] = &[
            ("runtime/alloc", 1, true),
            ("runtime/dealloc", 1, true),
            ("runtime/panic", 2, true),
            ("catch-runtime-error", 1, true),
            ("runtime/rc_underflow_check", 1, true),
            ("runtime/alloc_string", 2, true),
            ("runtime/string_read", 1, true),
            ("runtime/vec_new", 1, true),
            ("runtime/vec_drop", 2, false),
            ("runtime/run_io", 1, true),
            ("cranelisp_ivar_create", 1, true),
            ("cranelisp_ivar_spark", 1, true),
            ("cranelisp_ivar_force", 1, true),
            ("vec-set-copy", 4, true),
            ("vec-push-copy", 3, true),
            ("vec-push-grow", 2, true),
            // Trace family (FIXME 0254 / tracing.md §3.3).
            ("cranelisp_trace_enter", 4, false),
            ("cranelisp_trace_exit", 2, true),
            ("cranelisp_trace_swap_got", 4, true),
            ("cranelisp_trace_restore_got", 2, false),
            ("cranelisp_collect_trace", 0, true),
            ("cranelisp_trace_first_child_nanos", 1, true),
            ("cranelisp_trace_name", 1, true),
            ("cranelisp_trace_params", 1, true),
            ("cranelisp_trace_result", 1, true),
            ("cranelisp_trace_children", 1, true),
            ("cranelisp_trace_nanos", 1, true),
            ("cranelisp_trace_format", 2, true),
        ];
        for (name, params, ret) in expected {
            let e = intrinsics_table()
                .iter()
                .find(|e| e.name == *name)
                .unwrap_or_else(|| panic!("no entry for {name}"));
            assert_eq!(e.param_count, *params, "{name} param_count");
            assert_eq!(e.has_return, *ret, "{name} has_return");
        }
    }

    /// `is_runtime` classification: `runtime/`-prefixed names + the IVar and
    /// trace families are runtime infrastructure (true); the `vec-*-copy` /
    /// `vec-push-grow` COW targets are user-visible-named (false). Documents the
    /// classification's intent.
    #[test]
    fn is_runtime_classification() {
        for e in intrinsics_table() {
            let want = e.name.starts_with("runtime/")
                || e.name.starts_with("cranelisp_ivar_")
                || e.name.starts_with("cranelisp_trace_")
                || e.name == "cranelisp_collect_trace";
            assert_eq!(
                e.is_runtime, want,
                "{} is_runtime classification (runtime/ + ivar + trace are true; vec COW false)",
                e.name
            );
        }
        // Pin the explicit false set — the user-visible-named backend targets
        // plus the `catch-runtime-error` combinator (a language-level primitive).
        for name in ["vec-set-copy", "vec-push-copy", "vec-push-grow", "catch-runtime-error"] {
            let e = intrinsics_table().iter().find(|e| e.name == name).unwrap();
            assert!(!e.is_runtime, "{name} must be is_runtime: false");
        }
    }
}
