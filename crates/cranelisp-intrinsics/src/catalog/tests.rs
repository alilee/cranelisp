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
    "runtime/rc_dec_check",
    "runtime/alloc_string",
    "runtime/string_read",
    "runtime/vec_new",
    "runtime/vec_drop",
    "runtime/run_io",
    "runtime/sleep_pollfn",
    "cranelisp_ivar_create",
    "cranelisp_ivar_spark",
    "cranelisp_ivar_force",
    "cranelisp_ivar_dealloc",
    "cranelisp_spark_budget_try_reserve",
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

/// Name-set completeness + uniqueness: the table contains exactly the 32
/// expected names — no more, no fewer — and no name repeats (BC §6
/// guardrail; positive + negative coverage).
#[test]
fn name_set_is_exactly_the_expected_32() {
    let names: Vec<&str> = intrinsics_table().iter().map(|e| e.name).collect();
    assert_eq!(names.len(), 32, "table must hold exactly 32 entries");
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
        ("runtime/rc_dec_check", 1, true),
        ("runtime/alloc_string", 2, true),
        ("runtime/string_read", 1, true),
        ("runtime/vec_new", 1, true),
        ("runtime/vec_drop", 2, false),
        ("runtime/run_io", 1, true),
        ("runtime/sleep_pollfn", 3, true),
        ("cranelisp_ivar_create", 1, true),
        ("cranelisp_ivar_spark", 1, true),
        ("cranelisp_ivar_force", 1, true),
        ("cranelisp_ivar_dealloc", 1, true),
        ("cranelisp_spark_budget_try_reserve", 1, true),
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
            || e.name == "cranelisp_collect_trace"
            || e.name == "cranelisp_spark_budget_try_reserve";
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
