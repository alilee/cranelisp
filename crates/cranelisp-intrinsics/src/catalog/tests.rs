use super::*;

/// The complete, expected name-set — the ABI contract. A name added or
/// dropped here without a corresponding extern is an unresolved-symbol
/// crash at JIT-finalize / `--link`, so the set is pinned explicitly.
const EXPECTED_NAMES: &[&str] = &[
    "runtime/alloc",
    "runtime/dealloc",
    "runtime/panic",
    "runtime/rc_underflow_check",
    "runtime/rc_dec_check",
    // S99 Wave 0.1 RC-op instrumentation tally helpers (env-gated via the
    // backend's `CRANELISP_RC_STATS` codegen gate; inert off). Added to the
    // table in S99 (`e63c4ca`); joined this expected set at S101 when the
    // crate lib tier entered the canonical run (default-members) and exposed
    // the stale 32-name pin.
    "runtime/rc_stat_inc",
    "runtime/rc_stat_dec",
    // Increment-II (§6.5 / §9.2) RC-stats tally helpers: reuse-hit/miss runtime
    // tallies on the COW arms + the `str-len` per-extern adaptation-pair tally.
    // Env-gated via the backend's `CRANELISP_RC_STATS` codegen gate; inert off.
    "runtime/reuse_hit",
    "runtime/reuse_miss",
    "runtime/extern_adapt_str_len",
    "runtime/alloc_string",
    "runtime/string_read",
    "runtime/vec_new",
    "runtime/vec_drop",
    "runtime/free_io_node",
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

/// Name-set completeness + uniqueness: the table contains exactly the
/// expected names — no more, no fewer — and no name repeats (BC §6
/// guardrail; positive + negative coverage).
#[test]
fn name_set_is_exactly_the_expected_names() {
    let names: Vec<&str> = intrinsics_table().iter().map(|e| e.name).collect();
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
    assert_eq!(
        sorted.len(),
        names.len(),
        "duplicate intrinsic name in table"
    );
}

/// Non-null ptrs: a mis-pathed fn reference would const-eval to a bad
/// address; assert every `ptr` is non-null.
#[test]
fn every_ptr_is_non_null() {
    for e in intrinsics_table() {
        assert!(!e.ptr.is_null(), "null ptr for intrinsic {}", e.name);
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
    // Pin the explicit false set — the user-visible-named backend targets.
    for name in ["vec-set-copy", "vec-push-copy", "vec-push-grow"] {
        let e = intrinsics_table().iter().find(|e| e.name == name).unwrap();
        assert!(!e.is_runtime, "{name} must be is_runtime: false");
    }
}

// spec: design/intrinsics/intrinsics-table.md §2.1 — the three rows whose
// hand copies disagreed with their functions carry the derived values (P-16).
#[test]
fn corrected_rows_carry_their_functions_signatures() {
    let row = |name: &str| {
        intrinsics_table()
            .iter()
            .find(|e| e.name == name)
            .unwrap_or_else(|| panic!("no entry for {name}"))
    };
    let panic = row("runtime/panic");
    assert_eq!(
        (panic.param_count, panic.has_return),
        (2, false),
        "runtime/panic never returns, so it declares no result"
    );
    let underflow = row("runtime/rc_underflow_check");
    assert_eq!((underflow.param_count, underflow.has_return), (2, true));
    let read = row("runtime/string_read");
    assert_eq!((read.param_count, read.has_return), (3, false));
}

// spec: design/intrinsics/intrinsics-table.md §2.2 — the poll-leaf row keeps
// the uniform-word declaration the backend's `sleep` lowering takes its
// address from.
#[test]
fn poll_leaf_row_declares_three_words_and_a_result() {
    let leaf = intrinsics_table()
        .iter()
        .find(|e| e.name == "runtime/sleep_pollfn")
        .expect("no entry for runtime/sleep_pollfn");
    assert_eq!((leaf.param_count, leaf.has_return), (3, true));
    assert!(leaf.is_runtime);
}

// ---------------------------------------------------------------------
// Detection proof for the derivation (P-16): each mismatched row must be
// refused by the compiler, and the matched control must compile. The cells
// compile `signature.rs` itself, as its own crate, with one planted row. The
// cell stands in for `IntrinsicEntry` and `cranelisp_platform::PollFn`; the
// real `runtime/sleep_pollfn` row compiling in this crate is the control
// against the real `PollFn`.
// ---------------------------------------------------------------------

/// Compile `signature.rs` with `row` in a promoted table; return rustc's stderr
/// on refusal, `None` on success.
fn compile_planted_row(label: &str, row: &str) -> Option<String> {
    let signature = concat!(env!("CARGO_MANIFEST_DIR"), "/src/catalog/signature.rs");
    let source = format!(
        r#"#![allow(dead_code, unused)]
mod catalog {{
    pub struct IntrinsicEntry {{
        pub name: &'static str,
        pub ptr: *const u8,
        pub param_count: usize,
        pub has_return: bool,
        pub is_runtime: bool,
    }}
    pub struct HostCtx;
    pub struct Waker;
    #[repr(i32)]
    pub enum Poll {{ Ready, Pending }}
    pub type PollFn = unsafe extern "C" fn(
        *mut std::ffi::c_void,
        *const HostCtx,
        *const Waker,
    ) -> Poll;
    #[path = "{signature}"]
    pub(crate) mod signature;
}}
use catalog::signature::{{catalog_row, poll_leaf_row}};
use catalog::{{HostCtx, Poll, Waker}};
use std::ffi::c_void;
extern "C" fn word(_: i64) -> i64 {{ 0 }}
extern "C" fn nothing(_: i64) {{}}
extern "C" fn narrow(_: bool) -> i64 {{ 0 }}
extern "C" fn half(_: i64) -> i32 {{ 0 }}
extern "C" fn diverge(_: i64) -> ! {{ loop {{}} }}
unsafe extern "C" fn leaf(_: *mut c_void, _: *const HostCtx, _: *const Waker) -> Poll {{
    Poll::Ready
}}
unsafe extern "C" fn wide_leaf(_: *mut c_void, _: *const HostCtx, _: *const Waker) -> i64 {{ 0 }}
pub fn rows() -> &'static [catalog::IntrinsicEntry] {{
    &[{row}]
}}
"#
    );
    let dir = std::env::temp_dir().join(format!(
        "intrinsics-catalog-cell-{}-{label}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).expect("cell dir");
    let file = dir.join("cell.rs");
    std::fs::write(&file, source).expect("write cell");
    let out = std::process::Command::new("rustc")
        .args([
            "--edition",
            "2024",
            "--crate-type",
            "lib",
            "--emit=metadata",
        ])
        .arg("--out-dir")
        .arg(&dir)
        .arg(&file)
        .output()
        .expect("run rustc");
    let _ = std::fs::remove_dir_all(&dir);
    (!out.status.success()).then(|| String::from_utf8_lossy(&out.stderr).into_owned())
}

#[track_caller]
fn assert_refused(label: &str, row: &str, code: &str) {
    let stderr = compile_planted_row(label, row)
        .unwrap_or_else(|| panic!("{label}: the mismatched row compiled: {row}"));
    // Every error must be the expected refusal, so a cell cannot pass on an
    // unrelated failure such as an unresolved import.
    let expected = format!("error[{code}]");
    let errors: Vec<&str> = stderr
        .lines()
        .filter(|l| l.starts_with("error") && !l.starts_with("error: aborting"))
        .collect();
    assert!(
        !errors.is_empty() && errors.iter().all(|l| l.starts_with(&expected)),
        "{label}: expected only {code}, got:\n{stderr}"
    );
}

// spec: design/intrinsics/intrinsics-table.md §2.1 — matched rows compile,
// including a diverging function declaring no result.
#[test]
fn derivation_accepts_matched_rows() {
    let rows = r#"
        catalog_row!("w", word, extern "C" fn(i64) -> i64, runtime: true),
        catalog_row!("n", nothing, extern "C" fn(i64), runtime: true),
        catalog_row!("d", diverge, extern "C" fn(i64) -> !, runtime: true),
    "#;
    if let Some(stderr) = compile_planted_row("control", rows) {
        panic!("the matched control must compile:\n{stderr}");
    }
}

// spec: design/intrinsics/intrinsics-table.md §2.1 — a row whose stated arity
// differs from its function does not compile.
#[test]
fn derivation_refuses_a_wrong_arity() {
    assert_refused(
        "arity",
        r#"catalog_row!("w", word, extern "C" fn(i64, i64) -> i64, runtime: true)"#,
        "E0605",
    );
}

// spec: design/intrinsics/intrinsics-table.md §2.1 — a row claiming a result
// its function does not return does not compile, for a void and a diverging
// function alike.
#[test]
fn derivation_refuses_a_wrong_return() {
    assert_refused(
        "void-return",
        r#"catalog_row!("n", nothing, extern "C" fn(i64) -> i64, runtime: true)"#,
        "E0605",
    );
    assert_refused(
        "diverging-return",
        r#"catalog_row!("d", diverge, extern "C" fn(i64) -> i64, runtime: true)"#,
        "E0605",
    );
}

// spec: design/intrinsics/intrinsics-table.md §2.1 — a parameter or result
// narrower than a 64-bit word does not compile.
#[test]
fn derivation_refuses_narrow_words() {
    assert_refused(
        "narrow-param",
        r#"catalog_row!("b", narrow, extern "C" fn(bool) -> i64, runtime: true)"#,
        "E0277",
    );
    assert_refused(
        "narrow-return",
        r#"catalog_row!("h", half, extern "C" fn(i64) -> i32, runtime: true)"#,
        "E0277",
    );
}

// spec: design/intrinsics/intrinsics-table.md §2.2 — the general derivation
// does not admit the 32-bit `Poll` return, so a poll leaf cannot be declared
// as a callable `i64`-returning target.
#[test]
fn derivation_refuses_a_poll_return() {
    assert_refused(
        "poll-return",
        r#"catalog_row!("p", leaf, catalog::PollFn, runtime: true)"#,
        "E0277",
    );
}

// spec: design/intrinsics/intrinsics-table.md §2.2 — the poll-leaf constructor
// accepts a function with exactly the trampoline's `PollFn` ABI.
#[test]
fn poll_leaf_constructor_accepts_a_poll_fn() {
    if let Some(stderr) = compile_planted_row("poll-leaf-control", r#"poll_leaf_row!("l", leaf)"#) {
        panic!("the matched poll leaf must compile:\n{stderr}");
    }
}

// spec: design/intrinsics/intrinsics-table.md §2.2 — the poll-leaf constructor
// refuses a function that is not a `PollFn`, including one with the right
// parameters and an `i64` result.
#[test]
fn poll_leaf_constructor_refuses_a_non_poll_fn() {
    assert_refused("poll-leaf-word", r#"poll_leaf_row!("w", word)"#, "E0605");
    assert_refused(
        "poll-leaf-wide",
        r#"poll_leaf_row!("x", wide_leaf)"#,
        "E0605",
    );
}
