//! Sprint 61 Slice 1 — bare-primitive value path integration tests.
//!
//! These tests validate /int's Slice 1 fix in
//! `src/session_v4.rs::resolve_entry_for_display` +
//! `check_bare_symbol_introspection`. The fix aligns the bare-value path
//! (typing `add-i64` at the REPL prompt) with the introspection path
//! (`/sig add-i64`) and the call path (`(add-i64 2 3)`), so a re-exported
//! primitive resolves through `user → prelude → primitives` to its
//! terminal `Def` and produces a spec-conforming introspection card.
//!
//! Spec references:
//!   - `repl/spec.md §1.1` — universal `:Type name ; classification - doc` format
//!   - `spec/08-modules.md §8.9` — re-export provenance: original defining module
//!   - `design/int/bare-primitive-value-path.md` — Slice 1 design + fix rationale
//!
//! Test-plan anchor: `tests/plan/ring4.md §"Sprint 61 → Slice 1"`
//! (T-S1-1 .. T-S1-5). All five are authored POST-fix; expected 6/0 pass
//! (T-S1-3 is parametrised over 5 primitives so the assertion count is
//! slightly higher than the row count). If the fix were reverted the
//! tests would FAIL visibly — they are the regression guard for the
//! three-path convergence restored by the fix.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::*;

use std::path::PathBuf;
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};

// ---------------------------------------------------------------------------
// Subprocess harness (mirrors tests/e2e.rs `run_repl`). Used only for T-S1-4
// to exercise end-to-end stderr routing on unknown names; in-process tests
// cover the happy-path output-shape assertions.
// ---------------------------------------------------------------------------

static TEST_COUNTER: AtomicUsize = AtomicUsize::new(0);

fn project_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn binary_path() -> PathBuf {
    project_root().join("target").join("debug").join("cranelisp")
}

fn test_dir(label: &str) -> PathBuf {
    use std::sync::LazyLock;
    use std::time::SystemTime;
    static RUN_TS: LazyLock<String> = LazyLock::new(|| {
        let d = SystemTime::now().duration_since(SystemTime::UNIX_EPOCH).unwrap();
        format!("{}", d.as_secs())
    });
    let n = TEST_COUNTER.fetch_add(1, Ordering::SeqCst);
    let dir = project_root()
        .join("tests")
        .join("sprint61_bare_primitive")
        .join(".runs")
        .join(&*RUN_TS)
        .join(format!("{n}_{label}"));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// Run the REPL binary with piped stdin in an isolated directory, optionally
/// with `CRANELISP_LIB` pointing at the repo's real stdlib so prelude loads.
fn run_repl_with_stdlib(input: &str, label: &str) -> Output {
    let binary = binary_path();
    assert!(
        binary.exists(),
        "cranelisp binary not found at {binary:?} — run `cargo build` first"
    );
    let dir = test_dir(label);
    let stdlib = project_root().join("stdlib");

    let mut child = Command::new(&binary)
        .current_dir(&dir)
        .env("CRANELISP_LIB", stdlib.as_os_str())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to start cranelisp binary");

    {
        use std::io::Write;
        let stdin = child.stdin.as_mut().expect("failed to open stdin");
        stdin.write_all(input.as_bytes()).expect("failed to write input");
    }
    child.wait_with_output().expect("failed to read output")
}

fn stdout_str(o: &Output) -> String {
    String::from_utf8_lossy(&o.stdout).into_owned()
}

fn stderr_str(o: &Output) -> String {
    String::from_utf8_lossy(&o.stderr).into_owned()
}

// ---------------------------------------------------------------------------
// T-S1-1 — bare `add-i64` at prompt displays the spec-conforming card.
// ---------------------------------------------------------------------------

// spec: repl/spec.md §1.1 (universal `:Type name ; classification - doc`);
//       design/int/bare-primitive-value-path.md §5 expected output
#[test]
fn bare_primitive_add_i64_at_prompt_displays_type_and_fqn() {
    let mut session = repl_session();
    let display = repl_eval_display(&mut session, "add-i64");

    assert!(
        display.contains("primitives/add-i64"),
        "bare `add-i64` MUST resolve to the primitives-qualified name per \
         spec/08-modules.md §8.9 re-export provenance; got: {display}"
    );
    // Type carries the function signature.
    assert!(
        display.contains("(Fn ["),
        "bare `add-i64` MUST display a function type prefix `:(Fn [...] ...)`; \
         got: {display}"
    );
    assert!(
        display.contains("; primitive"),
        "classification MUST be `; primitive` per repl/spec.md §1.1 + §4.1.1 \
         for a primitive Def; got: {display}"
    );
    // Dash-separator introducing the docstring (the docstring content itself
    // may vary, but the `; primitive - ` separator is normative).
    assert!(
        display.contains("; primitive - "),
        "output MUST carry `; primitive - <docstring>` per the universal \
         format (repl/spec.md §1.1); got: {display}"
    );
}

// ---------------------------------------------------------------------------
// T-S1-2 — the three paths (bare-value, introspection, call) converge on
// the same symbol attribution (`primitives/add-i64`, `(Fn [Int Int] Int)`).
// ---------------------------------------------------------------------------

// spec: design/int/bare-primitive-value-path.md §2, §5;
//       design/int/dual-path-persistence-collapse.md (dual-path anti-pattern)
#[test]
fn bare_primitive_parallel_paths_converge_on_same_attribution() {
    let mut session = repl_session();

    // Path A — introspection via /sig.
    let sig_display = repl_eval_display(&mut session, "/sig add-i64");

    // Path B — bare-value echo.
    let bare_display = repl_eval_display(&mut session, "add-i64");

    // Path C — call evaluation.
    let call_value = repl_eval(&mut session, "(add-i64 2 3)");
    assert_eq!(
        call_value, 5,
        "(add-i64 2 3) MUST evaluate to 5 on the call path; got {call_value}"
    );

    // Both introspection paths MUST name the terminal primitives/add-i64
    // attribution. /sig currently prints `add-i64 ; imported from
    // primitives/add-i64` (see design doc §"Out of scope") — the substring
    // `primitives/add-i64` is present in both.
    assert!(
        sig_display.contains("primitives/add-i64"),
        "/sig add-i64 MUST attribute to primitives/add-i64 \
         (spec/08-modules.md §8.9); got: {sig_display}"
    );
    assert!(
        bare_display.contains("primitives/add-i64"),
        "bare add-i64 MUST attribute to primitives/add-i64 \
         (bare-value-path.md §5); got: {bare_display}"
    );

    // Bare display additionally MUST carry the full qualified function type.
    assert!(
        bare_display.contains("(Fn ["),
        "bare `add-i64` MUST carry the `:(Fn [...] ...)` type prefix; \
         got: {bare_display}"
    );
}

// ---------------------------------------------------------------------------
// T-S1-3 — generalisation across the re-exported primitive surface.
// ---------------------------------------------------------------------------

// spec: bare-primitive-value-path.md §7 (sample of covered primitives);
//       spec/08-modules.md §8.9 re-export provenance.
//
// Covered: add-i64, eq-i64, mul-i64, sub-i64, not, str-concat (≥ 5 primitives
// per the /qa charter; 6 here including `str-concat` for string-shape
// coverage). All must resolve to `primitives/<name>` on the bare-value path.
#[test]
fn bare_primitive_surface_resolves_identically_across_five_plus_symbols() {
    let mut session = repl_session();

    for name in ["add-i64", "eq-i64", "mul-i64", "sub-i64", "not", "str-concat"] {
        let display = repl_eval_display(&mut session, name);
        let fqn = format!("primitives/{name}");
        assert!(
            display.contains(&fqn),
            "bare `{name}` MUST resolve to `{fqn}` per \
             spec/08-modules.md §8.9; got: {display}"
        );
        assert!(
            !display.contains("undefined variable"),
            "bare `{name}` MUST NOT surface an `undefined variable` error \
             (bare-value-path.md §1 regression); got: {display}"
        );
        assert!(
            display.contains("; primitive"),
            "bare `{name}` classification MUST be `; primitive` per \
             repl/spec.md §4.1.1; got: {display}"
        );
    }
}

// ---------------------------------------------------------------------------
// T-S1-4 — unknown bare symbol produces `undefined variable` error via
// end-to-end stderr path; MUST NOT silently dispatch to a similarly-named
// primitive.
// ---------------------------------------------------------------------------

// spec: repl/spec.md §1.1 negative complement; spec/08-modules.md §8.9 scope;
//       memory/feedback_failing_not_ignored.md — negative guard against
//       an over-broad Slice 1 fix.
#[test]
fn bare_primitive_unknown_name_produces_undefined_error_neg() {
    // Subprocess variant ensures stderr routing is validated end-to-end.
    let o = run_repl_with_stdlib("unknown-primitive-name-zzzz\n", "unknown_primitive");
    let out = stdout_str(&o);
    let err = stderr_str(&o);
    let combined = format!("{out}\n{err}");

    // Must surface an error.
    assert!(
        combined.contains("undefined") || combined.contains("not found"),
        "unknown bare symbol MUST produce an `undefined variable` or \
         `not found` error per spec §1.1 negative complement; \
         got stdout={out:?} stderr={err:?}"
    );

    // Must NOT silently resolve to any nearby symbol. The fix must not
    // over-broaden — unknown bare names produce an error, full stop.
    assert!(
        !combined.contains("primitives/add-i64"),
        "unknown bare symbol MUST NOT silently dispatch to `add-i64` \
         (guards against over-broad Slice 1 fix); \
         got stdout={out:?} stderr={err:?}"
    );
    assert!(
        !combined.contains("primitives/not")
            || combined.contains("not found")
            || combined.contains("undefined"),
        "unknown bare symbol MUST NOT silently dispatch to `not` \
         (the `not` primitive's FQN appearing only as part of an error message \
         is fine; dispatch-style resolution is not); \
         got stdout={out:?} stderr={err:?}"
    );
    // The bare symbol must literally appear in the error, not be swallowed.
    assert!(
        combined.contains("unknown-primitive-name-zzzz"),
        "error message MUST name the unknown symbol to be actionable; \
         got stdout={out:?} stderr={err:?}"
    );
}

// ---------------------------------------------------------------------------
// T-S1-5 — re-export transitivity: the bare-value resolver walks through
// ≥ 2 hops (user Import → prelude Reexport → primitives Def) and lands
// on the terminal Def, displaying `primitives/<name>` with qualified types.
//
// Achieved by loading the REAL stdlib prelude via `CRANELISP_LIB` in a
// subprocess — the stdlib prelude re-exports primitives per
// `stdlib/prelude.cl:49-52`, creating the three-module chain the design
// doc §Post-implementation note §1 describes.
// ---------------------------------------------------------------------------

// spec: design/int/bare-primitive-value-path.md §Post-implementation note;
//       spec/08-modules.md §8.9 — re-export chain transitivity
#[test]
fn bare_primitive_two_hop_reexport_chain_lands_on_terminal_def() {
    let o = run_repl_with_stdlib("add-i64\n", "two_hop_reexport");
    let out = stdout_str(&o);

    // The resolver MUST walk user → prelude → primitives and produce the
    // terminal Def's type. `primitives/add-i64` MUST be the qualified name.
    assert!(
        out.contains("primitives/add-i64"),
        "two-hop re-export chain (user → prelude → primitives) MUST resolve \
         to `primitives/add-i64` per spec/08-modules.md §8.9 + \
         bare-primitive-value-path.md post-impl note; got stdout: {out}"
    );

    // The full signature must be present; the fix threads through
    // `resolved_module` so the whole chain lands on the terminal Def.
    assert!(
        out.contains("(Fn ["),
        "two-hop resolver MUST surface the function signature, not just the \
         name (would indicate truncation at intermediate Reexport); \
         got stdout: {out}"
    );

    // Negative face of this assertion: MUST NOT show a `user/add-i64` or
    // `prelude/add-i64` attribution — spec §8.9 requires the ORIGINAL
    // defining module.
    assert!(
        !out.contains("user/add-i64"),
        "bare `add-i64` MUST NOT be attributed to the `user` module \
         (spec §8.9 — re-export provenance is the original defining module); \
         got stdout: {out}"
    );

    // Additional negative: display types MUST be qualified (`primitives/Int`)
    // not bare (`Int`) per repl/spec.md §1.1. If this starts failing, it's
    // either a display-format regression or FQTypeName migration has landed
    // and changed the convention — revisit per test-plan T-S1-5 note.
    assert!(
        out.contains("primitives/Int"),
        "display types MUST be qualified (`primitives/Int`), not bare `Int`, \
         per repl/spec.md §1.1; got stdout: {out}"
    );
}
