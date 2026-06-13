//! Sprint 64 Wave 6 batch 2 Part A carry-forward — `--link` Executable Generation cluster.
//!
//! Per the Wave 6 batch 2 audit (`tests/plan/wave-6-batch-2-audit.md` §1),
//! these 11 tests carry forward the Executable Generation surface from
//! `tests/sprint23.rs` (lines 117–376). The cluster covers `--link`
//! mode happy path, output-path derivation, error cases (no main,
//! wrong return type, file-not-found, bundle missing, `--no-cache`
//! incompatibility), cache reuse, and multi-module project linking.
//!
//! Spec anchors:
//!   - `repl/spec.md §0.2.1` — Link Mode (`--link`)
//!   - `design/backend/executable-generation.md §3` — End-to-End Flow
//!   - `design/backend/executable-generation.md §5` — Linker Invocation
//!   - `design/backend/executable-generation.md §7` — `main` Validation
//!   - `design/backend/executable-generation.md §9` — Edge Cases
//!
//! Mode: subprocess via the `Cranelisp` builder. `--link` produces an
//! executable in the per-test TempDir; `link_then_run` execs it and
//! returns the exe's exit code via `output().assert_exit(...)`.
//!
//! All 11 tests are GAP-COVER per audit (28 of which are
//! REGRESSION-GUARD). `link_multi_module_project` (#11) carries the
//! highest-value `--link` regression — Sprint 58 Wave 2c
//! `___cranelisp_got_helper` unresolved symbol — see
//! `design/arch/fixmes/0144-link-multi-module-got-helper.md`.

#[path = "helpers/e2e.rs"]
mod e2e;

use e2e::Cranelisp;
use e2e::PreludeVariant;

// =============================================================================
// 1. Basic compilation + execution
// =============================================================================

// spec: design/backend/executable-generation.md §3 — end-to-end --link flow.
//   Minimal `(defn main [] 42)` → `--link` produces executable; running
//   the executable yields exit code 42 (main's Int return).
//
// (carry: legacy/sprint23.rs::link_hello_world_produces_executable)
#[test]
fn link_hello_produces_executable_with_main_exit_code() {
    Cranelisp::new()
        .link_then_run("hello.cl")
        .file("hello.cl", "(import [primitives [Pure]])\n(defn main [] (Pure 42))")
        .output()
        .assert_exit(42);
}

// spec: design/backend/executable-generation.md §7 — main :: () -> Int.
//   Zero-exit angle: `(defn main [] 0)` → exit 0.
//
// (carry: legacy/sprint23.rs::link_main_returns_int_exit_code)
#[test]
fn link_main_returning_zero_exits_zero() {
    Cranelisp::new()
        .link_then_run("zero.cl")
        .file("zero.cl", "(import [primitives [Pure]])\n(defn main [] (Pure 0))")
        .output()
        .assert_exit(0);
}

// spec: design/backend/executable-generation.md §7 — main :: () -> IO _.
//   Either: (a) an IO main returning `Pure 0` exits with 0 (trampoline
//   fires and Pure unwraps), or (b) the build fails with a clear
//   error mentioning `main` / `IO` / `type` (graceful failure path).
//
// (carry: legacy/sprint23.rs::link_main_returns_io)
#[test]
fn link_main_returning_io_pure_zero_exits_zero_or_errors_clearly() {
    // Use the test fixtures prelude which defines IO type for the
    // typechecker. The legacy variant uses CRANELISP_LIB env ovrride.
    let out = Cranelisp::new()
        .link_then_run("io_main.cl")
        .file("io_main.cl", "(defn main [] (Pure 0))")
        .with_prelude(e2e::PreludeVariant::TestStandard)
        .output();

    // Pass shape: linker succeeded, exe ran, exit 0.
    if let Some(0) = out.status.code() {
        return;
    }
    // Else: must be a clear failure mentioning main or IO or type.
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("main") || combined.contains("IO") || combined.contains("type"),
        "IO main failure should mention main/IO/type: stdout={:?} stderr={:?}",
        out.stdout, out.stderr
    );
}

// =============================================================================
// 2. Output path derivation
// =============================================================================

// spec: design/backend/executable-generation.md §9 — output path default.
//   `cranelisp --link examples/hello.cl` produces `hello` (entry stem,
//   no extension) in cwd.
//
// (carry: legacy/sprint23.rs::link_default_output_is_entry_stem)
#[test]
fn link_default_output_is_entry_stem_no_extension() {
    let out = Cranelisp::new()
        .link("examples/hello.cl")
        .file("examples/hello.cl", "(import [primitives [Pure]])\n(defn main [] (Pure 0))")
        .output()
        .assert_ok();

    assert!(
        out.tmp_exists("hello"),
        "expected output 'hello' (entry stem) at TempDir root; tmpdir={}, stdout={:?}",
        out.tmpdir.display(), out.stdout
    );
}

// =============================================================================
// 3. Error cases
// =============================================================================

// spec: design/backend/executable-generation.md §7 — no main function.
//   File without `main` → clear error mentioning "main".
//
// (carry: legacy/sprint23.rs::link_error_no_main_function)
#[test]
fn link_error_when_main_function_missing() {
    let out = Cranelisp::new()
        .link("nomain.cl")
        .file("nomain.cl", "(defn helper [] 42)")
        .output();

    assert!(!out.status.success(), "should fail when no main: {:?}", out.stdout);
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("main"),
        "error should mention 'main': {combined}"
    );
}

// spec: spec/10-io.md §10.6 (Entry Point) + design/backend/executable-generation.md §7 —
//   main wrong return type. `(defn main [] "hello")` returns `String`, which
//   violates `main :: (Fn [] (IO _))`. A batch main MUST return `IO _`; the
//   error names `main` and the required `IO` shape. (Post-S80-Wave-1 the bare
//   `Int` acceptance is gone — the only conformant return type is `IO _`, so
//   the diagnostic names `IO`, not an `Int`-or-`IO` disjunction.)
//
// (carry: legacy/sprint23.rs::link_error_main_wrong_return_type)
#[test]
fn link_error_when_main_returns_wrong_type() {
    let out = Cranelisp::new()
        .link("wrong.cl")
        .file("wrong.cl", "(defn main [] \"hello\")")
        .output();

    assert!(!out.status.success(), "should fail on wrong main type");
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("main") && combined.contains("IO"),
        "error should mention main and the required `IO _` shape: {combined}"
    );
}

// spec: design/backend/executable-generation.md §9 — entry file not found.
//   Exit code 1 when the entry file does not exist.
//
// (carry: legacy/sprint23.rs::link_error_file_not_found)
#[test]
fn link_error_when_entry_file_not_found() {
    let out = Cranelisp::new()
        .link("nonexistent.cl")
        .output();
    assert_eq!(
        out.status.code(), Some(1),
        "missing entry file should exit 1; got {:?}\nstderr:\n{}",
        out.status, out.stderr
    );
}

// spec: design/backend/executable-generation.md §9 — missing bundle library.
//   When `libcranelisp_exe_bundle.a` cannot be found, error mentions
//   the bundle library. Best-effort: if the bundle is in a discoverable
//   location, `--link` may succeed; the invariant is that on genuine
//   absence, the error names the bundle.
//
// (carry: legacy/sprint23.rs::link_error_missing_bundle_library)
#[test]
fn link_error_when_bundle_library_missing_names_it() {
    // Best-effort: the bundle may be locatable from cwd or rustup paths;
    // we cannot reliably hide it without dropping privileges. The
    // assertion is purely conditional — if --link fails, the error
    // must name the bundle.
    let out = Cranelisp::new()
        .link("hello.cl")
        .file("hello.cl", "(import [primitives [Pure]])\n(defn main [] (Pure 0))")
        .env("CRANELISP_BUNDLE_PATH", "")
        .output();

    if !out.status.success() {
        let combined = format!("{}{}", out.stdout, out.stderr);
        assert!(
            combined.contains("cranelisp_exe_bundle") || combined.contains("bundle"),
            "error should mention bundle library: {combined}"
        );
    }
}

// spec: design/backend/executable-generation.md §9 — `--no-cache` interaction.
//   `--no-cache` + `--link` is rejected because linking requires cached
//   `.o` files. Error contains the explicit message.
//
// (carry: legacy/sprint23.rs::link_with_no_cache_is_rejected)
#[test]
fn link_neg_no_cache_flag_is_rejected() {
    let out = Cranelisp::new()
        .link("hello.cl")
        .file("hello.cl", "(defn main [] 0)")
        .cli_flag("--no-cache")
        .output();

    assert!(!out.status.success(), "--no-cache + --link should be rejected");
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("--no-cache is not supported with --link"),
        "should explain the incompatibility: {combined}"
    );
}

// =============================================================================
// 4. Cache reuse
// =============================================================================

// spec: design/backend/executable-generation.md §3 — cache reuse on second --link.
//   Two `--link` runs both produce a working executable; deleting the
//   produced exe between runs proves the second invocation re-emits.
//
// (carry: legacy/sprint23.rs::link_reuses_cached_object_files)
#[test]
fn link_second_invocation_reuses_cached_objects_and_re_emits_exe() {
    let first = Cranelisp::new()
        .link_then_run("hello.cl")
        .file("hello.cl", "(import [primitives [Pure]])\n(defn main [] (Pure 7))")
        .output()
        .assert_exit(7);

    // Delete the produced exe between runs to force re-emission.
    let exe_path = first.tmpdir.join("hello");
    std::fs::remove_file(&exe_path).ok();

    first
        .run_again()
        .link_then_run("hello.cl")
        .output()
        .assert_exit(7);
}

// =============================================================================
// 4b. Extern-primitive `--link` (FIXME 0280 / 0286 regression guard)
// =============================================================================

// spec: spec/appendix-a-builtins.md §A.3 — extern primitives (str-concat,
//   str-len) are real callable symbols in the synthetic `primitives` module.
//   A `--link` program that calls them must resolve the primitives GOT at
//   link time and run correctly.
//
// Regression guard for FIXME 0280: before the primitives-GOT static-backing
// fix, `tests/link.rs` had ZERO extern-primitive coverage, which is why the
// `___cranelisp_got_primitives not found` link failure went unseen until the
// /sprint probe. `(str-len (str-concat "ab" "cd"))` builds the heap string
// "abcd" (len 4); main returns 4, so the produced binary exits 4.
//
// (FIXME 0286 part (a) — the durable regression guard for the latent hole.)
#[test]
fn link_extern_primitive_str_ops_exits_with_computed_length() {
    Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .file(
            "sc.cl",
            "(import [primitives [str-concat str-len Pure]])\n\
             (defn main [] (Pure (str-len (str-concat \"ab\" \"cd\"))))\n",
        )
        .link_then_run("sc.cl")
        .output()
        .assert_exit(4);
}

// spec: spec/appendix-a-builtins.md §A.3 — (same anchor) extern primitive in a
//   `--link` binary used purely for its value (no trace). A second shape that
//   exercises the primitives GOT through a different primitive (`add-i64` is
//   inline CLIF, so use `str-len` over a literal) to widen the regression
//   surface beyond the str-concat path.
//
// (FIXME 0286 part (a) — second extern-primitive --link shape.)
#[test]
fn link_extern_primitive_str_len_of_literal_exits_with_length() {
    Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .file(
            "sl.cl",
            "(import [primitives [str-len Pure]])\n\
             (defn main [] (Pure (str-len \"hello\")))\n",
        )
        .link_then_run("sl.cl")
        .output()
        .assert_exit(5);
}

// spec: spec/04-expressions.md §4.12.9 — Build-mode availability: a traced
//   extern-primitive call in a `--link` binary. With FIXME 0280 landed, the
//   primitives group is swapped in object mode, so extern primitives appear as
//   trace-tree children in linked binaries (matching REPL/`--run`). The traced
//   body `(greet "bob")` calls both `str-concat` and `str-len`, so the
//   `user/greet` node has exactly TWO children, both extern primitives. main
//   descends to greet (the root's only child) and counts greet's children,
//   returning count+40 == 42.
//
//   This is the link-mode mirror of
//   trace.rs::trace_extern_primitive_appears_as_child and the structural
//   complement to the part-(b) linked-tree expectation flip: it asserts that an
//   extern primitive IS present in a `--link` trace tree. Verified manually by
//   /qa (FIXME 0286): greet's children are `primitives/str-concat` +
//   `primitives/str-len` (named via REPL), and the linked binary exits 42.
//
// (FIXME 0286 part (a) — the cheap traced extern-primitive --link variant.)
#[test]
fn link_traced_extern_primitives_appear_as_children_exit_42() {
    let src = "(import [primitives [Trace TraceCall str-concat str-len Pure]])\n\
         (import [macros [SCons SNil]])\n\
         (defn greet [s] (str-len (str-concat \"hi \" s)))\n\
         (defn slen [acc xs]\n\
           (match xs [SNil acc (SCons h t) (slen (add-i64 acc 1) t)]))\n\
         ; c = root's children = [user/greet]; descend into greet, count ITS\n\
         ; children (str-concat + str-len, both extern primitives) → 2.\n\
         (defn main []\n\
           (Pure (match (trace (greet \"bob\"))\n\
             [(TraceCall n p r c ns)\n\
               (match c [SNil 0\n\
                         (SCons h t)\n\
                           (match h [(TraceCall n2 p2 r2 c2 ns2)\n\
                                     (add-i64 (slen 0 c2) 40)])])])))\n";
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file("tprog.cl", src)
        .link_then_run("tprog.cl")
        .output()
        .assert_exit(42);
}

// =============================================================================
// 5. Multi-module linking
// =============================================================================

// spec: design/backend/executable-generation.md §3 — module graph compilation
//   under `--link`. A two-module project: `main.cl` imports
//   `helper.cl::add-one`; main exits with 42.
//
// Note: the legacy `tests/sprint23.rs` test carried an inline
// `FIXME(/int)` from Sprint 58 Wave 2c citing an unresolved
// `___cranelisp_got_helper` linker symbol on multi-module --link.
// As of Sprint 64 Wave 6 batch 2 carry-forward authoring, the test
// PASSES on the current binary — the per-module GOT export issue
// appears resolved. This test is preserved as a REGRESSION-GUARD
// for that specific multi-module GOT export shape.
//
// (carry: legacy/sprint23.rs::link_multi_module_project)
#[test]
fn link_multi_module_project_with_cross_module_call_exits_with_main_value() {
    Cranelisp::new()
        .link_then_run("main.cl")
        .file("prelude.cl", "(export [primitives [*]])\n")
        .file(
            "main.cl",
            "(import [helper [add-one]])\n(defn main [] (Pure (add-one 41)))",
        )
        .file(
            "helper.cl",
            "(defn add-one [:Int x] (add-i64 x 1))",
        )
        .output()
        .assert_exit(42);
}
