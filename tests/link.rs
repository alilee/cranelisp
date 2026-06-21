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

// =============================================================================
// §9 Edge Cases — REPL-only `discover-tests` extern in a `--link` build
//
// REGRESSION GUARD pinning the DESTINATION behaviour (S86 D5a ruling,
// /arch 2026-06-17; FIXME 0406 LANDED S87 → /int `reject_dev_session_externs_in_link`).
// `discover-tests` is a DEV-SESSION-ONLY host extern: it is resolved only in a
// live session (int's `define_symbol`); the asymmetry with `catch-runtime-error`
// (a self-contained intrinsic that DOES work in `--link`) is deliberate and
// settled (test-discovery.md §4.5, "fourth convergence").
//
// A `--link` build of a module that references `discover-tests` is now REJECTED
// at compile time with a FRIENDLY diagnostic surfaced before the `cc` link step:
// it explains the symbol is REPL/dev-session-only and unavailable in `--link`,
// names the referencing site, and points at the remedy (`--run` / the REPL
// `/run-tests`). Non-zero exit, no exe produced. Because a whole module compiles
// to one object, importing even a PURE helper (`label` below) from a module that
// also defines a `discover-tests`-using fn drags the unresolved extern into the
// link — the friendly rejection fires on the body call site.
//
// This is the SETTLED destination, NOT a backend defect. The /arch ruling (D5a)
// rejected the earlier `assert_exit(0)` oracle — resolving the extern under
// `--link` would reopen the dev-session-only ruling and erase the
// capture/discovery asymmetry. FIXME 0406 replaced the earlier raw-linker
// `undefined reference to discover-tests` interim with this friendly message.
//
// spec: design/arch/test-discovery.md §4.5 — What `--link` users see.
#[test]
fn link_module_referencing_discover_tests_extern_fails_with_friendly_message() {
    let out = Cranelisp::new()
        .link_then_run("entry.cl")
        .file(
            "runner.cl",
            "(import [primitives [discover-tests Pure String]])\n\
             (defn run-all [] (discover-tests []))\n\
             (defn label [:String s] :String s)",
        )
        .file(
            "entry.cl",
            "(import [primitives [Pure]])\n\
             (import [runner [label]])\n\
             (defn main [] (Pure (label \"hi\")))",
        )
        .output();

    // DESTINATION (test-discovery.md §4.5): non-zero exit, no exe — the
    // dev-session-only extern is rejected at compile time with a friendly
    // diagnostic surfaced before linking. The actual message on this toolchain is:
    //   error: codegen error at 0..0: `discover-tests` is a REPL/dev-session-only
    //   builtin and is not available in `--link` builds (it scans the live
    //   session's symbol table, …). It is referenced by `runner/run-all`. Remove
    //   the reference, or run this program with `--run` or in the REPL (use
    //   `/run-tests` there to run tests).
    assert!(
        !out.status.success(),
        "expected --link rejection (discover-tests is dev-session-only), got exit {:?}\nstdout:\n{}\nstderr:\n{}",
        out.status.code(), out.stdout, out.stderr
    );
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("discover-tests"),
        "rejection must name the `discover-tests` symbol: {combined}"
    );
    // Friendly-message substrings (stable across phrasing tweaks): it explains
    // the symbol is dev-session-only, that this is a `--link` build, and points
    // at the `--run` remedy. Match the stable tokens, not the whole sentence.
    assert!(
        combined.contains("dev-session")
            && combined.contains("--link")
            && combined.contains("--run"),
        "rejection must be the friendly dev-session-only/--link diagnostic naming the remedy: {combined}"
    );
}

// =============================================================================
// §9 Edge Cases — cross-mode cache reuse drops a dependency object (D5, literal
//   `__cranelisp_got_<module>` symptom)
//
// FAILING-NOT-IGNORED defect repro for S86 D5 — the LITERAL reported symptom:
// an unresolved `__cranelisp_got_<module>` cross-module GOT-base data symbol
// (Decision 23). Isolation (S86 1.5a) found this is a CROSS-MODE CACHE-REUSE
// defect, distinct from the `discover-tests` AOT-extern issue pinned by the test
// above. A `--run` pass caches the dependency object (`helper.o`) tagged for the
// in-memory/JIT path; a subsequent `--link` in the SAME project dir reuses that
// cache but the emitted link command OMITS `helper.o` entirely (link line shows
// `__startup.o user.o __main_alias.o` — no `helper.o`), so `user.o`'s
// cross-module GOT-base reference `__cranelisp_got_helper` is undefined at link.
// Control: `--link` from a CLEAN cache (no prior `--run`) includes `helper.o`
// and links + runs fine — so the defect is specifically the reuse of a
// `--run`-produced cache state by a later `--link`.
//
// Owning crate: /backend (cache/object GOT emission + link-set assembly —
// `crates/cranelisp-backend/src/cache/{object.rs,linker.rs}`), with /int consult
// on cache-mode tagging / link-set assembly that drops the `--run`-cached
// dependency object. FIXME(/backend — D5 cache-reuse).
//
// spec: design/backend/executable-generation.md §9 — Edge Cases
#[test]
fn link_after_run_reuses_cache_and_resolves_cross_module_got() {
    // Step 1: `--run` populates the cache (exit 0 — value 7+3=... encoded via
    // a string round-trip just to force a real cross-module call into helper).
    let first = Cranelisp::new()
        .file(
            "helper.cl",
            "(import [primitives [Int add-i64]])\n\
             (defn add3 [:Int x] :Int (add-i64 x 3))",
        )
        .file(
            "user.cl",
            "(import [primitives [Pure Int]])\n\
             (import [helper [add3]])\n\
             (defn main [] (Pure (add3 39)))",
        )
        .run("user.cl")
        .output()
        .assert_exit(42);

    // Step 2: `--link` in the SAME dir (cache present). CORRECT: it links a
    // standalone exe that, when run, exits 42. Today this FAILS at `cc` with
    // `undefined reference to `__cranelisp_got_helper'`, exit 1 (helper.o
    // dropped from the link set).
    first
        .run_again()
        .link_then_run("user.cl")
        .output()
        .assert_exit(42);
}

// =============================================================================
// DEF-4 — multi-module + `(platform <P>)` + `--link` emits the per-platform
//   startup-stub hash symbol `__cranelisp_expected_hash_<plat>` MORE THAN ONCE
//   (Sprint 86 Wave E, /port discovery)
// =============================================================================
//
// FAILING-NOT-IGNORED defect repro for S86 DEF-4 — the LITERAL reported symptom:
//   codegen error … failed to define __cranelisp_expected_hash_<plat>:
//   Duplicate definition of identifier: __cranelisp_expected_hash_<plat>
//
// ROOT (traced, /port + /qa): the per-platform layout-hash gate symbols
// (`__cranelisp_expected_hash_<plat>`, `__cranelisp_layout_name_<plat>`,
// imported `__cranelisp_layout_hash_<plat>`) are baked once per `layout_checks`
// entry in `crates/cranelisp-backend/src/exe.rs` (~:221/:236). That vector is
// built in `src/session_v4.rs` (~:2227) by iterating `shared.kept_dlls`. When a
// `(platform <P>)` program spans MORE THAN ONE `.cl` module, the SAME platform
// is enumerated in `kept_dlls` once per module, so `layout_checks` carries
// duplicate entries for the same platform name and `exe.rs` tries to
// `define_data`/`define_cstr_data` the SAME `__cranelisp_expected_hash_<plat>`
// symbol twice → "Duplicate definition of identifier". The enumeration must be
// deduplicated by platform name before it reaches the backend.
//
// ISOLATION (verified /qa, 2026-06-18):
//   - A SINGLE-`.cl`-module `(platform shapes)` / `(platform web)` program
//     `--link`s FINE (binary produced, gate symbol defined exactly once) —
//     control: `tests/spec_platforms_adt.rs::platform_adt_roundtrip_link`.
//   - Adding ONE extra `.cl` module import (`helper.cl` below) to the SAME
//     `(platform web)` program triggers the duplicate. So the defect is the
//     GENERAL multi-module + platform + `--link` shape, NOT web-specific.
//   - `web` reproduces the EXACT reported signature
//     (`__cranelisp_expected_hash_web`); `shapes` reproduces the same defect
//     with `__cranelisp_expected_hash_shapes`. Both are layout-hash-exporting
//     platforms (they reference an ADT). `stdio` (no ADT, no layout hash)
//     exhibits a RELATED but DISTINCT duplicate-enumeration symptom — the
//     platform `.rcgu.o` set is listed twice on the link line → "multiple
//     definition of <rust alloc symbols>" — which confirms the shared root
//     (duplicated `kept_dlls` enumeration) without the hash-symbol signature.
//     We pin the hash-symbol variant (`web`) as the canonical DEF-4 repro.
//
// `web.cl` is dropped inline (two `deftype`s; the same shape the `web` platform
// DLL references by FQ identity — see exemplar/web.cl) so the repro is
// free-standing (no stdlib, no exemplar coupling). It uses `use_workspace_platforms`
// per existing platform/link tests.
//
// FAILING-NOT-IGNORED (RED today, flips GREEN when /dev dedups the enumeration):
// the CORRECT behaviour is that a multi-module `(platform web)` program `--link`s
// cleanly — the gate symbol is emitted exactly once and the link succeeds. The
// oracle below asserts that correct outcome (link success), so it is RED today
// (the duplicate-definition codegen error aborts the link) and flips GREEN the
// moment the enumeration is deduplicated. The current failure signature is
// recorded in the assertion message + this comment for the handoff, not asserted
// as the expected state (that would invert the discipline into a guard pinning
// the bug). Today's failure is:
//   codegen error … failed to define __cranelisp_expected_hash_web:
//   Duplicate definition of identifier: __cranelisp_expected_hash_web
//
// Owning skill: /int (the duplicate originates in the `kept_dlls`→`layout_checks`
// enumeration built in `src/session_v4.rs` ~:2227 — dedup by platform name
// before handoff), with /backend consult on the `exe.rs` symbol-emission loop
// (~:221/:236) which trusts its input is already deduped. FIXME(/int — DEF-4
// duplicate per-platform layout-hash enumeration on multi-module --link).
//
// spec: design/arch/platform-interface.md §7.3 — `--link` sequence (no live load step)
#[test]
fn link_multi_module_platform_emits_single_layout_hash_gate_symbol() {
    // The `web` platform's Request/Response ADTs as an ordinary `.cl` module
    // (platforms do not declare ADTs — platform-interface.md §3a). The DLL
    // references these by FQ identity `web/Request` / `web/Response`.
    let web_module = "(deftype Request \
         [:primitives/String method :primitives/String path :primitives/String body])\n\
         (deftype Response \
         [:primitives/Int status :primitives/String content-type :primitives/String body])\n";

    // The SECOND `.cl` module — a pure helper. Importing it is what forces the
    // program across more than one module and triggers the duplicate.
    let helper_module = "(import [primitives [Int add-i64]])\n\
         (defn add-one [:Int x] :Int (add-i64 x 1))\n";

    // The entry: `(platform web)` + import the second module. `listen` is a web
    // platform effect; `(add-one 8079)` forces a real cross-module call so the
    // helper module is genuinely part of the link set.
    let entry = "(platform web)\n\
         (import [primitives [bind Pure]])\n\
         (import [platform.web [listen]])\n\
         (import [web [Request Response]])\n\
         (import [helper [add-one]])\n\
         (defn main [] (bind (listen (add-one 8079)) (fn [_] (Pure 0))))\n";

    let out = Cranelisp::new()
        .use_workspace_platforms()
        .file("web.cl", web_module)
        .file("helper.cl", helper_module)
        .file("user.cl", entry)
        .link("user.cl")
        .output();

    // CORRECT (RED today, GREEN post-fix): the link succeeds and produces the
    // binary. Today this FAILS with `failed to define
    // __cranelisp_expected_hash_web: Duplicate definition of identifier:
    // __cranelisp_expected_hash_web` because the per-platform gate symbol is
    // enumerated once per `.cl` module. `assert_ok` panics with the full
    // stdout/stderr, so the DEF-4 duplicate signature is surfaced verbatim in
    // the failure message — the handoff record is the panic output.
    out.assert_ok();
}

// =============================================================================
// DEF-5 — linking TWO DISTINCT platforms into ONE `--link` binary fails: the
//   manifest entry point `cranelisp_platform_manifest` is exported un-namespaced
//   by EVERY platform DLL → `cc: multiple definition of cranelisp_platform_manifest`
//   (Sprint 86 Wave E)
// =============================================================================
//
// FAILING-NOT-IGNORED defect repro for S86 DEF-5 — the LITERAL reported symptom:
//   ld: … multiple definition of `cranelisp_platform_manifest';
//       … first defined here
//   collect2: error: ld returned 1 exit status
//
// ROOT (settled, /arch ruling 2026-06-17 — platform-interface.md §6.7 GO): the
// `declare_platform!` macro exports the manifest fn with a BARE
// `#[unsafe(no_mangle)]` name `cranelisp_platform_manifest` (`declare.rs:303-304`).
// EVERY platform's DLL therefore exports the SAME un-namespaced symbol. A
// single-platform `--link` is fine (one definition), but linking TWO DISTINCT
// platforms into one binary drags BOTH manifest objects onto the `cc` link line
// → duplicate-definition link failure. The manifest fn was the LONE holdout: the
// other two per-platform exports — the GOT (`__cranelisp_got_platform_<name>`)
// and the layout hash (`__cranelisp_layout_hash_<name>`) — are ALREADY namespaced
// per the §5.5.5 convention. The blessed fix (`/arch`, §6.7) is the pure rename
// `cranelisp_platform_manifest` → `cranelisp_platform_manifest_<name>`, bringing
// the manifest into line with the §5.5.5 invariant the other two exports follow.
//
// ISOLATION (verified /qa, 2026-06-18, on pristine HEAD):
//   - A SINGLE-platform `--link` (`(platform stdio)` alone, or `(platform shapes)`
//     alone) links fine — control: `link.rs::link_extern_primitive_*` (stdio path,
//     implicitly single-platform) and `spec_platforms_adt.rs::platform_adt_roundtrip_link`
//     (`shapes` alone). One manifest definition, no collision.
//   - Declaring BOTH `(platform stdio)` + `(platform shapes)` and importing one
//     effect from each (`print` from stdio, `area` from shapes — enough that BOTH
//     manifests are force-loaded and BOTH `.rcgu.o` sets reach the link line)
//     reproduces the EXACT reported signature on the `shapes` manifest object:
//       …/cranelisp_shapes.<hash>.rcgu.o: in function `cranelisp_platform_manifest':
//       …/crates/cranelisp-platform/src/declare.rs:304: multiple definition of
//       `cranelisp_platform_manifest'; …/cranelisp_stdio.<hash>.rcgu.o:
//       …/declare.rs:304: first defined here
//   - The two platforms are interchangeable for the repro — any two distinct
//     workspace platforms collide on the same bare symbol. stdio + shapes are the
//     two that most reliably co-occur from the e2e harness (`use_workspace_platforms`).
//
// FAILING-NOT-IGNORED (RED today, flips GREEN when /dev namespaces the manifest
// export per §6.7): the CORRECT post-fix behaviour is that a two-distinct-platform
// program `--link`s cleanly — each DLL exports its own `cranelisp_platform_manifest_<name>`,
// the two coexist, and the link succeeds. The oracle below asserts that correct
// outcome (link success), so it is RED today (the duplicate-definition `cc` link
// failure aborts) and flips GREEN the moment the manifest is namespaced. The
// current failure signature is recorded in this comment + surfaced verbatim by
// `assert_ok`'s panic (full stdout/stderr) for the handoff — it is NOT asserted as
// the expected state (that would invert the discipline into a guard pinning the bug).
//
// Owning skill: /platform (the `declare_platform!` macro export name —
// `crates/cranelisp-platform/src/declare.rs:303-304` + the §5.5.5 shared
// emit/consume helper in `lib.rs`), with /backend consult on the
// dispatch/import-side reader (`exe.rs` / `platform.rs`) that resolves the manifest
// by name (must follow the same `_<name>` rule). FIXME(/platform — DEF-5 manifest
// export namespacing per platform-interface.md §6.7).
//
// spec: design/arch/platform-interface.md §5.5.5 — GOT/symbols naming convention (every per-platform export name-suffixed, ABI v4)
#[test]
fn link_two_distinct_platforms_namespaced_manifest_coexist() {
    // The `shapes.cl` ADT module the `shapes` platform sig references by FQ
    // identity (`shapes/Rectangle`). Self-contained — no stdlib, no exemplar
    // coupling (matches spec_platforms_adt.rs::SHAPES_MODULE).
    let shapes_module =
        "(deftype Rectangle [:primitives/Int w :primitives/Int h])\n";

    // The entry: declare BOTH platforms, import ONE effect from EACH so both
    // manifests are force-loaded, and a `main` that sequences them. `print` from
    // stdio (`(Fn [String] (IO Int))`) and `area` from shapes
    // (`(Fn [shapes/Rectangle] (IO Int))`). `bind`/`Pure` thread the two IOs;
    // `main : (Fn [] (IO _))` is spec-conformant. Exit = inner Int = 12.
    let entry = "(platform stdio)\n\
         (platform shapes)\n\
         (import [primitives [bind Pure]])\n\
         (import [platform.stdio [print]])\n\
         (import [platform.shapes [area]])\n\
         (import [shapes [Rectangle]])\n\
         (defn main []\n\
           (bind (print \"two platforms\")\n\
             (fn [_] (area (Rectangle 3 4)))))\n";

    let out = Cranelisp::new()
        .use_workspace_platforms()
        .with_prelude(PreludeVariant::None)
        .file("shapes.cl", shapes_module)
        .file("user.cl", entry)
        .link("user.cl")
        .output();

    // CORRECT (RED today, GREEN post-fix): the link succeeds and produces the
    // binary. Today this FAILS at the `cc` link step with
    //   multiple definition of `cranelisp_platform_manifest'
    // because BOTH platform DLLs export the bare un-namespaced manifest symbol.
    // `assert_ok` panics with the full stdout/stderr, so the DEF-5 collision
    // signature is surfaced verbatim in the failure message — the handoff record
    // is the panic output.
    out.assert_ok();
}

// =============================================================================
// DEF-6 — a `--link` binary that REPEATEDLY marshals a heap ADT across the
//   host↔platform-DLL boundary corrupts the heap and SIGABRTs (`double free or
//   corruption`), exit 134 (Sprint 86, /port exemplar `main.cl` web server)
// =============================================================================
//
// FAILING-NOT-IGNORED defect repro for S86 DEF-6 — the LITERAL reported symptom:
//   the standalone `--link` binary of `exemplar/main.cl` (the Sudoku web server)
//   ABORTS with `double free or corruption (!prev)`, SIGABRT (exit 134), while
//   the SAME program under `--run` serves correctly. The crash was first read as
//   "double-free at STARTUP before bind"; isolation showed it is NOT a
//   startup/two-platform/multi-module bug — it is heap corruption that
//   ACCUMULATES over iterations of the serve loop (each `accept → handle → send`
//   round marshals a heap ADT across the platform-DLL boundary). The exemplar
//   only hit it because, with :8080 already taken, `listen` failed, the serve
//   loop then spun fast (accept on a never-bound listener returns immediately),
//   and the per-iteration corruption reached the heap-consistency abort.
//
// ISOLATION (verified /qa, 2026-06-18; full bisection in tests/plan/ledger.md
// S86-DEF-6 entry):
//   - web platform ALONE, trivial non-serving main (`(bind (listen p) (Pure 0))`)
//     on a FREE port: links + runs CLEAN (exit 0). So web-platform static init /
//     module init is NOT the trigger.
//   - TWO distinct platforms (web + stdio) + trivial main: links + runs CLEAN.
//     So this is NOT the DEF-5 two-platform shape, and NOT a multi-platform
//     startup-stub bug.
//   - All 5 exemplar modules linked in + a trivial `(defn main [] (Pure 0))`:
//     runs CLEAN. So multi-module presence is NOT the trigger.
//   - A bounded loop calling a platform effect that marshals a heap ADT
//     N times: CLEAN at N≤30, ABORTS (`double free or corruption (!prev)`,
//     exit 134) at N≥40. The threshold scales with iteration count — a slow
//     per-iteration heap corruption, not a one-shot startup bug.
//   - The corruption is NOT web-specific and NOT cranelisp's own ADT codegen:
//     * web `accept` (PRODUCES a Request ADT across the boundary) loop → aborts
//       (`double free or corruption (!prev)` — the exemplar's exact signature).
//     * web `send` (CONSUMES a Response ADT) loop → aborts
//       (`corrupted size vs. prev_size`).
//     * shapes `area` (CONSUMES a Rectangle ADT) loop → aborts
//       (`double free or corruption (!prev)`).  ← the generic shape pinned below
//     * CONTROL: a PURE-cranelisp construct+match of the SAME ADT in a 500-iter
//       loop (no platform effect) → CLEAN. So cranelisp's own ADT alloc/free is
//       fine; the corruption is in the shared platform-ABI ADT-marshaling path.
//   - RC trace at the abort shows a freshly-allocated value's refcount header
//     reading garbage (`dec … rc=64`) — the heap-chunk metadata (incl. the host
//     RC header) has been overwritten, consistent with an allocator-mismatch /
//     buffer-overrun in the consuming/producing convention, NOT an RC-counter
//     miscount (every RC-driven free lands on rc=0 cleanly before glibc aborts).
//
// We pin the GENERIC shape (shapes `area`, the simplest ADT-consuming workspace
// platform effect) rather than the web-specific shape: it is free-standing (no
// stdlib, no exemplar coupling), uses `use_workspace_platforms()` like the other
// platform/link tests, and reproduces the EXACT exemplar signature
// (`double free or corruption (!prev)`). The web shape would couple the guard to
// the exemplar web DLL; the generic shape is the better, narrower guard.
//
// FAILING-NOT-IGNORED (RED today, flips GREEN when /dev fixes the platform-ABI
// ADT-marshaling corruption): the CORRECT behaviour is that the bounded loop
// runs to completion and `main` returns `(Pure 0)` → the binary exits 0. The
// oracle asserts that correct outcome (exit 0), so it is RED today (SIGABRT /
// double-free, exit 134) and flips GREEN the moment the corruption is fixed. The
// loop count (200) is chosen well above the observed ~40 threshold so the repro
// is deterministic; it still completes in well under a second when clean.
//
// Owning skill: /platform (the shared `cranelisp-platform` crate's ADT-marshaling
// ABI — `CLAdt::construct` / `CLOwned` / `CLHeap::into_owned_consuming` and the
// host RC/alloc callbacks `alloc_with_tag` that the per-platform `--link` path
// invokes; `crates/cranelisp-platform/src/`). The web + shapes DLLs both only
// call these shared helpers and BOTH corrupt, while pure-cranelisp ADTs do not —
// so the defect is in the shared crate, not the individual DLLs. /backend consult
// on the host RC-header / GOT-baked alloc callbacks that the consuming convention
// (Decision 24) drives across the boundary. FIXME(/platform — DEF-6 platform-ABI
// ADT-marshaling heap corruption accumulating over repeated host↔DLL ADT crossings).
//
// spec: spec/10-io.md §10.10 — Platform ABI Contract
#[test]
fn link_repeated_platform_adt_marshal_does_not_corrupt_heap() {
    // The `shapes` ADT module the `shapes` platform sig references by FQ identity
    // (`shapes/Rectangle`). Self-contained (matches spec_platforms_adt.rs).
    let shapes_module =
        "(deftype Rectangle [:primitives/Int w :primitives/Int h])\n";

    // A bounded serve-loop analogue: construct a Rectangle and pass it across the
    // host↔DLL boundary to `area` (`(Fn [shapes/Rectangle] (IO Int))`) 200 times,
    // then return `(Pure 0)`. No prelude — `bind`/`Pure`/`sub-i64`/`eq-i64` are
    // primitives. `area` CONSUMES the heap ADT each iteration; the per-iteration
    // platform-ABI marshaling corruption accumulates to the heap-abort by N≥40,
    // so 200 reproduces deterministically. Post-fix, the loop completes and the
    // binary exits 0.
    let entry = "(platform shapes)\n\
         (import [primitives [bind Pure sub-i64 eq-i64]])\n\
         (import [platform.shapes [area]])\n\
         (import [shapes [Rectangle]])\n\
         (defn srv-loop [:primitives/Int n] :(primitives/IO primitives/Int)\n\
           (if (eq-i64 n 0)\n\
             (Pure 0)\n\
             (bind (area (Rectangle 3 4))\n\
               (fn [_] (srv-loop (sub-i64 n 1))))))\n\
         (defn main [] (srv-loop 200))\n";

    // CORRECT (RED today, GREEN post-fix): the produced binary runs the 200-iter
    // ADT-marshal loop to completion and exits 0. Today it ABORTS with
    //   double free or corruption (!prev)
    // (SIGABRT, exit 134) — the exemplar `main.cl` web-server signature — because
    // the shared platform-ABI ADT-marshaling path corrupts the heap a little on
    // every host↔DLL ADT crossing. `assert_exit(0)` panics with the captured
    // stdout/stderr + exit code, surfacing the SIGABRT signature verbatim for the
    // handoff record.
    Cranelisp::new()
        .use_workspace_platforms()
        .with_prelude(PreludeVariant::None)
        .file("shapes.cl", shapes_module)
        .file("user.cl", entry)
        .link_then_run("user.cl")
        .output()
        .assert_exit(0);
}
