// stdlib_conformance.rs — S110 §E SG-1: the stdlib-compile smoke gate.
//
// The CLASS this gate cures: a compiler regression that breaks a stdlib module's
// compilation must NOT be able to ship invisibly (the 0604 blast radius —
// `num.bits` and other deep submodules are unreachable from the 13 top-level
// `.cl` files, so a top-level-only probe would miss them).
//
// Design (design/int/index-worker-isolation.md context +
// [historical QA allocation](https://github.com/alilee/cranelisp/blob/dc78ddbee3107043925505531798667dc61f7a03/tests/plan/PLAN.md), S110 E,
// /qa-confirmed with two refinements):
//   1. Enumeration is RECURSIVE — every `stdlib/**/*.cl`, skipping `prelude.cl`
//      and every subtree declared private by its parent (`(mod- name)`, which
//      covers ALL `.test` submodules per the S109 P5-S2 conversion). No
//      hand-list anywhere — the walk + a light per-parent scan derives the set.
//   2. Shape: ONE enumerating test fn, a per-module `--run` subprocess loop
//      (each module compiles in its own subprocess + tmpdir), an AGGREGATED
//      failure report naming every failing module + its first error line (so one
//      run reports the full breakage set, not just the first).
//   3. Determinism: the gate runs `--run` (batch) — the background index feed is
//      REPL-only (R17), so the gate is deterministic by construction and is NOT
//      a race guard (the 0604 race is guarded by the §F ≥25× sweep). Its job is
//      the CLASS, not the race.
//
// Behind the ONE sanctioned `use_workspace_stdlib_for_stdlib_conformance_only()`
// gate (root CLAUDE.md §"Design Principles" — Stdlib separation; tests/CLAUDE.md
// §"Test isolation"). The [historical QA allocation](https://github.com/alilee/cranelisp/blob/dc78ddbee3107043925505531798667dc61f7a03/tests/plan/PLAN.md)
// records S110 E / SG-1.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::Cranelisp;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Duration;

/// The workspace `stdlib/` directory. Read-only on project_root — the gate only
/// reads the module tree to enumerate it; every compile runs in a per-module
/// tmpdir via the harness. `CARGO_MANIFEST_DIR` is the crate (workspace) root.
fn stdlib_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("stdlib")
}

/// Recursively collect every `*.cl` file under `dir`.
fn collect_cl_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_cl_files(&path, out);
        } else if path.extension().and_then(|e| e.to_str()) == Some("cl") {
            out.push(path);
        }
    }
}

/// The dotted module path for a stdlib file: relative to `stdlib/`, `.cl`
/// stripped, `/` → `.`. `stdlib/collections/vec.cl` → `collections.vec`.
fn module_path(file: &Path, stdlib: &Path) -> String {
    let rel = file.strip_prefix(stdlib).expect("file under stdlib");
    let no_ext = rel.with_extension("");
    no_ext
        .components()
        .map(|c| c.as_os_str().to_string_lossy().into_owned())
        .collect::<Vec<_>>()
        .join(".")
}

/// Does `parent_file` declare `child` as a PRIVATE submodule via `(mod- child)`?
/// A declaration line's trimmed head is `(mod- ` (comment lines start `;;`, so a
/// prose mention of `(mod- test)` in a `;;` comment is not matched).
fn declares_private_child(parent_file: &Path, child: &str) -> bool {
    let Ok(text) = fs::read_to_string(parent_file) else {
        return false;
    };
    for line in text.lines() {
        let t = line.trim_start();
        if let Some(rest) = t.strip_prefix("(mod- ") {
            let name: String = rest
                .chars()
                .take_while(|c| !c.is_whitespace() && *c != ')')
                .collect();
            if name == child {
                return true;
            }
        }
    }
    false
}

/// A module is private (skip) if ANY of its path prefixes is declared private by
/// the parent `.cl` that owns that component — which also covers everything
/// UNDER a private module (the ancestor's `(mod- child)` catches the whole
/// subtree). `collections.vec.test` is private because `collections/vec.cl`
/// declares `(mod- test)`.
fn is_private_module(components: &[&str], stdlib: &Path) -> bool {
    for k in 1..components.len() {
        // Parent module = components[0..k]; its file is stdlib/<that>.cl.
        let parent_file = stdlib.join(components[0..k].join("/")).with_extension("cl");
        let child = components[k];
        if declares_private_child(&parent_file, child) {
            return true;
        }
    }
    false
}

/// Public modules that `--run` must refuse under REPL §16.6: `testing.runner`
/// compiles functions that reference `discover-tests`, and `testing` declares
/// it as a public child. A compiled reference spreading into any other module
/// fails that module's exit-0 condition.
const REFUSED_UNDER_RUN: [&str; 2] = ["testing", "testing.runner"];

/// The §16.6 diagnostic names the reference (`src/exe.rs`
/// `refuse_dev_session_externs`).
const REFUSAL_WORDING: &str = "references `discover-tests`";

// spec: repl/spec/16-test-discovery.md §16.6 Availability by Invocation Mode —
// every public stdlib module compiles; one without a compiled `discover-tests`
// reference also runs under `--run` (a program importing its full surface
// `[*]` and returning `0` from `main` exits 0); §16.6 refuses the named set, so
// for those modules the refusal is the pass and exit 0 is a failure. A module
// that fails to compile reports its compile error, not the refusal. The gate
// enumerates the module set RECURSIVELY (skipping `prelude.cl` and every
// `(mod- …)` private subtree) and reports EVERY failing module in one run.
#[test]
fn stdlib_all_public_modules_compile_and_run() {
    let stdlib = stdlib_dir();
    let mut files = Vec::new();
    collect_cl_files(&stdlib, &mut files);
    files.sort();

    let mut public_modules: Vec<String> = Vec::new();
    for f in &files {
        let name = module_path(f, &stdlib);
        if name == "prelude" {
            continue;
        }
        let comps: Vec<&str> = name.split('.').collect();
        if is_private_module(&comps, &stdlib) {
            continue;
        }
        public_modules.push(name);
    }
    public_modules.sort();
    public_modules.dedup();

    assert!(
        !public_modules.is_empty(),
        "enumeration found zero public stdlib modules — the walk/skip logic is \
         broken (found {} .cl files under {})",
        files.len(),
        stdlib.display()
    );

    // Per-module subprocess loop: each module compiles in its own tmpdir; a
    // trivial `main` returning 0 makes exit 0 the pass condition. Cache ON within
    // the test's own tmpdir (transitive deps compile once per module).
    let mut failures: Vec<(String, String)> = Vec::new();
    for m in &public_modules {
        // `main` must return `IO _` under the workspace prelude (batch main
        // shape); `Pure` wraps the trivial `0` exit code. `Pure` is imported
        // explicitly from `primitives` because a module with an explicit
        // `(import …)` does not receive the implicit prelude glob, so a bare
        // `Pure` would be `undefined variable` — an artefact of the probe, not a
        // module defect.
        let probe =
            format!("(import [{m} [*]])\n(import [primitives [Pure]])\n(defn main [] (Pure 0))\n");
        let out = Cranelisp::new()
            .use_workspace_stdlib_for_stdlib_conformance_only()
            .file("main.cl", &probe)
            .run("main.cl")
            .timeout(Duration::from_secs(90))
            .output();
        let combined = format!("{}\n{}", out.stdout, out.stderr);
        let first_err = || {
            combined
                .lines()
                .find(|l| {
                    let l = l.trim();
                    !l.is_empty() && !l.starts_with(":primitives/")
                })
                .unwrap_or("<no error line captured>")
                .trim()
                .to_string()
        };
        if REFUSED_UNDER_RUN.contains(&m.as_str()) {
            if out.status.success() {
                failures.push((m.clone(), "exit 0; REPL §16.6 requires refusal".to_string()));
            } else if !combined.contains(REFUSAL_WORDING) {
                failures.push((m.clone(), format!("not the §16.6 refusal: {}", first_err())));
            }
        } else if !out.status.success() {
            failures.push((m.clone(), first_err()));
        }
    }

    if !failures.is_empty() {
        let report = failures
            .iter()
            .map(|(m, e)| format!("  {m:32} → {e}"))
            .collect::<Vec<_>>()
            .join("\n");
        panic!(
            "SG-1: {} of {} public stdlib modules FAILED to compile/run under \
             `--run` (aggregated report — the full breakage set):\n{}",
            failures.len(),
            public_modules.len(),
            report
        );
    }
}

// =============================================================================
// BD-M3 — the STDLIB-ROUTE conformance row (binder matrix, sanctioned stdlib
// exception). `def`/`const` are stdlib macros (`stdlib/defs.cl`) that expand to
// native `defn`/`defmacro`, so the §5 binder rule reaches them AFTER expansion
// (spec §5 intro: "a qualified head such as `(def fmt/x 1)` … is rejected on the
// same principle"). This is the real user-facing route (the forms users actually
// write), exercised behind the ONE sanctioned workspace-stdlib gate. Reject cell
// is RED today (silent-accept) → flips at W3; the located-span provenance shares
// the BD-M2 int re-anchoring seam (W4, FIXME 0650). Bare-head positive is GREEN.
// =============================================================================

// A REPL session with the workspace stdlib (its prelude auto-loads, so `def`/
// `const` are in scope without an explicit import — an explicit `(import …)` would
// suppress the implicit prelude glob and lose the macros). REPL mode also sidesteps
// the batch-`main` shape (`Pure` is not in the prelude glob).
fn stdlib_repl(stdin: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .use_workspace_stdlib_for_stdlib_conformance_only()
        .repl()
        .stdin(stdin)
        .timeout(Duration::from_secs(90))
        .output()
}

/// Exercise a public core.io program through the three user-visible modes.
fn core_io_mode_failures(label: &str, source: &str) -> Vec<String> {
    let repl = stdlib_repl(&format!("{source}(main)\n"));
    let run = Cranelisp::new()
        .use_workspace_stdlib_for_stdlib_conformance_only()
        .run("user.cl")
        .user(source)
        .timeout(Duration::from_secs(90))
        .output();
    let link = Cranelisp::new()
        .use_workspace_stdlib_for_stdlib_conformance_only()
        .link_then_run("user.cl")
        .user(source)
        .timeout(Duration::from_secs(90))
        .output();

    let mut failures = Vec::new();
    for (mode, expected_repl_value, out) in [
        ("REPL", true, repl),
        ("--run", false, run),
        ("--link", false, link),
    ] {
        let succeeds = if expected_repl_value {
            out.status.success() && out.stdout.contains(":primitives/Int 0")
        } else {
            out.status.code() == Some(0)
        };
        if !succeeds {
            failures.push(format!(
                "{label} {mode}: expected REPL Int 0 or batch exit 0; status={:?}\n\
                 stdout:\n{}\nstderr:\n{}",
                out.status.code(),
                out.stdout,
                out.stderr
            ));
        }
    }
    failures
}

fn assert_stdlib_repl_result(label: &str, source: &str, expected: &str) {
    let out = stdlib_repl(source);
    let details = format!(
        "status={:?}\nstdout:\n{}\nstderr:\n{}",
        out.status, out.stdout, out.stderr
    );
    assert!(
        out.status.success(),
        "{label} must complete without abort or timeout; {details}"
    );
    assert!(
        out.stdout.contains(expected),
        "{label} must produce {expected:?}; {details}"
    );
}

const TIMEOUT_CODEGEN_BACKSTOP: &str =
    "generic value reference 'Some' reached codegen without a mono instance";
const TIMEOUT_LOSER_MARKER: &str = "S121_TIMEOUT_CANCELLED_LOSER_SHOULD_NOT_PRINT";

/// Exercise one timeout program through the three user-visible execution faces.
/// The vector is deliberately aggregated so the public subject and both
/// controls remain observable together if any face regresses.
fn timeout_mode_failures(label: &str, source: &str) -> Vec<String> {
    let repl_input = format!("{source}(main)\n");
    let repl = stdlib_repl(&repl_input);
    let run = Cranelisp::new()
        .use_workspace_stdlib_for_stdlib_conformance_only()
        .run("user.cl")
        .user(source)
        .timeout(Duration::from_secs(90))
        .output();
    let link = Cranelisp::new()
        .use_workspace_stdlib_for_stdlib_conformance_only()
        .link_then_run("user.cl")
        .user(source)
        .timeout(Duration::from_secs(90))
        .output();

    let mut failures = Vec::new();
    for (mode, expected_repl_value, out) in [
        ("REPL", true, repl),
        ("--run", false, run),
        ("--link", false, link),
    ] {
        let combined = format!("{}\n{}", out.stdout, out.stderr);
        let timer_outcome = if expected_repl_value {
            combined.contains(":primitives/Int 0")
        } else {
            out.status.code() == Some(0)
        };
        if !out.status.success() || !timer_outcome || combined.contains(TIMEOUT_CODEGEN_BACKSTOP) {
            failures.push(format!(
                "{label} {mode}: expected the timer/None outcome (REPL Int 0 or batch exit 0) \\
                 without `{TIMEOUT_CODEGEN_BACKSTOP}`; status={:?}\nstdout:\n{}\nstderr:\n{}",
                out.status.code(),
                out.stdout,
                out.stderr
            ));
        }
    }
    failures
}

/// Keep the process alive after a timer win, so a non-cancelled losing action
/// would have time to emit its marker rather than merely being cut off at exit.
fn timeout_cancellation_mode_failures() -> Vec<String> {
    const SOURCE: &str = "(platform stdio)\n(import [core.io [timeout]])\n(import [platform.stdio [print]])\n(import [primitives [Pure bind sleep Some None]])\n(defn losing-action [] (bind (sleep 50) (fn [_] (print \"S121_TIMEOUT_CANCELLED_LOSER_SHOULD_NOT_PRINT\"))))\n(defn main [] (bind (timeout 10 (losing-action)) (fn [r] (bind (sleep 100) (fn [_] (match r [None (Pure 0) (Some _) (Pure 1)]))))))\n";
    let repl_input = format!("{SOURCE}(main)\n");
    let repl = Cranelisp::new()
        .use_workspace_stdlib_for_stdlib_conformance_only()
        .use_workspace_platforms()
        .repl()
        .stdin(&repl_input)
        .timeout(Duration::from_secs(90))
        .output();
    let run = Cranelisp::new()
        .use_workspace_stdlib_for_stdlib_conformance_only()
        .use_workspace_platforms()
        .run("user.cl")
        .user(SOURCE)
        .timeout(Duration::from_secs(90))
        .output();
    let link = Cranelisp::new()
        .use_workspace_stdlib_for_stdlib_conformance_only()
        .use_workspace_platforms()
        .link_then_run("user.cl")
        .user(SOURCE)
        .timeout(Duration::from_secs(90))
        .output();

    let mut failures = Vec::new();
    for (mode, expected_repl_value, out) in [
        ("REPL", true, repl),
        ("--run", false, run),
        ("--link", false, link),
    ] {
        let combined = format!("{}\n{}", out.stdout, out.stderr);
        let timer_outcome = if expected_repl_value {
            combined.contains(":primitives/Int 0")
        } else {
            out.status.code() == Some(0)
        };
        if !out.status.success() || !timer_outcome || combined.contains(TIMEOUT_LOSER_MARKER) {
            failures.push(format!(
                "timeout cancellation {mode}: expected timer/None (REPL Int 0 or batch exit 0) \\
                 and no delayed loser marker `{TIMEOUT_LOSER_MARKER}`; status={:?}\nstdout:\n{}\nstderr:\n{}",
                out.status.code(), out.stdout, out.stderr
            ));
        }
    }
    failures
}

fn copy_dir_recursive(source: &Path, destination: &Path) -> std::io::Result<()> {
    fs::create_dir_all(destination)?;
    for entry in fs::read_dir(source)? {
        let entry = entry?;
        let from = entry.path();
        let to = destination.join(entry.file_name());
        if entry.file_type()?.is_dir() {
            copy_dir_recursive(&from, &to)?;
        } else if entry.file_type()?.is_file() {
            fs::copy(&from, &to)?;
        }
    }
    Ok(())
}

/// Copy the public stdlib into a test-private lib root and make exactly the
/// counterfactual replacement in its own `core/io.cl`.
fn copied_stdlib_timeout_lambda_counterfactual(cr: &Cranelisp) {
    // read-only on project_root: the workspace stdlib is copied into the
    // harness TempDir; only that private copy is modified.
    let copied_stdlib = cr.tmpdir_path().join("stdlib-counterfactual");
    copy_dir_recursive(&stdlib_dir(), &copied_stdlib).expect("copy stdlib into test TempDir");
    let core_io = copied_stdlib.join("core/io.cl");
    let original = fs::read_to_string(&core_io).expect("read copied core/io.cl");
    assert_eq!(
        original.matches("map-io Some").count(),
        1,
        "the counterfactual requires exactly one workspace `map-io Some` occurrence"
    );
    let replacement = original.replacen("map-io Some", "map-io (fn [x] (Some x))", 1);
    assert_eq!(
        replacement.matches("map-io (fn [x] (Some x))").count(),
        1,
        "the counterfactual must contain exactly its one lambda replacement"
    );
    fs::write(&core_io, replacement).expect("write copied core/io.cl counterfactual");
}

/// Same public-import subject as `timeout_mode_failures`, but its lib root is a
/// fresh copied stdlib in which the sole `map-io Some` form is lambda-wrapped.
fn timeout_counterfactual_mode_failures(source: &str) -> Vec<String> {
    let repl_input = format!("{source}(main)\n");
    let repl = Cranelisp::new();
    copied_stdlib_timeout_lambda_counterfactual(&repl);
    let repl = repl
        .lib_dir("stdlib-counterfactual")
        .repl()
        .stdin(&repl_input)
        .timeout(Duration::from_secs(90))
        .output();

    let run = Cranelisp::new();
    copied_stdlib_timeout_lambda_counterfactual(&run);
    let run = run
        .lib_dir("stdlib-counterfactual")
        .run("user.cl")
        .user(source)
        .timeout(Duration::from_secs(90))
        .output();

    let link = Cranelisp::new();
    copied_stdlib_timeout_lambda_counterfactual(&link);
    let link = link
        .lib_dir("stdlib-counterfactual")
        .link_then_run("user.cl")
        .user(source)
        .timeout(Duration::from_secs(90))
        .output();

    let mut failures = Vec::new();
    for (mode, expected_repl_value, out) in [
        ("REPL", true, repl),
        ("--run", false, run),
        ("--link", false, link),
    ] {
        let combined = format!("{}\n{}", out.stdout, out.stderr);
        let timer_outcome = if expected_repl_value {
            combined.contains(":primitives/Int 0")
        } else {
            out.status.code() == Some(0)
        };
        if !out.status.success() || !timer_outcome || combined.contains(TIMEOUT_CODEGEN_BACKSTOP) {
            failures.push(format!(
                "copied-stdlib lambda counterfactual {mode}: expected the timer/None outcome \\
                 (REPL Int 0 or batch exit 0) without `{TIMEOUT_CODEGEN_BACKSTOP}`; status={:?}\nstdout:\n{}\nstderr:\n{}",
                out.status.code(), out.stdout, out.stderr
            ));
        }
    }
    failures
}

// Public `core.io/timeout` is a derived race: a 10 ms timer MUST beat the
// 1000 ms action, returning `None` and therefore exit 0.  The local sibling
// preserves the timeout/race/sleep/bind/Option/match shape, but makes the
// winner arm's constructor reference a lambda.  It intentionally does not
// import `core.io`. The S121 repair confirmed the private typecheck P4
// successor-discovery seam for concrete function values; this e2e keeps the
// public timeout behaviour and its value-reference controls pinned.
// spec: spec/10-io.md §10.12.8 + §10.12.9 — derived `timeout` races an effect against a millisecond timer, returns `None` when the timer wins, and cancels the loser; spec/11-stdlib.md §11 — a public stdlib import remains usable.
// defect: class=wrong-reject locus=crates/cranelisp-typecheck/src/traits/monomorphise.rs::monomorphise_inner_function_values found=S121 owner=/dev
//   — fixed S121: P4 successor discovery now monomorphises concrete bare
//   function values reached in a rechecked generic body.
#[test]
fn stdlib_timeout_public_concrete_call_and_lambda_control_across_modes() {
    // Retained verbatim from docs' S121 timeout.cl artifact.
    const PUBLIC_SUBJECT: &str = "(import [core.io [timeout]])\n(import [primitives [Pure bind sleep Some None]])\n(defn main [] (bind (timeout 10 (sleep 1000)) (fn [r] (match r [(Some v) (Pure 1) None (Pure 0)]))))\n";
    const LAMBDA_CONTROL: &str = "(import [primitives [Pure bind race sleep Some None]])\n(defn map-io [f io-val] (bind io-val (fn [x] (Pure (f x)))))\n(defn timeout [d io] (race (map-io (fn [x] (Some x)) io) (map-io (fn [_] None) (sleep d))))\n(defn main [] (bind (timeout 10 (sleep 1000)) (fn [r] (match r [(Some v) (Pure 1) None (Pure 0)]))))\n";

    let control_failures = timeout_mode_failures("lambda control", LAMBDA_CONTROL);
    let counterfactual_failures = timeout_counterfactual_mode_failures(PUBLIC_SUBJECT);
    let cancellation_failures = timeout_cancellation_mode_failures();
    let subject_failures = timeout_mode_failures("public core.io/timeout subject", PUBLIC_SUBJECT);
    assert!(
        control_failures.is_empty()
            && counterfactual_failures.is_empty()
            && cancellation_failures.is_empty()
            && subject_failures.is_empty(),
        "`map-io (fn [x] (Some x))` lambda control failures (must be empty):\n{}\n\
         copied-stdlib lambda counterfactual failures (must be empty):\n{}\n\
         timeout cancellation failures (must be empty):\n{}\n\
         public `core.io/timeout` failures (must be empty; fixed S121):\n{}",
        control_failures.join("\n\n"),
        counterfactual_failures.join("\n\n"),
        cancellation_failures.join("\n\n"),
        subject_failures.join("\n\n"),
    );
}

// One public executable check for the six `core.io` families that cannot enter
// the in-language discovery runner: its zero exit requires every scalar or
// structural observation below to agree.

// This is the smallest ordered `sequence-io` composition that retains the
// public List result and distinguishes both element order and list termination.
// spec: spec/10-io.md §10.3 + §10.12.8 — public sequence IO returns its values
// in action order; spec/11-stdlib.md §11 — public core.io helpers are usable.
#[test]
fn stdlib_core_io_ordered_two_action_sequence_reduction_across_modes() {
    const SOURCE: &str = r#"
(import [core.io [sequence-io]])
(import [collections.list [List Nil Cons]])
(import [primitives [IO Pure bind eq-i64]])

(defn nested-action [x] (bind (Pure x) (fn [v] (Pure v))))

(defn main []
  (bind (sequence-io (Cons (nested-action 1) (Cons (nested-action 2) Nil)))
        (fn [xs]
          (match xs [(Cons a rest-a)
                       (match rest-a [(Cons b rest-b)
                                      (match rest-b [Nil (Pure (if (eq-i64 a 1) (if (eq-i64 b 2) 0 1) 1))
                                                     _ (Pure 1)])
                                      _ (Pure 1)])
                     _ (Pure 1)]))))
"#;
    let failures = core_io_mode_failures("ordered two-action sequence reduction", SOURCE);
    assert!(
        failures.is_empty(),
        "ordered two-action sequence reduction failures:\n{}",
        failures.join("\n\n")
    );
}

// Control for the reduction above: the two actions are explicitly bound and
// their results are assembled into the same List shape before the same order
// and termination observation.
// spec: spec/10-io.md §10.3 + §10.12.8 — explicit bind preserves public IO
// action order; spec/11-stdlib.md §11 — public core.io imports remain usable.
#[test]
fn stdlib_core_io_ordered_two_action_explicit_bind_control_across_modes() {
    const SOURCE: &str = r#"
(import [core.io [sequence-io]])
(import [collections.list [List Nil Cons]])
(import [primitives [IO Pure bind eq-i64]])

(defn nested-action [x] (bind (Pure x) (fn [v] (Pure v))))

(defn main []
  (bind (nested-action 1)
        (fn [a]
          (bind (nested-action 2)
                (fn [b]
                  (let [xs (Cons a (Cons b Nil))]
                    (match xs [(Cons x rest-x)
                                 (match rest-x [(Cons y rest-y)
                                                (match rest-y [Nil (Pure (if (eq-i64 x 1) (if (eq-i64 y 2) 0 1) 1))
                                                               _ (Pure 1)])
                                                _ (Pure 1)])
                               _ (Pure 1)])))))))
"#;
    let failures = core_io_mode_failures("ordered two-action explicit-bind control", SOURCE);
    assert!(
        failures.is_empty(),
        "ordered two-action explicit-bind control failures:\n{}",
        failures.join("\n\n")
    );
}

// Multiplicity control for the reduced subject: `sequence-io` still receives a
// nested Bind action and returns a List, but it sequences only one action.
// spec: spec/10-io.md §10.3 + §10.12.8 — public sequence IO returns its values
// in action order; spec/11-stdlib.md §11 — public core.io helpers are usable.
#[test]
fn stdlib_core_io_one_nested_action_sequence_control_across_modes() {
    const SOURCE: &str = r#"
(import [core.io [sequence-io]])
(import [collections.list [List Nil Cons]])
(import [primitives [IO Pure bind eq-i64]])

(defn nested-action [x] (bind (Pure x) (fn [v] (Pure v))))

(defn main []
  (bind (sequence-io (Cons (nested-action 1) Nil))
        (fn [xs]
          (match xs [(Cons x rest)
                       (match rest [Nil (Pure (if (eq-i64 x 1) 0 1))
                                    _ (Pure 1)])
                     _ (Pure 1)]))))
"#;
    let failures = core_io_mode_failures("one nested-action sequence control", SOURCE);
    assert!(
        failures.is_empty(),
        "one nested-action sequence control failures:\n{}",
        failures.join("\n\n")
    );
}

// Empty input has no actions and must return the empty List rather than a
// synthesized element, hang, or process failure.
// spec: spec/10-io.md §10.3 + §10.12.8 — empty public sequence IO returns an
// empty result; spec/11-stdlib.md §11 — public core.io helpers are usable.
#[test]
fn stdlib_core_io_empty_sequence_returns_empty_across_modes() {
    const SOURCE: &str = r#"
(import [core.io [sequence-io]])
(import [collections.list [List Nil]])
(import [primitives [IO Pure bind]])

(defn main []
  (bind (sequence-io :(List (IO Int)) Nil)
        (fn [xs] (match xs [Nil (Pure 0) _ (Pure 1)]))))
"#;
    let failures = core_io_mode_failures("empty sequence result", SOURCE);
    assert!(
        failures.is_empty(),
        "empty sequence result failures:\n{}",
        failures.join("\n\n")
    );
}

// spec: spec/10-io.md §10.3 + §10.12.8 — `>>`/mapping/conditional/sequence IO composition and both derived-timeout outcomes execute through a public `core.io` import; spec/11-stdlib.md §11 — public stdlib imports remain usable.
// defect: class=rc-miscount locus=public `core.io` composition boundary (internal source/locus unassigned) — the valid all-family program aborts with `STALE RC DEC` before its required zero result in REPL, `--run`, and `--link`.
#[test]
fn stdlib_core_io_public_scalar_driver_across_modes() {
    const SOURCE: &str = r#"
(import [core.io [>> map-io when-io unless-io sequence-io timeout]])
(import [collections.list [List Nil Cons]])
(import [primitives [IO Pure bind sleep Some None add-i64 eq-i64]])

(defn all-zero [xs]
  (match xs [Nil true
             (Cons x rest) (if (eq-i64 x 0) (all-zero rest) false)]))

(defn check-then []
  (bind (>> (Pure 1) (Pure 2)) (fn [x] (Pure (if (eq-i64 x 2) 0 1)))))
(defn check-map []
  (bind (map-io (fn [x] (add-i64 x 1)) (Pure 2))
        (fn [x] (Pure (if (eq-i64 x 3) 0 1)))))
(defn check-when-true []
  (bind (when-io true (Pure 4)) (fn [x] (Pure (if (eq-i64 x 4) 0 1)))))
(defn check-when-false []
  (bind (when-io false (Pure 99)) (fn [x] (Pure (if (eq-i64 x 0) 0 1)))))
(defn check-unless-true []
  (bind (unless-io true (Pure 99)) (fn [x] (Pure (if (eq-i64 x 0) 0 1)))))
(defn check-unless-false []
  (bind (unless-io false (Pure 5)) (fn [x] (Pure (if (eq-i64 x 5) 0 1)))))
(defn check-empty-sequence []
  (bind (sequence-io :(List (IO Int)) Nil)
        (fn [xs] (match xs [Nil (Pure 0) _ (Pure 1)]))))
(defn check-ordered-sequence []
  (bind (sequence-io (Cons (Pure 1) (Cons (Pure 2) (Cons (Pure 3) Nil))))
        (fn [xs] (match xs [(Cons a rest-a)
                             (match rest-a [(Cons b rest-b)
                                           (match rest-b [(Cons c rest-c)
                                                         (match rest-c [Nil (Pure (if (eq-i64 a 1) (if (eq-i64 b 2) (if (eq-i64 c 3) 0 1) 1) 1))
                                                                        _ (Pure 1)])
                                                         _ (Pure 1)])
                                           _ (Pure 1)])
                             _ (Pure 1)]))))
(defn check-fast-timeout []
  (bind (timeout 100 (Pure 9))
        (fn [r] (match r [(Some v) (Pure (if (eq-i64 v 9) 0 1)) None (Pure 1)]))))
(defn check-timed-timeout []
  (bind (timeout 10 (sleep 1000))
        (fn [r] (match r [None (Pure 0) (Some _) (Pure 1)]))))

(defn main []
  (bind (sequence-io (Cons (check-then)
                      (Cons (check-map)
                      (Cons (check-when-true)
                      (Cons (check-when-false)
                      (Cons (check-unless-true)
                      (Cons (check-unless-false)
                      (Cons (check-empty-sequence)
                      (Cons (check-ordered-sequence)
                      (Cons (check-fast-timeout)
                      (Cons (check-timed-timeout) Nil)))))))))))
        (fn [results] (Pure (if (all-zero results) 0 1)))))
"#;
    let repl = stdlib_repl(&format!("{SOURCE}(main)\n"));
    let run = Cranelisp::new()
        .use_workspace_stdlib_for_stdlib_conformance_only()
        .run("user.cl")
        .user(SOURCE)
        .timeout(Duration::from_secs(90))
        .output();
    let link = Cranelisp::new()
        .use_workspace_stdlib_for_stdlib_conformance_only()
        .link_then_run("user.cl")
        .user(SOURCE)
        .timeout(Duration::from_secs(90))
        .output();

    let mut failures = Vec::new();
    for (mode, expected_repl_value, out) in [
        ("REPL", true, repl),
        ("--run", false, run),
        ("--link", false, link),
    ] {
        let combined = format!("{}\n{}", out.stdout, out.stderr);
        let mode_succeeds = if expected_repl_value {
            out.status.success() && combined.contains(":primitives/Int 0")
        } else {
            out.status.code() == Some(0)
        };
        if !mode_succeeds {
            failures.push(format!(
                "public core.io scalar driver {mode}: expected REPL Int 0 or batch exit 0; \\
                 status={:?}\nstdout:\n{}\nstderr:\n{}",
                out.status.code(),
                out.stdout,
                out.stderr
            ));
        }
    }
    assert!(
        failures.is_empty(),
        "public core.io scalar driver failures:\n{}",
        failures.join("\n\n")
    );
}

// This control preserves the public imports, actions, order, values, and final
// zero observation above. It changes only the outer aggregation from
// `sequence-io` to explicit nested `bind` calls.
// spec: spec/10-io.md §10.3 + §10.12.8 — the same public IO composition executes through a public `core.io` import; spec/11-stdlib.md §11 — public stdlib imports remain usable.
#[test]
fn stdlib_core_io_nested_bind_outer_aggregation_control_across_modes() {
    const SOURCE: &str = r#"
(import [core.io [>> map-io when-io unless-io sequence-io timeout]])
(import [collections.list [List Nil Cons]])
(import [primitives [IO Pure bind sleep Some None add-i64 eq-i64]])

(defn all-zero [xs]
  (match xs [Nil true
             (Cons x rest) (if (eq-i64 x 0) (all-zero rest) false)]))

(defn check-then []
  (bind (>> (Pure 1) (Pure 2)) (fn [x] (Pure (if (eq-i64 x 2) 0 1)))))
(defn check-map []
  (bind (map-io (fn [x] (add-i64 x 1)) (Pure 2))
        (fn [x] (Pure (if (eq-i64 x 3) 0 1)))))
(defn check-when-true []
  (bind (when-io true (Pure 4)) (fn [x] (Pure (if (eq-i64 x 4) 0 1)))))
(defn check-when-false []
  (bind (when-io false (Pure 99)) (fn [x] (Pure (if (eq-i64 x 0) 0 1)))))
(defn check-unless-true []
  (bind (unless-io true (Pure 99)) (fn [x] (Pure (if (eq-i64 x 0) 0 1)))))
(defn check-unless-false []
  (bind (unless-io false (Pure 5)) (fn [x] (Pure (if (eq-i64 x 5) 0 1)))))
(defn check-empty-sequence []
  (bind (sequence-io :(List (IO Int)) Nil)
        (fn [xs] (match xs [Nil (Pure 0) _ (Pure 1)]))))
(defn check-ordered-sequence []
  (bind (sequence-io (Cons (Pure 1) (Cons (Pure 2) (Cons (Pure 3) Nil))))
        (fn [xs] (match xs [(Cons a rest-a)
                             (match rest-a [(Cons b rest-b)
                                           (match rest-b [(Cons c rest-c)
                                                         (match rest-c [Nil (Pure (if (eq-i64 a 1) (if (eq-i64 b 2) (if (eq-i64 c 3) 0 1) 1) 1))
                                                                        _ (Pure 1)])
                                                         _ (Pure 1)])
                                           _ (Pure 1)])
                             _ (Pure 1)]))))
(defn check-fast-timeout []
  (bind (timeout 100 (Pure 9))
        (fn [r] (match r [(Some v) (Pure (if (eq-i64 v 9) 0 1)) None (Pure 1)]))))
(defn check-timed-timeout []
  (bind (timeout 10 (sleep 1000))
        (fn [r] (match r [None (Pure 0) (Some _) (Pure 1)]))))

(defn main []
  (bind (check-then)
        (fn [then-result]
          (bind (check-map)
                (fn [map-result]
                  (bind (check-when-true)
                        (fn [when-true-result]
                          (bind (check-when-false)
                                (fn [when-false-result]
                                  (bind (check-unless-true)
                                        (fn [unless-true-result]
                                          (bind (check-unless-false)
                                                (fn [unless-false-result]
                                                  (bind (check-empty-sequence)
                                                        (fn [empty-sequence-result]
                                                          (bind (check-ordered-sequence)
                                                                (fn [ordered-sequence-result]
                                                                  (bind (check-fast-timeout)
                                                                        (fn [fast-timeout-result]
                                                                          (bind (check-timed-timeout)
                                                                                (fn [timed-timeout-result]
                                                                                  (Pure (if (all-zero (Cons then-result
                                                                                                            (Cons map-result
                                                                                                            (Cons when-true-result
                                                                                                            (Cons when-false-result
                                                                                                            (Cons unless-true-result
                                                                                                            (Cons unless-false-result
                                                                                                            (Cons empty-sequence-result
                                                                                                            (Cons ordered-sequence-result
                                                                                                            (Cons fast-timeout-result
                                                                                                            (Cons timed-timeout-result Nil))))))))))) 0 1)))))))))))))))))))))
))
"#;
    let repl = stdlib_repl(&format!("{SOURCE}(main)\n"));
    let run = Cranelisp::new()
        .use_workspace_stdlib_for_stdlib_conformance_only()
        .run("user.cl")
        .user(SOURCE)
        .timeout(Duration::from_secs(90))
        .output();
    let link = Cranelisp::new()
        .use_workspace_stdlib_for_stdlib_conformance_only()
        .link_then_run("user.cl")
        .user(SOURCE)
        .timeout(Duration::from_secs(90))
        .output();

    let mut failures = Vec::new();
    for (mode, expected_repl_value, out) in [
        ("REPL", true, repl),
        ("--run", false, run),
        ("--link", false, link),
    ] {
        let combined = format!("{}\n{}", out.stdout, out.stderr);
        let mode_succeeds = if expected_repl_value {
            out.status.success() && combined.contains(":primitives/Int 0")
        } else {
            out.status.code() == Some(0)
        };
        if !mode_succeeds {
            failures.push(format!(
                "public core.io nested-bind control {mode}: expected REPL Int 0 or batch exit 0; \\
                 status={:?}\nstdout:\n{}\nstderr:\n{}",
                out.status.code(),
                out.stdout,
                out.stderr
            ));
        }
    }
    assert!(
        failures.is_empty(),
        "public core.io nested-bind control failures:\n{}",
        failures.join("\n\n")
    );
}

// The explicit `core.syntax` surface supplies macro authors with structural
// access to reader-folded annotations: predicate, optional annotation half, and
// one-layer subject-or-identity projection. The one macro below exercises a
// reader-folded argument, an ordinary argument, and a raw constructor control.
// spec: spec/09-macros.md §9.1.2 + §9.2 — macros receive `SexpAnnotated` for a reader-folded annotation and may return its subject as expansion output; spec/11-stdlib.md §11 — public stdlib helpers are reachable by explicit import.
#[test]
fn stdlib_core_syntax_annotated_helpers_macro_client_across_modes() {
    const SOURCE: &str = "(import [core.syntax [annotated? annotation unannotate]])\n(import [macros [SexpAnnotated SexpSym SexpInt]])\n(import [primitives [Pure Some None add-i64]])\n(defmacro annotation-client [x] (if (annotated? x) (match (annotation x) [(Some _) (unannotate x) None (SexpInt 90)]) (match (annotation x) [None (unannotate x) (Some _) (SexpInt 91)])))\n(defmacro raw-annotation-control [] (let [raw (SexpAnnotated (SexpSym \"Int\") (SexpInt 4))] (if (annotated? raw) (match (annotation raw) [(Some _) (unannotate raw) None (SexpInt 92)]) (SexpInt 93))))\n(defn main [] (Pure (add-i64 (add-i64 (annotation-client :Int 7) (annotation-client 8)) (raw-annotation-control))))\n";
    let repl = stdlib_repl(&format!("{SOURCE}(main)\n"));
    let run = Cranelisp::new()
        .use_workspace_stdlib_for_stdlib_conformance_only()
        .run("user.cl")
        .user(SOURCE)
        .timeout(Duration::from_secs(90))
        .output();
    let link = Cranelisp::new()
        .use_workspace_stdlib_for_stdlib_conformance_only()
        .link_then_run("user.cl")
        .user(SOURCE)
        .timeout(Duration::from_secs(90))
        .output();

    let mut failures = Vec::new();
    for (mode, expected_repl_value, out) in [
        ("REPL", true, repl),
        ("--run", false, run),
        ("--link", false, link),
    ] {
        let combined = format!("{}\n{}", out.stdout, out.stderr);
        let mode_succeeds = if expected_repl_value {
            out.status.success() && combined.contains(":primitives/Int 19")
        } else {
            out.status.code() == Some(19)
        };
        if !mode_succeeds {
            failures.push(format!(
                "annotated-Sexp macro client {mode}: expected REPL Int 19 or batch exit 19; \\
                 status={:?}\nstdout:\n{}\nstderr:\n{}",
                out.status.code(),
                out.stdout,
                out.stderr
            ));
        }
    }
    assert!(
        failures.is_empty(),
        "explicit core.syntax annotated-Sexp helper client failures:\n{}",
        failures.join("\n\n")
    );
}

// Q10 — derive macros on the omitted public shapes. Each subject runs in its
// own child so an abort or timeout is reported by the Rust harness.

// spec: spec/09-macros.md §9.3 + spec/05-definitions.md §5.2 +
// spec/07-traits.md §7.1 — derive-Eq compares every field of a two-field
// product.
#[test]
fn stdlib_derive_eq_two_field_product() {
    assert_stdlib_repl_result(
        "derive-Eq two-field product",
        "(import [derive [derive-Eq]])\n\
         (import [compare.eq [Eq = !=]])\n\
         (import [primitives [Int]])\n\
         (deftype Point [:Int x :Int y])\n\
         (derive-Eq (deftype Point [:Int x :Int y]))\n\
         (if (= (Point 1 2) (Point 1 2)) (!= (Point 1 2) (Point 1 3)) false)\n",
        ":primitives/Bool true",
    );
}

// spec: spec/09-macros.md §9.3 + spec/05-definitions.md §5.2 +
// spec/07-traits.md §7.1 — derive-Ord compares later fields when the preceding
// field is equal.
#[test]
fn stdlib_derive_ord_two_field_product() {
    assert_stdlib_repl_result(
        "derive-Ord two-field product",
        "(import [derive [derive-Ord]])\n\
         (import [compare.ord [Ord <]])\n\
         (import [primitives [Int]])\n\
         (deftype Point [:Int x :Int y])\n\
         (derive-Ord (deftype Point [:Int x :Int y]))\n\
         (< (Point 1 2) (Point 1 3))\n",
        ":primitives/Bool true",
    );
}

// spec: spec/09-macros.md §9.3 + spec/05-definitions.md §5.2 +
// spec/07-traits.md §7.1 — derive-Display renders both fields of a two-field
// product in declaration order.
#[test]
fn stdlib_derive_display_two_field_product() {
    assert_stdlib_repl_result(
        "derive-Display two-field product",
        "(import [derive [derive-Display]])\n\
         (import [text.display [Display show]])\n\
         (import [primitives [Int]])\n\
         (deftype Point [:Int x :Int y])\n\
         (derive-Display (deftype Point [:Int x :Int y]))\n\
         (show (Point 1 2))\n",
        ":primitives/String \"Point(1 2)\"",
    );
}

// spec: spec/09-macros.md §9.3 + spec/05-definitions.md §5.2 +
// spec/07-traits.md §7.1 — constructor declaration order determines Ord for a
// three-constructor nullary enum.
#[test]
fn stdlib_derive_ord_three_constructor_enum() {
    assert_stdlib_repl_result(
        "derive-Ord three-constructor enum",
        "(import [derive [derive-Ord]])\n\
         (import [compare.ord [Ord <]])\n\
         (deftype Rank Low Middle High)\n\
         (derive-Ord (deftype Rank Low Middle High))\n\
         (if (< Low Middle) (< Middle High) false)\n",
        ":primitives/Bool true",
    );
}

// spec: spec/09-macros.md §9.3 + spec/05-definitions.md §5.2 +
// spec/07-traits.md §7.1 — adjacent controls: every derive macro accepts one
// data field, while Eq and Display accept the same three-constructor enum shape
// used by the Ord subject.
#[test]
fn stdlib_derive_adjacent_arity_controls() {
    assert_stdlib_repl_result(
        "derive adjacent arity controls",
        "(import [derive [derive-Eq derive-Ord derive-Display]])\n\
         (import [compare.eq [Eq =]])\n\
         (import [compare.ord [Ord <]])\n\
         (import [text.display [Display show]])\n\
         (import [primitives [Int String str-eq]])\n\
         (deftype Level (Lvl [:Int n]))\n\
         (derive-Eq (deftype Level (Lvl [:Int n])))\n\
         (derive-Ord (deftype Level (Lvl [:Int n])))\n\
         (derive-Display (deftype Level (Lvl [:Int n])))\n\
         (deftype Colour Red Green Blue)\n\
         (derive-Eq (deftype Colour Red Green Blue))\n\
         (derive-Display (deftype Colour Red Green Blue))\n\
         (if (= (Lvl 1) (Lvl 1))\n\
             (if (< (Lvl 1) (Lvl 2))\n\
                 (if (str-eq (show (Lvl 1)) \"Lvl(1)\")\n\
                     (if (= Red Red) (str-eq (show Blue) \"Blue\") false)\n\
                     false)\n\
                 false)\n\
             false)\n",
        ":primitives/Bool true",
    );
}

// BD-M3 (reject cell) — `(def fmt/x 1)` via the stdlib `def` macro: a qualified
// head reaches the binder reject after expansion. RED today (silent-accept /
// incidental); flips at W3. The located span provenance shares the BD-M2 int
// re-anchoring seam (W4, FIXME 0650).
// spec: spec/05-definitions.md §5 + §5.7 — `def` expands to a native binder; a
// qualified head is rejected on the binder principle.
// defect: class=silent-accept locus=crates/cranelisp-frontend/src/ast_builder.rs (post-expansion binder reject, def macro route) found=S113 owner=/dev
#[test]
fn stdlib_def_qualified_head_rejected_binder_neg() {
    let out = stdlib_repl("(def fmt/x 1)\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.to_lowercase().contains("error"),
        "the stdlib `def` route with a qualified head `fmt/x` MUST be a compile-\
         time error (§5 binder principle reaches macro expansion); got:\n{c}"
    );
    assert!(
        !c.contains("undefined function") && !out.stdout.contains("user/fmt/x"),
        "the reject MUST NOT surface as an `undefined function` codegen leak nor \
         silently bind `user/fmt/x`; got:\n{c}"
    );
}

// BD-M3 (bare-head positive TWIN) — `(def x 1)` via the stdlib `def` macro binds
// normally; `x` reads back `:primitives/Int 1`. GREEN.
// spec: spec/05-definitions.md §5.7 — a bare `def` head binds normally.
#[test]
fn stdlib_def_bare_head_accepts_twin() {
    let out = stdlib_repl("(def x 1)\nx\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.contains(":primitives/Int 1"),
        "a bare `def x 1` head MUST bind and `x` read back `:primitives/Int 1`; \
         got:\n{c}"
    );
}

// BD-M3 (const reject cell) — the `const` macro route, same principle.
// spec: spec/05-definitions.md §5 + §5.6 — `const` expands to a native binder.
// defect: class=silent-accept locus=crates/cranelisp-frontend/src/ast_builder.rs (post-expansion binder reject, const macro route) found=S113 owner=/dev
#[test]
fn stdlib_const_qualified_head_rejected_binder_neg() {
    let out = stdlib_repl("(const fmt/PI 3)\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.to_lowercase().contains("error"),
        "the stdlib `const` route with a qualified head `fmt/PI` MUST be a compile-\
         time error (§5 binder principle); got:\n{c}"
    );
    assert!(
        !out.stdout.contains("user/fmt/PI"),
        "the qualified `const` head MUST NOT silently bind; got:\n{}",
        out.stdout
    );
}
