//! The shared test runner: `--test`, `/run-tests` and `/run-all-tests`.
//!
//! Requirements: `repl/spec/00-cli-invocation.md` §0.2.2 and
//! `repl/spec/16-test-discovery.md` §§16.1, 16.2 and 16.6. Cells TR-1 to TR-6
//! are allocated in `tests/plan/s122-evidence-delta.md` §"Shared test runner
//! and `--test`".
//!
//! The report is required on stdout, not required to be alone there, so the
//! cells assert the presence and order of report lines, never exclusivity.

#[path = "helpers/mod.rs"]
mod helpers;

use std::collections::BTreeSet;

use helpers::e2e::{CrOutput, Cranelisp, repl_output_lines};

// =============================================================================
// Report reading
// =============================================================================

/// One per-test report line: `  <fq-name> ....... <outcome>`, trimmed.
#[derive(Debug, Clone, PartialEq, Eq)]
struct ResultLine {
    name: String,
    line: String,
}

/// Per-test result lines in output order. A result line's first token is an
/// FQ `module/test-…` name and its remainder, after the dot padding, is `ok`,
/// `FAILED: …` or `PANIC: …` (§16.2 Report).
fn result_lines(lines: &[String]) -> Vec<ResultLine> {
    lines
        .iter()
        .filter_map(|raw| {
            let line = raw.trim();
            let (name, rest) = line.split_once(char::is_whitespace)?;
            if !name.contains("/test-") {
                return None;
            }
            let outcome = rest.trim_start().trim_start_matches('.').trim_start();
            (outcome == "ok" || outcome.starts_with("FAILED:") || outcome.starts_with("PANIC:"))
                .then(|| ResultLine {
                    name: name.to_string(),
                    line: line.to_string(),
                })
        })
        .collect()
}

/// Summary lines (`N passed…`) with any trailing ` in <time>` masked.
fn summaries(lines: &[String]) -> Vec<String> {
    lines
        .iter()
        .map(|l| l.trim())
        .filter(|l| {
            l.split_once(' ')
                .is_some_and(|(n, rest)| n.parse::<u32>().is_ok() && rest.starts_with("passed"))
        })
        .map(|l| l.split(" in ").next().unwrap_or(l).to_string())
        .collect()
}

fn stdout_lines(out: &CrOutput) -> Vec<String> {
    out.stdout.lines().map(str::to_string).collect()
}

fn names(results: &[ResultLine]) -> BTreeSet<String> {
    results.iter().map(|r| r.name.clone()).collect()
}

fn set(items: &[&str]) -> BTreeSet<String> {
    items.iter().map(|s| s.to_string()).collect()
}

fn has_line(lines: &[String], exact: &str) -> bool {
    lines.iter().any(|l| l.trim() == exact)
}

/// Collects every failed observation so one run logs the complete RED reason.
#[derive(Default)]
struct Checks(Vec<String>);

impl Checks {
    fn check(&mut self, ok: bool, what: impl Into<String>) {
        if !ok {
            self.0.push(what.into());
        }
    }

    fn finish(self, out: &[&CrOutput]) {
        if self.0.is_empty() {
            return;
        }
        let mut msg = format!("{} failed observation(s):\n", self.0.len());
        for f in &self.0 {
            msg.push_str(&format!("  - {f}\n"));
        }
        for (i, o) in out.iter().enumerate() {
            msg.push_str(&format!(
                "--- output {i}: exit {:?}\n--- stdout:\n{}\n--- stderr:\n{}\n",
                o.status.code(),
                o.stdout,
                o.stderr
            ));
        }
        panic!("{msg}");
    }
}

/// No report of any shape: no result line, no summary and no empty-run line.
fn no_report(lines: &[String]) -> bool {
    result_lines(lines).is_empty()
        && summaries(lines).is_empty()
        && !has_line(lines, "No tests found")
}

// =============================================================================
// TR-1 — execution, report and parity (§16.1, §16.2, §0.2.2)
// =============================================================================

/// No `main`. Exact-typed tests in FQ order: pass, fail, panic, pass; then
/// `test-e`, the bare-`None` shape that typecheck pins to exactly
/// `(Fn [] (Option String))` (design/typecheck/monomorphisation.md §3.2), so it
/// runs and passes; and `test-f`, mistyped `(Fn [] (Option Int))`.
const TR1_USER: &str = "(import [primitives [*]])\n\
    (defn test-a [] (if true None (Some \"never\")))\n\
    (defn test-b [] (Some \"boom\"))\n\
    (defn test-c [] (if (eq-i64 (div-i64 1 0) 0) None (Some \"unreached\")))\n\
    (defn test-d [] (if true None (Some \"never\")))\n\
    (defn test-e [] None)\n\
    (defn test-f [] (Some 1))\n";

const TR1_ORDER: [&str; 5] = [
    "user/test-a",
    "user/test-b",
    "user/test-c",
    "user/test-d",
    "user/test-e",
];

fn tr1_outcomes_hold(checks: &mut Checks, leg: &str, results: &[ResultLine]) {
    let order: Vec<&str> = results.iter().map(|r| r.name.as_str()).collect();
    checks.check(
        order == TR1_ORDER,
        format!("{leg}: result lines in FQ order are exactly {TR1_ORDER:?}; got {order:?}"),
    );
    let line = |n: &str| {
        results
            .iter()
            .find(|r| r.name == n)
            .map(|r| r.line.as_str())
            .unwrap_or("")
    };
    checks.check(
        line("user/test-a").ends_with(" ok"),
        format!("{leg}: test-a ends in `ok`"),
    );
    checks.check(
        line("user/test-b").ends_with("FAILED: boom"),
        format!("{leg}: test-b ends in `FAILED: boom`"),
    );
    checks.check(
        line("user/test-c").contains("PANIC:") && line("user/test-c").contains("division by zero"),
        format!("{leg}: test-c reports `PANIC:` with the division-by-zero message"),
    );
    checks.check(
        line("user/test-d").ends_with(" ok"),
        format!("{leg}: test-d runs after the failure and the panic, and ends in `ok`"),
    );
    checks.check(
        line("user/test-e").ends_with(" ok"),
        format!("{leg}: the pinned bare-`None` test-e ends in `ok`"),
    );
}

// spec: repl/spec/16-test-discovery.md §16.2 Running Tests — execution continues
// past a failure and a panic; FQ result lines and a summary; a mistyped test is
// excluded and warned (§16.1); `--test` writes the report to stdout, warnings to
// stderr, exits 1 on any failure, and needs no `main` (§0.2.2); `/run-tests`
// prints the same result lines and summary (one runner, timing masked).
#[test]
fn test_mode_runs_every_test_reports_fq_lines_and_matches_run_tests() {
    let cli = Cranelisp::new().user(TR1_USER).test("user.cl").output();
    let repl = Cranelisp::new()
        .user(TR1_USER)
        .repl()
        .stdin("/run-tests\n")
        .output();

    let mut checks = Checks::default();
    let cli_lines = stdout_lines(&cli);
    let cli_results = result_lines(&cli_lines);
    checks.check(
        cli.status.code() == Some(1),
        "--test: exit 1 when a test failed or panicked",
    );
    tr1_outcomes_hold(&mut checks, "--test", &cli_results);
    checks.check(
        summaries(&cli_lines) == ["3 passed, 2 failed"],
        format!(
            "--test: one summary `3 passed, 2 failed`; got {:?}",
            summaries(&cli_lines)
        ),
    );
    checks.check(
        cli.stderr.contains("user/test-f"),
        "--test: stderr warns about the mistyped test by its FQ name `user/test-f`",
    );

    let repl_lines = repl_output_lines(&repl.stdout);
    let repl_results = result_lines(&repl_lines);
    tr1_outcomes_hold(&mut checks, "/run-tests", &repl_results);
    checks.check(
        !repl_results.is_empty() && repl_results == cli_results,
        "/run-tests: result lines are identical to --test's",
    );
    checks.check(
        !summaries(&repl_lines).is_empty() && summaries(&repl_lines) == summaries(&cli_lines),
        format!(
            "/run-tests: summary equals --test's with timing masked; got {:?}",
            summaries(&repl_lines)
        ),
    );
    checks.check(
        repl_lines
            .iter()
            .map(String::as_str)
            .chain(repl.stderr.lines())
            .any(|l| l.to_lowercase().contains("warning") && l.contains("user/test-f")),
        "/run-tests: a warning line names the mistyped `user/test-f`",
    );
    checks.finish(&[&cli, &repl]);
}

// =============================================================================
// TR-2 and TR-3 — `main` is not called; chain selection (§0.2.2)
// =============================================================================

/// Entry `user`: imports `a`, which exports from `b`; `b` declares `(mod c)`;
/// the entry declares an unimported `(mod- priv)`; a project-root prelude.
/// Loaded but outside the chain: `al` (alias-only import, loaded through its
/// alias), `nul` (null import, loaded by an FQ reference) and `fq` (FQ
/// auto-load only). Every module defines one passing test. `main` is a bare
/// `Int` that panics if called.
fn tr3_project() -> Cranelisp {
    let module = |f: &str, t: &str| {
        format!(
            "(import [primitives [*]])\n(defn {f} [] 3)\n\
             (defn test-{t} [] (if true None (Some \"{t}\")))\n"
        )
    };
    Cranelisp::new()
        .user(
            "(import [primitives [*]])\n\
             (import [a [fa]])\n\
             (import [(al alx) []])\n\
             (import [nul []])\n\
             (mod- priv)\n\
             (defn test-entry [] (if true None (Some \"entry\")))\n\
             (defn use-others [] (add-i64 (alx/f) (add-i64 (nul/g) (fq/h))))\n\
             (defn main [] (div-i64 1 0))\n",
        )
        .file(
            "a.cl",
            "(import [primitives [*]])\n(export [b [fb]])\n(defn fa [] 1)\n\
             (defn test-a [] (if true None (Some \"a\")))\n",
        )
        .file(
            "b.cl",
            "(import [primitives [*]])\n(mod c)\n(defn fb [] 2)\n\
             (defn test-b [] (if true None (Some \"b\")))\n",
        )
        .file("b/c.cl", &module("fc", "c"))
        .file("user/priv.cl", &module("fp", "priv"))
        .file("al.cl", &module("f", "al"))
        .file("nul.cl", &module("g", "nul"))
        .file("fq.cl", &module("h", "fq"))
        .prelude(
            "(import [primitives [*]])\n\
             (defn test-prelude [] (if true None (Some \"prelude\")))\n",
        )
}

const TR3_SELECTED: [&str; 6] = [
    "a/test-a",
    "b.c/test-c",
    "b/test-b",
    "prelude/test-prelude",
    "user.priv/test-priv",
    "user/test-entry",
];

// spec: repl/spec/00-cli-invocation.md §0.2.2 Test Mode (`--test`) — the test
// modules are the entry module and the project modules reachable through
// non-empty `import`/`export` entries, declared submodules and the implicit
// prelude; not through an alias-only import, a null import or an FQ auto-load.
// The set is the same on a cache-restored rerun. TR-2: `main` is not called.
#[test]
fn test_mode_selects_exactly_the_import_chain_fresh_and_cached() {
    let fresh = tr3_project().test("user.cl").output();
    let mut checks = Checks::default();
    let fresh_names = names(&result_lines(&stdout_lines(&fresh)));
    checks.check(
        fresh_names == set(&TR3_SELECTED),
        format!("fresh: the selected set is exactly {TR3_SELECTED:?}; got {fresh_names:?}"),
    );
    // TR-2: a bare-Int `main` that panics is neither validated nor called.
    checks.check(
        fresh.status.code() == Some(0),
        "fresh: exit 0, every selected test passes",
    );
    checks.check(
        !fresh.stderr.contains("main") && !fresh.stderr.contains("division by zero"),
        "fresh: stderr names neither `main` nor `division by zero`",
    );
    let fresh_snapshot = (fresh.status, fresh.stdout.clone(), fresh.stderr.clone());

    let cached = fresh
        .run_again()
        .test("user.cl")
        .env("CRANELISP_MODULE_TRACE", "1")
        .output();
    let cached_names = names(&result_lines(&stdout_lines(&cached)));
    checks.check(
        cached_names == set(&TR3_SELECTED),
        format!("cached: the selected set is unchanged; got {cached_names:?}"),
    );
    checks.check(cached.status.code() == Some(0), "cached: exit 0");
    // The rerun is a cache restore: the chain's imported modules load from
    // `.cranelisp-cache/` (the `CRANELISP_MODULE_TRACE` cache-hit line).
    for module in ["a", "b"] {
        let hit = format!("module-trace: cache hit (.meta valid) for {module}");
        checks.check(
            cached.stderr.lines().any(|l| l.trim() == hit),
            format!("cached: stderr carries `{hit}`"),
        );
    }
    if !checks.0.is_empty() {
        eprintln!(
            "fresh run: exit {:?}\n--- stdout:\n{}\n--- stderr:\n{}",
            fresh_snapshot.0.code(),
            fresh_snapshot.1,
            fresh_snapshot.2
        );
    }
    checks.finish(&[&cached]);
}

// =============================================================================
// TR-4 — the library stop (§0.2.2, §16.2.2)
// =============================================================================

/// `lib/` is a lib directory inside the project. The entry imports library
/// module `lm`; `lm` declares child `kid` and imports project module `p`.
fn tr4_project() -> Cranelisp {
    Cranelisp::new()
        .lib_dir("lib")
        .user(
            "(import [primitives [*]])\n(import [lm [fl]])\n\
             (defn test-u [] (if true None (Some \"u\")))\n",
        )
        .file(
            "lib/lm.cl",
            "(import [primitives [*]])\n(import [p [fp]])\n(mod kid)\n\
             (defn fl [] (fp))\n\
             (defn test-lm [] (if true None (Some \"lm\")))\n",
        )
        .file(
            "lib/lm/kid.cl",
            "(import [primitives [*]])\n\
             (defn test-kid [] (if true None (Some \"kid\")))\n",
        )
        .file(
            "p.cl",
            "(import [primitives [*]])\n(defn fp [] 5)\n\
             (defn test-p [] (if true None (Some \"p\")))\n",
        )
}

// spec: repl/spec/00-cli-invocation.md §0.2.2 Test Mode (`--test`) — the chain
// stops at a library module, even one in a lib directory inside the project: the
// library module, its declared child, and a project module reachable only
// through it are not test modules; a lib-directory prelude brings no tests.
#[test]
fn test_mode_neg_chain_stops_at_library_modules_and_library_prelude() {
    let through_lib = tr4_project().test("user.cl").output();
    let lib_prelude = Cranelisp::new()
        .lib_dir("lib")
        .user(
            "(import [primitives [*]])\n\
             (defn test-u2 [] (if true None (Some \"u2\")))\n",
        )
        .file(
            "lib/prelude.cl",
            "(import [primitives [*]])\n\
             (defn test-libprelude [] (if true None (Some \"libprelude\")))\n",
        )
        .test("user.cl")
        .output();

    let mut checks = Checks::default();
    let got = names(&result_lines(&stdout_lines(&through_lib)));
    checks.check(
        got == set(&["user/test-u"]),
        format!("library stop: only `user/test-u` is reported; got {got:?}"),
    );
    checks.check(through_lib.status.code() == Some(0), "library stop: exit 0");
    let got = names(&result_lines(&stdout_lines(&lib_prelude)));
    checks.check(
        got == set(&["user/test-u2"]),
        format!("library prelude: only `user/test-u2` is reported; got {got:?}"),
    );
    checks.check(
        lib_prelude.status.code() == Some(0),
        "library prelude: exit 0",
    );
    checks.finish(&[&through_lib, &lib_prelude]);
}

// spec: repl/spec/16-test-discovery.md §16.2.2 `/run-all-tests` [R4] — loaded
// project modules are run and library modules are excluded, including a lib
// directory inside the project root: `lm` and its child are excluded while the
// project module `p`, loaded only through `lm`, is included.
#[test]
fn run_all_tests_neg_excludes_library_modules_under_the_project_root() {
    let out = tr4_project().repl().stdin("/run-all-tests\n").output();
    let got = names(&result_lines(&repl_output_lines(&out.stdout)));
    let mut checks = Checks::default();
    checks.check(
        got == set(&["p/test-p", "user/test-u"]),
        format!("`/run-all-tests` reports exactly p and user; got {got:?}"),
    );
    checks.finish(&[&out]);
}

// =============================================================================
// TR-5 — batch refusal of `discover-tests` (§16.6; replaces DT-1)
// =============================================================================

fn tr5_program(with_helper: bool) -> String {
    let helper = if with_helper {
        "(defn helper [] (discover-tests []))\n"
    } else {
        ""
    };
    format!(
        "(import [primitives [discover-tests Pure None Some]])\n\
         {helper}\
         (defn test-t [] (if true None (Some \"t\")))\n\
         (defn main [] (Pure 7))\n"
    )
}

fn discover_tests_lines(stderr: &str) -> Vec<String> {
    stderr
        .lines()
        .filter(|l| l.contains("discover-tests"))
        .map(str::to_string)
        .collect()
}

// spec: repl/spec/16-test-discovery.md §16.6 Availability by Invocation Mode
// [S122] — an uncalled function referencing `discover-tests` is refused under
// `--run`, `--link` and `--test` before anything runs or is written, with one
// diagnostic naming the primitive, the referencing function, the REPL and
// `--test`; an import alone is not a reference.
#[test]
fn batch_modes_neg_refuse_uncalled_discover_tests_reference_with_one_diagnostic() {
    let program = tr5_program(true);
    let run = Cranelisp::new()
        .file("main.cl", &program)
        .run("main.cl")
        .output();
    let link = Cranelisp::new()
        .file("main.cl", &program)
        .link("main.cl")
        .output();
    let test = Cranelisp::new()
        .file("main.cl", &program)
        .test("main.cl")
        .output();

    let mut checks = Checks::default();
    for (mode, out) in [("--run", &run), ("--link", &link), ("--test", &test)] {
        checks.check(
            out.status.code() == Some(1),
            format!("{mode}: exit 1 (not main's 7)"),
        );
        let named = ["discover-tests", "helper", "REPL", "--test"];
        checks.check(
            named.iter().all(|n| out.stderr.contains(n)),
            format!("{mode}: stderr names each of {named:?}"),
        );
    }
    let run_diag = discover_tests_lines(&run.stderr);
    checks.check(
        !run_diag.is_empty()
            && run_diag == discover_tests_lines(&link.stderr)
            && run_diag == discover_tests_lines(&test.stderr),
        "the `discover-tests` diagnostic lines are identical in all three modes",
    );
    checks.check(!link.tmp_exists("main"), "--link: no executable is written");
    checks.check(
        no_report(&stdout_lines(&test)),
        "--test: no result line, summary or `No tests found`",
    );
    checks.finish(&[&run, &link, &test]);
}

// spec: repl/spec/16-test-discovery.md §16.6 Availability by Invocation Mode
// [S122] — an `import` of `discover-tests` alone is not a reference and is not
// rejected: `--run` runs `main` and `--test` runs the tests.
#[test]
fn batch_modes_accept_import_only_of_discover_tests() {
    let program = tr5_program(false);
    let run = Cranelisp::new()
        .file("main.cl", &program)
        .run("main.cl")
        .output();
    let test = Cranelisp::new()
        .file("main.cl", &program)
        .test("main.cl")
        .output();

    let mut checks = Checks::default();
    checks.check(run.status.code() == Some(7), "--run: exit 7 from `main`");
    checks.check(test.status.code() == Some(0), "--test: exit 0");
    let lines = stdout_lines(&test);
    let got = names(&result_lines(&lines));
    checks.check(
        got == set(&["main/test-t"]),
        format!("--test: reports `main/test-t`; got {got:?}"),
    );
    checks.check(
        summaries(&lines) == ["1 passed"],
        format!("--test: summary `1 passed`; got {:?}", summaries(&lines)),
    );
    checks.finish(&[&run, &test]);
}

// spec: repl/spec/16-test-discovery.md §16.6 Availability by Invocation Mode
// [S122] — the refusal also covers a function body restored from the module
// cache: a REPL session caches `h`, then `--run` of an entry importing only
// `h`'s pure `label` is refused (design/int/test-runner.md §9 falsifier).
#[test]
fn run_neg_refuses_discover_tests_reference_restored_from_cache() {
    let h = "(import [primitives [discover-tests add-i64]])\n\
             (defn finder [] (discover-tests []))\n\
             (defn label [x] (add-i64 x 0))\n";
    let warm = Cranelisp::new()
        .file("h.cl", h)
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n(import [h [label]])\n\
             (defn main [] (Pure (label 7)))\n",
        )
        .repl()
        .stdin("(import [h [label]])\n")
        .output();
    let warm_stdout = warm.stdout.clone();
    let run = warm
        .run_again()
        .run("main.cl")
        .env("CRANELISP_MODULE_TRACE", "1")
        .output();

    let mut checks = Checks::default();
    let hit = "module-trace: cache hit (.meta valid) for h";
    checks.check(
        run.stderr.lines().any(|l| l.trim() == hit),
        format!("precondition: `h` is restored from the REPL-warmed cache (`{hit}`)"),
    );
    checks.check(run.status.code() == Some(1), "--run: exit 1 (not main's 7)");
    // Exit 1 alone does not discriminate: an unrefused restored body can also
    // fail at load with an unresolved-symbol error. The §16.6 diagnostic does.
    let named = ["discover-tests", "finder", "REPL", "--test"];
    checks.check(
        named.iter().all(|n| run.stderr.contains(n)),
        format!("--run: stderr names each of {named:?}"),
    );
    if !checks.0.is_empty() {
        eprintln!("warming REPL stdout:\n{warm_stdout}");
    }
    checks.finish(&[&run]);
}

// =============================================================================
// TR-6 — process conventions (§0.2.2, §0.2.1.1, §0.5.5)
// =============================================================================

const ONE_TEST: &str = "(import [primitives [*]])\n\
    (defn test-one [] (if true None (Some \"one\")))\n";

// spec: repl/spec/00-cli-invocation.md §0.2.2 Test Mode (`--test`) — `--test`
// with `--run` or `--link`, and with `-o` (§0.2.1.1), is a usage error: exit 1,
// the usage hint on stderr, and no test runs.
#[test]
fn test_mode_neg_combined_with_run_link_or_output_is_usage_error() {
    for extra in [&["--run"][..], &["--link"][..], &["-o", "x"][..]] {
        let mut cr = Cranelisp::new().user(ONE_TEST).test("user.cl");
        for flag in extra {
            cr = cr.cli_flag(flag);
        }
        let out = cr.output();
        let mut checks = Checks::default();
        checks.check(out.status.code() == Some(1), format!("{extra:?}: exit 1"));
        checks.check(
            out.stderr.contains("usage:"),
            format!("{extra:?}: usage hint on stderr"),
        );
        checks.check(
            no_report(&stdout_lines(&out)),
            format!("{extra:?}: no report"),
        );
        checks.check(
            !out.tmp_exists("x") && !out.tmp_exists("user"),
            format!("{extra:?}: no artifact"),
        );
        checks.finish(&[&out]);
    }
}

// spec: repl/spec/00-cli-invocation.md §0.5.5 Error Handling [R4 S52] — under
// `--test` a missing entry source file is an error on stderr naming it, exit 1;
// it is not an empty run.
#[test]
fn test_mode_neg_missing_entry_file_errors_without_report() {
    let out = Cranelisp::new().test("nope.cl").output();
    let mut checks = Checks::default();
    checks.check(out.status.code() == Some(1), "exit 1");
    checks.check(
        out.stderr.contains("nope"),
        "stderr names the missing `nope.cl`",
    );
    checks.check(
        no_report(&stdout_lines(&out)),
        "no report, and not `No tests found`",
    );
    checks.finish(&[&out]);
}

// spec: repl/spec/00-cli-invocation.md §0.2.2 Test Mode (`--test`) — on
// compilation failure the error goes to stderr, no test runs and the exit
// status is non-zero.
#[test]
fn test_mode_neg_compile_error_runs_no_test() {
    let out = Cranelisp::new()
        .user(&format!("{ONE_TEST}(defn bad [] (add-i64 1 \"s\"))\n"))
        .test("user.cl")
        .output();
    let mut checks = Checks::default();
    checks.check(!out.status.success(), "non-zero exit");
    checks.check(
        !out.stderr.trim().is_empty(),
        "the compile error is on stderr",
    );
    checks.check(
        no_report(&stdout_lines(&out)),
        "no test runs and no report is written",
    );
    checks.finish(&[&out]);
}

// spec: repl/spec/16-test-discovery.md §16.2 Running Tests — an empty run's
// report is the single line `No tests found`; `--test` exits 0 (§0.2.2).
#[test]
fn test_mode_empty_run_reports_no_tests_found_and_exits_zero() {
    let out = Cranelisp::new()
        .user("(import [primitives [*]])\n(defn f [] 1)\n")
        .test("user.cl")
        .output();
    let mut checks = Checks::default();
    checks.check(out.status.code() == Some(0), "exit 0");
    checks.check(
        has_line(&stdout_lines(&out), "No tests found"),
        "stdout carries the line `No tests found`",
    );
    checks.finish(&[&out]);
}
