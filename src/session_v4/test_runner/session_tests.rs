//! Live-session cells for the shared runner's REPL clients and batch
//! bookkeeping (`design/int/test-runner.md` §10). Each builds a real session,
//! compiles through the ordinary eval or registration path and observes the
//! runner's output.

use std::path::Path;

use cranelisp_types::{CodegenBehaviour, ModuleFullPath};

use crate::session_v4::{CompilerSession, RunMode, SessionSettings};

fn session(root: &Path, run_mode: RunMode, lib_dirs: Vec<std::path::PathBuf>) -> CompilerSession {
    let mut s = CompilerSession::new(
        SessionSettings {
            no_color: true,
            no_cache: true,
            codegen_behaviour: CodegenBehaviour::InMemoryAndObject,
            priority_workers: 1,
            nice_workers: 0,
            run_mode,
        },
        root.to_path_buf(),
        "user",
    )
    .expect("test session bootstrap");
    s.set_lib_dirs(lib_dirs);
    s
}

fn repl_with(root: &Path, forms: &[&str]) -> CompilerSession {
    let mut s = session(root, RunMode::Repl, Vec::new());
    for form in std::iter::once(&"(import [primitives [*]])").chain(forms) {
        s.eval(form)
            .unwrap_or_else(|e| panic!("fixture form `{form}` must compile: {e}"));
    }
    s
}

/// Result lines of a report: `  <fq> ..... <outcome>`, as `(fq, outcome)`.
fn result_lines(report: &str) -> Vec<(String, String)> {
    report
        .lines()
        .filter_map(|line| {
            let (name, rest) = line.trim().split_once(' ')?;
            name.contains("/test-").then(|| {
                let outcome = rest.trim_start_matches(['.', ' ']);
                (name.to_string(), outcome.to_string())
            })
        })
        .collect()
}

// spec: repl/spec/16-test-discovery.md §16.2 Running Tests — an empty run's
// report is exactly `No tests found`, for `/run-tests`, `/run-tests <module>`
// and `/run-all-tests` alike (design §10 run row 7).
#[test]
fn repl_clients_report_no_tests_found_for_an_empty_run() {
    let root = tempfile::tempdir().unwrap();
    let s = repl_with(root.path(), &["(defn helper [] 1)"]);
    assert_eq!(s.handle_run_tests(""), "No tests found");
    assert_eq!(s.handle_run_tests("user"), "No tests found");
    assert_eq!(s.handle_run_all_tests(), "No tests found");
}

// spec: repl/spec/16-test-discovery.md §16.2 Running Tests — a failing test's
// `(Some reason)` is observed, then released exactly once (design §6.2; §10
// run row 2): the run leaves no runtime allocation behind.
#[test]
fn run_tests_releases_a_failing_tests_value() {
    let root = tempfile::tempdir().unwrap();
    let s = repl_with(root.path(), &[ALLOCATING_TEST]);
    let (report, allocated, released) = heap_traffic(|| s.handle_run_tests(""));
    assert_eq!(
        result_lines(&report),
        [("user/test-b".to_string(), "FAILED: boom".to_string())],
        "{report}"
    );
    assert!(
        allocated > 0,
        "the failing value is heap-allocated by the call"
    );
    assert_eq!(
        released, allocated,
        "every allocation made by the test run is released: {report}"
    );
}

// spec: repl/spec/16-test-discovery.md §16.1 Test Function Convention — a
// `test-` function whose scheme is not `(Fn [] (Option String))` is excluded
// and warned; an exact-typed sibling still runs (design §10 discovery row 2).
#[test]
fn run_tests_excludes_and_warns_a_mistyped_test() {
    let root = tempfile::tempdir().unwrap();
    let s = repl_with(
        root.path(),
        &[
            "(defn test-int [] 5)",
            "(defn test-ok [] (if true None (Some \"never\")))",
        ],
    );
    let report = s.handle_run_tests("");
    assert_eq!(
        result_lines(&report),
        [("user/test-ok".to_string(), "ok".to_string())],
        "{report}"
    );
    assert!(
        report
            .lines()
            .any(|l| l.contains("; warning:") && l.contains("user/test-int")),
        "the mistyped test is warned by its FQ name: {report}"
    );
}

// spec: repl/spec/16-test-discovery.md §16.2.2 `/run-all-tests` — a library
// module is excluded even when its lib directory lies inside the project root;
// a project module loaded through it is included (design §10 selection row 11).
#[test]
fn run_all_tests_excludes_a_library_module_inside_the_project() {
    let root = tempfile::tempdir().unwrap();
    let lib = root.path().join("lib");
    std::fs::create_dir_all(&lib).unwrap();
    std::fs::write(
        lib.join("lm.cl"),
        "(import [primitives [*]])\n(import [p [fp]])\n(defn fl [] (fp))\n\
         (defn test-lm [] (if true None (Some \"lm\")))\n",
    )
    .unwrap();
    std::fs::write(
        root.path().join("p.cl"),
        "(import [primitives [*]])\n(defn fp [] 5)\n\
         (defn test-p [] (if true None (Some \"p\")))\n",
    )
    .unwrap();
    let mut s = session(root.path(), RunMode::Repl, vec![lib]);
    s.eval("(import [lm [fl]])")
        .unwrap_or_else(|e| panic!("library import must compile: {e}"));
    let report = s.handle_run_all_tests();
    let names: Vec<String> = result_lines(&report).into_iter().map(|(n, _)| n).collect();
    assert_eq!(names, ["p/test-p"], "{report}");
}

/// Allocations and deallocations made while `f` runs.
fn heap_traffic<T>(f: impl FnOnce() -> T) -> (T, usize, usize) {
    let allocs = cranelisp_intrinsics::alloc::alloc_count();
    let deallocs = cranelisp_intrinsics::alloc::dealloc_count();
    let value = f();
    (
        value,
        cranelisp_intrinsics::alloc::alloc_count() - allocs,
        cranelisp_intrinsics::alloc::dealloc_count() - deallocs,
    )
}

const ALLOCATING_TEST: &str = "(defn test-b [] (Some (str-concat \"bo\" \"om\")))";

/// A `--test`-shaped session: the entry `user.cl` holds `forms`, compiled
/// through ordinary batch registration.
fn batch_with(root: &Path, forms: &[&str]) -> CompilerSession {
    let mut source = String::from("(import [primitives [*]])\n");
    for form in forms {
        source.push_str(form);
        source.push('\n');
    }
    std::fs::write(root.join("user.cl"), source).unwrap();
    let mut s = session(root, RunMode::Run, Vec::new());
    s.register_module("user").expect("entry compiles");
    s.wait_inmem_complete().expect("entry loads");
    s
}

// spec: design/int/test-runner.md §6.1 — a release target that cannot be
// resolved is `Err` from preparation, and no test body has run (§10 run
// row 6).
#[test]
fn unresolvable_release_target_fails_before_any_test_runs() {
    let root = tempfile::tempdir().unwrap();
    let s = batch_with(root.path(), &[ALLOCATING_TEST]);
    let (control, allocated, _) = heap_traffic(|| s.run_tests());
    let control = control.unwrap_or_else(|e| panic!("the unplanted run succeeds: {e}"));
    assert_eq!(control.exit_code(), 1, "{}", control.text());
    assert!(allocated > 0, "the control run executed the test body");

    s.shared
        .fresh_jit_drop_glues
        .retain(|(module, _), _| module.as_ref() != "user");
    let (planted, allocated, _) = heap_traffic(|| s.run_tests());
    let Err(error) = planted else {
        panic!("a missing release target must be refused before running");
    };
    assert!(error.to_string().contains("drop glue"), "{error}");
    assert_eq!(allocated, 0, "no test body ran");
}

// spec: repl/spec/16-test-discovery.md §16.6 Availability by Invocation Mode —
// `run_tests` refuses a program referencing `discover-tests` and runs no test
// (design/int/test-runner.md §10 refusal row 3).
#[test]
fn run_tests_refuses_a_discover_tests_reference_before_running() {
    let forms = ["(defn helper [] (discover-tests []))", ALLOCATING_TEST];
    let root = tempfile::tempdir().unwrap();
    let s = batch_with(root.path(), &forms);
    let (refused, allocated, _) = heap_traffic(|| s.run_tests());
    let Err(error) = refused else {
        panic!("a program referencing discover-tests must be refused");
    };
    let message = error.to_string();
    for token in ["discover-tests", "user/helper", "REPL", "--test"] {
        assert!(message.contains(token), "names `{token}`: {message}");
    }
    assert_eq!(allocated, 0, "no test body ran");

    let repl_root = tempfile::tempdir().unwrap();
    let repl = repl_with(repl_root.path(), &forms);
    assert!(
        repl.handle_run_tests("").contains("FAILED: boom"),
        "the REPL runner applies no refusal"
    );
}

// spec: repl/spec/00-cli-invocation.md §0.5.5 Error Handling — rule 2 is about
// absence: under `--test` an existing entry with no tests is an empty run.
// Entry registration refuses a missing file (`lifecycle::entry_registration_tests`).
#[test]
fn run_tests_reports_an_existing_entry_without_tests_as_an_empty_run() {
    let root = tempfile::tempdir().unwrap();
    let s = batch_with(root.path(), &[]);
    let report = s
        .run_tests()
        .unwrap_or_else(|e| panic!("an entry without tests is an empty run: {e}"));
    assert_eq!(report.text(), "No tests found");
    assert_eq!(report.exit_code(), 0);
}

// spec: design/int/test-runner.md §4.1 — the fresh dependency prologue records
// a module's source file with introspection off, so batch classification reads
// the same fact as the REPL (§10 selection row 8).
#[test]
fn batch_dependency_load_records_its_file_path() {
    let root = tempfile::tempdir().unwrap();
    std::fs::write(root.path().join("a.cl"), "(defn fa [] 1)\n").unwrap();
    std::fs::write(
        root.path().join("user.cl"),
        "(import [a [fa]])\n(defn g [] (fa))\n",
    )
    .unwrap();
    let mut s = session(root.path(), RunMode::Run, Vec::new());
    s.register_module("user").expect("entry compiles");
    s.wait_inmem_complete().expect("entry loads");
    let recorded = s
        .shared
        .typecheck_products
        .get(&ModuleFullPath::from("a"))
        .and_then(|tp| tp.file_path.clone());
    assert_eq!(recorded, Some(root.path().join("a.cl")));
}
