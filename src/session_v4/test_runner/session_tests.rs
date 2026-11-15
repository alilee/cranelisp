//! Live-session cells for the test child's engine and batch bookkeeping
//! (`design/int/test-runner.md` §10). Each builds a real session, compiles
//! through the ordinary eval or registration path and reads the records the
//! engine writes. The supervisor's process launch is the end-to-end cells'.

use std::path::Path;

use cranelisp_types::{CodegenBehaviour, CranelispError, FQSymbol, ModuleFullPath};

use super::child::{Record, read_records};
use super::run::TestOutcome;
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

/// What one engine run recorded: its warnings and `(test, outcome)` pairs.
#[derive(Debug, Default)]
struct ChildRun {
    warnings: Vec<String>,
    outcomes: Vec<(String, TestOutcome)>,
    ended: bool,
}

/// Run the child engine over `modules` (the REPL selection) or the entry
/// chain, and read back what it recorded.
fn run_child(
    s: &CompilerSession,
    modules: Option<&[ModuleFullPath]>,
    resume_after: Option<&FQSymbol>,
) -> Result<ChildRun, CranelispError> {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("records");
    s.run_tests(&path, modules, resume_after)?;
    let mut run = ChildRun::default();
    let mut open = None;
    for record in read_records(&path).expect("the records decode") {
        match record {
            Record::Warning(message) => run.warnings.push(message),
            Record::Start(id) => open = Some(id.to_string()),
            Record::Outcome(outcome) => run.outcomes.push((open.take().unwrap(), outcome)),
            Record::End => run.ended = true,
        }
    }
    Ok(run)
}

fn user() -> Vec<ModuleFullPath> {
    vec![ModuleFullPath::from("user")]
}

fn fail(reason: &str) -> TestOutcome {
    TestOutcome::Fail {
        reason: reason.to_string(),
    }
}

// spec: repl/spec/16-test-discovery.md §16.2 Running Tests — an empty
// selection runs nothing and completes, for a module selection and for the
// `/run-all-tests` selection alike (design §10 run row 7).
#[test]
fn an_empty_selection_records_no_test_and_completes() {
    let root = tempfile::tempdir().unwrap();
    let s = repl_with(root.path(), &["(defn helper [] 1)"]);
    for modules in [user(), s.selection_inputs().non_library_modules()] {
        let run = run_child(&s, Some(&modules), None).unwrap();
        assert!(run.outcomes.is_empty() && run.ended, "{run:?}");
    }
}

// spec: repl/spec/16-test-discovery.md §16.2 Running Tests — a failing test's
// `(Some reason)` is observed, then released exactly once (design §6.2; §10
// run row 2): the run leaves no runtime allocation behind.
#[test]
fn run_tests_releases_a_failing_tests_value() {
    let root = tempfile::tempdir().unwrap();
    let s = repl_with(root.path(), &[ALLOCATING_TEST]);
    let (run, allocated, released) = heap_traffic(|| run_child(&s, Some(&user()), None).unwrap());
    assert_eq!(run.outcomes, [("user/test-b".to_string(), fail("boom"))]);
    assert!(
        allocated > 0,
        "the failing value is heap-allocated by the call"
    );
    assert_eq!(
        released, allocated,
        "every allocation made by the test run is released"
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
    let run = run_child(&s, Some(&user()), None).unwrap();
    assert_eq!(
        run.outcomes,
        [("user/test-ok".to_string(), TestOutcome::Pass)]
    );
    assert!(
        run.warnings.len() == 1 && run.warnings[0].contains("user/test-int"),
        "the mistyped test is warned once by its FQ name: {run:?}"
    );
}

// spec: design/int/test-runner.md §10 test-child row 5 — a resume point runs
// only the eligible tests that sort after it.
#[test]
fn a_resume_point_runs_only_the_tests_after_it() {
    let root = tempfile::tempdir().unwrap();
    let s = batch_with(
        root.path(),
        &[
            "(defn test-a [] None)",
            "(defn test-b [] None)",
            "(defn test-c [] None)",
        ],
    );
    let after = FQSymbol {
        module: ModuleFullPath::from("user"),
        symbol: cranelisp_types::Symbol::from("test-a"),
    };
    let run = run_child(&s, None, Some(&after)).unwrap();
    let names: Vec<_> = run.outcomes.iter().map(|(name, _)| name.as_str()).collect();
    assert_eq!(names, ["user/test-b", "user/test-c"]);
    let all = run_child(&s, None, None).unwrap();
    assert_eq!(
        all.outcomes.len(),
        3,
        "control: no resume point runs every test"
    );
}

// spec: design/int/test-runner.md §10 test-child row 8 — a REPL child, which
// runs with a module selection and without the object cache, writes nothing
// into the project: no cache directory and no backing file.
#[test]
fn a_repl_child_writes_no_project_file() {
    let root = tempfile::tempdir().unwrap();
    let s = batch_with(root.path(), &[ALLOCATING_TEST]);
    let before = project_files(root.path());
    let run = run_child(&s, Some(&user()), None).unwrap();
    assert_eq!(run.outcomes.len(), 1);
    s.wait_object_complete().unwrap();
    assert_eq!(project_files(root.path()), before);
    assert_eq!(before, ["user.cl"]);
}

fn project_files(root: &Path) -> Vec<String> {
    let mut names: Vec<String> = std::fs::read_dir(root)
        .unwrap()
        .map(|entry| entry.unwrap().file_name().to_string_lossy().into_owned())
        .collect();
    names.sort();
    names
}

// spec: design/int/test-runner.md §6.5 — the child loads a selected module that
// the entry chain does not reach, then runs its tests.
#[test]
fn a_selected_module_outside_the_entry_chain_is_loaded() {
    let root = tempfile::tempdir().unwrap();
    std::fs::write(
        root.path().join("side.cl"),
        "(import [primitives [*]])\n(defn test-side [] None)\n",
    )
    .unwrap();
    let s = batch_with(root.path(), &[]);
    let side = vec![ModuleFullPath::from("side")];
    let run = run_child(&s, Some(&side), None).unwrap();
    assert_eq!(
        run.outcomes,
        [("side/test-side".to_string(), TestOutcome::Pass)]
    );

    let missing = vec![ModuleFullPath::from("absent")];
    let error = run_child(&s, Some(&missing), None).unwrap_err();
    assert!(error.to_string().contains("absent"), "{error}");
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
    let modules = s.selection_inputs().non_library_modules();
    let run = run_child(&s, Some(&modules), None).unwrap();
    let names: Vec<_> = run.outcomes.into_iter().map(|(n, _)| n).collect();
    assert_eq!(names, ["p/test-p"]);
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
    let (control, allocated, _) = heap_traffic(|| run_child(&s, None, None));
    let control = control.unwrap_or_else(|e| panic!("the unplanted run succeeds: {e}"));
    assert_eq!(
        control.outcomes,
        [("user/test-b".to_string(), fail("boom"))]
    );
    assert!(allocated > 0, "the control run executed the test body");

    s.shared
        .fresh_jit_drop_glues
        .retain(|(module, _), _| module.as_ref() != "user");
    let (planted, allocated, _) = heap_traffic(|| run_child(&s, None, None));
    let Err(error) = planted else {
        panic!("a missing release target must be refused before running");
    };
    assert!(error.to_string().contains("drop glue"), "{error}");
    assert_eq!(allocated, 0, "no test body ran");
}

// spec: repl/spec/16-test-discovery.md §16.6 Availability by Invocation Mode —
// `run_tests` refuses a program referencing `discover-tests` and runs no test,
// with a REPL selection too, because every test runs in a test child
// (design/int/test-runner.md §10 refusal row 3, §6.5).
#[test]
fn run_tests_refuses_a_discover_tests_reference_before_running() {
    let forms = ["(defn helper [] (discover-tests []))", ALLOCATING_TEST];
    let root = tempfile::tempdir().unwrap();
    let s = batch_with(root.path(), &forms);
    for modules in [None, Some(user())] {
        let (refused, allocated, _) = heap_traffic(|| run_child(&s, modules.as_deref(), None));
        let Err(error) = refused else {
            panic!("a program referencing discover-tests must be refused");
        };
        let message = error.to_string();
        for token in ["discover-tests", "user/helper", "REPL", "--test"] {
            assert!(message.contains(token), "names `{token}`: {message}");
        }
        assert_eq!(allocated, 0, "no test body ran");
    }
}

// spec: repl/spec/00-cli-invocation.md §0.5.5 Error Handling — rule 2 is about
// absence: under `--test` an existing entry with no tests is an empty run.
// Entry registration refuses a missing file (`lifecycle::entry_registration_tests`).
#[test]
fn run_tests_reports_an_existing_entry_without_tests_as_an_empty_run() {
    let root = tempfile::tempdir().unwrap();
    let s = batch_with(root.path(), &[]);
    let run = run_child(&s, None, None)
        .unwrap_or_else(|e| panic!("an entry without tests is an empty run: {e}"));
    assert!(run.outcomes.is_empty() && run.ended, "{run:?}");
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
