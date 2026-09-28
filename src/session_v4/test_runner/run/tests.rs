use std::sync::atomic::{AtomicI64, Ordering};

use cranelisp_types::{FQTypeName, Symbol, TypeName};

use super::*;
use crate::result_owner::test_support::{
    RecordingResolver, record, tables_with_adt, take_events, test_code,
};

/// The last `(Some "boom")` box a failing test body returned.
static FAIL_VALUE: AtomicI64 = AtomicI64::new(0);

extern "C" fn passes() -> i64 {
    record("call pass");
    0
}

extern "C" fn fails() -> i64 {
    record("call fail");
    let reason = cranelisp_intrinsics::heap_string::alloc_string(b"boom") as i64;
    let some = cranelisp_intrinsics::alloc::alloc_with_rc(16);
    // SAFETY: a fresh 16-byte payload: the `Some` tag, then its one field.
    unsafe {
        *(some.add(16) as *mut i64) = 1;
        *(some.add(cranelisp_backend::heap::HeapAdt::field_offset(0) as usize) as *mut i64) =
            reason;
    }
    FAIL_VALUE.store(some as i64, Ordering::SeqCst);
    some as i64
}

extern "C" fn panics() -> i64 {
    record("call panic");
    cranelisp_intrinsics::panic::set_runtime_error("division by zero".to_string());
    0
}

fn user() -> ModuleFullPath {
    ModuleFullPath::from("user")
}

fn option_string() -> Type {
    Type::ADT(
        FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("Option")),
        vec![Type::String],
    )
}

fn prepared(name: &str, body: extern "C" fn() -> i64) -> PreparedTest {
    let tables = tables_with_adt(
        &ModuleFullPath::from("primitives"),
        "Option",
        &[("None", 0), ("Some", 1)],
    );
    let release = ReleasePlan::new(
        option_string(),
        None,
        &user(),
        &tables,
        &RecordingResolver::new(),
    )
    .expect("an (Option String) result has a release target");
    PreparedTest {
        id: id(name),
        call: Some(PreparedCall {
            code: body as *const u8,
            code_owner: test_code(),
            release,
        }),
    }
}

fn id(name: &str) -> FQSymbol {
    FQSymbol {
        module: user(),
        symbol: Symbol::from(name),
    }
}

fn outcomes(prepared: Vec<PreparedTest>) -> Vec<(String, TestOutcome)> {
    execute(prepared)
        .into_iter()
        .map(|(id, outcome)| (id.to_string(), outcome))
        .collect()
}

// spec: repl/spec/16-test-discovery.md §16.2 Running Tests — a failure and a
// panic do not stop the run: pass, fail, panic, pass give four outcomes in
// order and the last test runs (design/int/test-runner.md §10 run row 1).
#[test]
fn failure_and_panic_do_not_stop_the_run() {
    take_events();
    let got = outcomes(vec![
        prepared("test-a", passes),
        prepared("test-b", fails),
        prepared("test-c", panics),
        prepared("test-d", passes),
    ]);
    assert_eq!(
        got,
        [
            ("user/test-a".to_string(), TestOutcome::Pass),
            (
                "user/test-b".to_string(),
                TestOutcome::Fail {
                    reason: "boom".to_string()
                }
            ),
            (
                "user/test-c".to_string(),
                TestOutcome::Panic {
                    reason: "division by zero".to_string()
                }
            ),
            ("user/test-d".to_string(), TestOutcome::Pass),
        ]
    );
    let fail = FAIL_VALUE.load(Ordering::SeqCst);
    assert_eq!(
        take_events(),
        [
            "call pass".to_string(),
            "glue(0)".to_string(),
            "call fail".to_string(),
            format!("glue({fail})"),
            "call panic".to_string(),
            "call pass".to_string(),
            "glue(0)".to_string(),
        ]
    );
}

// spec: repl/spec/16-test-discovery.md §16.2 Running Tests — a failing test's
// `(Some reason)` is observed and then released exactly once (§10 run row 2).
#[test]
fn failing_value_is_observed_then_released_once() {
    take_events();
    let got = outcomes(vec![prepared("test-b", fails)]);
    assert_eq!(
        got[0].1,
        TestOutcome::Fail {
            reason: "boom".to_string()
        }
    );
    let fail = FAIL_VALUE.load(Ordering::SeqCst);
    assert_eq!(
        take_events(),
        ["call fail".to_string(), format!("glue({fail})")]
    );
}

// spec: repl/spec/16-test-discovery.md §16.2 Running Tests — a passing test's
// `None` is a `Mixed` result and is released exactly once too (§10 run row 3).
#[test]
fn passing_none_is_released_once() {
    take_events();
    assert_eq!(
        outcomes(vec![prepared("test-a", passes)])[0].1,
        TestOutcome::Pass
    );
    assert_eq!(take_events(), ["call pass", "glue(0)"]);
}

// spec: repl/spec/16-test-discovery.md §16.2 Running Tests — a panicking test
// produces no result, so no release glue runs (§10 run row 4).
#[test]
fn panic_runs_no_release_glue() {
    take_events();
    assert_eq!(
        outcomes(vec![prepared("test-c", panics)])[0].1,
        TestOutcome::Panic {
            reason: "division by zero".to_string()
        }
    );
    assert_eq!(take_events(), ["call panic"]);
}

// spec: repl/spec/16-test-discovery.md §16.2 Running Tests — an eligible test
// with no callable code is reported failed, never passed (§10 run row 5).
#[test]
fn test_without_code_is_reported_failed() {
    let got = outcomes(vec![PreparedTest {
        id: id("test-x"),
        call: None,
    }]);
    assert_eq!(
        got[0].1,
        TestOutcome::Fail {
            reason: UNAVAILABLE_REASON.to_string()
        }
    );
    let report = TestRunReport::new(
        execute(vec![PreparedTest {
            id: id("test-x"),
            call: None,
        }]),
        Vec::new(),
        Duration::ZERO,
    );
    assert_eq!(report.exit_code(), 1);
}

// spec: repl/spec/00-cli-invocation.md §0.2.2 Test Mode (`--test`) — exit 0 when
// nothing failed or panicked, including an empty run whose text is exactly
// `No tests found`; otherwise 1 (§10 run row 7).
#[test]
fn report_text_and_exit_code_come_from_the_same_outcomes() {
    let pass = |name: &str| (id(name), TestOutcome::Pass);
    let all_pass = TestRunReport::new(
        vec![pass("test-a"), pass("test-b")],
        Vec::new(),
        Duration::ZERO,
    );
    assert_eq!(all_pass.exit_code(), 0);
    let dots = ".".repeat(REPORT_NAME_WIDTH - "user/test-a".len());
    assert_eq!(
        all_pass.text(),
        format!("  user/test-a {dots} ok\n  user/test-b {dots} ok\n\n2 passed in 0.00ms")
    );

    let failed = TestRunReport::new(
        vec![
            pass("test-a"),
            (
                id("test-b"),
                TestOutcome::Fail {
                    reason: "boom".to_string(),
                },
            ),
        ],
        Vec::new(),
        Duration::ZERO,
    );
    assert_eq!(failed.exit_code(), 1);
    assert!(
        failed.text().ends_with("1 passed, 1 failed in 0.00ms"),
        "{}",
        failed.text()
    );

    let panicked = TestRunReport::new(
        vec![(
            id("test-c"),
            TestOutcome::Panic {
                reason: "division by zero".to_string(),
            },
        )],
        Vec::new(),
        Duration::ZERO,
    );
    assert_eq!(panicked.exit_code(), 1);
    assert!(panicked.text().contains("user/test-c"));
    assert!(panicked.text().contains("PANIC: division by zero"));

    let warning = Warning {
        kind: cranelisp_types::WarningKind::Other,
        message: "mistyped".to_string(),
        span: cranelisp_types::Span::SYNTHETIC,
    };
    let empty = TestRunReport::new(Vec::new(), vec![warning], Duration::ZERO);
    assert_eq!(empty.text(), "No tests found");
    assert_eq!(empty.exit_code(), 0);
    assert_eq!(empty.warnings().len(), 1, "warnings survive an empty run");
}
