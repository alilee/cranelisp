//! U-19: an inline bind continuation must release its unused heap argument.
//! Intake: tests/plan/s123-evidence-delta.md §3.10, carried to S124.
//! Filing: sprints/actions/ACT-1050-inline-bind-continuation-unused-heap-argument-leak-intake.md.
//! The lambda-body type-loss mechanism remains provisional.

mod helpers;

use helpers::marginal::{Child, MarginalPair};

#[derive(Clone, Copy, Debug)]
enum Mode {
    Run,
    Link,
    Repl,
}

fn child(body: &str, mode: Mode, moves_off: bool) -> Child {
    let program = format!(
        "(import [primitives [*]])\n\
         (defn k [v] (Pure 49))\n\
         (defn main [] {body})\n"
    );
    let c = match mode {
        Mode::Run => Child::new(&program),
        Mode::Link => Child::new(&program).link_then_run(),
        Mode::Repl => Child::repl(&format!("{program}(main)\n")),
    }
    .env("CRANELISP_RC_DEC_CHECK", "1");
    if moves_off {
        c.env("CRANELISP_NO_OWNERSHIP", "1")
    } else {
        c
    }
}

fn check(subject: &str, payload: &str, mode: Mode, moves_off: bool) {
    let control = format!("(let [k (fn [v] (Pure 49))] (bind (Pure {payload}) k))");
    let m = MarginalPair::new(
        &format!("U-19 {mode:?} moves_off={moves_off}: {subject}"),
        child(&control, mode, moves_off),
        child(subject, mode, moves_off),
    )
    .measure();
    eprintln!("{}", m.report());
    for half in [m.control(), m.subject()] {
        let expected_exit = if matches!(mode, Mode::Repl) { 0 } else { 49 };
        assert_eq!(
            half.exit_code(),
            Some(expected_exit),
            "{}\n{}",
            m.report(),
            half.stderr
        );
        if matches!(mode, Mode::Repl) {
            assert!(
                half.stdout.contains(":primitives/Int 49"),
                "{}",
                half.stdout
            );
        }
    }
    m.assert_balanced("U-19: binding the same continuation must not change heap release");
}

// spec: spec/12-runtime.md §12.3.1 — unreachable bind arguments are freed.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/control_flow/lambda.rs::compile_lambda found=S123 owner=/dev — provisional locus (ACT-1050)
#[test]
fn unused_heap_argument_is_released_run_moves_on() {
    check(
        "(bind (Pure [49]) (fn [v] (Pure 49)))",
        "[49]",
        Mode::Run,
        false,
    );
}

// spec: spec/12-runtime.md §12.3.1 — unreachable bind arguments are freed.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/control_flow/lambda.rs::compile_lambda found=S123 owner=/dev — provisional locus (ACT-1050)
#[test]
fn nested_unused_heap_argument_is_released_run_moves_on() {
    check(
        "(bind (Pure [[49]]) (fn [v] (Pure 49)))",
        "[[49]]",
        Mode::Run,
        false,
    );
}

// spec: spec/12-runtime.md §12.3.1 — used and named continuations release once.
#[test]
fn used_and_named_continuations_balance_run_moves_on() {
    check(
        "(bind (Pure [49]) (fn [v] (Pure (vec-get v 0))))",
        "[49]",
        Mode::Run,
        false,
    );
    check("(bind (Pure [49]) k)", "[49]", Mode::Run, false);
}

// spec: spec/12-runtime.md §12.3.1 — unreachable bind arguments are freed.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/control_flow/lambda.rs::compile_lambda found=S123 owner=/dev — provisional locus (ACT-1050)
#[test]
fn unused_heap_argument_is_released_run_moves_off() {
    check(
        "(bind (Pure [49]) (fn [v] (Pure 49)))",
        "[49]",
        Mode::Run,
        true,
    );
}

// spec: spec/12-runtime.md §12.3.1 — unreachable bind arguments are freed.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/control_flow/lambda.rs::compile_lambda found=S123 owner=/dev — provisional locus (ACT-1050)
#[test]
fn nested_unused_heap_argument_is_released_run_moves_off() {
    check(
        "(bind (Pure [[49]]) (fn [v] (Pure 49)))",
        "[[49]]",
        Mode::Run,
        true,
    );
}

// spec: spec/12-runtime.md §12.3.1 — used and named continuations release once.
#[test]
fn used_and_named_continuations_balance_run_moves_off() {
    check(
        "(bind (Pure [49]) (fn [v] (Pure (vec-get v 0))))",
        "[49]",
        Mode::Run,
        true,
    );
    check("(bind (Pure [49]) k)", "[49]", Mode::Run, true);
}

// spec: spec/12-runtime.md §12.3.1 — unreachable bind arguments are freed.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/control_flow/lambda.rs::compile_lambda found=S123 owner=/dev — provisional locus (ACT-1050)
#[test]
fn unused_heap_argument_is_released_link_moves_on() {
    check(
        "(bind (Pure [49]) (fn [v] (Pure 49)))",
        "[49]",
        Mode::Link,
        false,
    );
}

// spec: spec/12-runtime.md §12.3.1 — unreachable bind arguments are freed.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/control_flow/lambda.rs::compile_lambda found=S123 owner=/dev — provisional locus (ACT-1050)
#[test]
fn nested_unused_heap_argument_is_released_link_moves_on() {
    check(
        "(bind (Pure [[49]]) (fn [v] (Pure 49)))",
        "[[49]]",
        Mode::Link,
        false,
    );
}

// spec: spec/12-runtime.md §12.3.1 — used and named continuations release once.
#[test]
fn used_and_named_continuations_balance_link_moves_on() {
    check(
        "(bind (Pure [49]) (fn [v] (Pure (vec-get v 0))))",
        "[49]",
        Mode::Link,
        false,
    );
    check("(bind (Pure [49]) k)", "[49]", Mode::Link, false);
}

// spec: spec/12-runtime.md §12.3.1 — unreachable bind arguments are freed.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/control_flow/lambda.rs::compile_lambda found=S123 owner=/dev — provisional locus (ACT-1050)
#[test]
fn unused_heap_argument_is_released_link_moves_off() {
    check(
        "(bind (Pure [49]) (fn [v] (Pure 49)))",
        "[49]",
        Mode::Link,
        true,
    );
}

// spec: spec/12-runtime.md §12.3.1 — unreachable bind arguments are freed.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/control_flow/lambda.rs::compile_lambda found=S123 owner=/dev — provisional locus (ACT-1050)
#[test]
fn nested_unused_heap_argument_is_released_link_moves_off() {
    check(
        "(bind (Pure [[49]]) (fn [v] (Pure 49)))",
        "[[49]]",
        Mode::Link,
        true,
    );
}

// spec: spec/12-runtime.md §12.3.1 — used and named continuations release once.
#[test]
fn used_and_named_continuations_balance_link_moves_off() {
    check(
        "(bind (Pure [49]) (fn [v] (Pure (vec-get v 0))))",
        "[49]",
        Mode::Link,
        true,
    );
    check("(bind (Pure [49]) k)", "[49]", Mode::Link, true);
}

// spec: spec/12-runtime.md §12.3.1 — unreachable bind arguments are freed.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/control_flow/lambda.rs::compile_lambda found=S123 owner=/dev — provisional locus (ACT-1050)
#[test]
fn unused_heap_argument_is_released_repl_moves_on() {
    check(
        "(bind (Pure [49]) (fn [v] (Pure 49)))",
        "[49]",
        Mode::Repl,
        false,
    );
}

// spec: spec/12-runtime.md §12.3.1 — unreachable bind arguments are freed.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/control_flow/lambda.rs::compile_lambda found=S123 owner=/dev — provisional locus (ACT-1050)
#[test]
fn nested_unused_heap_argument_is_released_repl_moves_on() {
    check(
        "(bind (Pure [[49]]) (fn [v] (Pure 49)))",
        "[[49]]",
        Mode::Repl,
        false,
    );
}

// spec: spec/12-runtime.md §12.3.1 — used and named continuations release once.
#[test]
fn used_and_named_continuations_balance_repl_moves_on() {
    check(
        "(bind (Pure [49]) (fn [v] (Pure (vec-get v 0))))",
        "[49]",
        Mode::Repl,
        false,
    );
    check("(bind (Pure [49]) k)", "[49]", Mode::Repl, false);
}

// spec: spec/12-runtime.md §12.3.1 — unreachable bind arguments are freed.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/control_flow/lambda.rs::compile_lambda found=S123 owner=/dev — provisional locus (ACT-1050)
#[test]
fn unused_heap_argument_is_released_repl_moves_off() {
    check(
        "(bind (Pure [49]) (fn [v] (Pure 49)))",
        "[49]",
        Mode::Repl,
        true,
    );
}

// spec: spec/12-runtime.md §12.3.1 — unreachable bind arguments are freed.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/control_flow/lambda.rs::compile_lambda found=S123 owner=/dev — provisional locus (ACT-1050)
#[test]
fn nested_unused_heap_argument_is_released_repl_moves_off() {
    check(
        "(bind (Pure [[49]]) (fn [v] (Pure 49)))",
        "[[49]]",
        Mode::Repl,
        true,
    );
}

// spec: spec/12-runtime.md §12.3.1 — used and named continuations release once.
#[test]
fn used_and_named_continuations_balance_repl_moves_off() {
    check(
        "(bind (Pure [49]) (fn [v] (Pure (vec-get v 0))))",
        "[49]",
        Mode::Repl,
        true,
    );
    check("(bind (Pure [49]) k)", "[49]", Mode::Repl, true);
}
