use super::*;

// spec: spec/12-runtime.md §12.7.5 — a language panic's report is the prefix,
// then the message, on one line (P-14 composition).
#[test]
fn panic_report_is_the_prefix_then_the_message() {
    let fault = Fault::Panic("src/m.cl:3: division by zero");
    assert_eq!(
        fault.report(),
        "error: runtime panic: src/m.cl:3: division by zero\n"
    );
    assert_eq!(fault.exit_status(), PANIC_EXIT_STATUS);
    assert_eq!(PANIC_EXIT_STATUS, 1);
}

// spec: spec/12-runtime.md §12.7.6 — a dispatch fault names the platform
// function and its cause, without the panic prefix (P-14 composition).
#[test]
fn dispatch_fault_report_names_the_function_without_the_panic_prefix() {
    let fault = Fault::Dispatch {
        fn_name: "stdio/read-line",
        cause: "device unavailable",
    };
    let report = fault.report();
    assert_eq!(
        report,
        "platform fn `stdio/read-line` dispatch failed: device unavailable\n"
    );
    assert!(!report.starts_with(PANIC_REPORT_PREFIX));
    assert_eq!(fault.exit_status(), PANIC_EXIT_STATUS);
}

// spec: design/intrinsics/process-lifecycle.md §1.1 — a runtime defect reports
// `error: runtime defect: <payload>` on one line, and is not a language panic.
#[test]
fn runtime_defect_report_is_one_line_without_the_panic_prefix() {
    let report = Fault::RuntimeDefect("index out of bounds").report();
    assert_eq!(report, "error: runtime defect: index out of bounds\n");
    assert!(!report.starts_with(PANIC_REPORT_PREFIX));
    assert_eq!(Fault::RuntimeDefect("x").exit_status(), PANIC_EXIT_STATUS);
}

// spec: design/intrinsics/process-lifecycle.md §1.1 — the backstop is not a
// language panic and keeps its own status.
#[test]
fn backstop_report_is_the_diagnostic_with_its_own_status() {
    let backstop = Fault::BackstopExpired("block_on_reactor: OneShot backstop exceeded 1s");
    assert_eq!(
        backstop.report(),
        "block_on_reactor: OneShot backstop exceeded 1s\n"
    );
    assert_eq!(backstop.exit_status(), 70);
}

// spec: design/intrinsics/process-lifecycle.md §1.1 — switch-install misuse
// reports a located configuration message, not a language panic.
#[test]
fn configuration_report_names_its_site_without_the_panic_prefix() {
    let fault = Fault::Configuration {
        site: "cranelisp_install_runtime_switches",
        detail: "a runtime switch was read before the install",
    };
    let report = fault.report();
    assert_eq!(
        report,
        "error: runtime configuration: cranelisp_install_runtime_switches: \
         a runtime switch was read before the install\n"
    );
    assert!(!report.starts_with(PANIC_REPORT_PREFIX));
    assert_eq!(fault.exit_status(), PANIC_EXIT_STATUS);
}

/// Every report kind, each carrying `text` in every interpolated field.
fn reports_carrying(text: &str) -> [String; 5] {
    [
        Fault::Panic(text).report(),
        Fault::Dispatch {
            fn_name: text,
            cause: text,
        }
        .report(),
        Fault::RuntimeDefect(text).report(),
        Fault::BackstopExpired(text).report(),
        Fault::Configuration {
            site: text,
            detail: text,
        }
        .report(),
    ]
}

// spec: spec/12-runtime.md §12.7.5, §12.7.6; design/intrinsics/process-lifecycle.md
// §1.1 — every report is one stderr line, whatever its payload carries.
#[test]
fn a_multi_line_payload_yields_a_one_line_report_of_every_kind() {
    for report in reports_carrying("first\nsecond\r\nthird\u{2028}fourth\u{85}fifth") {
        assert_eq!(report.lines().count(), 1, "{report:?}");
        assert!(report.ends_with('\n'), "{report:?}");
        assert!(
            !report[..report.len() - 1].contains(['\n', '\r', '\u{2028}', '\u{85}']),
            "{report:?}"
        );
    }
}

// spec: spec/12-runtime.md §12.7.6 — a dispatch fault's cause cannot forge a
// line that reads as a language panic.
#[test]
fn a_dispatch_cause_cannot_forge_a_panic_prefixed_line() {
    let report = Fault::Dispatch {
        fn_name: "platform.device/read",
        cause: "device failed\nerror: runtime panic: unrelated",
    }
    .report();
    assert_eq!(
        report,
        "platform fn `platform.device/read` dispatch failed: \
         device failed\\nerror: runtime panic: unrelated\n"
    );
    assert!(
        report.lines().all(|l| !l.starts_with(PANIC_REPORT_PREFIX)),
        "{report:?}"
    );
}

// spec: design/intrinsics/process-lifecycle.md §1.1 — line breaks and other
// control characters are written as escapes; printable text, including a
// backslash, passes through unchanged.
#[test]
fn control_characters_are_escaped_and_printable_text_is_unchanged() {
    let [panic, ..] = reports_carrying("a\tb\u{1b}[31mc\u{0}d\\e \u{e9}");
    assert_eq!(
        panic,
        "error: runtime panic: a\\tb\\u{1b}[31mc\\u{0}d\\e \u{e9}\n"
    );
}

// spec: design/intrinsics/process-lifecycle.md §1.1 — the single-line control:
// a payload with no control characters is reported verbatim in every kind.
#[test]
fn a_single_line_payload_is_reported_verbatim_in_every_kind() {
    let text = "src/m.cl:3: division by zero; path C:\\tmp";
    assert_eq!(
        reports_carrying(text),
        [
            format!("error: runtime panic: {text}\n"),
            format!("platform fn `{text}` dispatch failed: {text}\n"),
            format!("error: runtime defect: {text}\n"),
            format!("{text}\n"),
            format!("error: runtime configuration: {text}: {text}\n"),
        ]
    );
}

// spec: design/intrinsics/process-lifecycle.md §1.1 — termination is claimed
// once per process; every later claimant loses (P-14 claim transition).
#[test]
fn termination_is_claimed_once() {
    let flag = AtomicBool::new(false);
    assert_eq!(claim(&flag), Claim::Won);
    assert_eq!(claim(&flag), Claim::Lost);
    assert_eq!(claim(&flag), Claim::Lost);
}

// spec: spec/12-runtime.md §12.7.4.2 — a non-IO main's result is the driver's
// result.
#[test]
fn run_program_returns_a_non_io_main_result() {
    assert_eq!(cranelisp_run_program(main_returns_7 as *const u8, false), 7);
}

// spec: spec/12-runtime.md §12.7.4.2 — an IO main is forced and reduces to its
// inner value; the driver releases the tree.
#[test]
fn run_program_forces_an_io_main_to_its_inner_value() {
    let before = (crate::alloc::alloc_count(), crate::alloc::dealloc_count());
    assert_eq!(
        cranelisp_run_program(main_returns_io_pure as *const u8, true),
        42
    );
    let after = (crate::alloc::alloc_count(), crate::alloc::dealloc_count());
    assert!(
        after.1 - before.1 >= 1,
        "the driver must release the IO tree it was handed"
    );
}

/// A clean non-IO `main` returning a constant. `extern "C" fn() -> i64`.
extern "C" fn main_returns_7() -> i64 {
    7
}

/// A `main` returning an IO `Pure(42)` node base pointer. ABI-10 layout
/// `[header(16) | tag=PURE(8) | value(8) | payload witness(8)]`; the driver
/// forces it via the IO trampoline and reduces to the inner value. The witness
/// is `0` (`Scalar`) — both the force and the teardown read it.
extern "C" fn main_returns_io_pure() -> i64 {
    let base = crate::alloc::alloc_with_rc(24);
    unsafe {
        // tag at offset 16 = IO_TAG_PURE (0); value at 24; witness at 32.
        *((base as isize + 16) as *mut i64) = cranelisp_platform::IO_TAG_PURE;
        *((base as isize + 24) as *mut i64) = 42;
        *((base as isize + 32) as *mut i64) = 0;
    }
    base as i64
}

// ---------------------------------------------------------------------
// P-14 / P-13 child cells: the terminator observed from outside a process.
// ---------------------------------------------------------------------

use crate::test_child::{self, selected};

fn child(name: &str) -> String {
    test_child::child_path(module_path!(), name)
}

fn raise(msg: &str) -> ! {
    runtime_panic(msg.as_ptr(), msg.len())
}

#[test]
fn child_raises_one_language_panic() {
    if !selected("child_raises_one_language_panic") {
        return;
    }
    print!("OUTPUT-BEFORE-PANIC");
    raise("boom");
}

#[test]
fn child_two_threads_raise_together() {
    if !selected("child_two_threads_raise_together") {
        return;
    }
    let barrier = std::sync::Arc::new(std::sync::Barrier::new(2));
    let threads: Vec<_> = ["first", "second"]
        .into_iter()
        .map(|msg| {
            let barrier = barrier.clone();
            std::thread::spawn(move || {
                barrier.wait();
                raise(msg);
            })
        })
        .collect();
    for t in threads {
        let _ = t.join();
    }
    eprintln!("RESUMED-AFTER-PANIC");
}

#[test]
fn child_leaks_then_panics() {
    if !selected("child_leaks_then_panics") {
        return;
    }
    let leaked = crate::alloc::alloc_with_rc(8) as i64;
    // One counted inc reads the RC-stats gate, which registers its exit printer.
    crate::rc::rc_inc(leaked);
    raise("leaking panic");
}

#[test]
fn child_dispatch_fault_with_a_forged_panic_line() {
    if !selected("child_dispatch_fault_with_a_forged_panic_line") {
        return;
    }
    terminate(Fault::Dispatch {
        fn_name: "platform.device/read",
        cause: "device failed\nerror: runtime panic: unrelated",
    });
}

// spec: spec/12-runtime.md §12.7.6 — a dispatch fault whose cause carries a
// line break and the panic prefix ends the process with one unprefixed stderr
// line.
#[test]
fn terminator_writes_a_multi_line_dispatch_cause_as_one_unprefixed_line() {
    let end = test_child::run(&child("child_dispatch_fault_with_a_forged_panic_line"), &[]);
    assert_eq!(end.code, Some(PANIC_EXIT_STATUS), "{}", end.stderr);
    assert!(
        end.report_lines().is_empty(),
        "forged panic line:\n{}",
        end.stderr
    );
    let reports: Vec<_> = end
        .stderr
        .lines()
        .filter(|l| l.contains("device failed") || l.contains("unrelated"))
        .collect();
    assert_eq!(
        reports,
        ["platform fn `platform.device/read` dispatch failed: \
          device failed\\nerror: runtime panic: unrelated"],
        "{}",
        end.stderr
    );
}

// spec: spec/12-runtime.md §12.7.4, §12.7.5 — a panic reports once on stderr
// with the prefix and ends the process with status 1 (P-14).
#[test]
fn terminator_reports_once_and_exits_with_panic_status() {
    let end = test_child::run(&child("child_raises_one_language_panic"), &[]);
    end.assert_panicked_with("boom");
    assert!(
        !end.stdout.contains(PANIC_REPORT_PREFIX),
        "report on stdout"
    );
}

// spec: spec/12-runtime.md §12.7.5 — output written before the panic precedes
// the report (P-14 ordering cell).
#[test]
fn terminator_flushes_prior_output_before_the_report() {
    let merged = test_child::run_merged(&child("child_raises_one_language_panic"));
    let before = merged.find("OUTPUT-BEFORE-PANIC");
    let report = merged.find("error: runtime panic: boom");
    assert!(
        matches!((before, report), (Some(b), Some(r)) if b < r),
        "prior output must precede the report:\n{merged}"
    );
}

// spec: spec/12-runtime.md §12.4.3 — concurrent panics produce one report,
// naming one of the raised messages (P-14 two-raiser cell).
#[test]
fn terminator_reports_one_of_two_concurrent_raisers() {
    let end = test_child::run(&child("child_two_threads_raise_together"), &[]);
    assert_eq!(end.code, Some(PANIC_EXIT_STATUS), "{}", end.stderr);
    let lines = end.report_lines();
    assert_eq!(lines.len(), 1, "exactly one report:\n{}", end.stderr);
    assert!(
        lines[0] == "error: runtime panic: first" || lines[0] == "error: runtime panic: second",
        "{}",
        lines[0]
    );
    assert!(!end.stderr.contains("RESUMED"), "{}", end.stderr);
}

// spec: design/intrinsics/process-lifecycle.md §1.4 — after a panic, armed
// M3 parity stands down with one line instead of aborting, and `[RC_STATS]`
// still prints (P-13).
#[test]
fn armed_parity_stands_down_after_a_panic() {
    let end = test_child::run(
        &child("child_leaks_then_panics"),
        &[("CRANELISP_ALLOC_PARITY", "1"), ("CRANELISP_RC_STATS", "1")],
    );
    end.assert_panicked_with("leaking panic");
    let stand_downs = end
        .stderr
        .lines()
        .filter(|l| l.starts_with("[ALLOC_PARITY] not checked"))
        .count();
    assert_eq!(stand_downs, 1, "one stand-down line:\n{}", end.stderr);
    assert!(!end.stderr.contains("IMBALANCE"), "{}", end.stderr);
    assert!(end.stderr.contains("[RC_STATS]"), "{}", end.stderr);
}
