//! Panic exit observations needing a shared pipe or an on-disk stderr sink.
mod helpers;

use helpers::e2e::{Cranelisp, binary_path};
use std::io::{Read, Write};
use std::process::{Command, ExitStatus, Stdio};
use std::time::{Duration, Instant};

fn capture(repl: bool, panic: bool, trace: bool) -> (ExitStatus, String, String) {
    let program = if panic {
        "(import [prelude []])\n(platform stdio)\n(import [platform.stdio [print]])\n(import [primitives [*]])\n(defn main [] (bind (print \"BEFORE-PANIC\") (fn [_] (Pure (div-i64 1 0)))))\n"
    } else {
        "(import [prelude []])\n(platform stdio)\n(import [platform.stdio [print]])\n(defn main [] (print \"BEFORE-PANIC\"))\n"
    };
    let fixture = Cranelisp::new().user(program);
    let dir = fixture.tmpdir_path();
    let trace_path = dir.join("trace.log");
    let mut cmd = Command::new(binary_path());
    cmd.current_dir(&dir)
        .args(["--no-cache", "--no-color"])
        .env("CRANELISP_LIB", "")
        .env("CRANELISP_NO_ENV", "1")
        .env("CRANELISP_AGENT_PROVIDER", "")
        .env(
            "CRANELISP_PLATFORM_PATH",
            helpers::e2e::workspace_root().join("target/debug"),
        )
        .stdin(Stdio::piped());
    if !repl {
        cmd.args(["--run", "user.cl"]);
    }
    let (mut reader, writer) = std::io::pipe().unwrap();
    cmd.stdout(writer.try_clone().unwrap());
    if trace {
        drop(writer);
        cmd.env("CRANELISP_IO_TRACE", "1")
            .stderr(std::fs::File::create(&trace_path).unwrap());
    } else {
        cmd.stderr(writer);
    }
    let mut child = cmd.spawn().unwrap();
    drop(cmd);
    let drain = std::thread::spawn(move || {
        let mut text = String::new();
        reader.read_to_string(&mut text).unwrap();
        text
    });
    if repl {
        child
            .stdin
            .take()
            .unwrap()
            .write_all(b"(primitives/add-i64 300 17)\n(main)\n(primitives/add-i64 800 13)\n")
            .unwrap();
    } else {
        drop(child.stdin.take());
    }
    let deadline = Instant::now() + Duration::from_secs(5);
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break status;
        }
        if Instant::now() > deadline {
            child.kill().unwrap();
            child.wait().unwrap();
            panic!("panic stream fixture must exit within 5s");
        }
        std::thread::sleep(Duration::from_millis(10));
    };
    let output = drain.join().unwrap();
    let sink = if trace {
        std::fs::read_to_string(trace_path).unwrap()
    } else {
        String::new()
    };
    (status, output, sink)
}

fn precede_panic(text: &str, markers: &[&str]) -> bool {
    let report =
        regex::Regex::new(r"(?m)^error: runtime panic: (?:.+:[0-9]+: )?division by zero$").unwrap();
    let reports: Vec<_> = report.find_iter(text).collect();
    let [report] = reports.as_slice() else {
        return false;
    };
    if text.matches("division by zero").count() != 1 {
        return false;
    }
    let mut previous = None;
    for marker in markers {
        let Some(at) = text.find(marker) else {
            return false;
        };
        if at >= report.start() || previous.is_some_and(|p| p >= at) {
            return false;
        }
        previous = Some(at);
    }
    true
}

// spec: spec/12-runtime.md §12.7.5 — P-5: prior print reaches the shared pipe first.
#[test]
fn print_output_precedes_panic_on_merged_pipe_run() {
    let (status, text, _) = capture(false, true, false);
    assert!(
        matches!(status.code(), Some(c) if c != 0),
        "{status:?}\n{text}"
    );
    assert!(
        precede_panic(&text, &["BEFORE-PANIC"]),
        "print must precede panic report on merged pipe:\n{text}"
    );
}

// spec: spec/12-runtime.md §12.7.4.1 — P-5: prior REPL result and print precede panic.
#[test]
fn prior_repl_result_and_print_precede_panic_on_merged_pipe() {
    let (status, text, _) = capture(true, true, false);
    assert!(
        matches!(status.code(), Some(c) if c != 0)
            && precede_panic(&text, &[":primitives/Int 317", "BEFORE-PANIC"])
            && !text.contains(":primitives/Int 813")
            && text.matches("user> ").count() == 2,
        "prior result and print must precede the exiting panic:\nstatus:{status:?}\n{text}"
    );
}

// spec: spec/12-runtime.md §12.7.4.2 — P-12: pre-panic trace events reach the file sink.
#[test]
fn panic_exit_flushes_pre_panic_trace_events_to_file() {
    let (status, stdout, trace) = capture(false, true, true);
    assert!(
        matches!(status.code(), Some(c) if c != 0),
        "{status:?}\n{stdout}\n{trace}"
    );
    assert!(
        stdout.contains("BEFORE-PANIC"),
        "prior IO did execute: {stdout}"
    );
    assert!(
        trace.contains("TrampolineEnter") && trace.contains("PlatformEffect"),
        "file sink must hold pre-panic IO events:\n{trace}"
    );
}

// spec: spec/12-runtime.md §12.7.5 — stream capture's no-panic control delivers output.
#[test]
fn stream_captures_deliver_output_and_trace_without_panic_control() {
    for trace in [false, true] {
        let (status, stdout, sink) = capture(false, false, trace);
        assert!(status.success(), "{status:?}\n{stdout}\n{sink}");
        assert!(stdout.contains("BEFORE-PANIC"));
        assert!(!stdout.contains("runtime panic:") && !sink.contains("runtime panic:"));
        if trace {
            assert!(
                sink.contains("TrampolineEnter") && sink.contains("PlatformEffect"),
                "{sink}"
            );
        }
    }
}

// spec: spec/12-runtime.md §12.7.5 — detection proof for merged-stream ordering.
#[test]
fn stream_order_checker_rejects_reversed_or_missing_delivery() {
    let report = "error: runtime panic: division by zero\n";
    assert!(precede_panic(
        &format!("317\nBEFORE\n{report}"),
        &["317", "BEFORE"]
    ));
    assert!(precede_panic(
        "317\nBEFORE\nerror: runtime panic: user.cl:2: division by zero\n",
        &["317", "BEFORE"]
    ));
    for wrong in [
        format!("{report}317\nBEFORE\n"),
        format!("317\n{report}BEFORE\n"),
        format!("BEFORE\n317\n{report}"),
        format!("317\n{report}"),
        format!("317\nBEFORE\n{report}{report}"),
    ] {
        assert!(
            !precede_panic(&wrong, &["317", "BEFORE"]),
            "checker accepted {wrong:?}"
        );
    }
}
