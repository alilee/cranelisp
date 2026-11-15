use std::collections::VecDeque;

use super::*;

fn id(name: &str) -> FQSymbol {
    FQSymbol {
        module: ModuleFullPath::from("user"),
        symbol: Symbol::from(name),
    }
}

fn panic_line(message: &str) -> Option<String> {
    Some(format!("{PANIC_REPORT_PREFIX}{message}"))
}

/// A child that ran `tests`, passing each, then ended with the last one open.
fn open_child(passed: &[&str], open: &str, exit: ChildExit, line: Option<String>) -> ChildEnding {
    let mut records = Vec::new();
    for name in passed {
        records.push(Record::Start(id(name)));
        records.push(Record::Outcome(TestOutcome::Pass));
    }
    records.push(Record::Start(id(open)));
    ChildEnding {
        records,
        exit,
        stderr: StderrTail {
            last_line: line.clone(),
            last_panic_line: line,
        },
    }
}

fn completed_child(passed: &[&str]) -> ChildEnding {
    let mut ending = open_child(&[], "unused", ChildExit::Status(0), None);
    ending.records.clear();
    for name in passed {
        ending.records.push(Record::Start(id(name)));
        ending.records.push(Record::Outcome(TestOutcome::Pass));
    }
    ending.records.push(Record::End);
    ending
}

/// Replays scripted child endings and records each resume point. It refuses
/// to start more children than it has endings, which bounds a supervisor that
/// would otherwise restart without end.
struct Scripted {
    endings: VecDeque<ChildEnding>,
    resumes: Vec<Option<FQSymbol>>,
}

impl Scripted {
    fn new(endings: Vec<ChildEnding>) -> Self {
        Self {
            endings: endings.into(),
            resumes: Vec::new(),
        }
    }
}

impl ChildLauncher for Scripted {
    fn run_child(
        &mut self,
        resume_after: Option<&FQSymbol>,
    ) -> Result<ChildEnding, CranelispError> {
        self.resumes.push(resume_after.cloned());
        self.endings
            .pop_front()
            .ok_or_else(|| internal_error("child-count bound exceeded".to_string()))
    }
}

fn report_lines(report: &TestRunReport) -> Vec<String> {
    report
        .text()
        .lines()
        .filter(|line| line.contains("/test-"))
        .map(|line| {
            let (name, rest) = line.trim().split_once(' ').unwrap();
            format!("{name} {}", rest.trim_start_matches(['.', ' ']))
        })
        .collect()
}

// spec: design/int/test-runner.md §10 test-child row 1 — each row of the §6.5
// table: `end` completes the run; an open test with the panic status and a
// prefixed stderr line is a panic carrying the rest of that line; the panic
// status without a prefixed line, another status, and a signal are failures;
// neither an open test nor `end` stops the run.
#[test]
fn classification_maps_each_row_of_the_ending_table() {
    let done = classify(&completed_child(&["test-a"])).unwrap();
    assert_eq!(done.next, Next::Done);
    assert_eq!(done.completed, [(id("test-a"), TestOutcome::Pass)]);

    let panicked = open_child(
        &[],
        "test-b",
        ChildExit::Status(PANIC_EXIT_STATUS),
        panic_line("division by zero"),
    );
    assert_eq!(
        classify(&panicked).unwrap().next,
        Next::RestartAfter(
            id("test-b"),
            TestOutcome::Panic {
                reason: "division by zero".to_string()
            }
        )
    );

    for (exit, line) in [
        (ChildExit::Status(PANIC_EXIT_STATUS), None),
        (ChildExit::Status(PANIC_EXIT_STATUS + 1), panic_line("late")),
        (ChildExit::Signal(9), panic_line("late")),
    ] {
        let next = classify(&open_child(&[], "test-c", exit, line))
            .unwrap()
            .next;
        assert!(
            matches!(&next, Next::RestartAfter(open, TestOutcome::Fail { .. }) if *open == id("test-c")),
            "{exit:?} is a failure of the open test, not a panic: {next:?}"
        );
    }

    let nothing = ChildEnding {
        records: vec![Record::Warning("w".to_string())],
        exit: ChildExit::Status(1),
        stderr: StderrTail::default(),
    };
    assert_eq!(classify(&nothing).unwrap().next, Next::Stopped);
}

// spec: design/int/test-runner.md §10 test-child row 2 — the endings pass,
// panic, pass, signal, pass give five outcomes in FQ order from three
// children, restarted after the panicking and the signalled test.
#[test]
fn scripted_endings_restart_after_each_open_test() {
    let mut launcher = Scripted::new(vec![
        open_child(
            &["test-a"],
            "test-b",
            ChildExit::Status(PANIC_EXIT_STATUS),
            panic_line("division by zero"),
        ),
        open_child(&["test-c"], "test-d", ChildExit::Signal(11), None),
        completed_child(&["test-e"]),
    ]);
    let report = supervise(&mut launcher).unwrap();
    assert_eq!(
        report_lines(&report),
        [
            "user/test-a ok",
            "user/test-b PANIC: division by zero",
            "user/test-c ok",
            "user/test-d FAILED: test process was killed by signal 11",
            "user/test-e ok",
        ]
    );
    assert_eq!(
        launcher.resumes,
        [None, Some(id("test-b")), Some(id("test-d"))]
    );
    assert_eq!(report.exit_code(), 1);
    assert!(report.text().ends_with("ms"), "{}", report.text());
    assert!(
        report.text().contains("3 passed, 2 failed"),
        "{}",
        report.text()
    );
}

// spec: design/int/test-runner.md §10 test-child row 3 — a restarted child that
// records nothing stops the run with `Err` and no further child; a child that
// reopens a test at or before its resume point is refused rather than
// restarted, so the run of `N` tests stays within `N + 1` children. The
// scripted launcher's own bound is the detection proof for a supervisor that
// restarts regardless.
#[test]
fn a_child_that_makes_no_progress_stops_the_run() {
    let mut silent = Scripted::new(vec![
        open_child(
            &[],
            "test-a",
            ChildExit::Status(PANIC_EXIT_STATUS),
            panic_line("boom"),
        ),
        ChildEnding {
            records: Vec::new(),
            exit: ChildExit::Status(1),
            stderr: StderrTail::default(),
        },
        completed_child(&["test-z"]),
    ]);
    assert!(supervise(&mut silent).is_err());
    assert_eq!(silent.resumes.len(), 2, "no child after the silent one");

    let mut repeating = Scripted::new(vec![
        open_child(&[], "test-b", ChildExit::Signal(9), None),
        open_child(&[], "test-b", ChildExit::Signal(9), None),
        completed_child(&[]),
    ]);
    let error = supervise(&mut repeating).err().expect("a rerun is refused");
    assert!(error.to_string().contains("user/test-b"), "{error}");
    assert_eq!(repeating.resumes.len(), 2);

    let mut bounded = Scripted::new(vec![open_child(&[], "test-a", ChildExit::Signal(9), None)]);
    let error = supervise(&mut bounded)
        .err()
        .expect("the bound stops the run");
    assert!(error.to_string().contains("bound"), "{error}");
}

// spec: design/int/test-runner.md §10 test-child row 6 — the record codec
// round-trips every record, including a reason spanning lines and one holding
// the escape character, one line per record.
#[test]
fn record_codec_round_trips_a_reason_spanning_lines() {
    let records = [
        Record::Warning("mistyped\n  test".to_string()),
        Record::Start(FQSymbol {
            module: ModuleFullPath::from("a.b"),
            symbol: Symbol::from("test-x"),
        }),
        Record::Outcome(TestOutcome::Pass),
        Record::Outcome(TestOutcome::Fail {
            reason: "line one\nline two \\n end\\".to_string(),
        }),
        Record::Outcome(TestOutcome::Panic {
            reason: "p".to_string(),
        }),
        Record::End,
    ];
    for record in &records {
        let line = record.encode();
        assert_eq!(line.matches('\n').count(), 1, "one line: {line:?}");
        assert_eq!(
            Record::decode(line.trim_end_matches('\n')).as_ref(),
            Some(record)
        );
    }
    for malformed in ["start nomodule", "pass extra", "fail bad\\escape", "bogus"] {
        assert_eq!(Record::decode(malformed), None, "{malformed}");
    }
}

// spec: design/int/test-runner.md §10 test-child row 7 — a restart rescans the
// same sources, so only the first child's warnings reach the report.
#[test]
fn warnings_come_from_the_first_child_only() {
    let with_warning = |mut ending: ChildEnding| {
        ending
            .records
            .insert(0, Record::Warning("mistyped user/test-w".to_string()));
        ending
    };
    let mut launcher = Scripted::new(vec![
        with_warning(open_child(
            &[],
            "test-a",
            ChildExit::Status(PANIC_EXIT_STATUS),
            panic_line("boom"),
        )),
        with_warning(completed_child(&["test-b"])),
    ]);
    let report = supervise(&mut launcher).unwrap();
    let warnings: Vec<_> = report
        .warnings()
        .iter()
        .map(|w| w.message.as_str())
        .collect();
    assert_eq!(warnings, ["mistyped user/test-w"]);
}

// spec: design/int/test-runner.md §10 test-child row 4 — the child command line
// is the client's arguments, then `--test` and the child arguments: the record
// file, each selected module in order and, after a restart, the resume point.
#[test]
fn child_command_line_appends_the_child_arguments() {
    let client: Vec<OsString> = ["t", "--no-cache"].iter().map(OsString::from).collect();
    let modules = [ModuleFullPath::from("a.b"), ModuleFullPath::from("c")];
    let line = child_command_line(
        &client,
        Path::new("/run/records-2"),
        Some(&modules),
        Some(&id("test-b")),
    );
    let expected: Vec<OsString> = [
        "t",
        "--no-cache",
        "--test",
        RECORDS_FLAG,
        "/run/records-2",
        MODULE_FLAG,
        "a.b",
        MODULE_FLAG,
        "c",
        RESUME_FLAG,
        "user/test-b",
    ]
    .iter()
    .map(OsString::from)
    .collect();
    assert_eq!(line, expected);

    let first = child_command_line(&client, Path::new("/r"), None, None);
    assert_eq!(
        first.iter().filter(|arg| *arg == "--test").count(),
        1,
        "{first:?}"
    );
    assert!(
        !first
            .iter()
            .any(|arg| arg == MODULE_FLAG || arg == RESUME_FLAG)
    );
}

// spec: design/int/test-runner.md §10 test-child row 4 — the child inherits the
// parent's environment with `CRANELISP_NO_ENV=1` added, so it does not re-read
// the environment files its parent already supplied.
#[test]
fn child_environment_disables_the_file_supply() {
    let command = child_command(Path::new("/bin/cranelisp"), vec!["--test".into()]);
    let envs: Vec<_> = command.get_envs().collect();
    assert_eq!(
        envs,
        [(
            std::ffi::OsStr::new(NO_ENV_VAR),
            Some(std::ffi::OsStr::new("1"))
        )]
    );
    assert_eq!(command.get_args().collect::<Vec<_>>(), ["--test"]);
}

const DISPATCH_FAULT: &str = "platform fn `p/f` dispatch failed: boom";

/// A child that ended with `user/test-f` open after writing `lines` to stderr,
/// keeping the tail the relay would keep.
fn faulted_child(exit: ChildExit, lines: &[&str]) -> ChildEnding {
    let mut ending = open_child(&[], "test-f", exit, None);
    ending.stderr = relay_stderr(lines.join("\n").as_bytes(), std::io::sink());
    ending
}

fn open_outcome(ending: &ChildEnding) -> TestOutcome {
    match classify(ending).unwrap().next {
        Next::RestartAfter(open, outcome) if open == id("test-f") => outcome,
        next => panic!("expected a restart after user/test-f, got {next:?}"),
    }
}

// spec: design/int/test-runner.md §10 test-child row 9 — the cause of a fail:
// an open test, status 1, no prefixed line, and stderr of DLL panic-hook lines
// followed by a dispatch fault report is a fail whose reason carries the status
// and that final line, and it is not a panic.
#[test]
fn a_status_fail_names_the_final_stderr_line() {
    let ending = faulted_child(
        ChildExit::Status(1),
        &[
            "thread '<unnamed>' panicked at platforms/p/src/lib.rs:3:5:",
            "boom",
            DISPATCH_FAULT,
        ],
    );
    assert_eq!(
        open_outcome(&ending),
        TestOutcome::Fail {
            reason: format!("test process exited with status 1 without a result: {DISPATCH_FAULT}")
        }
    );
}

// spec: design/int/test-runner.md §10 test-child row 9 — negative legs: with no
// stderr the reason names only the status; a signal names only the signal
// though stderr has lines; the panic row is unchanged when a later line follows
// the prefixed one.
#[test]
fn a_fail_names_only_what_the_ending_supports() {
    assert_eq!(
        open_outcome(&faulted_child(ChildExit::Status(1), &[])),
        TestOutcome::Fail {
            reason: "test process exited with status 1 without a result".to_string()
        }
    );
    assert_eq!(
        open_outcome(&faulted_child(
            ChildExit::Signal(11),
            &["hook", DISPATCH_FAULT]
        )),
        TestOutcome::Fail {
            reason: "test process was killed by signal 11".to_string()
        }
    );
    let prefixed = format!("{PANIC_REPORT_PREFIX}division by zero");
    assert_eq!(
        open_outcome(&faulted_child(
            ChildExit::Status(PANIC_EXIT_STATUS),
            &[&prefixed, "a later line"],
        )),
        TestOutcome::Panic {
            reason: "division by zero".to_string()
        }
    );
}

// spec: design/int/test-runner.md §10 test-child row 9 — the stderr relay
// copies every line through and keeps the final line and, separately, the last
// prefixed line.
#[test]
fn relay_keeps_the_final_line_and_the_last_prefixed_line_separately() {
    let early = format!("{PANIC_REPORT_PREFIX}first");
    let late = format!("{PANIC_REPORT_PREFIX}second");
    let input = format!("hook\n{early}\n{late}\ntrailing report\n");
    let mut relayed = Vec::new();
    let tail = relay_stderr(input.as_bytes(), &mut relayed);
    assert_eq!(String::from_utf8(relayed).unwrap(), input);
    assert_eq!(
        tail,
        StderrTail {
            last_line: Some("trailing report".to_string()),
            last_panic_line: Some(late),
        }
    );
}

// spec: design/int/test-runner.md §6.5 — the record transport is per run: the
// supervisor owns a fresh directory, so records it did not cause cannot reach
// its report (REPL §16.2, one result per selected test). A directory already at
// a candidate name, here holding a forged record, is passed over and survives
// the run untouched.
#[test]
fn run_directory_is_fresh_and_never_another_runs() {
    let base = tempfile::tempdir().unwrap();
    let taken = base.path().join("taken");
    std::fs::create_dir(&taken).unwrap();
    let forged = "start user/test-forged\npass\n";
    std::fs::write(taken.join("records-1"), forged).unwrap();

    let dir = RunDir::create_in(base.path(), ["taken".to_string(), "fresh".to_string()])
        .expect("a fresh candidate remains");
    assert_eq!(dir.path, base.path().join("fresh"));
    assert!(
        read_records(&dir.path.join("records-1"))
            .unwrap()
            .is_empty()
    );
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let mode = std::fs::metadata(&dir.path).unwrap().permissions().mode();
        assert_eq!(mode & 0o077, 0, "the run directory is private: {mode:o}");
    }
    drop(dir);

    assert!(!base.path().join("fresh").exists());
    assert_eq!(
        std::fs::read_to_string(taken.join("records-1")).unwrap(),
        forged
    );
    let refused = RunDir::create_in(base.path(), ["taken".to_string()]);
    assert!(refused.is_err(), "an existing directory is never adopted");
    assert!(taken.join("records-1").exists());
}

// spec: design/int/test-runner.md §6.5 — each child writes a fresh record file;
// an existing file at the path is refused rather than appended to.
#[test]
fn record_sink_refuses_an_existing_file() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("records-1");
    std::fs::write(&path, "start user/test-forged\n").unwrap();
    assert!(RecordSink::create(&path).is_err());
    assert_eq!(
        std::fs::read_to_string(&path).unwrap(),
        "start user/test-forged\n"
    );

    let fresh = dir.path().join("records-2");
    let mut sink = RecordSink::create(&fresh).unwrap();
    sink.write(&Record::End).unwrap();
    assert_eq!(read_records(&fresh).unwrap(), [Record::End]);
}
