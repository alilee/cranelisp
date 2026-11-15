//! The test child and its supervisor (`design/int/test-runner.md` §6.5).
//!
//! A runtime panic ends the process running the test, so the runner runs its
//! tests in a child process of this binary and restarts the child after a
//! panic. The supervisor never compiles or runs a test. It reads the records
//! the child streams to a file, classifies how each child ended and builds the
//! one `TestRunReport`. The record format is private to this module.

use std::ffi::OsString;
use std::io::{BufRead, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::Instant;

use cranelisp_intrinsics::panic::{PANIC_EXIT_STATUS, PANIC_REPORT_PREFIX};
use cranelisp_types::{
    CranelispError, ErrorLocation, FQSymbol, ModuleFullPath, Span, Symbol, Warning, WarningKind,
};

use super::run::{TestOutcome, TestRunReport};

/// The child's record-file argument. With the two below these are internal
/// spellings (`repl/spec/00-cli-invocation.md` §0.2.2, Internal child
/// arguments); `src/main.rs` parses the same three.
const RECORDS_FLAG: &str = "--test-child-records";
/// One selected module; repeated, in selection order.
const MODULE_FLAG: &str = "--test-child-module";
/// The resume point: only tests that sort after this FQ name run.
const RESUME_FLAG: &str = "--test-child-resume";

/// Added to the child's environment so the child does not re-read the
/// environment files its parent already supplied
/// (`design/int/environment.md` §2.2).
const NO_ENV_VAR: &str = "CRANELISP_NO_ENV";

/// One record in the child's record file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum Record {
    /// A §16.1 discovery warning. Warnings precede the first `Start`.
    Warning(String),
    /// Written before the test is called.
    Start(FQSymbol),
    /// The outcome of the test last started.
    Outcome(TestOutcome),
    /// Written after the last outcome.
    End,
}

impl Record {
    /// One line, with the reason escaped so that it cannot span lines.
    fn encode(&self) -> String {
        match self {
            Record::Warning(message) => format!("warning {}\n", escape(message)),
            Record::Start(id) => format!("start {id}\n"),
            Record::Outcome(TestOutcome::Pass) => "pass\n".to_string(),
            Record::Outcome(TestOutcome::Fail { reason }) => format!("fail {}\n", escape(reason)),
            Record::Outcome(TestOutcome::Panic { reason }) => {
                format!("panic {}\n", escape(reason))
            }
            Record::End => "end\n".to_string(),
        }
    }

    fn decode(line: &str) -> Option<Record> {
        let (tag, rest) = line.split_once(' ').unwrap_or((line, ""));
        Some(match tag {
            "warning" => Record::Warning(unescape(rest)?),
            "start" => Record::Start(parse_fq(rest)?),
            "pass" if rest.is_empty() => Record::Outcome(TestOutcome::Pass),
            "fail" => Record::Outcome(TestOutcome::Fail {
                reason: unescape(rest)?,
            }),
            "panic" => Record::Outcome(TestOutcome::Panic {
                reason: unescape(rest)?,
            }),
            "end" if rest.is_empty() => Record::End,
            _ => return None,
        })
    }
}

fn escape(text: &str) -> String {
    text.replace('\\', "\\\\").replace('\n', "\\n")
}

fn unescape(text: &str) -> Option<String> {
    let mut out = String::with_capacity(text.len());
    let mut chars = text.chars();
    while let Some(c) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        match chars.next()? {
            '\\' => out.push('\\'),
            'n' => out.push('\n'),
            _ => return None,
        }
    }
    Some(out)
}

/// An FQ test name as `FQSymbol`'s display writes it: the module path, which
/// contains no `/`, then `/` and the symbol.
fn parse_fq(text: &str) -> Option<FQSymbol> {
    let (module, symbol) = text.split_once('/')?;
    (!module.is_empty() && !symbol.is_empty()).then(|| FQSymbol {
        module: ModuleFullPath::from(module),
        symbol: Symbol::from(symbol),
    })
}

/// The child's append-only record file. Each record is one `write`, so a
/// record written before the process ends at a panic survives it.
pub(super) struct RecordSink {
    file: std::fs::File,
    path: PathBuf,
}

impl RecordSink {
    pub(super) fn create(path: &Path) -> Result<Self, CranelispError> {
        let file = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(path)
            .map_err(|e| record_error(path, &e))?;
        Ok(Self {
            file,
            path: path.to_path_buf(),
        })
    }

    pub(super) fn write(&mut self, record: &Record) -> Result<(), CranelispError> {
        self.file
            .write_all(record.encode().as_bytes())
            .map_err(|e| record_error(&self.path, &e))
    }
}

fn record_error(path: &Path, error: &std::io::Error) -> CranelispError {
    internal_error(format!(
        "test child cannot write its record file {}: {error}",
        path.display()
    ))
}

fn internal_error(message: String) -> CranelispError {
    CranelispError::ModuleError {
        message,
        location: ErrorLocation::from_span(Span::SYNTHETIC),
    }
}

/// How a child process ended.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum ChildExit {
    Status(i32),
    Signal(i32),
}

/// Everything the supervisor reads from one ended child.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct ChildEnding {
    pub(super) records: Vec<Record>,
    pub(super) exit: ChildExit,
    pub(super) stderr: StderrTail,
}

/// What the supervisor keeps of a child's stderr after relaying it.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(super) struct StderrTail {
    /// The final line, whatever it begins with. When the runtime's terminator
    /// ended the child this is its fault report.
    pub(super) last_line: Option<String>,
    /// The last line that began with the panic report prefix.
    pub(super) last_panic_line: Option<String>,
}

/// Starts one child and waits for it to end. The production launcher spawns
/// this binary; module tests script the endings.
pub(super) trait ChildLauncher {
    fn run_child(&mut self, resume_after: Option<&FQSymbol>)
    -> Result<ChildEnding, CranelispError>;
}

/// What one child's records and ending mean (the §6.5 table).
#[derive(Debug, PartialEq, Eq)]
struct Classified {
    warnings: Vec<String>,
    completed: Vec<(FQSymbol, TestOutcome)>,
    next: Next,
}

#[derive(Debug, PartialEq, Eq)]
enum Next {
    /// `end` was recorded: the run is complete.
    Done,
    /// A test was open when the child ended; restart after it.
    RestartAfter(FQSymbol, TestOutcome),
    /// Neither an open test nor `end`: the run could not proceed.
    Stopped,
}

fn classify(ending: &ChildEnding) -> Result<Classified, CranelispError> {
    let mut warnings = Vec::new();
    let mut completed = Vec::new();
    let mut open: Option<FQSymbol> = None;
    let mut ended = false;
    for record in &ending.records {
        match record {
            Record::Warning(message) => warnings.push(message.clone()),
            Record::Start(id) => open = Some(id.clone()),
            Record::Outcome(outcome) => match open.take() {
                Some(id) => completed.push((id, outcome.clone())),
                None => return Err(malformed("an outcome with no started test")),
            },
            Record::End => ended = true,
        }
    }
    let next = match (open, ended) {
        (None, true) => Next::Done,
        (Some(id), false) => Next::RestartAfter(id, open_test_outcome(ending)),
        (Some(_), true) => return Err(malformed("`end` with a test still open")),
        (None, false) => Next::Stopped,
    };
    Ok(Classified {
        warnings,
        completed,
        next,
    })
}

fn malformed(what: &str) -> CranelispError {
    internal_error(format!("test child record file is malformed: {what}"))
}

/// The outcome of the test that was open when its child ended. A panic is
/// classified by the panic status AND a prefixed stderr line together; the
/// status alone is shared with other failures. Any other status names the
/// child's final stderr line, which is the terminator's fault report when the
/// runtime ended the child; a signal leaves no report.
fn open_test_outcome(ending: &ChildEnding) -> TestOutcome {
    match (ending.exit, &ending.stderr.last_panic_line) {
        (ChildExit::Status(PANIC_EXIT_STATUS), Some(line)) => TestOutcome::Panic {
            reason: line
                .strip_prefix(PANIC_REPORT_PREFIX)
                .unwrap_or(line)
                .to_string(),
        },
        (ChildExit::Status(code), _) => {
            let status = format!("test process exited with status {code} without a result");
            TestOutcome::Fail {
                reason: match &ending.stderr.last_line {
                    Some(cause) => format!("{status}: {cause}"),
                    None => status,
                },
            }
        }
        (ChildExit::Signal(signal), _) => TestOutcome::Fail {
            reason: format!("test process was killed by signal {signal}"),
        },
    }
}

/// Run children until the run completes, restarting after each open test.
///
/// Every restart follows a child that consumed at least one test, and the
/// resume point must advance in FQ order, so a run of `N` tests uses at most
/// `N + 1` children.
pub(super) fn supervise(
    launcher: &mut impl ChildLauncher,
) -> Result<TestRunReport, CranelispError> {
    let start = Instant::now();
    let mut outcomes: Vec<(FQSymbol, TestOutcome)> = Vec::new();
    let mut warnings: Option<Vec<String>> = None;
    let mut resume: Option<FQSymbol> = None;
    loop {
        let ending = launcher.run_child(resume.as_ref())?;
        let classified = classify(&ending)?;
        // A restart rescans the same sources, so only the first child's
        // warnings are reported.
        warnings.get_or_insert(classified.warnings);
        outcomes.extend(classified.completed);
        match classified.next {
            Next::Done => break,
            Next::Stopped => {
                return Err(internal_error(
                    "the test run stopped before it completed; the test child's \
                     diagnostic is above"
                        .to_string(),
                ));
            }
            Next::RestartAfter(id, outcome) => {
                if resume.as_ref().is_some_and(|previous| id <= *previous) {
                    return Err(internal_error(format!(
                        "the test child reran `{id}` after resuming past it"
                    )));
                }
                outcomes.push((id.clone(), outcome));
                resume = Some(id);
            }
        }
    }
    let warnings = warnings
        .unwrap_or_default()
        .into_iter()
        .map(|message| Warning {
            kind: WarningKind::Other,
            message,
            span: Span::SYNTHETIC,
        })
        .collect();
    Ok(TestRunReport::new(outcomes, warnings, start.elapsed()))
}

/// The child's command line after the executable: the client's arguments
/// without its mode flag, then `--test` and the child arguments.
fn child_command_line(
    client_args: &[OsString],
    records: &Path,
    modules: Option<&[ModuleFullPath]>,
    resume_after: Option<&FQSymbol>,
) -> Vec<OsString> {
    let mut args = client_args.to_vec();
    args.push("--test".into());
    args.push(RECORDS_FLAG.into());
    args.push(records.as_os_str().to_owned());
    for module in modules.unwrap_or_default() {
        args.push(MODULE_FLAG.into());
        args.push(module.as_ref().into());
    }
    if let Some(id) = resume_after {
        args.push(RESUME_FLAG.into());
        args.push(id.to_string().into());
    }
    args
}

/// The child process: `args` after the executable, the parent's environment
/// plus the file-supply switch, stdout inherited and stderr piped for relay.
fn child_command(exe: &Path, args: Vec<OsString>) -> Command {
    let mut command = Command::new(exe);
    command
        .args(args)
        .env(NO_ENV_VAR, "1")
        .stdin(Stdio::null())
        .stdout(Stdio::inherit())
        .stderr(Stdio::piped());
    command
}

/// The production launcher: this binary, one child at a time, each with its
/// own record file in a per-run directory.
struct ProcessLauncher<'a> {
    exe: PathBuf,
    client_args: &'a [OsString],
    modules: Option<&'a [ModuleFullPath]>,
    dir: RunDir,
    children: usize,
}

impl ChildLauncher for ProcessLauncher<'_> {
    fn run_child(
        &mut self,
        resume_after: Option<&FQSymbol>,
    ) -> Result<ChildEnding, CranelispError> {
        self.children += 1;
        let records = self.dir.path.join(format!("records-{}", self.children));
        let mut child = child_command(
            &self.exe,
            child_command_line(self.client_args, &records, self.modules, resume_after),
        )
        .spawn()
        .map_err(|e| internal_error(format!("cannot start the test child: {e}")))?;
        let stderr = child
            .stderr
            .take()
            .map(|piped| relay_stderr(piped, std::io::stderr()))
            .unwrap_or_default();
        let status = child
            .wait()
            .map_err(|e| internal_error(format!("cannot wait for the test child: {e}")))?;
        Ok(ChildEnding {
            records: read_records(&records)?,
            exit: exit_of(status),
            stderr,
        })
    }
}

/// Relay the child's stderr to `out` line by line as it arrives, keeping its
/// tail for classification.
fn relay_stderr(stderr: impl std::io::Read, mut out: impl Write) -> StderrTail {
    let mut tail = StderrTail::default();
    for line in std::io::BufReader::new(stderr).split(b'\n') {
        let Ok(bytes) = line else { break };
        let _ = out.write_all(&bytes);
        let _ = out.write_all(b"\n");
        let _ = out.flush();
        let text = String::from_utf8_lossy(&bytes).into_owned();
        if text.starts_with(PANIC_REPORT_PREFIX) {
            tail.last_panic_line = Some(text.clone());
        }
        tail.last_line = Some(text);
    }
    tail
}

fn exit_of(status: std::process::ExitStatus) -> ChildExit {
    if let Some(code) = status.code() {
        return ChildExit::Status(code);
    }
    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt;
        if let Some(signal) = status.signal() {
            return ChildExit::Signal(signal);
        }
    }
    ChildExit::Status(-1)
}

/// A child that ended before creating its record file recorded nothing.
pub(super) fn read_records(path: &Path) -> Result<Vec<Record>, CranelispError> {
    let text = match std::fs::read_to_string(path) {
        Ok(text) => text,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(Vec::new()),
        Err(e) => {
            return Err(internal_error(format!(
                "cannot read the test child's record file {}: {e}",
                path.display()
            )));
        }
    };
    text.lines()
        .map(|line| Record::decode(line).ok_or_else(|| malformed(line)))
        .collect()
}

/// A per-run temporary directory, removed when the run ends.
struct RunDir {
    path: PathBuf,
}

impl RunDir {
    fn create() -> Result<Self, CranelispError> {
        static RUNS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
        let run = RUNS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("cranelisp-test-run-{}-{run}", std::process::id()));
        std::fs::create_dir_all(&path).map_err(|e| {
            internal_error(format!(
                "cannot create the test run directory {}: {e}",
                path.display()
            ))
        })?;
        Ok(Self { path })
    }
}

impl Drop for RunDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.path);
    }
}

/// Supervise one test run: start the test child of this binary with
/// `client_args`, restart it after each panicking test, and report.
///
/// `client_args` are the client's command-line arguments without the program
/// name and without `--test`, so the child resolves the same target with the
/// same worker and cache settings. `modules` is the REPL's selection; `None`
/// has the child walk the entry chain, as `--test` does.
///
/// This needs no session: the supervisor compiles and runs nothing itself.
/// Each child's stderr is relayed to this process's stderr as it arrives; its
/// stdout is inherited.
///
/// **Errors:** `Err` means the run could not start, or a child ended with
/// neither a test open nor the run complete, for example on a compile error
/// or a refused `discover-tests` reference. The child's own diagnostic has
/// then already reached stderr.
pub fn supervise_tests(
    child_args: &[OsString],
    modules: Option<&[ModuleFullPath]>,
) -> Result<TestRunReport, CranelispError> {
    let exe = std::env::current_exe()
        .map_err(|e| internal_error(format!("cannot locate the compiler executable: {e}")))?;
    let mut launcher = ProcessLauncher {
        exe,
        client_args: child_args,
        modules,
        dir: RunDir::create()?,
        children: 0,
    };
    supervise(&mut launcher)
}

#[cfg(test)]
mod tests;
