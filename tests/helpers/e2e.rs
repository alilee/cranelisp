//! E2E harness for Cranelisp subprocess tests.
//!
//! Implements the `Cranelisp` builder + `CrInvocation` + `CrOutput`
//! per `tests/plan/helpers-api.md`. Per-test fresh `tempfile::TempDir`
//! by construction. Pipe-then-parse-stdin pattern only.
//!
//! Subprocess only — no `cranelisp::session_v4::CompilerSession`, no
//! `SharedState`, no internal-API construction. Per the strategy
//! direction recorded in `memory/project_test_strategy.md` (2026-05-03).

#![allow(dead_code)]

use std::ffi::OsString;
use std::fs;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Stdio};
use std::time::{Duration, Instant};

use regex::Regex;

// =============================================================================
// Errors
// =============================================================================

/// Failure modes the harness can hit before `CrOutput` is produced.
#[derive(Debug)]
pub enum CrError {
    /// `target/debug/cranelisp` not found at the expected path.
    BinaryNotFound(PathBuf),
    /// Spawn failed (permission, ENOENT on a CWD, etc.).
    SpawnFailed(io::Error),
    /// Child did not exit within the configured timeout.
    Timeout(Duration),
    /// Writing piped stdin failed (broken pipe, child died early).
    StdinWriteFailed(io::Error),
    /// Fixture source path is missing or unreadable.
    FixtureMissing(PathBuf),
}

impl std::fmt::Display for CrError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CrError::BinaryNotFound(p) => {
                write!(f, "cranelisp binary not found at {} — run `cargo build` first", p.display())
            }
            CrError::SpawnFailed(e) => write!(f, "spawn failed: {e}"),
            CrError::Timeout(d) => write!(f, "child did not exit within {d:?}"),
            CrError::StdinWriteFailed(e) => write!(f, "stdin write failed: {e}"),
            CrError::FixtureMissing(p) => write!(f, "fixture missing or unreadable: {}", p.display()),
        }
    }
}

impl std::error::Error for CrError {}

// =============================================================================
// PreludeVariant
// =============================================================================

/// Curated test prelude variants. Stored as fixture files under
/// `tests/fixtures/preludes/`; the harness copies the right one to
/// `prelude.cl` in the per-test TempDir.
#[derive(Debug, Clone, Copy)]
pub enum PreludeVariant {
    /// No prelude file dropped.
    None,
    /// `(import [primitives [*]])` only — bare primitive names, no
    /// traits, no ADTs, no operators. File: `preludes/primitives-only.cl`.
    PrimitivesOnly,
    /// Option, Result, Num, Eq, Ord — `tests/fixtures/preludes/test-standard.cl`
    /// (currently the existing `tests/fixtures/prelude.cl` content).
    TestStandard,
}

impl PreludeVariant {
    /// Filename under `tests/fixtures/preludes/` for this variant.
    /// `None` returns `None`.
    fn fixture_filename(&self) -> Option<&'static str> {
        match self {
            PreludeVariant::None => None,
            PreludeVariant::PrimitivesOnly => Some("primitives-only.cl"),
            PreludeVariant::TestStandard => Some("test-standard.cl"),
        }
    }
}

// =============================================================================
// Mode
// =============================================================================

#[derive(Debug, Clone)]
enum Mode {
    Repl,
    Run(String),
    Link(String),
    LinkThenRun(String),
}

// =============================================================================
// Cranelisp builder
// =============================================================================

/// One Cranelisp invocation. Builder pattern: configure, then run.
///
/// Defaults:
///  - mode: REPL (no `--run`, no `--link`)
///  - prelude: NONE (no prelude file dropped; binary's auto-discovery
///    finds nothing in the fresh TempDir)
///  - stdin: empty
///  - lib_dirs: empty
///  - env: clean — no trace flags, no special vars
///  - cwd: a fresh per-test TempDir (held inside the builder)
pub struct Cranelisp {
    /// Per-test TempDir. Held until the resulting `CrOutput` drops so
    /// fixtures and `.cranelisp-cache/` survive for inspection.
    tmpdir: tempfile::TempDir,
    mode: Mode,
    stdin: String,
    env: Vec<(String, String)>,
    cli_flags: Vec<String>,
    /// Directories under TempDir to add to CRANELISP_LIB.
    lib_dirs: Vec<PathBuf>,
    /// Use the workspace stdlib/ directory for CRANELISP_LIB.
    use_workspace_stdlib: bool,
    /// Use the workspace target/debug/ for CRANELISP_PLATFORM_PATH.
    use_workspace_platforms: bool,
    /// Hard wall-clock cap.
    timeout: Duration,
}

impl Cranelisp {
    /// Construct a fresh builder backed by a per-test `tempfile::TempDir`.
    pub fn new() -> Self {
        let tmpdir = tempfile::tempdir().expect("TempDir creation");
        Cranelisp {
            tmpdir,
            mode: Mode::Repl,
            stdin: String::new(),
            env: Vec::new(),
            cli_flags: Vec::new(),
            lib_dirs: Vec::new(),
            use_workspace_stdlib: false,
            use_workspace_platforms: false,
            timeout: Duration::from_secs(30),
        }
    }

    // === Mode (mutually exclusive) ============================================

    /// Run as REPL (default). Equivalent to no `--run`/`--link`.
    pub fn repl(mut self) -> Self {
        self.mode = Mode::Repl;
        self
    }

    /// Batch run via `--run <file>`.
    pub fn run(mut self, file: &str) -> Self {
        self.mode = Mode::Run(file.to_string());
        self
    }

    /// Link via `--link <file>` only — produces an executable, does not run it.
    pub fn link(mut self, file: &str) -> Self {
        self.mode = Mode::Link(file.to_string());
        self
    }

    /// Link via `--link <file>` and then exec the produced binary.
    pub fn link_then_run(mut self, file: &str) -> Self {
        self.mode = Mode::LinkThenRun(file.to_string());
        self
    }

    // === On-disk fixture composition =========================================

    /// Drop a file at `rel_path` under the per-test TempDir; creates parent dirs.
    pub fn file(self, rel_path: &str, contents: &str) -> Self {
        let full = self.tmpdir.path().join(rel_path);
        if let Some(parent) = full.parent() {
            fs::create_dir_all(parent)
                .unwrap_or_else(|e| panic!("create_dir_all {}: {e}", parent.display()));
        }
        fs::write(&full, contents)
            .unwrap_or_else(|e| panic!("write {}: {e}", full.display()));
        self
    }

    /// Convenience: drop `user.cl` with the given contents (the conventional entry).
    pub fn user(self, contents: &str) -> Self {
        self.file("user.cl", contents)
    }

    /// Convenience: drop `prelude.cl` with the given contents at TempDir root.
    pub fn prelude(self, contents: &str) -> Self {
        self.file("prelude.cl", contents)
    }

    /// Materialise a named prelude variant from the catalogue.
    pub fn with_prelude(self, variant: PreludeVariant) -> Self {
        let Some(filename) = variant.fixture_filename() else {
            return self;
        };
        let src = workspace_root()
            .join("tests")
            .join("fixtures")
            .join("preludes")
            .join(filename);
        let contents = fs::read_to_string(&src)
            .unwrap_or_else(|e| panic!("read prelude fixture {}: {e}", src.display()));
        self.file("prelude.cl", &contents)
    }

    /// Copy `tests/fixtures/<src>` into TempDir at `<dst>`. Read-only on src.
    pub fn fixture(self, src: &str, dst: &str) -> Self {
        let from = workspace_root().join("tests").join("fixtures").join(src);
        if !from.exists() {
            panic!("fixture missing: {}", from.display());
        }
        let to = self.tmpdir.path().join(dst);
        if let Some(parent) = to.parent() {
            fs::create_dir_all(parent)
                .unwrap_or_else(|e| panic!("create_dir_all {}: {e}", parent.display()));
        }
        fs::copy(&from, &to)
            .unwrap_or_else(|e| panic!("copy {} -> {}: {e}", from.display(), to.display()));
        self
    }

    /// Recursive variant: copy `tests/fixtures/<src_dir>/` tree into `<dst_dir>/`.
    pub fn fixture_tree(self, src_dir: &str, dst_dir: &str) -> Self {
        let from = workspace_root().join("tests").join("fixtures").join(src_dir);
        if !from.exists() {
            panic!("fixture tree missing: {}", from.display());
        }
        let to = self.tmpdir.path().join(dst_dir);
        copy_dir_recursive(&from, &to)
            .unwrap_or_else(|e| panic!("copy tree {} -> {}: {e}", from.display(), to.display()));
        self
    }

    // === Search-path & platform configuration ================================

    /// Add a directory under TempDir to `CRANELISP_LIB`.
    pub fn lib_dir(mut self, dir_under_tmpdir: &str) -> Self {
        self.lib_dirs.push(self.tmpdir.path().join(dir_under_tmpdir));
        self
    }

    /// **Gated escape hatch — only `tests/stdlib.rs` may legitimately call this.**
    /// Sets `CRANELISP_LIB` to the workspace `stdlib/` directory. Named
    /// verbosely so misuse is visible in PR review and `git grep` audits;
    /// stdlib conformance is the single named exception to the
    /// "tests must not depend on stdlib" rule (root `CLAUDE.md`
    /// §"Design Principles" — Stdlib separation).
    pub fn use_workspace_stdlib_for_stdlib_conformance_only(mut self) -> Self {
        self.use_workspace_stdlib = true;
        self
    }

    /// Sets `CRANELISP_PLATFORM_PATH` to the workspace `target/debug/` so the
    /// child can `dlopen` the workspace platform DLLs (`stdio`, `test-capture`).
    pub fn use_workspace_platforms(mut self) -> Self {
        self.use_workspace_platforms = true;
        self
    }

    // === Stdin ==============================================================

    /// Pipe a literal string to the child's stdin.
    pub fn stdin(mut self, lines: &str) -> Self {
        self.stdin = lines.to_string();
        self
    }

    /// Pipe a slice of lines joined by `\n` (with a trailing newline).
    pub fn stdin_lines(mut self, lines: &[&str]) -> Self {
        let mut s = lines.join("\n");
        s.push('\n');
        self.stdin = s;
        self
    }

    // === Environment & flags ================================================

    /// Append a `(key, val)` to the child's env. Last write wins.
    pub fn env(mut self, key: &str, val: &str) -> Self {
        self.env.push((key.to_string(), val.to_string()));
        self
    }

    /// Append a raw CLI flag passed to the cranelisp binary. Escape hatch.
    pub fn cli_flag(mut self, flag: &str) -> Self {
        self.cli_flags.push(flag.to_string());
        self
    }

    // === Run ================================================================

    /// Materialise the invocation, spawn the child, capture output.
    /// Panics on any `CrError` (binary missing, spawn fail, timeout, IO).
    pub fn output(self) -> CrOutput {
        match self.try_output() {
            Ok(out) => out,
            Err(e) => panic!("Cranelisp::output failed: {e}"),
        }
    }

    /// Non-panicking variant — returns the `CrError` instead.
    pub fn try_output(self) -> Result<CrOutput, CrError> {
        let invocation = self.materialise();
        invocation.spawn_and_capture()
    }

    /// Materialise the invocation snapshot just before spawn.
    fn materialise(self) -> CrInvocationOwned {
        let binary = workspace_root()
            .join("target")
            .join("debug")
            .join("cranelisp");

        let mut args: Vec<String> = Vec::new();
        let mode_post: Option<(PathBuf, bool)> = match &self.mode {
            Mode::Repl => None,
            Mode::Run(file) => {
                args.push("--run".to_string());
                args.push(file.clone());
                None
            }
            Mode::Link(file) => {
                args.push("--link".to_string());
                args.push(file.clone());
                None
            }
            Mode::LinkThenRun(file) => {
                args.push("--link".to_string());
                args.push(file.clone());
                // Caller wants the produced binary executed too. The convention
                // is the linker emits `<stem>` next to the source. We stash the
                // produced-binary path so spawn_and_capture can run it after
                // link succeeds.
                let stem = Path::new(file)
                    .file_stem()
                    .and_then(|s| s.to_str())
                    .unwrap_or("a.out")
                    .to_string();
                let produced = self.tmpdir.path().join(stem);
                Some((produced, true))
            }
        };

        for f in &self.cli_flags {
            args.push(f.clone());
        }

        // Build env overlay.
        let mut env: Vec<(String, String)> = Vec::new();
        if !self.lib_dirs.is_empty() || self.use_workspace_stdlib {
            // Compose CRANELISP_LIB.
            let mut parts: Vec<OsString> = Vec::new();
            for d in &self.lib_dirs {
                parts.push(d.as_os_str().to_owned());
            }
            if self.use_workspace_stdlib {
                parts.push(workspace_root().join("stdlib").into_os_string());
            }
            // Use ':' as a separator; we expect single-dir use mostly.
            let joined = parts
                .iter()
                .map(|p| p.to_string_lossy().into_owned())
                .collect::<Vec<_>>()
                .join(":");
            env.push(("CRANELISP_LIB".to_string(), joined));
        }
        if self.use_workspace_platforms {
            env.push((
                "CRANELISP_PLATFORM_PATH".to_string(),
                workspace_root()
                    .join("target")
                    .join("debug")
                    .to_string_lossy()
                    .into_owned(),
            ));
        }
        for (k, v) in self.env {
            env.push((k, v));
        }

        let cwd = self.tmpdir.path().to_path_buf();

        CrInvocationOwned {
            binary,
            args,
            cwd,
            env,
            stdin: self.stdin,
            timeout: self.timeout,
            tmpdir: self.tmpdir,
            link_then_run: mode_post,
        }
    }
}

impl Default for Cranelisp {
    fn default() -> Self {
        Self::new()
    }
}

// =============================================================================
// CrInvocation — public snapshot
// =============================================================================

/// The fully-resolved invocation snapshot. Constructed by `Cranelisp::output`
/// just before `Command::spawn`. Kept as a separate type so the spawn step
/// is testable in isolation (does the right argv get assembled?).
#[derive(Debug, Clone)]
pub struct CrInvocation {
    /// Path to `target/debug/cranelisp`.
    pub binary: PathBuf,
    /// Argv (excluding `argv[0]`).
    pub args: Vec<String>,
    /// Working directory the child sees (== project_root from its perspective).
    pub cwd: PathBuf,
    /// Environment overlay applied on top of the parent's env.
    pub env: Vec<(String, String)>,
    /// Stdin to pipe.
    pub stdin: String,
    /// Hard wall-clock cap for the child run.
    pub timeout: Duration,
}

/// Internal owned form: holds the TempDir handle until `CrOutput` takes it.
struct CrInvocationOwned {
    binary: PathBuf,
    args: Vec<String>,
    cwd: PathBuf,
    env: Vec<(String, String)>,
    stdin: String,
    timeout: Duration,
    tmpdir: tempfile::TempDir,
    /// If Some, after the child completes successfully, exec the produced binary.
    link_then_run: Option<(PathBuf, bool)>,
}

impl CrInvocationOwned {
    fn spawn_and_capture(self) -> Result<CrOutput, CrError> {
        if !self.binary.exists() {
            return Err(CrError::BinaryNotFound(self.binary.clone()));
        }

        let started = Instant::now();
        let mut cmd = Command::new(&self.binary);
        cmd.current_dir(&self.cwd)
            .args(&self.args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        for (k, v) in &self.env {
            cmd.env(k, v);
        }

        let mut child = cmd.spawn().map_err(CrError::SpawnFailed)?;

        if !self.stdin.is_empty() {
            let mut stdin = child.stdin.take().expect("piped stdin");
            stdin
                .write_all(self.stdin.as_bytes())
                .map_err(CrError::StdinWriteFailed)?;
            // Drop stdin to close the pipe so the child can EOF-out of REPL.
            drop(stdin);
        } else {
            // Close stdin so REPL exits on EOF.
            drop(child.stdin.take());
        }

        // Wait with timeout. Simple polling loop — keep it minimal.
        let deadline = started + self.timeout;
        loop {
            match child.try_wait() {
                Ok(Some(_status)) => break,
                Ok(None) => {
                    if Instant::now() >= deadline {
                        let _ = child.kill();
                        let _ = child.wait();
                        return Err(CrError::Timeout(self.timeout));
                    }
                    std::thread::sleep(Duration::from_millis(20));
                }
                Err(e) => return Err(CrError::SpawnFailed(e)),
            }
        }

        let output = child
            .wait_with_output()
            .map_err(CrError::SpawnFailed)?;
        let elapsed = started.elapsed();

        let mut status = output.status;
        let mut stdout = String::from_utf8_lossy(&output.stdout).into_owned();
        let mut stderr = String::from_utf8_lossy(&output.stderr).into_owned();

        // If link_then_run is set and link succeeded, exec the produced binary.
        if let Some((produced, _)) = &self.link_then_run {
            if status.success() && produced.exists() {
                let started2 = Instant::now();
                let mut cmd2 = Command::new(produced);
                cmd2.current_dir(&self.cwd)
                    .stdin(Stdio::null())
                    .stdout(Stdio::piped())
                    .stderr(Stdio::piped());
                for (k, v) in &self.env {
                    cmd2.env(k, v);
                }
                let out2 = cmd2.output().map_err(CrError::SpawnFailed)?;
                stdout.push_str(&String::from_utf8_lossy(&out2.stdout));
                stderr.push_str(&String::from_utf8_lossy(&out2.stderr));
                status = out2.status;
                let _ = started2; // elapsed already captured for overall run
            }
        }

        let tmpdir_path = self.tmpdir.path().to_path_buf();
        Ok(CrOutput {
            status,
            stdout,
            stderr,
            elapsed,
            tmpdir: tmpdir_path,
            _td: Some(self.tmpdir),
        })
    }
}

// =============================================================================
// CrOutput — captured outcome
// =============================================================================

/// Captured outcome of a Cranelisp child process.
pub struct CrOutput {
    pub status: ExitStatus,
    pub stdout: String,
    pub stderr: String,
    pub elapsed: Duration,
    pub tmpdir: PathBuf,
    /// Held internally so cleanup runs on drop.
    _td: Option<tempfile::TempDir>,
}

impl CrOutput {
    // === Exit-code shortcuts ================================================

    /// Assert the child exited with code 0.
    pub fn assert_ok(self) -> Self {
        if !self.status.success() {
            panic!(
                "expected exit 0, got status={:?}\nstdout:\n{}\nstderr:\n{}",
                self.status, self.stdout, self.stderr
            );
        }
        self
    }

    /// Assert the child exited with a specific code.
    pub fn assert_exit(self, code: i32) -> Self {
        match self.status.code() {
            Some(c) if c == code => self,
            other => panic!(
                "expected exit {code}, got {:?}\nstdout:\n{}\nstderr:\n{}",
                other, self.stdout, self.stderr
            ),
        }
    }

    /// Assert the child terminated by signal (no exit code, e.g. SIGSEGV).
    pub fn assert_signaled(self) -> Self {
        if self.status.code().is_some() {
            panic!(
                "expected signal termination, got exit {:?}\nstdout:\n{}\nstderr:\n{}",
                self.status.code(),
                self.stdout,
                self.stderr
            );
        }
        self
    }

    // === Stdout assertions ==================================================

    /// Assert stdout equals expected exactly.
    pub fn assert_stdout_eq(self, expected: &str) -> Self {
        if self.stdout != expected {
            panic!(
                "stdout mismatch\nexpected:\n{}\nactual:\n{}",
                expected, self.stdout
            );
        }
        self
    }

    /// Assert stdout contains the literal substring.
    pub fn assert_stdout_contains(self, needle: &str) -> Self {
        if !self.stdout.contains(needle) {
            panic!(
                "stdout missing expected substring '{}'\nstdout:\n{}",
                needle, self.stdout
            );
        }
        self
    }

    /// Assert stdout matches the given pre-compiled regex.
    pub fn assert_stdout_matches(self, re: &Regex) -> Self {
        if !re.is_match(&self.stdout) {
            panic!(
                "stdout does not match regex {:?}\nstdout:\n{}",
                re.as_str(),
                self.stdout
            );
        }
        self
    }

    // === Stderr assertions ==================================================

    /// **Spec-correct check**: when no `CRANELISP_*_TRACE` env var is set
    /// (the harness default), stderr MUST be empty per `repl/spec.md §5.1`.
    pub fn assert_stderr_empty(self) -> Self {
        if !self.stderr.is_empty() {
            panic!(
                "expected empty stderr (spec: repl/spec.md §5.1)\nstderr:\n{}",
                self.stderr
            );
        }
        self
    }

    /// Assert stderr contains the literal substring.
    pub fn assert_stderr_contains(self, needle: &str) -> Self {
        if !self.stderr.contains(needle) {
            panic!(
                "stderr missing expected substring '{}'\nstderr:\n{}",
                needle, self.stderr
            );
        }
        self
    }

    // === Snapshot / golden ==================================================

    /// Compare against `tests/fixtures/golden/<name>.txt` exactly.
    /// Updates with `CRANELISP_TEST_UPDATE_GOLDENS=1`.
    pub fn assert_golden(self, name: &str) -> Self {
        let path = workspace_root()
            .join("tests")
            .join("fixtures")
            .join("golden")
            .join(format!("{name}.txt"));
        if std::env::var("CRANELISP_TEST_UPDATE_GOLDENS").ok().as_deref() == Some("1") {
            if let Some(p) = path.parent() {
                fs::create_dir_all(p).expect("create golden dir");
            }
            fs::write(&path, &self.stdout).expect("write golden");
            return self;
        }
        let expected = fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("golden missing at {}: {e}", path.display()));
        if expected != self.stdout {
            panic!(
                "golden '{name}' mismatch\nexpected:\n{}\nactual:\n{}",
                expected, self.stdout
            );
        }
        self
    }

    /// Compare against the golden after applying each regex as a mask
    /// (every match replaced with the regex's literal source string).
    /// Use for output containing pointer addresses, timing, etc.
    pub fn assert_golden_masked(self, name: &str, masks: &[&Regex]) -> Self {
        let mut masked = self.stdout.clone();
        for re in masks {
            masked = re.replace_all(&masked, re.as_str()).into_owned();
        }
        let path = workspace_root()
            .join("tests")
            .join("fixtures")
            .join("golden")
            .join(format!("{name}.txt"));
        if std::env::var("CRANELISP_TEST_UPDATE_GOLDENS").ok().as_deref() == Some("1") {
            if let Some(p) = path.parent() {
                fs::create_dir_all(p).expect("create golden dir");
            }
            fs::write(&path, &masked).expect("write golden");
            return self;
        }
        let expected = fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("golden missing at {}: {e}", path.display()));
        if expected != masked {
            panic!(
                "golden '{name}' (masked) mismatch\nexpected:\n{}\nactual:\n{}",
                expected, masked
            );
        }
        self
    }

    // === Tmpdir inspection ==================================================

    /// Read a file under the per-test TempDir. Panics if missing.
    pub fn read_tmp(&self, rel_path: &str) -> String {
        let full = self.tmpdir.join(rel_path);
        fs::read_to_string(&full)
            .unwrap_or_else(|e| panic!("read_tmp {}: {e}", full.display()))
    }

    /// Test whether a path exists under the per-test TempDir.
    pub fn tmp_exists(&self, rel_path: &str) -> bool {
        self.tmpdir.join(rel_path).exists()
    }

    // === Cache-hit pattern (run binary twice in same TempDir) ==============

    /// Re-launch a fresh `Cranelisp` builder bound to the same TempDir,
    /// preserving the prior invocation's on-disk state (notably
    /// `.cranelisp-cache/`). Used to test cache-hit behaviour.
    ///
    /// The TempDir handle transfers from the consumed `CrOutput` into
    /// the new `Cranelisp`; `first.tmpdir` becomes invalid after the
    /// `run_again()` call.
    pub fn run_again(mut self) -> Cranelisp {
        let td = self
            ._td
            .take()
            .expect("run_again: TempDir already consumed");
        Cranelisp {
            tmpdir: td,
            mode: Mode::Repl,
            stdin: String::new(),
            env: Vec::new(),
            cli_flags: Vec::new(),
            lib_dirs: Vec::new(),
            use_workspace_stdlib: false,
            use_workspace_platforms: false,
            timeout: Duration::from_secs(30),
        }
    }
}

// =============================================================================
// Internal helpers
// =============================================================================

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn copy_dir_recursive(src: &Path, dst: &Path) -> io::Result<()> {
    fs::create_dir_all(dst)?;
    for entry in fs::read_dir(src)? {
        let entry = entry?;
        let ty = entry.file_type()?;
        let from = entry.path();
        let to = dst.join(entry.file_name());
        if ty.is_dir() {
            copy_dir_recursive(&from, &to)?;
        } else if ty.is_file() {
            fs::copy(&from, &to)?;
        }
    }
    Ok(())
}
