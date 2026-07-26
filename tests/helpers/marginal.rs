//! `helpers::marginal` — the **marginal-balance harness**.
//!
//! An exact-balance assertion over a compiler child (`allocs == deallocs` at
//! exit) is only as truthful as the child's baseline. Sprint 118 established
//! that it is not truthful at all today: **every** child that loads the stdlib
//! prelude carries a program-independent compile-time residual — 1143
//! allocations at S118 HEAD — from the int-side macro-turn marshal boundary
//! (FIXME 0889; `tests/plan/s118-test-plan.md` §2.5). An absolute
//! `allocs == deallocs` cell over such a child measures ONLY that residual. It
//! reads RED no matter what the runtime behaviour it is named after does, and
//! it would read GREEN again the moment 0889 is fixed *even if the named
//! runtime behaviour had rotted in the meantime*. Either way the cell is not an
//! instrument.
//!
//! The cure is accounting, not thresholds. This module measures a **pair** of
//! children that differ in exactly one thing — the workload under test — and
//! asserts on the **marginal** quantity
//!
//! ```text
//!     marginal_residual = (subject.allocs − subject.deallocs)
//!                       − (control.allocs − control.deallocs)
//! ```
//!
//! Every term common to both children — prelude load, macro expansion, session
//! bootstrap, the 0889 residual itself — cancels. What survives the subtraction
//! is exactly what the workload contributed, which is what the cell's name
//! claims to be about. The instrument stays valid after 0889 is fixed: the
//! common term simply goes to zero and the marginal is unchanged (0889
//! §"Resolution requirements", third bullet).
//!
//! A **threshold** ("residual ≤ 1400") is the anti-pattern this replaces: it
//! encodes today's ambient number into the assertion, so it silently absorbs
//! new leaks up to the slack and has to be re-derived every time the baseline
//! moves. A marginal has no slack to absorb anything and never needs
//! re-deriving.
//!
//! ## What varies between control and subject — and what must not
//!
//! The pair's ONE axis of variation is the caller's choice, and it is either:
//!
//!  - the **program** (`Child::new(src)`) — e.g. the same loop shape threading
//!    an `Int` accumulator (control) vs a persistent-collection `conj`
//!    (subject); or
//!  - the **library tree** (`Child::lib_file`) — e.g. a mini-prelude whose
//!    macro is defined-but-never-invoked (control) vs the same tree with one
//!    invocation (subject). This is the axis the FIXME-0889 exact-value pins
//!    use.
//!
//! Everything else is identical **by construction**, not by discipline: both
//! children are spawned from the same resolved binary, into freshly-created
//! private temp directories, with `--run --no-cache` (no cache hit can serve
//! one child a compile the other performed), through `env_clear()` plus one
//! enumerated allow-list, and with the same instrument armed. There is no
//! inherited environment to differ, and no shared state to carry over.
//!
//! ## The drive is a THIRD axis, and it is per-pair, never within one
//!
//! `Child::link_then_run()` measures the produced executable of a `--link`
//! instead of the JIT `--run` child (`--no-cache` is rejected by `--link`, so
//! the fresh per-child temp directory is what isolates the cache there). Both
//! halves of a pair MUST use the same drive — a control and subject that differ
//! in mode subtract two unrelated numbers. A cell wanting both faces measures
//! two pairs and asserts each, which is also what makes a mode divergence
//! visible as a divergence (root `CLAUDE.md`: a REPL/`--run`/`--link`
//! difference is always a defect).
//!
//! ## Environment allow-list (`env_clear` + exactly these)
//!
//! | Variable | Why |
//! |---|---|
//! | `CRANELISP_LIB` | the library tree under measurement |
//! | `CRANELISP_PLATFORM_PATH` | platform DLL resolution for the lane's target dir |
//! | `PATH` | **link drive only** — `--link` shells out to `cc` |
//! | instrument vars | see [`Instrument`] — armed per child, never at suite scope |
//! | `Child::env` extras | caller-declared, applied to that child only |
//!
//! Nothing else is passed — no `HOME`, no ambient `CRANELISP_*`.
//! This is the `intrinsics_m3_detection_s116` child pattern, and it is what
//! keeps the arming per-subprocess: see `tests/detector_arming_discipline_guard.rs`
//! and `design/intrinsics/diagnostic-modes.md` §7.1 (a `std::env::set_var`
//! against the `LazyLock` detector ledger is a silent no-op — arming that only
//! LOOKS armed).
//!
//! ## Cost
//!
//! A pair is two full compiler children with `--no-cache`, so a marginal cell
//! costs roughly twice an absolute one. That is the price of the instrument
//! being truthful; do not "optimise" it by caching a control measurement across
//! tests — a shared control is shared state, and the residual it is subtracting
//! is exactly the kind of thing that drifts with load and ordering.
//!
//! Provenance: S118 Branch-F closure (user decision 2026-07-26,
//! `sprints/SPRINT.md` §Notes). This is deliberately the first instance of the
//! commissioned S119 structural option paper's "marginal-balance harness"
//! option — built to be reused, not inlined into one cell.

#![allow(dead_code)]

use std::fmt::Write as _;
use std::path::PathBuf;
use std::process::{Command, ExitStatus, Stdio};
use std::time::{Duration, Instant};

use super::e2e::{binary_path, workspace_root};

/// Default wall-clock cap for ONE child. A full-stdlib `--run --no-cache`
/// child is a few seconds on a warm build; this is a hang fence, not a budget.
const DEFAULT_TIMEOUT: Duration = Duration::from_secs(120);

// =============================================================================
// Instrument
// =============================================================================

/// Which allocator instrument the pair is read through. Both report the same
/// two underlying counters; they differ in the code path that publishes them,
/// so a cell picks the one whose path it is actually about.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Instrument {
    /// `CRANELISP_RC_STATS=1` — the normal-exit `[RC_STATS]` counter line.
    /// Non-aborting: the child runs to completion and its exit code is the
    /// program's own value, so a cell can assert the result alongside the
    /// balance.
    RcStats,
    /// `CRANELISP_ALLOC_PARITY=1` **and** `CRANELISP_ALLOC_PARITY_DUMP=1` — the
    /// M3 detector's atexit path.
    ///
    /// The hard variable is what arms the detector (imbalance ⇒ dump, then
    /// `abort()`); the dump variable additionally makes the BALANCED case print
    /// its ledger line instead of exiting silently. Arming both means the
    /// counters are readable in either outcome — which is what a marginal needs,
    /// since it must subtract two numbers whether or not either child happened
    /// to be balanced. The hard abort is deliberately left armed: a cell that
    /// names the M3 wiring must exercise the production path, and the marginal
    /// is computed from the report the abort prints.
    AllocParity,
}

impl Instrument {
    fn env(self) -> &'static [(&'static str, &'static str)] {
        match self {
            Instrument::RcStats => &[("CRANELISP_RC_STATS", "1")],
            Instrument::AllocParity => &[
                ("CRANELISP_ALLOC_PARITY", "1"),
                ("CRANELISP_ALLOC_PARITY_DUMP", "1"),
            ],
        }
    }

    /// Extract `(allocs, deallocs)` from a child's stderr.
    ///
    /// `RcStats`: the `[RC_STATS] … allocs=N deallocs=N …` line.
    /// `AllocParity`: `ALLOC_COUNT=N DEALLOC_COUNT=N`, which appears in BOTH the
    /// imbalance report and the balanced ledger.
    fn parse(self, stderr: &str) -> Result<(i64, i64), String> {
        let (marker, alloc_key, dealloc_key) = match self {
            Instrument::RcStats => ("[RC_STATS]", "allocs=", "deallocs="),
            Instrument::AllocParity => ("[ALLOC_PARITY]", "ALLOC_COUNT=", "DEALLOC_COUNT="),
        };
        let line = stderr
            .lines()
            .find(|l| l.contains(marker) && l.contains(alloc_key))
            .ok_or_else(|| format!("no `{marker}` line carrying `{alloc_key}`"))?;
        let field = |k: &str| -> Result<i64, String> {
            line.split_whitespace()
                .find_map(|t| t.strip_prefix(k).and_then(|v| v.parse::<i64>().ok()))
                .ok_or_else(|| format!("no `{k}` in: {line}"))
        };
        Ok((field(alloc_key)?, field(dealloc_key)?))
    }
}

// =============================================================================
// Child — one half of a pair
// =============================================================================

/// The library tree a child compiles against.
#[derive(Clone, Debug)]
enum Lib {
    /// No `CRANELISP_LIB` at all.
    None,
    /// The workspace `stdlib/` tree. The ONE sanctioned stdlib touchpoint
    /// (root `CLAUDE.md` §"Stdlib separation"); a cell using it says so in its
    /// own header.
    WorkspaceStdlib,
    /// A tree materialised from inline `(relative path, contents)` pairs into a
    /// private temp directory. Self-describing: the fixture is readable at the
    /// callsite, which matters most for the pins whose whole point is the exact
    /// number a specific two-module shape produces.
    Files(Vec<(String, String)>),
}

/// How a child is driven — the mode face the pair is measured through.
///
/// A pair measures ONE drive; a cell that wants both faces measures two pairs,
/// because a REPL/`--run`/`--link` divergence is itself a defect and the two
/// numbers are separate evidence.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Drive {
    /// `--run user.cl --no-cache`; counters come from the compiler child's own
    /// exit report (the JIT ran the program in-process).
    Run,
    /// `--link user.cl`, then exec the produced executable; counters come from
    /// the PRODUCED binary's exit report, never the linking child's.
    ///
    /// `--no-cache` is rejected by `--link`, so cache isolation rests on the
    /// per-child fresh temp directory instead (there is nothing for a cache to
    /// hit — the tree is created empty for this measurement).
    LinkThenRun,
}

/// One measured compiler child: a single-file program, a library tree, the
/// drive, and any caller-declared extra environment.
#[derive(Clone, Debug)]
pub struct Child {
    program: String,
    lib: Lib,
    drive: Drive,
    extra_env: Vec<(String, String)>,
}

impl Child {
    /// A child running `program` as `user.cl` under `--run --no-cache`.
    pub fn new(program: &str) -> Self {
        Child {
            program: program.to_string(),
            lib: Lib::None,
            drive: Drive::Run,
            extra_env: Vec::new(),
        }
    }

    /// Drive this child through `--link` and then exec the produced binary,
    /// measuring the PRODUCED binary. Use for the `--link` face of an ownership
    /// pair: the two modes emit through different lowering paths, so a leak
    /// present in one and absent in the other is a finding, not a duplicate.
    pub fn link_then_run(mut self) -> Self {
        self.drive = Drive::LinkThenRun;
        self
    }

    /// Point `CRANELISP_LIB` at the workspace `stdlib/` tree.
    ///
    /// Named verbosely for the same reason as the `Cranelisp` builder's
    /// equivalent: tests are stdlib-free by rule, and every exception must be
    /// visible to `git grep`.
    pub fn use_workspace_stdlib_for_stdlib_conformance_only(mut self) -> Self {
        self.lib = Lib::WorkspaceStdlib;
        self
    }

    /// Add one file to an inline library tree (repeatable). `rel` may contain
    /// directory components (`fn/option.cl`); parents are created.
    pub fn lib_file(mut self, rel: &str, contents: &str) -> Self {
        match &mut self.lib {
            Lib::Files(v) => v.push((rel.to_string(), contents.to_string())),
            _ => self.lib = Lib::Files(vec![(rel.to_string(), contents.to_string())]),
        }
        self
    }

    /// Add one environment variable to THIS child only. Applied after the
    /// allow-list and after the instrument, so a cell can arm an extra detector
    /// on one side of a pair.
    pub fn env(mut self, key: &str, val: &str) -> Self {
        self.extra_env.push((key.to_string(), val.to_string()));
        self
    }
}

// =============================================================================
// Outcome types
// =============================================================================

/// One child's captured outcome plus the counters its instrument reported.
pub struct ChildOutcome {
    pub status: ExitStatus,
    pub stdout: String,
    pub stderr: String,
    pub allocs: i64,
    pub deallocs: i64,
    pub elapsed: Duration,
    /// Held so the temp directories outlive the measurement.
    _tmp: Vec<tempfile::TempDir>,
}

impl ChildOutcome {
    /// `allocs − deallocs` — this child's ABSOLUTE residual, ambient term
    /// included. Report it; do not assert on it (see the module header).
    pub fn residual(&self) -> i64 {
        self.allocs - self.deallocs
    }

    /// The child's exit code, or `None` if it died by signal.
    pub fn exit_code(&self) -> Option<i32> {
        self.status.code()
    }
}

/// A measured control/subject pair.
pub struct Marginal {
    label: String,
    instrument: Instrument,
    control: ChildOutcome,
    subject: ChildOutcome,
}

impl Marginal {
    pub fn control(&self) -> &ChildOutcome {
        &self.control
    }
    pub fn subject(&self) -> &ChildOutcome {
        &self.subject
    }

    /// Allocations the workload added over the control.
    pub fn allocs(&self) -> i64 {
        self.subject.allocs - self.control.allocs
    }
    /// Deallocations the workload added over the control.
    pub fn deallocs(&self) -> i64 {
        self.subject.deallocs - self.control.deallocs
    }
    /// **The quantity of interest**: `subject.residual − control.residual`.
    /// Zero means the workload freed everything it allocated; every term common
    /// to both children has cancelled.
    pub fn residual(&self) -> i64 {
        self.subject.residual() - self.control.residual()
    }

    /// The measurement, rendered for a failure message or a header update.
    pub fn report(&self) -> String {
        let mut s = String::new();
        let _ = write!(
            s,
            "marginal accounting [{}] via {:?}\n  \
             control: allocs={} deallocs={} residual={} exit={:?}\n  \
             subject: allocs={} deallocs={} residual={} exit={:?}\n  \
             MARGINAL: allocs={} deallocs={} residual={}",
            self.label,
            self.instrument,
            self.control.allocs,
            self.control.deallocs,
            self.control.residual(),
            self.control.exit_code(),
            self.subject.allocs,
            self.subject.deallocs,
            self.subject.residual(),
            self.subject.exit_code(),
            self.allocs(),
            self.deallocs(),
            self.residual(),
        );
        s
    }

    /// Assert the workload leaked nothing and over-freed nothing — the
    /// both-polarity fence, stated marginally. `what` names the contract in the
    /// failure message.
    pub fn assert_balanced(&self, what: &str) -> &Self {
        self.assert_residual(0, what)
    }

    /// Assert an EXACT marginal residual. Used by the FIXME-0889 documented-
    /// residual pins, where any movement off the recorded number — a partial
    /// fix, a regression, or the real fix — must flip the cell and force the
    /// record to be updated.
    pub fn assert_residual(&self, expected: i64, what: &str) -> &Self {
        assert_eq!(
            self.residual(),
            expected,
            "{what}\nexpected MARGINAL residual {expected}, measured {}.\n{}\
             \n--- control stderr (tail) ---\n{}\n--- subject stderr (tail) ---\n{}",
            self.residual(),
            self.report(),
            tail(&self.control.stderr),
            tail(&self.subject.stderr),
        );
        self
    }
}

fn tail(s: &str) -> String {
    let lines: Vec<&str> = s.lines().collect();
    let start = lines.len().saturating_sub(12);
    lines[start..].join("\n")
}

// =============================================================================
// MarginalPair — the builder
// =============================================================================

/// A control/subject pair awaiting measurement.
pub struct MarginalPair {
    label: String,
    control: Child,
    subject: Child,
    instrument: Instrument,
    timeout: Duration,
}

impl MarginalPair {
    /// `label` names the workload being isolated — it is what the failure
    /// message says the marginal is *of*.
    pub fn new(label: &str, control: Child, subject: Child) -> Self {
        MarginalPair {
            label: label.to_string(),
            control,
            subject,
            instrument: Instrument::RcStats,
            timeout: DEFAULT_TIMEOUT,
        }
    }

    pub fn instrument(mut self, instrument: Instrument) -> Self {
        self.instrument = instrument;
        self
    }

    pub fn timeout(mut self, timeout: Duration) -> Self {
        self.timeout = timeout;
        self
    }

    /// Spawn both children (control first, subject second — sequentially, so
    /// they never contend) and compute the marginal.
    pub fn measure(self) -> Marginal {
        let control = run_child(&self.control, self.instrument, self.timeout, "control");
        let subject = run_child(&self.subject, self.instrument, self.timeout, "subject");
        Marginal {
            label: self.label,
            instrument: self.instrument,
            control,
            subject,
        }
    }
}

// =============================================================================
// Spawning
// =============================================================================

/// `PATH` for the link drive: `--link` invokes `cc`, and the harness's
/// `env_clear()` removes the runner's `PATH`. Inherited when present so the
/// lane's toolchain is the one used, with a POSIX fallback for a runner that
/// has none.
fn link_path() -> String {
    std::env::var("PATH").unwrap_or_else(|_| "/usr/bin:/bin".to_string())
}

fn run_child(spec: &Child, instrument: Instrument, timeout: Duration, role: &str) -> ChildOutcome {
    let mut tmps: Vec<tempfile::TempDir> = Vec::new();

    let work = tempfile::tempdir().expect("tempdir");
    std::fs::write(work.path().join("user.cl"), &spec.program).expect("write user.cl");

    // Resolve CRANELISP_LIB.
    let lib: Option<PathBuf> = match &spec.lib {
        Lib::None => None,
        Lib::WorkspaceStdlib => Some(workspace_root().join("stdlib")),
        Lib::Files(files) => {
            let td = tempfile::tempdir().expect("lib tempdir");
            for (rel, contents) in files {
                let path = td.path().join(rel);
                if let Some(parent) = path.parent() {
                    std::fs::create_dir_all(parent).expect("mkdir lib subdir");
                }
                std::fs::write(&path, contents).expect("write lib file");
            }
            let p = td.path().to_path_buf();
            tmps.push(td);
            Some(p)
        }
    };

    let binary = binary_path();
    assert!(
        binary.exists(),
        "compiler binary not built at {}: build before running marginal cells",
        binary.display()
    );
    // The platform DLLs live beside the lane's binary — derive rather than
    // hard-code `target/debug`, so the agent lane stays isolated (0615).
    let platform_path = binary
        .parent()
        .expect("binary has a parent directory")
        .to_path_buf();

    let mut cmd = Command::new(&binary);
    cmd.env_clear()
        .current_dir(work.path())
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    match spec.drive {
        Drive::Run => {
            cmd.args(["--run", "user.cl", "--no-cache"]);
        }
        Drive::LinkThenRun => {
            cmd.args(["--link", "user.cl"]);
            // `--link` shells out to `cc`, which `env_clear()` would otherwise
            // make unfindable. The one allow-list entry the link drive adds.
            cmd.env("PATH", link_path());
        }
    }
    if let Some(lib) = &lib {
        cmd.env("CRANELISP_LIB", lib);
    }
    cmd.env("CRANELISP_PLATFORM_PATH", &platform_path);
    // The instrument is armed on whichever process the counters are READ from.
    // For the link drive that is the produced binary, not the linking compiler
    // child — arming the linker too would publish a second, irrelevant ledger.
    if spec.drive == Drive::Run {
        for (k, v) in instrument.env() {
            cmd.env(k, v);
        }
    }
    for (k, v) in &spec.extra_env {
        cmd.env(k, v);
    }

    let started = Instant::now();
    let mut child = cmd.spawn().expect("spawn compiler child");
    let deadline = started + timeout;
    loop {
        match child.try_wait() {
            Ok(Some(_)) => break,
            Ok(None) => {
                if Instant::now() >= deadline {
                    let _ = child.kill();
                    let _ = child.wait();
                    panic!("marginal {role} child exceeded {timeout:?}");
                }
                std::thread::sleep(Duration::from_millis(20));
            }
            Err(e) => panic!("marginal {role} child wait failed: {e}"),
        }
    }
    let out = child.wait_with_output().expect("collect child output");
    let mut elapsed = started.elapsed();
    let mut stdout = String::from_utf8_lossy(&out.stdout).into_owned();
    let mut stderr = String::from_utf8_lossy(&out.stderr).into_owned();
    let mut status = out.status;

    if spec.drive == Drive::LinkThenRun {
        assert!(
            status.success(),
            "marginal {role} child failed to LINK — a pair cannot be subtracted \
             if one side never produced a binary.\nexit={:?}\nstdout:\n{stdout}\nstderr:\n{stderr}",
            status.code()
        );
        let produced = work.path().join("user");
        assert!(
            produced.exists(),
            "marginal {role} child linked but produced no `user` executable in {}",
            work.path().display()
        );
        let mut run = Command::new(&produced);
        run.env_clear()
            .current_dir(work.path())
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .env("PATH", link_path());
        for (k, v) in instrument.env() {
            run.env(k, v);
        }
        for (k, v) in &spec.extra_env {
            run.env(k, v);
        }
        let produced_out = run.output().expect("run produced executable");
        elapsed = started.elapsed();
        stdout = String::from_utf8_lossy(&produced_out.stdout).into_owned();
        stderr = String::from_utf8_lossy(&produced_out.stderr).into_owned();
        status = produced_out.status;
    }

    let (allocs, deallocs) = instrument.parse(&stderr).unwrap_or_else(|e| {
        panic!(
            "marginal {role} child produced no readable {instrument:?} counters ({e}).\n\
             A pair cannot be subtracted if one side did not report — this is a harness \
             or a child-startup failure, never a balance verdict.\n\
             exit={:?}\nstdout:\n{stdout}\nstderr:\n{stderr}",
            status.code()
        )
    });

    tmps.push(work);
    ChildOutcome {
        status,
        stdout,
        stderr,
        allocs,
        deallocs,
        elapsed,
        _tmp: tmps,
    }
}
