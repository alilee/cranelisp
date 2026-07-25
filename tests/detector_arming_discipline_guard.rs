//! Structural gate for the S118 certification split: **detector arming is
//! child-subprocess-scoped, never suite-scoped** (`tests/plan/s118-test-plan.md`
//! §1 ruling 3, structural; `design/intrinsics/diagnostic-modes.md` §7.1;
//! `sprints/SPRINT.md` §Architecture-review ruling 3). Authored by `/testing` in
//! S118 W1; a hit here is a W1 FAIL.
//!
//! WHY THIS IS A STRUCTURAL GATE AND NOT A CONVENTION. Two independent failure
//! modes, both silent:
//!
//!  1. **Baseline destruction.** The deterministic suite's exit contract is an
//!     exact failure SET. A globally-armed M3 (`CRANELISP_ALLOC_PARITY`) aborts
//!     every still-red leak guard in the corpus at exit, so the arithmetic that
//!     the whole sprint reconciles against stops meaning anything — and it stops
//!     meaning anything QUIETLY, as a pile of exit-134s that look like the
//!     defects under investigation.
//!  2. **Arming that only LOOKS armed.** `diagnostic-modes.md` §7.1 records the
//!     mechanism: the detector ledger is a `LazyLock`, so a `std::env::set_var`
//!     issued after first touch is a no-op. A test that arms with `set_var` and
//!     then asserts "the detector did not fire" is asserting nothing at all, and
//!     reads GREEN forever. This is the worse of the two — a false capability
//!     claim in the certification record.
//!
//! THE LEGAL FORM, and the only one: arming values are set on a CHILD process
//! being constructed — `Command::env`/`env_clear` (the `intrinsics_m3_detection_s116`
//! plant-child pattern) or the `Cranelisp` builder's `.env(…)` (the
//! `ms_p8_conj_leak` armed-parity leg). Both are per-subprocess by construction
//! and are what this gate deliberately does NOT flag.
//!
//! WHAT IS FLAGGED (three greps over the corpus this suite owns):
//!
//!  A. any `std::env::set_var` / `env::set_var` naming a `CRANELISP_*` variable
//!     anywhere under `tests/` — process-global, and per §7.1 a silent no-op for
//!     the detectors;
//!  B. any read of a DETECTOR variable out of the test process's OWN environment
//!     (`env::var`/`env::var_os`) — a test whose behaviour depends on ambient
//!     arming is a test whose result is not reproducible from its source;
//!  C. any suite-scope export of a DETECTOR variable in the suite's own runner
//!     surfaces — `.config/nextest.toml` and `tests/scripts/*.sh` — where an
//!     `export`/`env FOO=1` reaches EVERY child of the run.
//!
//! SCOPING (deliberately narrow, so the gate has no false positives to train
//! anyone to ignore). Only the six DETECTOR variables are in scope for B and C;
//! the analysis toggles and trace variables (`CRANELISP_NO_OWNERSHIP`,
//! `CRANELISP_RC_TRACE`, `CRANELISP_CODEGEN_TRACE`, …) are NOT detectors — they
//! change lowering or verbosity, they do not abort a child on an invariant
//! violation, and `tests/scripts/suite_polarity.sh` legitimately sweeps the
//! ownership toggle at suite scope. Grep A is broader (`CRANELISP_*`) on purpose:
//! `set_var` on any compiler variable inside a test process is a shared-state
//! write across nextest's in-process test threads regardless of which variable
//! it names.
//!
//! `/review` enforces the same rule per change-set; this file is the standing
//! mechanical half.
//
// spec: (CI guard — no single spec §) — the normative statements are
//       `tests/plan/s118-test-plan.md` §1 (certification split, ruling 3) and
//       `design/intrinsics/diagnostic-modes.md` §7.1 (lane-scoped arming;
//       `set_var` is a silent no-op against the LazyLock ledger).

use std::process::Command;

/// The DETECTOR variables — the ones whose arming aborts a child on an invariant
/// violation and therefore destroys a red baseline when armed suite-wide.
/// `diagnostic-modes.md` §7.1 + plan §1 enumerate exactly these.
const DETECTOR_VARS: &[&str] = &[
    "CRANELISP_QUARANTINE_FREED",
    "CRANELISP_SCRUB_FREED",
    "CRANELISP_ALLOC_PARITY",
    "CRANELISP_RC_DEC_CHECK",
    "CRANELISP_TEST_FAULTS",
    "CRANELISP_TEST_FAULT",
];

/// Suite-runner surfaces whose environment reaches EVERY child of a run.
const SUITE_SCOPE_FILES: &[&str] = &[".config/nextest.toml"];

fn workspace_root() -> &'static str {
    env!("CARGO_MANIFEST_DIR")
}

/// `grep -rnE` under the workspace root, returning `(file, code)` pairs with
/// comment-only lines dropped (a comment naming a variable is documentation, not
/// an assignment — this file is itself full of such lines).
fn grep(pattern: &str, paths: &[&str], include: Option<&str>) -> Vec<(String, String)> {
    let mut args: Vec<String> = vec!["-rnE".to_string()];
    if let Some(inc) = include {
        args.push(format!("--include={inc}"));
    }
    args.push(pattern.to_string());
    for p in paths {
        args.push((*p).to_string());
    }
    let out = Command::new("grep")
        .args(&args)
        .current_dir(workspace_root())
        .output()
        .expect("grep must be available");
    let text = String::from_utf8_lossy(&out.stdout);
    let mut hits = Vec::new();
    for line in text.lines() {
        // grep -n output: `path:lineno:code` (code may itself contain `:`).
        let mut parts = line.splitn(3, ':');
        let file = parts.next().unwrap_or("").to_string();
        let _lineno = parts.next().unwrap_or("");
        let code = parts.next().unwrap_or("").to_string();
        let t = code.trim_start();
        if t.starts_with("//") || t.starts_with('#') || t.starts_with(";") {
            continue; // documentation, not an assignment
        }
        // This guard file names every variable it defends; excluding it keeps the
        // gate from tripping on its own allow-list.
        if file.ends_with("detector_arming_discipline_guard.rs") {
            continue;
        }
        hits.push((file, code));
    }
    hits
}

// GREP A — `set_var` of any `CRANELISP_*` variable anywhere in the test corpus.
// Process-global mutation of the environment inside a test process, and — for
// the detectors specifically — a silent no-op that LOOKS like arming
// (`diagnostic-modes.md` §7.1: the ledger is a `LazyLock`). There is no legal
// use: arming belongs on the child `Command`/builder.
// spec: (CI guard) — `tests/plan/s118-test-plan.md` §1 ruling 3.
#[test]
fn no_test_sets_a_cranelisp_variable_in_its_own_process() {
    let hits = grep(r#"set_var\s*\(\s*"CRANELISP_"#, &["tests/"], Some("*.rs"));
    let offenders: Vec<String> = hits
        .iter()
        .map(|(f, c)| format!("  {}: {}", f, c.trim()))
        .collect();
    assert!(
        offenders.is_empty(),
        "SUITE-SCOPE ARMING DETECTED — a test sets a CRANELISP_* variable in its \
         OWN process. Two independent faults: (1) it is process-global, so it \
         leaks across nextest's in-process test threads; (2) for the detector \
         variables it is a SILENT NO-OP against the LazyLock ledger \
         (`design/intrinsics/diagnostic-modes.md` §7.1), so any \"the detector \
         did not fire\" assertion downstream of it asserts nothing and reads \
         GREEN forever. Arm on the CHILD instead: `Command::env`/`env_clear` \
         (see tests/intrinsics_m3_detection_s116.rs) or the `Cranelisp` \
         builder's `.env(…)` (see tests/ms_p8_conj_leak.rs).\n{}",
        offenders.join("\n"),
    );
}

// GREP B — a test reading a DETECTOR variable out of its own environment. A test
// whose behaviour depends on ambient arming is not reproducible from its source,
// and it is the shape that would let a suite-scope export change verdicts
// silently. (`CARGO_TARGET_DIR` and `CRANELISP_TEST_UPDATE_GOLDENS` in
// `helpers/e2e.rs` are harness plumbing, not detectors, and are out of scope by
// construction — DETECTOR_VARS is the whole pattern.)
// spec: (CI guard) — `tests/plan/s118-test-plan.md` §1 ruling 3.
#[test]
fn no_test_reads_a_detector_variable_from_its_own_environment() {
    let pattern = format!(r#"env::var(_os)?\s*\(\s*"({})""#, DETECTOR_VARS.join("|"));
    let hits = grep(&pattern, &["tests/"], Some("*.rs"));
    let offenders: Vec<String> = hits
        .iter()
        .map(|(f, c)| format!("  {}: {}", f, c.trim()))
        .collect();
    assert!(
        offenders.is_empty(),
        "A test reads a DETECTOR variable from its own process environment. Test \
         verdicts must be reproducible from the test source, not from how the \
         suite was invoked; and no test file may consult ambient arming \
         (`tests/plan/s118-test-plan.md` §1). Construct the armed CHILD \
         explicitly instead.\n{}",
        offenders.join("\n"),
    );
}

// GREP C — a DETECTOR variable exported at SUITE scope by the suite's own runner
// surfaces (`.config/nextest.toml` and `tests/scripts/*.sh`). This is the
// baseline-destroying form: an armed M3 there aborts every still-red leak guard
// in the corpus and the failure SET the sprint reconciles against stops meaning
// anything. NOT flagged: `env -u CRANELISP_…` (unsetting is the hygiene the
// golden-CLIF lane already does), and the non-detector analysis toggles that
// `tests/scripts/suite_polarity.sh` legitimately sweeps.
// spec: (CI guard) — `tests/plan/s118-test-plan.md` §1 ruling 3.
#[test]
fn no_suite_scope_export_arms_a_detector() {
    let pattern = format!(
        r#"(^|[[:space:]"'])({})[[:space:]]*="#,
        DETECTOR_VARS.join("|")
    );
    let mut paths: Vec<&str> = vec!["tests/scripts/"];
    paths.extend_from_slice(SUITE_SCOPE_FILES);
    let hits: Vec<(String, String)> = grep(&pattern, &paths, None)
        .into_iter()
        // `env -u VAR` / `-u VAR` is an UNSET — the opposite of arming.
        .filter(|(_, c)| !c.contains("-u "))
        .collect();
    let offenders: Vec<String> = hits
        .iter()
        .map(|(f, c)| format!("  {}: {}", f, c.trim()))
        .collect();
    assert!(
        offenders.is_empty(),
        "SUITE-SCOPE DETECTOR ARMING in a runner surface. Every child of the run \
         inherits it: an armed M3 aborts every still-red leak guard at exit and \
         destroys the failure-set arithmetic the certification contract is \
         written against (`tests/plan/s118-test-plan.md` §1). Arm per child, in \
         the test that needs it.\n{}",
        offenders.join("\n"),
    );
}

// The gate's own capability fence (METHOD §2.2 — an instrument is unverified
// until it is proven to detect). Each grep is re-run against a SYNTHETIC line
// that must match, and against a legal-form line that must NOT: without this,
// all three tests above would pass identically against a rotted regex that
// matches nothing. No live code is involved, so this fence cannot expire when
// someone else's change lands.
// spec: (CI guard) — `tests/plan/s118-test-plan.md` §1 ruling 3.
#[test]
fn arming_gate_capability_matches_offenders_and_spares_the_legal_form() {
    fn matches(pattern: &str, line: &str) -> bool {
        let out = Command::new("grep")
            .args(["-qE", pattern])
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::null())
            .spawn()
            .and_then(|mut c| {
                use std::io::Write;
                c.stdin.take().unwrap().write_all(line.as_bytes())?;
                c.wait()
            })
            .expect("grep must be available");
        out.success()
    }

    // A — the set_var form is caught in both spellings.
    let a = r#"set_var\s*\(\s*"CRANELISP_"#;
    for offender in [
        r#"    std::env::set_var("CRANELISP_ALLOC_PARITY", "1");"#,
        r#"    env::set_var( "CRANELISP_SCRUB_FREED", "1");"#,
    ] {
        assert!(matches(a, offender), "grep A missed: {offender}");
    }
    for legal in [
        r#"    cmd.env("CRANELISP_ALLOC_PARITY", "1");"#,
        r#"    let b = b.env("CRANELISP_TEST_FAULT", plant);"#,
    ] {
        assert!(!matches(a, legal), "grep A false-positived on: {legal}");
    }

    // B — reading a detector out of the process env is caught; harness plumbing
    // and non-detector variables are spared.
    let b = format!(r#"env::var(_os)?\s*\(\s*"({})""#, DETECTOR_VARS.join("|"));
    for offender in [
        r#"    if std::env::var("CRANELISP_ALLOC_PARITY").is_ok() {"#,
        r#"    let f = std::env::var_os("CRANELISP_TEST_FAULTS");"#,
    ] {
        assert!(matches(&b, offender), "grep B missed: {offender}");
    }
    for legal in [
        r#"    if std::env::var("CRANELISP_TEST_UPDATE_GOLDENS").is_ok() {"#,
        r#"    match std::env::var_os("CARGO_TARGET_DIR") {"#,
        r#"    b = b.env("CRANELISP_NO_OWNERSHIP", "1");"#,
    ] {
        assert!(!matches(&b, legal), "grep B false-positived on: {legal}");
    }

    // C — a suite-scope export is caught; an `env -u` unset and a non-detector
    // toggle sweep are spared.
    let c = format!(
        r#"(^|[[:space:]"'])({})[[:space:]]*="#,
        DETECTOR_VARS.join("|")
    );
    for offender in [
        r#"export CRANELISP_ALLOC_PARITY=1"#,
        r#"run_polarity "armed" "CRANELISP_RC_DEC_CHECK=1""#,
    ] {
        assert!(matches(&c, offender), "grep C missed: {offender}");
    }
    for legal in [
        r#"run_polarity "no_ownership" "CRANELISP_NO_OWNERSHIP=1""#,
        r#"# arming CRANELISP_ALLOC_PARITY at suite scope is forbidden"#,
    ] {
        assert!(!matches(&c, legal), "grep C false-positived on: {legal}");
    }
    // The `env -u` spare is applied as a post-filter in the test above, not in
    // the regex; assert the filter's predicate holds for the shape it defends.
    assert!("        -u CRANELISP_RC_DEC_CHECK \\".contains("-u "));
}
