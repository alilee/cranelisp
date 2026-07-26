//! Standing gate: **record-vs-source citation drift is measured continuously,
//! not by discipline.**
//!
//! Root `CLAUDE.md` §Assurance ("Records are claims too") names
//! `scripts/verify-citations.py` as the *mechanism* that replaces "remember to
//! verify the `refers_to:` claim before disposing a FIXME". A mechanism that
//! only runs when someone remembers to run it is the discipline it was meant to
//! replace. This file is the wiring that makes it run on every
//! `cargo nextest run`.
//!
//! WHAT THE GATE CHECKS (the script's whole remit — deliberately judgement-free):
//!
//!   1. PATH   — a cited repository path exists;
//!   2. LINE   — a `path:N` / `path:N-M` citation names a line inside the file;
//!   3. SYMBOL — a `path::symbol` or `bare_file.rs::symbol` citation names an
//!               identifier that actually occurs in that file.
//!
//! It does NOT check that the cited line still *means* what the citing document
//! claims. That is semantic and stays human. What it kills is the class a single
//! file-open would have refuted — the class the sprint record shows costing whole
//! sprints: a locus naming a file the symbol was never in, a tranche scoped at a
//! file in a crate that has none, a documented API that exists nowhere.
//!
//! THE BASELINE IS A RATCHET, NOT A SUPPRESSION LIST.
//! `scripts/citation-drift-baseline.txt` records the *known-stale backlog* so the
//! check can gate a repo that already has one. Entries may be DELETED when a
//! citation is repaired; entries are NEVER ADDED by hand — a new finding is a new
//! stale record, and stopping those landing is the entire point of the gate. If
//! this test goes RED, the fix is to repair the citation, never to re-baseline.
//!
//! SCOPE: `--corpus live` — plan-of-record documents only. Dated records and
//! archives (`design/**/archive/`, `sprintNN-*.md`, `audits/*-sNNN.md`,
//! `*-YYYYMMDD.md`) are excluded by the script: a dated record citing a line that
//! has since moved is an accurate record of its moment, not drift.
//!
//! OWNERSHIP: the script and its baseline are not `/testing`'s to edit; this file
//! is the executing consumer only.

use std::fs;
use std::path::Path;
use std::process::Command;

/// The checked-in project root. `// read-only on project_root` — every test here
/// reads the checked-in corpus, the script, and the baseline; the only thing it
/// ever writes is a scratch document under the git-ignored `target/`.
fn workspace_root() -> &'static str {
    env!("CARGO_MANIFEST_DIR")
}

const SCRIPT: &str = "scripts/verify-citations.py";
const BASELINE: &str = "scripts/citation-drift-baseline.txt";

/// A completed invocation of the gate: exit status plus everything it said.
struct GateRun {
    code: Option<i32>,
    output: String,
}

impl GateRun {
    fn passed(&self) -> bool {
        self.code == Some(0)
    }
}

/// Run the gate exactly as `CLAUDE.md` §Assurance documents it. `extra_docs` are
/// repo-relative explicit document paths; when non-empty the script checks ONLY
/// those (the corpus selector is inert), which is how the detection proof below
/// exercises the identical invocation against a scratch document instead of the
/// tracked tree.
fn run_gate(extra_docs: &[&str]) -> GateRun {
    require_python3();
    let mut args: Vec<String> = vec![
        SCRIPT.to_string(),
        "--corpus".to_string(),
        "live".to_string(),
        "--baseline".to_string(),
        BASELINE.to_string(),
    ];
    args.extend(extra_docs.iter().map(|d| (*d).to_string()));

    let out = Command::new("python3")
        .args(&args)
        .current_dir(workspace_root())
        .output()
        .expect("python3 must be spawnable — require_python3() checked this");

    let stdout = String::from_utf8_lossy(&out.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&out.stderr).into_owned();
    let mut output = stdout;
    if !stderr.trim().is_empty() {
        output.push_str("\n--- stderr ---\n");
        output.push_str(&stderr);
    }
    GateRun {
        code: out.status.code(),
        output,
    }
}

/// The interpreter is a hard prerequisite of this gate, and its absence is
/// reported as a LOUD FAILURE rather than a quiet pass.
///
/// There is no runtime "skip" in Rust's test harness, and a `println!` on the
/// pass path is captured by nextest and therefore invisible — indistinguishable
/// from the check having run and found nothing, which is exactly the failure mode
/// `CLAUDE.md` §Assurance exists to stop ("a check that has never fired against a
/// deliberately planted fault is indistinguishable from a check that cannot
/// fire"). A visible failure naming the missing prerequisite is the honest
/// degradation; installing `python3` — or deleting this gate deliberately — are
/// the only two ways past it.
fn require_python3() {
    let probe = Command::new("python3").arg("--version").output();
    assert!(
        probe.is_ok(),
        "CITATION-DRIFT GATE CANNOT RUN — `python3` is not on PATH.\n\
         This is NOT a pass: the gate at {SCRIPT} is the mechanism root \
         `CLAUDE.md` §Assurance names for record-vs-source drift, and an \
         un-runnable check is indistinguishable from a check that finds nothing. \
         Install python3 (no third-party packages are needed — the script is \
         stdlib-only) and re-run."
    );
}

// The gate itself. Every citation in the live documentation corpus resolves
// against source, modulo the known-stale ratchet.
//
// spec: CLAUDE.md §Assurance — §"Records are claims too" (the
//       `scripts/verify-citations.py` mechanism and its ratchet baseline)
#[test]
fn live_corpus_citations_resolve_against_source() {
    let run = run_gate(&[]);
    assert!(
        run.passed(),
        "CITATION DRIFT — a record in the live documentation corpus cites source \
         that does not back it up (exit {:?}).\n\n\
         Each finding below is a claim a single file-open refutes: a path that \
         does not exist, a line number past the end of its file, or a \
         `file::symbol` naming an identifier that is not in that file. Root \
         `CLAUDE.md` §Assurance — \"Records are claims too\".\n\n\
         FIX THE CITATION, NOT THE BASELINE. `{BASELINE}` is a ratchet: entries \
         may be deleted when a citation is repaired, and are never added by hand \
         — a new finding is a new stale record, and stopping those landing is \
         what this gate is for. Re-check locally with:\n\
         \x20   python3 {SCRIPT} --corpus live --baseline {BASELINE}\n\n\
         {}",
        run.code,
        run.output,
    );
}

/// A document body whose ONE citation is deliberately false: `drop_glue.rs` is a
/// real file, and `totally_fictional_symbol` occurs nowhere in the tree.
///
/// The prose is kept clear of the script's exemption markers — "retired",
/// "deleted", "no such", "does not exist", "historical", "e.g.", … — which
/// excuse a citation on a line that is openly discussing something absent. This
/// is not hypothetical fussiness: the first draft of this fence read "and no such
/// identifier was ever written", which the script correctly exempted, and the
/// positive leg reported the gate as unable to detect. An exempted plant is a
/// detection proof that proves nothing.
const PLANTED_STALE: &str = "\
# Detection-proof scratch document

The locus is crates/cranelisp-backend/src/drop_glue.rs::totally_fictional_symbol \
and that identifier was never written.
";

/// The same shape with a citation that genuinely resolves —
/// `request_vec_elem_adapter` really is defined in that file. The negative leg
/// must be a document the gate INSPECTS and clears, not a document it ignores;
/// otherwise "silent" proves nothing.
const CLEAN_CITATION: &str = "\
# Detection-proof scratch document

The locus is crates/cranelisp-backend/src/drop_glue.rs::request_vec_elem_adapter \
and that identifier is really there.
";

// The gate's own capability fence: `CLAUDE.md` §Assurance — "an instrument is
// unverified until it is proven to detect", and the negative leg (silence when
// the fault is absent) is as load-bearing as the positive one. Without this, the
// test above would read GREEN identically if the script had rotted into checking
// nothing at all.
//
// Both legs run the IDENTICAL invocation the gate uses — same flags, same
// baseline — against a scratch document, so the proof covers the real command
// line and not a weakened variant. In particular the positive leg proves the
// ratchet does not blanket-tolerate: a NEW finding fails even with `--baseline`
// supplied.
//
// The scratch document lives under the git-ignored `target/` and NOT in a system
// temp dir, for two reasons: the script rejects documents outside the repository
// root, and planting a fault into a tracked file (even transiently) is a
// tree-race hazard against every other agent sharing this working tree.
//
// spec: CLAUDE.md §Assurance — §"Records are claims too" (instrument detection
//       proof; both polarities)
#[test]
fn citation_gate_detects_a_planted_stale_citation_and_clears_a_sound_one() {
    let target = Path::new(workspace_root()).join("target");
    fs::create_dir_all(&target).expect("target/ must be creatable");
    let scratch =
        tempfile::TempDir::new_in(&target).expect("scratch dir under target/ must be creatable");
    let dir = scratch
        .path()
        .file_name()
        .and_then(|n| n.to_str())
        .expect("tempdir name must be UTF-8")
        .to_string();

    fs::write(scratch.path().join("planted.md"), PLANTED_STALE).expect("write planted doc");
    fs::write(scratch.path().join("clean.md"), CLEAN_CITATION).expect("write clean doc");
    let planted = format!("target/{dir}/planted.md");
    let clean = format!("target/{dir}/clean.md");

    // NEGATIVE LEG — the fault is absent, so the gate stays silent.
    let sound = run_gate(&[&clean]);
    assert!(
        sound.passed(),
        "NEGATIVE LEG FAILED — the citation gate reported a finding against a \
         document whose only citation resolves \
         (`crates/cranelisp-backend/src/drop_glue.rs::request_vec_elem_adapter`). \
         A gate that fires on sound records trains everyone to ignore it, and the \
         next real drift lands unread (exit {:?}).\n\n{}",
        sound.code,
        sound.output,
    );
    // Silence is only meaningful if the citation was actually INSPECTED. A
    // document the script exempted, skipped, or never parsed also produces exit
    // 0, and would make this leg vacuous — so pin the counters.
    assert!(
        sound.output.contains("1 symbols verified") && sound.output.contains("0 exempt"),
        "NEGATIVE LEG IS VACUOUS — the gate exited 0 on the sound document, but \
         did not report the citation as an inspected-and-verified symbol. \
         Silence from a citation that was never checked is not evidence the \
         check works.\n\n{}",
        sound.output,
    );

    // POSITIVE LEG — the planted fault is detected, and for the RIGHT reason.
    let planted_run = run_gate(&[&planted]);
    assert!(
        !planted_run.passed(),
        "POSITIVE LEG FAILED — the citation gate did NOT detect a planted stale \
         citation (`drop_glue.rs::totally_fictional_symbol`, an identifier that \
         occurs nowhere in the tree). The gate above is therefore proving \
         nothing: an instrument that cannot fire is indistinguishable from one \
         that found no faults (`CLAUDE.md` §Assurance).\n\n{}",
        planted_run.output,
    );
    // A guard failing for the wrong reason — an argparse error, a traceback, a
    // missing baseline file — is indistinguishable from a guard working, so the
    // detection is pinned to the finding text, not merely to a non-zero exit.
    assert_eq!(
        planted_run.code,
        Some(1),
        "POSITIVE LEG FIRED FOR THE WRONG REASON — expected exit 1 (findings \
         reported), got {:?}. An interpreter or argument error exiting non-zero \
         would satisfy a bare `!passed()` assertion while detecting nothing.\n\n{}",
        planted_run.code,
        planted_run.output,
    );
    assert!(
        planted_run.output.contains("SYMBOL")
            && planted_run.output.contains("totally_fictional_symbol"),
        "POSITIVE LEG FIRED FOR THE WRONG REASON — exit 1, but the output does \
         not name the planted symbol under the SYMBOL check, so the failure is \
         not the detection this fence claims to prove.\n\n{}",
        planted_run.output,
    );
}
