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
//! WHAT THE GATE CHECKS — the three checks, the live-corpus scope, and what the
//! gate deliberately does NOT catch (doc→doc citations, definition-site claims,
//! the `sprints/SPRINT.md` lifecycle path) are carried once, in
//! `scripts/verify-citations.py`'s docstring. The fences below name the
//! condition they prove rather than restating the rule.
//!
//! THE BASELINE IS A RATCHET, NOT A SUPPRESSION LIST.
//! `scripts/citation-drift-baseline.txt` records the *known-stale backlog* so the
//! check can gate a repo that already has one. Entries may be DELETED when a
//! citation is repaired; entries are NEVER ADDED by hand — a new finding is a new
//! stale record, and stopping those landing is the entire point of the gate. If
//! this test goes RED, the fix is to repair the citation, never to re-baseline.
//!
//! OWNERSHIP (`sprints/METHOD.md` §3.1): `scripts/verify-*.py` is `test`'s and
//! changes only alongside the fence that proves the change detects; the baseline
//! is `qa`'s ratchet, and this file never regenerates it.

use std::fs;
use std::path::{Path, PathBuf};
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

/// A scheduling record citing an action file that was never written. The name is
/// deliberately plausible — a real action-file shape, no `NN`/`<…>` placeholder
/// characters (the script treats those as templates, not claims) and none of the
/// exemption markers.
const PLANTED_SCHEDULING_STALE: &str = "\
# Detection-proof scratch document

Wave 4 carries the budget decision from sprints/actions/ACT-0721-tail-call-budget.md \
into the closing report.
";

/// A record citing the retired per-role command mechanism. Before S120 this file
/// really existed; the class the widening exists to catch is a record that still
/// points at it. Only a root covering `.claude/` can see a dead *target*.
const PLANTED_HOST_STALE: &str = "\
# Detection-proof scratch document

The dispatch preamble for that surface is .claude/commands/typecheck.md and it is \
read at the start of every run.
";

/// Three citations, one into each newly covered surface, and all three resolve:
/// the scheduling corpus, the Claude host adapters, and the shared role package.
const CLEAN_WIRING_CITATIONS: &str = "\
# Detection-proof scratch document

Cranelisp adds sprints/METHOD.md to the shared contracts. The consumer allocation \
lives at .claude/agents/qa.md and the contract it names is \
.agents/skills/qa/SKILL.md, which is where the role authority sits.
";

// Detection proof for the S120 widening (`tests/plan/s120-evidence-delta.md`
// §2 D-1, condition C5). The gate above could go GREEN with the widening
// entirely absent — the
// three surfaces it now covers are exactly the ones it used to skip silently,
// and a skipped citation and a verified citation both produce exit 0.
//
// The two positive legs prove PATH resolution now reaches a `sprints/` target
// and a `.claude/` target. The negative leg proves the three surfaces are
// INSPECTED rather than merely tolerated: it pins the verified-path counter, so
// a regression that put any of them back outside `looks_like_source_path` shows
// up as `2 paths` instead of silence.
//
// spec: CLAUDE.md §Assurance — §"Records are claims too" (instrument detection
//       proof; both polarities)
#[test]
fn citation_gate_detects_planted_scheduling_and_host_faults_and_clears_sound_wiring() {
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

    for (name, body) in [
        ("scheduling.md", PLANTED_SCHEDULING_STALE),
        ("host.md", PLANTED_HOST_STALE),
        ("wiring.md", CLEAN_WIRING_CITATIONS),
    ] {
        fs::write(scratch.path().join(name), body).expect("write scratch doc");
    }

    // NEGATIVE LEG — all three citations resolve, and the gate says so by
    // counting them. Exit 0 alone would be satisfied by a script that never
    // recognised any of the three as a citation at all, which is precisely the
    // pre-widening behaviour this fence discriminates.
    let sound = run_gate(&[&format!("target/{dir}/wiring.md")]);
    assert!(
        sound.passed(),
        "NEGATIVE LEG FAILED — the citation gate reported a finding against a \
         document whose three citations (`sprints/METHOD.md`, \
         `.claude/agents/qa.md`, `.agents/skills/qa/SKILL.md`) all resolve \
         (exit {:?}).\n\n{}",
        sound.code,
        sound.output,
    );
    assert!(
        sound.output.contains("3 paths") && sound.output.contains("0 exempt"),
        "NEGATIVE LEG IS VACUOUS — the gate exited 0, but did not report three \
         inspected-and-verified paths. A citation the script skipped because \
         `sprints/`, `.claude/` or `.agents/` is not a recognised root produces \
         exit 0 just as a verified one does, so the count is the whole \
         evidence.\n\n{}",
        sound.output,
    );

    // POSITIVE LEG 1 — a scheduling record pointing at an action file that does
    // not exist. Three METHOD/ROADMAP/artefacts deletions in this sprint broke
    // roughly twenty citations that this instrument could not see before the
    // S120 widening.
    let scheduling = run_gate(&[&format!("target/{dir}/scheduling.md")]);
    assert_eq!(
        scheduling.code,
        Some(1),
        "POSITIVE LEG FAILED — a planted citation to \
         `sprints/actions/ACT-0721-tail-call-budget.md`, which does not exist, \
         did not produce exit 1. The scheduling corpus is therefore still \
         outside the instrument and `CLAUDE.md` §Assurance's mechanism claim \
         does not cover it.\n\n{}",
        scheduling.output,
    );
    assert!(
        scheduling.output.contains("PATH")
            && scheduling
                .output
                .contains("sprints/actions/ACT-0721-tail-call-budget.md"),
        "POSITIVE LEG FIRED FOR THE WRONG REASON — exit 1, but the output does \
         not name the planted path under the PATH check. An argparse error or a \
         traceback exits non-zero while detecting nothing.\n\n{}",
        scheduling.output,
    );

    // POSITIVE LEG 2 — a record still pointing at the retired command
    // mechanism. `.claude/` earns its place as a root precisely because it is a
    // dead *target*: only a root lets the checker see one.
    let host = run_gate(&[&format!("target/{dir}/host.md")]);
    assert_eq!(
        host.code,
        Some(1),
        "POSITIVE LEG FAILED — a planted citation to \
         `.claude/commands/typecheck.md`, a file the S120 migration deleted, did \
         not produce exit 1. Records still naming the retired command mechanism \
         stay invisible.\n\n{}",
        host.output,
    );
    assert!(
        host.output.contains("PATH") && host.output.contains(".claude/commands/typecheck.md"),
        "POSITIVE LEG FIRED FOR THE WRONG REASON — exit 1, but the output does \
         not name the planted path under the PATH check.\n\n{}",
        host.output,
    );
}

/// The gate's own corpus listing under the corpus selector the gate uses.
/// Returns the exit code, the listed repo-relative documents, and everything the
/// run said (for a failure message that can be acted on).
fn list_live_corpus() -> (Option<i32>, Vec<String>, String) {
    require_python3();
    let out = Command::new("python3")
        .args([SCRIPT, "--corpus", "live", "--list-docs"])
        .current_dir(workspace_root())
        .output()
        .expect("python3 must be spawnable — require_python3() checked this");

    let stdout = String::from_utf8_lossy(&out.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&out.stderr).into_owned();
    let docs: Vec<String> = stdout
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty())
        .map(str::to_string)
        .collect();
    let mut output = stdout;
    if !stderr.trim().is_empty() {
        output.push_str("\n--- stderr ---\n");
        output.push_str(&stderr);
    }
    (out.status.code(), docs, output)
}

/// One document per glob the S120 widening added to `DOC_GLOBS`. Each is a real
/// checked-in file — the test asserts that below, because "is a member" is only
/// evidence about a glob if the file it stands for exists.
const CORPUS_MEMBERS: &[&str] = &[
    "sprints/METHOD.md",               // sprints/**/*.md
    ".claude/agents/qa.md",            // .claude/agents/*.md
    ".github/agents/qa.agent.md",      // .github/agents/*.md
    ".github/copilot-instructions.md", // the explicit single-file glob
];

/// The one package document `**/CLAUDE.md` would otherwise sweep in. Package
/// prose is package-root-relative, verified by the package, and rewritten at
/// every converge, so scanning it would let a package edit fail the consumer
/// gate.
const CORPUS_NON_MEMBER: &str = ".agents/CLAUDE.md";

// Corpus-membership fence (`tests/plan/s120-evidence-delta.md` §2 D-1, condition
// C6). The two positive fences above prove the *roots* —
// PATH resolution now reaches `sprints/` and `.claude/` targets — and prove
// nothing about the *corpus*, because `collect_docs` returns explicit document
// arguments before it ever consults `DOC_GLOBS`. Deleting all four S120 globs
// therefore leaves both of them, and the live gate, green: measured at S120, 431
// documents instead of 466, and still 0 findings.
//
// The leg is self-arming: membership and absence are asserted from ONE listing,
// so a `--list-docs` that reported everything fails the absence half and one
// that reported nothing fails the membership half. It deliberately does not pin
// the document total — every record added to the project moves that number, and
// a count bumped without looking is the ratchet failure the widening exists to
// stop.
//
// spec: CLAUDE.md §Assurance — §"Records are claims too" (the corpus the
//       `scripts/verify-citations.py` mechanism actually scans)
#[test]
fn citation_gate_corpus_holds_the_scheduling_and_host_surfaces_and_excludes_the_package() {
    let root = Path::new(workspace_root());

    // ARMING — every path this test reasons about is on disk right now. Without
    // this, a member assertion could pass against a stale expectation and an
    // absence assertion is satisfied by a file that simply is not there.
    for member in CORPUS_MEMBERS {
        assert!(
            root.join(member).is_file(),
            "FENCE UNARMED — `{member}` stands for one of the corpus globs the \
             S120 widening added, and it is not on disk. Membership of a file \
             that does not exist is not evidence about the glob; point this at a \
             live file on that surface, or the glob itself is what changed."
        );
    }
    assert!(
        root.join(CORPUS_NON_MEMBER).is_file(),
        "FENCE UNARMED — `{CORPUS_NON_MEMBER}` is not on disk, so its absence \
         from the corpus proves nothing about the exclusion. It is the package \
         document `**/CLAUDE.md` would otherwise sweep in; if the package \
         dropped it, this leg needs a different package-owned document."
    );
    let archived: Vec<PathBuf> = fs::read_dir(root.join("sprints/archive"))
        .map(|entries| {
            entries
                .filter_map(Result::ok)
                .map(|e| e.path())
                .filter(|p| p.extension().is_some_and(|x| x == "md"))
                .collect()
        })
        .unwrap_or_default();
    assert!(
        !archived.is_empty(),
        "FENCE UNARMED — `sprints/archive/` holds no `.md` files, so \"no \
         archived sprint is in the live corpus\" is vacuously true. The live \
         filter is what keeps the widened `sprints/**/*.md` glob from enrolling \
         121 historical records (measured: `--corpus all` reports 707 findings \
         from that directory alone)."
    );

    let (code, docs, output) = list_live_corpus();
    assert_eq!(
        code,
        Some(0),
        "CORPUS LISTING FAILED — `{SCRIPT} --corpus live --list-docs` did not \
         exit 0. Without a listing, corpus membership is unmeasurable and the \
         four S120 globs are graded by inspection.\n\n{output}"
    );

    for member in CORPUS_MEMBERS {
        assert!(
            docs.iter().any(|d| d == member),
            "CORPUS GAP — `{member}` is not in the live corpus. The glob that \
             admits it has been removed or narrowed, and every citation in that \
             surface is now unchecked. This is invisible to the two detection \
             fences above: they pass explicit document paths, which bypass \
             `DOC_GLOBS` entirely.\n\nListed {} documents.",
            docs.len(),
        );
    }
    assert!(
        !docs.iter().any(|d| d == CORPUS_NON_MEMBER),
        "PACKAGE PROSE RE-ENTERED THE CORPUS — `{CORPUS_NON_MEMBER}` is listed. \
         The shared package is a submodule whose prose is package-root-relative \
         and rewritten at every converge; scanning it lets a package edit fail \
         this consumer's gate.\n\nListed {} documents.",
        docs.len(),
    );
    let archived_in_corpus: Vec<&String> = docs
        .iter()
        .filter(|d| d.starts_with("sprints/archive/"))
        .collect();
    assert!(
        archived_in_corpus.is_empty(),
        "ARCHIVE ENTERED THE LIVE CORPUS — {} archived sprint record(s) are \
         listed, starting with {:?}. A dated or archived record citing a line \
         that has since moved is an accurate record of its moment, not drift; \
         the live filter is what keeps the widened `sprints/**/*.md` glob from \
         enrolling all {} of them.",
        archived_in_corpus.len(),
        archived_in_corpus.first(),
        archived.len(),
    );
}

/// The standing guidance in `design/review/`: it calls itself the live review
/// standard and routes `review` to the contract and the principles it assembles
/// a review from. A live convention file is a record like any other.
const STANDING_REVIEW_DOC: &str = "design/review/CLAUDE.md";

/// A dated record in the same directory, and the reason the exclusion exists: a
/// review written against S61's tree cites lines that have since moved, which is
/// an accurate record of its moment.
const DATED_REVIEW_RECORD: &str = "design/review/sprint-61-final.md";

// Lifecycle classification of the `review/` directory
// (`tests/plan/s120-evidence-delta.md` §2 D-1, condition C8). The live filter
// excluded the whole directory, so `design/review/CLAUDE.md` — live guidance,
// not a dated record — was unchecked, and it really did route `review` to the
// retired `.claude/commands/review.md` for the whole S120 migration. The
// correction is a classification, not a suppression, and its direction matters:
// the gate went green because `review` repaired those two citations, never
// because they were enrolled in the ratchet.
//
// Both halves come from ONE listing, so the leg is self-arming: a filter that
// admitted the directory wholesale fails the exclusion half, and one that
// dropped the classification fails the membership half. The directory's other
// undated files are deliberately unasserted here — `review` states which of them
// are standing before any is admitted, because admitting a directory without
// reading its members is the error this condition corrects.
//
// spec: CLAUDE.md §Assurance — §"Records are claims too" (a live convention file
//       is a record; a dated one is history)
#[test]
fn citation_gate_corpus_holds_standing_review_guidance_but_not_its_dated_records() {
    let root = Path::new(workspace_root());

    for path in [STANDING_REVIEW_DOC, DATED_REVIEW_RECORD] {
        assert!(
            root.join(path).is_file(),
            "FENCE UNARMED — `{path}` is not on disk, so neither its membership \
             nor its absence is evidence about how `design/review/` is \
             classified. Point this leg at a live standing document and a live \
             dated record in that directory, or the directory itself is what \
             changed."
        );
    }

    let (code, docs, output) = list_live_corpus();
    assert_eq!(
        code,
        Some(0),
        "CORPUS LISTING FAILED — `{SCRIPT} --corpus live --list-docs` did not \
         exit 0, so the classification is unmeasurable.\n\n{output}"
    );

    assert!(
        docs.iter().any(|d| d == STANDING_REVIEW_DOC),
        "STANDING GUIDANCE IS OUTSIDE THE CORPUS — `{STANDING_REVIEW_DOC}` is not \
         listed, so the live filter is again excluding the `review/` directory \
         wholesale. That is how a convention file went on routing `review` to a \
         retired mechanism with the gate green.\n\nListed {} documents.",
        docs.len(),
    );
    assert!(
        !docs.iter().any(|d| d == DATED_REVIEW_RECORD),
        "DATED REVIEW RECORD ENTERED THE CORPUS — `{DATED_REVIEW_RECORD}` is \
         listed. The classification admits standing guidance under a `review/` \
         directory, not the dated records beside it; a review written against an \
         older tree cites lines that have since moved, and enrolling those is \
         backlog, not drift.\n\nListed {} documents.",
        docs.len(),
    );
}

/// A scheduling record whose ONE citation is the active sprint plan. No other
/// path-like token appears, so every counter this fence pins is about that one
/// citation.
const LIFECYCLE_ONLY_CITATION: &str = "\
# Detection-proof scratch document

The wave list for this increment is carried by sprints/SPRINT.md and read at \
every gate.
";

/// The between-sprints control: a `sprints/` citation of the same shape that is
/// NOT the lifecycle path, and is equally absent. It must still be reported —
/// otherwise the lifecycle rule is indistinguishable from `sprints/` having
/// fallen back out of the roots.
const ORDINARY_SPRINTS_CITATION: &str = "\
# Detection-proof scratch document

The phase list for the increment is carried by sprints/METHOD.md and read at \
every gate.
";

/// The mid-sprint control: a citation that is present in the scratch root and
/// ordinary. Verifying it is what shows the root is a working checker, so the
/// lifecycle path's `0 paths` is a rule rather than a dead instrument.
const PRESENT_ORDINARY_CITATION: &str = "\
# Detection-proof scratch document

The instrument for this class is scripts/verify-citations.py and it runs on \
every suite.
";

/// A synthetic repository root under the git-ignored `target/`, carrying the
/// gate's script, its baseline, and a sprint plan only when `mid_sprint`.
///
/// `verify-citations.py` derives its repository root from its own location, so a
/// copy of it IS a root — which is how BOTH delivery phases get exercised in one
/// run. Root `CLAUDE.md` §Delivery makes `sprints/SPRINT.md` present while a
/// sprint runs and absent between sprints, and neither shape can be staged in
/// the checked-in tree: this working tree is shared, and creating or deleting
/// live coordination state under other agents is not an option. Testing whichever
/// shape the tree happens to be in would also make the fence itself
/// phase-dependent — it would fail at Phase 7 on the archive it exists to
/// survive.
fn scratch_repo(base: &Path, name: &str, mid_sprint: bool) -> PathBuf {
    let root = base.join(name);
    let source = Path::new(workspace_root());
    for input in [SCRIPT, BASELINE] {
        let dst = root.join(input);
        fs::create_dir_all(dst.parent().expect("script paths have a parent"))
            .expect("create scratch script dir");
        fs::copy(source.join(input), &dst).expect("copy gate input into scratch root");
    }
    let plan = root.join("sprints/SPRINT.md");
    if mid_sprint {
        fs::create_dir_all(plan.parent().expect("plan path has a parent"))
            .expect("create scratch sprints dir");
        fs::write(&plan, "# Sprint plan\n\nWave 1 is open.\n").expect("write scratch sprint plan");
    }
    assert_eq!(
        plan.is_file(),
        mid_sprint,
        "scratch root `{name}` is not in the delivery phase it claims — the two \
         phases are the whole discrimination this fence makes"
    );
    fs::create_dir_all(root.join("notes")).expect("create scratch doc dir");
    fs::write(root.join("notes/lifecycle.md"), LIFECYCLE_ONLY_CITATION).expect("write scratch doc");
    root
}

/// The script, run inside `root` so it resolves citations against that root
/// rather than the checked-in tree.
fn run_script_in(root: &Path, args: &[&str]) -> GateRun {
    require_python3();
    let out = Command::new("python3")
        .arg(SCRIPT)
        .args(args)
        .current_dir(root)
        .output()
        .expect("python3 must be spawnable — require_python3() checked this");

    let mut output = String::from_utf8_lossy(&out.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&out.stderr);
    if !stderr.trim().is_empty() {
        output.push_str("\n--- stderr ---\n");
        output.push_str(&stderr);
    }
    GateRun {
        code: out.status.code(),
        output,
    }
}

/// The gate's invocation, run inside `root`.
fn run_gate_in(root: &Path, doc: &str) -> GateRun {
    run_script_in(root, &["--corpus", "live", "--baseline", BASELINE, doc])
}

// Lifecycle-path fence (`tests/plan/s120-evidence-delta.md` §2 D-1, condition
// C7). `sprints/SPRINT.md` is coordination state, not a
// source claim: root `CLAUDE.md` §Delivery makes it present while a sprint runs
// and absent between sprints, archived to `sprints/archive/sprint-NNN.md`. Under
// a `sprints/` root a naive existence test gives a verdict that follows the
// delivery phase rather than the record — green today, 174 `PATH` findings
// across 76 documents the moment this sprint's Phase 7 archives the file — and
// green for the wrong reason meanwhile, since a design note meaning S108's
// §Findings resolves against S120's file. So the path is recognised and counted,
// never verified, never a finding.
//
// Both delivery phases run here, on synthetic roots, so the fence is itself
// phase-independent: one that only ever exercised whichever shape the tree
// happened to be in would fail at Phase 7 on the very archive it exists to
// survive. Each root carries its own control, because "no finding" is also what
// a root that resolves nothing at all produces.
//
// spec: CLAUDE.md §Assurance — §"Records are claims too" (a lifecycle path is
//       not a record claim; the instrument says so in both delivery phases)
#[test]
fn citation_gate_counts_the_sprint_lifecycle_path_without_ever_verifying_it() {
    let target = Path::new(workspace_root()).join("target");
    fs::create_dir_all(&target).expect("target/ must be creatable");
    let scratch =
        tempfile::TempDir::new_in(&target).expect("scratch dir under target/ must be creatable");

    // LEG 1 — MID-SPRINT, the plan present. The citation is recognised (one
    // citation, not zero) and still contributes no verified path: an existence
    // test that happened to pass is not what the rule says, and `0 paths` is
    // what tells the two apart.
    let mid = scratch_repo(scratch.path(), "mid-sprint", true);
    fs::write(mid.join("notes/ordinary.md"), PRESENT_ORDINARY_CITATION).expect("write scratch doc");

    let present = run_gate_in(&mid, "notes/lifecycle.md");
    assert_eq!(
        present.code,
        Some(0),
        "LEG 1 FAILED — a document citing only `sprints/SPRINT.md` produced a \
         finding in a root where the plan is present. Whatever the reason, the \
         gate is making a claim about coordination state.\n\n{}",
        present.output,
    );
    assert!(
        present.output.contains("1 citations (0 paths")
            && present.output.contains(", 1 lifecycle)"),
        "LEG 1 IS VACUOUS OR WRONG-SHAPED — expected the citation to be counted \
         and left unverified: `1 citations (0 paths` and `1 lifecycle`. Zero \
         citations means the path is not recognised at all, so a rename of the \
         file would be equally invisible; a verified path means the gate is \
         resolving coordination state, which is green only for as long as the \
         sprint runs.\n\n{}",
        present.output,
    );

    // LEG 1 CONTROL — an ordinary citation that is present in the same root IS
    // verified. Without it, `0 paths` above would be satisfied just as well by a
    // root in which nothing resolves.
    let live_root = run_gate_in(&mid, "notes/ordinary.md");
    assert_eq!(
        live_root.code,
        Some(0),
        "LEG 1 CONTROL FAILED — `scripts/verify-citations.py`, which is present \
         in this root, was reported as a finding.\n\n{}",
        live_root.output,
    );
    assert!(
        live_root.output.contains("1 citations (1 paths")
            && live_root.output.contains(", 0 lifecycle)"),
        "LEG 1 CONTROL IS VACUOUS — the root did not verify an ordinary present \
         path, so leg 1's `0 paths` is not evidence about the lifecycle rule: a \
         root that resolves nothing reports `0 paths` for every citation.\n\n{}",
        live_root.output,
    );

    // LEG 2 — BETWEEN SPRINTS, the plan absent. Same document, same flags; the
    // rule has to be indifferent to the phase, so the counters must match leg 1
    // exactly.
    let between = scratch_repo(scratch.path(), "between-sprints", false);
    fs::write(between.join("notes/ordinary.md"), ORDINARY_SPRINTS_CITATION)
        .expect("write scratch doc");

    let absent = run_gate_in(&between, "notes/lifecycle.md");
    assert_eq!(
        absent.code,
        Some(0),
        "LEG 2 FAILED — with `sprints/SPRINT.md` absent, a document citing it \
         produced a finding. This is the between-sprints verdict, and it is what \
         turns the live gate RED with 174 findings across 76 documents the moment \
         Phase 7 archives the plan.\n\n{}",
        absent.output,
    );
    assert!(
        absent.output.contains("1 citations (0 paths") && absent.output.contains(", 1 lifecycle)"),
        "LEG 2 IS VACUOUS OR WRONG-SHAPED — expected exactly leg 1's counters, \
         `1 citations (0 paths` and `1 lifecycle`. A rule that reads differently \
         either side of the archive is the phase-following verdict this one \
         replaces.\n\n{}",
        absent.output,
    );

    // LEG 2 CONTROL — an ordinary `sprints/` citation, equally absent in this
    // root, is still reported. This is what makes leg 2's silence mean "the
    // lifecycle path is exempt" rather than "`sprints/` is not a root here".
    let control = run_gate_in(&between, "notes/ordinary.md");
    assert_eq!(
        control.code,
        Some(1),
        "LEG 2 CONTROL FAILED — in the same root, an absent `sprints/METHOD.md` \
         was not reported either, so leg 2's silence is not evidence about the \
         lifecycle rule: a root where `sprints/` is no longer a source root \
         produces exactly the same exit 0.\n\n{}",
        control.output,
    );
    assert!(
        control.output.contains("PATH") && control.output.contains("sprints/METHOD.md"),
        "LEG 2 CONTROL FIRED FOR THE WRONG REASON — exit 1, but the output does \
         not name `sprints/METHOD.md` under the PATH check. A traceback from \
         running the script out of a copied root exits non-zero while measuring \
         nothing.\n\n{}",
        control.output,
    );
}

/// A rule the ratchet's owner authored into the baseline's header and nowhere
/// the writer can rediscover it. The checked-in file carries exactly this shape
/// of text: the standing exception under which a corpus widening regenerates the
/// ratchet once.
const BASELINE_OWNER_RULE: &str =
    "# Owner rule: a widening regenerates this file once, and qa verifies the diff.";

/// A scratch document citing an action file absent from the scratch root, so the
/// regeneration below has something to record.
const SCRATCH_STALE_CITATION: &str = "\
# Detection-proof scratch document

The budget decision is carried by sprints/actions/ACT-0721-tail-call-budget.md.
";

// `--write-baseline` preserves the header its owner wrote.
//
// Regeneration is the one moment the ratchet's policy is being applied, and it
// was also the one moment that policy could vanish: the writer emitted a fixed
// header of its own, so regenerating over the checked-in file replaced `qa`'s
// widening exception — one of its few durable carriers — with boilerplate.
// Nothing would have failed; the rule simply would not have been there the next
// time anyone looked.
//
// Both legs run in one test because either alone is satisfied by a writer that
// is wrong in the other direction: one that always echoes whatever file it finds
// passes the preservation leg and writes a headerless file on a fresh path, and
// one that always emits its default passes the fresh-path leg.
//
// spec: CLAUDE.md §Assurance — §"Records are claims too" (the ratchet's own
//       policy is a record, and regeneration must not delete it)
#[test]
fn baseline_regeneration_preserves_the_owner_authored_header() {
    let target = Path::new(workspace_root()).join("target");
    fs::create_dir_all(&target).expect("target/ must be creatable");
    let scratch =
        tempfile::TempDir::new_in(&target).expect("scratch dir under target/ must be creatable");

    // A synthetic root: the script derives its repository root from its own
    // location, so a copy of it IS a root, and the regeneration below can never
    // reach the checked-in ratchet.
    let root = scratch.path().join("root");
    let script = root.join(SCRIPT);
    fs::create_dir_all(script.parent().expect("script path has a parent"))
        .expect("create scratch script dir");
    fs::copy(Path::new(workspace_root()).join(SCRIPT), &script).expect("copy script into root");
    fs::create_dir_all(root.join("notes")).expect("create scratch doc dir");
    fs::write(root.join("notes/stale.md"), SCRATCH_STALE_CITATION).expect("write scratch doc");

    // FRESH-PATH LEG, and the arming for the leg after it: with no file to carry
    // forward, the writer emits its own header — and that header does not
    // contain the owner rule, which is what makes the rule's survival below
    // evidence of preservation rather than of boilerplate.
    let fresh = "scripts/fresh-baseline.txt";
    let run = run_script_in(
        &root,
        &[
            "--corpus",
            "live",
            "--write-baseline",
            fresh,
            "notes/stale.md",
        ],
    );
    assert_eq!(
        run.code,
        Some(0),
        "FENCE UNARMED — `--write-baseline` to a fresh path did not exit 0, so \
         neither leg here is measuring the writer.\n\n{}",
        run.output,
    );
    let default_header = fs::read_to_string(root.join(fresh)).expect("read fresh baseline");
    assert!(
        !default_header.contains(BASELINE_OWNER_RULE),
        "FENCE UNARMED — the writer's own default header already contains the \
         owner rule, so finding it after a regeneration would prove nothing \
         about preservation.\n\n{default_header}"
    );
    assert!(
        default_header.starts_with('#') && default_header.contains(" entries."),
        "FRESH-PATH LEG FAILED — writing a baseline where none existed produced \
         no header and no entry count. The file has to explain itself to the \
         next reader; a bare list of fingerprints does not.\n\n{default_header}"
    );

    // PRESERVATION LEG — regenerate over a baseline whose header carries a rule
    // the writer has no way to reconstruct, and the rule survives.
    let owned = "scripts/owned-baseline.txt";
    fs::write(
        root.join(owned),
        format!("# Ratchet baseline.\n{BASELINE_OWNER_RULE}\n# 0 entries.\n"),
    )
    .expect("write owner-authored baseline");
    let run = run_script_in(
        &root,
        &[
            "--corpus",
            "live",
            "--write-baseline",
            owned,
            "notes/stale.md",
        ],
    );
    assert_eq!(
        run.code,
        Some(0),
        "PRESERVATION LEG FAILED — regenerating over an existing baseline did \
         not exit 0.\n\n{}",
        run.output,
    );
    let rewritten = fs::read_to_string(root.join(owned)).expect("read regenerated baseline");
    assert!(
        rewritten.contains(BASELINE_OWNER_RULE),
        "OWNER RULE DELETED BY REGENERATION — the header the ratchet's owner \
         wrote is gone from the regenerated file. A widening is exactly when \
         that rule is being applied, and this is the writer removing it at that \
         moment, silently.\n\n{rewritten}"
    );
    assert!(
        rewritten.contains("# 1 entries.") && rewritten.contains("ACT-0721-tail-call-budget.md"),
        "PRESERVATION LEG IS VACUOUS — the header survived but the file was not \
         regenerated: the entry count was not refreshed to the one finding in \
         this root, so a writer that left the file untouched would pass this \
         leg.\n\n{rewritten}"
    );
    assert_eq!(
        rewritten.matches("# 0 entries.").count(),
        0,
        "STALE COUNT CARRIED FORWARD — the previous header's entry count is \
         still in the file beside the new one. The count is a fact about the \
         entries below it, not part of the owner's prose.\n\n{rewritten}"
    );
}
