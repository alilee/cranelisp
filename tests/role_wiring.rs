//! Standing gate: **the declared role set and its wiring agree, measured on every
//! `cargo nextest run`.**
//!
//! Why the agreement is measured rather than assumed — the four independent
//! copies each dispatch depends on, and the two sprints they drifted across — is
//! carried in `scripts/verify-role-wiring.py`'s docstring. This file is the
//! wiring that runs it on every suite, plus its detection proof.
//!
//! `design/arch/principles/CLAUDE.md` grades its own reachability invariant
//! "asserted, with named falsifiers", and names two that did not exist: a
//! Phase-7 `ls`-against-the-index reconciliation "until a repository check runs
//! the reconciliation", and "the adapter-inventory check" for an adapter that
//! drops the first-read. W5 is the first; W6 is the second — W2 reads an
//! adapter's name, allocation and contract path, all of which stay correct while
//! the standard the role applies goes missing. Both are permanent rather than a
//! Phase-7 memory item because a reconciliation depending on remembering is the
//! failure state root `CLAUDE.md` §Assurance names.
//!
//! WHAT THE GATE CHECKS — the conditions are carried once, in
//! `scripts/verify-role-wiring.py`'s docstring, and are not restated here; this
//! file names each one it proves detects. The boundary of what it can reach —
//! the *declared* allocation, never the executed one — is carried there too.

use std::fs;
use std::os::unix::fs::symlink;
use std::path::{Path, PathBuf};
use std::process::Command;

/// The checked-in project root. `// read-only on project_root` — the gate reads
/// the checked-in declaration, adapters, contracts and principles; the only
/// thing this file writes is scratch copies under the git-ignored `target/`.
fn workspace_root() -> &'static str {
    env!("CARGO_MANIFEST_DIR")
}

const SCRIPT: &str = "scripts/verify-role-wiring.py";

/// Everything the gate reads. The scratch copy is built from this list, so a
/// check that grows a new input and is not added here fails the clean leg below
/// rather than silently degrading the detection proof.
const WIRING_INPUTS: &[&str] = &[
    "CLAUDE.md",
    ".claude/agents",
    ".claude/settings.json",
    ".github/agents",
    ".agents/skill-composition.toml",
    ".agents/skills",
    // W7's determinant: the shared package's own frontmatter is the definitive
    // model and effort allocation, and the gate reads it rather than carrying a
    // role-to-tier table.
    ".agents/agents",
    ".agents/tools/subagent_telemetry.py",
    ".agents/tools/claude_role.py",
    "design/arch/principles.md",
    "design/arch/principles",
    // W6's determinant: METHOD §1.1 states which roles owe the first-read, and
    // the gate reads the set from there rather than carrying its own copy.
    "sprints/METHOD.md",
];

struct GateRun {
    code: Option<i32>,
    output: String,
}

/// Run the gate against `root` — the same command line for the checked-in tree
/// and for a scratch copy, so the detection proof covers the real invocation.
fn run_gate(root: &Path) -> GateRun {
    require_python3();
    let out = Command::new("python3")
        .arg(SCRIPT)
        .arg(root)
        .current_dir(workspace_root())
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

/// The interpreter is a hard prerequisite, and its absence is a LOUD FAILURE
/// rather than a quiet pass — an un-runnable check is indistinguishable from a
/// check that finds nothing (`CLAUDE.md` §Assurance).
fn require_python3() {
    assert!(
        Command::new("python3").arg("--version").output().is_ok(),
        "ROLE-WIRING GATE CANNOT RUN — `python3` is not on PATH. This is NOT a \
         pass: {SCRIPT} is stdlib-only (Python 3.11+ for `tomllib`); install it \
         or delete this gate deliberately."
    );
}

fn copy_tree(src: &Path, dst: &Path) {
    if src.is_dir() {
        fs::create_dir_all(dst).expect("create scratch dir");
        for entry in fs::read_dir(src).expect("read source dir") {
            let entry = entry.expect("read dir entry");
            copy_tree(&entry.path(), &dst.join(entry.file_name()));
        }
    } else {
        if let Some(parent) = dst.parent() {
            fs::create_dir_all(parent).expect("create scratch parent");
        }
        fs::copy(src, dst).expect("copy scratch file");
    }
}

/// A faithful copy of every input the gate reads, under the git-ignored
/// `target/`. Planting a fault into the tracked tree — even transiently — is a
/// race hazard against any other agent sharing this working tree.
fn scratch_copy(base: &Path, name: &str) -> PathBuf {
    let root = base.join(name);
    let source = Path::new(workspace_root());
    for input in WIRING_INPUTS {
        copy_tree(&source.join(input), &root.join(input));
    }
    symlink("../.agents/skills", root.join(".claude/skills")).expect("scratch skills symlink");
    root
}

// The gate itself.
//
// spec: CLAUDE.md §Roles — the twelve dispatched roles, their contracts in the
//       pinned `.agents` package, and the host adapters that expose them
#[test]
fn role_wiring_agrees_across_declaration_adapters_contracts_and_principles() {
    let run = run_gate(Path::new(workspace_root()));
    assert_eq!(
        run.code,
        Some(0),
        "ROLE WIRING DRIFT — the twelve roles root `CLAUDE.md` §Roles declares no \
         longer agree with the adapters, contracts, composition, dispatch wiring \
         or principle index that carry them.\n\n\
         Each finding below is one copy of a fact disagreeing with another copy. \
         A role whose adapter is missing cannot be dispatched; an adapter naming \
         the wrong contract dispatches the wrong role; a Principle absent from \
         `design/arch/principles.md` is not in force even though its file is on \
         disk. Re-check locally with:\n\
         \x20   python3 {SCRIPT}\n\n\
         {}",
        run.output,
    );
}

// The gate's own capability fence: `CLAUDE.md` §Assurance — "an instrument is
// unverified until it is proven to detect", with the negative leg (silence when
// the fault is absent) as load-bearing as the positive one.
//
// One plant per condition, each on its own scratch copy so a plant cannot mask
// another. The clean leg pins the counters: a script that stopped enumerating
// adapters, composed skills, principles, the first-read set or the allocation
// pairs would exit 0 exactly as a correct one does, so "12 roles", "2 composed
// skills", "26 principles", "4 first-read roles" and "12 allocation pairs" are
// the evidence that the run inspected something.
//
// Each plant is the smallest edit that produces the failure class, and W4's is
// deliberately a hook that runs a REAL script rather than a missing one: a check
// that only tested the command's existence would pass it.
//
// spec: CLAUDE.md §Assurance — §"Records are claims too" (instrument detection
//       proof; both polarities)
#[test]
fn role_wiring_gate_detects_planted_adapter_and_principle_faults_and_clears_a_sound_copy() {
    let target = Path::new(workspace_root()).join("target");
    fs::create_dir_all(&target).expect("target/ must be creatable");
    let scratch =
        tempfile::TempDir::new_in(&target).expect("scratch dir under target/ must be creatable");
    let base = scratch.path();

    // NEGATIVE LEG — an unmodified copy passes, and says how much it looked at.
    let clean = scratch_copy(base, "clean");
    let sound = run_gate(&clean);
    assert_eq!(
        sound.code,
        Some(0),
        "NEGATIVE LEG FAILED — the gate reported a finding against an unmodified \
         copy of the checked-in wiring. A gate that fires on sound wiring trains \
         everyone to ignore it, and the next real drift lands unread.\n\n{}",
        sound.output,
    );
    assert!(
        sound.output.contains("12 roles")
            && sound.output.contains("2 composed skills")
            && sound.output.contains("26 principles")
            && sound.output.contains("4 first-read roles")
            && sound.output.contains("12 allocation pairs"),
        "NEGATIVE LEG IS VACUOUS — the gate exited 0 on the sound copy without \
         reporting the twelve declared roles, two composed support skills, \
         twenty-six indexed Principles, four first-read roles and twelve \
         local↔shared allocation pairs it inspected. A script that enumerated \
         nothing exits 0 too, and W3, W6 and W7 in particular are loops over a \
         set: an empty set passes them. W7's count is the only thing separating \
         \"every adapter agrees with its shared carrier\" from \"no carrier was \
         ever opened\". (If the counts changed deliberately, this assertion is \
         the place that records it, and `{}` is the list the copy is built \
         from.)\n\n{}",
        "WIRING_INPUTS",
        sound.output,
    );

    // POSITIVE LEG 1 (W1) — a declared role loses its Claude adapter. This is
    // the drift class the package converge can introduce at any increment.
    let missing_adapter = scratch_copy(base, "missing-adapter");
    fs::remove_file(missing_adapter.join(".claude/agents/docs.md")).expect("remove plant target");
    let run = run_gate(&missing_adapter);
    assert_eq!(
        run.code,
        Some(1),
        "POSITIVE LEG FAILED (W1) — deleting `.claude/agents/docs.md` from the \
         copy did not produce exit 1. A declared role with no adapter is \
         undispatchable, and the gate cannot see it.\n\n{}",
        run.output,
    );
    assert!(
        run.output.contains("W1") && run.output.contains("`docs`"),
        "POSITIVE LEG FIRED FOR THE WRONG REASON (W1) — exit 1, but the output \
         does not name role `docs` under W1. A traceback or an argument error \
         exits non-zero while detecting nothing.\n\n{}",
        run.output,
    );

    // POSITIVE LEG 2 (W2) — an adapter that names a different role than its
    // filename. The inventory check (W1) is blind to this: the file is present
    // and correctly named on disk, and only its frontmatter lies.
    let wrong_name = scratch_copy(base, "wrong-adapter-name");
    let adapter = wrong_name.join(".claude/agents/spec.md");
    let body = fs::read_to_string(&adapter).expect("read plant target");
    fs::write(
        &adapter,
        body.replacen("name: spec", "name: specification", 1),
    )
    .expect("write plant");
    let run = run_gate(&wrong_name);
    assert_eq!(
        run.code,
        Some(1),
        "POSITIVE LEG FAILED (W2) — rewriting `.claude/agents/spec.md` to \
         `name: specification` did not produce exit 1, so an adapter that \
         dispatches the wrong role passes the gate.\n\n{}",
        run.output,
    );
    assert!(
        run.output.contains("W2") && run.output.contains(".claude/agents/spec.md"),
        "POSITIVE LEG FIRED FOR THE WRONG REASON (W2) — exit 1, but the output \
         does not name the adapter file under W2.\n\n{}",
        run.output,
    );

    // POSITIVE LEG 3 (W3) — a composed support skill whose contract is gone.
    // `quality-standards` is named by `[support].skills` and by every role's
    // `always`; every role contract opens by requiring it. It is not a declared
    // role, so W1 is blind to it by construction, and a role dispatched without
    // it loses the shared provenance and risk-weighting standards silently.
    let missing_skill = scratch_copy(base, "missing-composed-skill");
    fs::remove_dir_all(missing_skill.join(".agents/skills/quality-standards"))
        .expect("remove plant target");
    let run = run_gate(&missing_skill);
    assert_eq!(
        run.code,
        Some(1),
        "POSITIVE LEG FAILED (W3) — removing `.agents/skills/quality-standards/` \
         from the copy did not produce exit 1. The composition would then name a \
         support skill with no contract on disk, and every role that loads it \
         gets nothing.\n\n{}",
        run.output,
    );
    assert!(
        run.output.contains("W3") && run.output.contains("quality-standards"),
        "POSITIVE LEG FIRED FOR THE WRONG REASON (W3) — exit 1, but the output \
         does not name `quality-standards` under W3. W1 does not cover it: it is \
         a support skill, not a declared role.\n\n{}",
        run.output,
    );

    // POSITIVE LEG 4 (W4) — one lifecycle event's hook rewritten to run a
    // different real script. Only half the dispatch record is then written, and
    // the summary reads as if the missing half's rows had simply never been
    // dispatched. The hook-command match is the only W4 branch with logic; the
    // absent-file and symlink branches are read-verified only.
    let wrong_hook = scratch_copy(base, "wrong-telemetry-hook");
    let settings = wrong_hook.join(".claude/settings.json");
    let body = fs::read_to_string(&settings).expect("read plant target");
    let at = body
        .find("\"SubagentStop\"")
        .expect("the checked-in settings.json must declare a SubagentStop hook");
    let (head, tail) = body.split_at(at);
    let rewritten = tail.replacen(
        ".agents/tools/subagent_telemetry.py",
        ".agents/tools/claude_role.py",
        1,
    );
    assert_ne!(
        tail, rewritten,
        "PLANT DID NOT APPLY (W4) — no `subagent_telemetry.py` command follows \
         the `SubagentStop` key in the copied settings, so nothing was rewritten \
         and the leg below would be testing the unmodified file."
    );
    fs::write(&settings, format!("{head}{rewritten}")).expect("write plant");
    let run = run_gate(&wrong_hook);
    assert_eq!(
        run.code,
        Some(1),
        "POSITIVE LEG FAILED (W4) — pointing the `SubagentStop` hook at \
         `.agents/tools/claude_role.py` did not produce exit 1. Dispatch rows \
         would open and never close, and `dispatch_stats.py` omits open rows \
         entirely, so the loss is invisible in the summary.\n\n{}",
        run.output,
    );
    assert!(
        run.output.contains("W4") && run.output.contains("SubagentStop"),
        "POSITIVE LEG FIRED FOR THE WRONG REASON (W4) — exit 1, but the output \
         does not name the `SubagentStop` event under W4. The substituted \
         command is a real file in the package, so an existence-only check would \
         report nothing here and the exit code would have to come from \
         somewhere else.\n\n{}",
        run.output,
    );

    // POSITIVE LEG 5 (W5) — a Principle file with no index line. The index is
    // the single carrier of the set (`design/arch/principles/CLAUDE.md`), so a
    // file without a line is a Principle that is not in force while looking, to
    // anyone listing the directory, exactly like one that is.
    let orphan = scratch_copy(base, "orphan-principle");
    fs::write(
        orphan.join("design/arch/principles/27-planted-orphan-principle.md"),
        "---\nnumber: 27\ntitle: Planted orphan\n---\n\n# Principle 27 — Planted orphan\n",
    )
    .expect("write plant");
    let run = run_gate(&orphan);
    assert_eq!(
        run.code,
        Some(1),
        "POSITIVE LEG FAILED (W5) — adding a principle file with no line in \
         `design/arch/principles.md` did not produce exit 1. The reachability \
         falsifier `design/arch/principles/CLAUDE.md` names is therefore still \
         absent.\n\n{}",
        run.output,
    );
    assert!(
        run.output.contains("W5") && run.output.contains("27-planted-orphan-principle.md"),
        "POSITIVE LEG FIRED FOR THE WRONG REASON (W5) — exit 1, but the output \
         does not name the orphaned principle file under W5.\n\n{}",
        run.output,
    );

    // POSITIVE LEG 6 (W6) — an adapter that drops the principles first-read.
    // W1 and W2 are both blind to it: the file is present, correctly named, and
    // carries its allocation and its contract path. The role still dispatches —
    // it just dispatches without the standard it is meant to apply, which is the
    // S65/S76 drift class in its quietest form.
    let dropped_first_read = scratch_copy(base, "adapter-drops-first-read");
    let adapter = dropped_first_read.join(".claude/agents/dev.md");
    let body = fs::read_to_string(&adapter).expect("read plant target");
    let stripped: String = body
        .lines()
        .filter(|l| !l.contains("design/arch/principles.md"))
        .map(|l| format!("{l}\n"))
        .collect();
    assert_ne!(
        body, stripped,
        "PLANT DID NOT APPLY (W6) — `.claude/agents/dev.md` in the copy names no \
         `design/arch/principles.md`, so nothing was removed and the leg below \
         would be testing the unmodified file. Either the adapter already dropped \
         the first-read (the checked-in gate would be RED) or `dev` is no longer \
         one of the roles METHOD §1.1 obliges."
    );
    fs::write(&adapter, stripped).expect("write plant");
    let run = run_gate(&dropped_first_read);
    assert_eq!(
        run.code,
        Some(1),
        "POSITIVE LEG FAILED (W6) — removing the principles first-read from \
         `.claude/agents/dev.md` did not produce exit 1. \
         `design/arch/principles/CLAUDE.md` grades the reachability invariant \
         \"asserted, with named falsifiers\" and names this check as the \
         falsifier for a dropped first-read; without detection the claim stays \
         asserted.\n\n{}",
        run.output,
    );
    assert!(
        run.output.contains("W6") && run.output.contains(".claude/agents/dev.md"),
        "POSITIVE LEG FIRED FOR THE WRONG REASON (W6) — exit 1, but the output \
         does not name the adapter file under W6. In particular a W6 finding \
         that the METHOD sentence itself was unreadable would exit 1 while \
         proving nothing about the adapters.\n\n{}",
        run.output,
    );

    // POSITIVE LEG 7 (W7) — a consumer adapter that silently remaps a role away
    // from the package's definitive allocation. W1 and W2 are both blind: the
    // file is present, correctly named, cites its contract, and carries a
    // perfectly well-formed `model:` — it is just not the allocated one, and the
    // transport prefers this copy, so `qa` would execute on the wrong tier with
    // every other gate green.
    //
    // `model:` and `effort:` are compared in one loop body over the two keys, so
    // this plant exercises the comparison itself; what proves the loop reached
    // every role is the clean leg's `12 allocation pairs`.
    let remapped = scratch_copy(base, "remapped-allocation");
    let adapter = remapped.join(".claude/agents/qa.md");
    let body = fs::read_to_string(&adapter).expect("read plant target");
    let rewritten = body.replacen("model: fable", "model: opus", 1);
    assert_ne!(
        body, rewritten,
        "PLANT DID NOT APPLY (W7) — `.claude/agents/qa.md` in the copy declares \
         no `model: fable`, so nothing was rewritten and the leg below would be \
         testing the unmodified file. Either `qa`'s allocation moved (in which \
         case the shared carrier moved with it and this plant needs a new value) \
         or the adapter lost its allocation, which W2 would report."
    );
    fs::write(&adapter, rewritten).expect("write plant");
    let run = run_gate(&remapped);
    assert_eq!(
        run.code,
        Some(1),
        "POSITIVE LEG FAILED (W7) — remapping `.claude/agents/qa.md` to \
         `model: opus` while `.agents/agents/qa.md` allocates `fable` did not \
         produce exit 1. `.agents/CLAUDE.md` §Execution tiers makes the shared \
         frontmatter definitive and forbids a consumer remapping it; without \
         detection that rule is asserted and a local remap executes \
         unobserved.\n\n{}",
        run.output,
    );
    assert!(
        run.output.contains("W7")
            && run.output.contains("`qa`")
            && run.output.contains("opus")
            && run.output.contains("fable"),
        "POSITIVE LEG FIRED FOR THE WRONG REASON (W7) — exit 1, but the output \
         does not name role `qa` under W7 with both the local and the shared \
         value. A checker that never opened `.agents/agents/qa.md` — or that \
         compared the adapter against itself — cannot report the pair, and a \
         finding naming only one side would not distinguish which copy \
         drifted.\n\n{}",
        run.output,
    );
}
