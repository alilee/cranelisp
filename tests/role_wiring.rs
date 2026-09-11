//! Standing gate: shared consumer conformance and Cranelisp's local role wiring.
//!
//! `scripts/verify-role-wiring.py` carries the condition list and invokes the
//! package-owned consumer checker before local checks. This file makes that gate
//! run on every suite and proves both its clean and planted-fault polarities.

use std::fs;
use std::os::unix::fs::symlink;
use std::path::{Path, PathBuf};
use std::process::Command;

/// `// read-only on project_root` — the gate reads checked-in wiring. Detection
/// plants are made only in scratch copies under the git-ignored `target/`.
fn workspace_root() -> &'static str {
    env!("CARGO_MANIFEST_DIR")
}

const SCRIPT: &str = "scripts/verify-role-wiring.py";

/// Every input the composed gate reads. The package is copied whole because its
/// checker deliberately discovers package facts, including plugin manifests.
const WIRING_INPUTS: &[&str] = &[
    "CLAUDE.md",
    ".agents-consumer.toml",
    ".gitmodules",
    ".claude/agents",
    ".claude/settings.json",
    ".github/agents",
    ".agents",
    "design/arch/principles.md",
    "design/arch/principles",
    "sprints/METHOD.md",
];

struct GateRun {
    code: Option<i32>,
    output: String,
}

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

fn require_python3() {
    assert!(
        Command::new("python3").arg("--version").output().is_ok(),
        "ROLE-WIRING GATE CANNOT RUN — `python3` is not on PATH. This is not a \
         pass: the shared checker requires Python 3.11 or newer."
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

fn scratch_copy(base: &Path, name: &str) -> PathBuf {
    let root = base.join(name);
    let source = Path::new(workspace_root());
    for input in WIRING_INPUTS {
        copy_tree(&source.join(input), &root.join(input));
    }
    symlink("../.agents/skills", root.join(".claude/skills")).expect("scratch skills symlink");
    root
}

fn rewrite_once(path: &Path, from: &str, to: &str, label: &str) {
    let body = fs::read_to_string(path).expect("read plant target");
    let rewritten = body.replacen(from, to, 1);
    assert_ne!(body, rewritten, "PLANT DID NOT APPLY ({label})");
    fs::write(path, rewritten).expect("write plant");
}

// spec: CLAUDE.md §Roles — eleven dispatched subordinate roles and the host
//       wiring that exposes their shared contracts
#[test]
fn role_wiring_agrees_with_shared_consumer_contract_and_local_adapters() {
    let run = run_gate(Path::new(workspace_root()));
    assert_eq!(
        run.code,
        Some(0),
        "ROLE WIRING DRIFT — shared consumer conformance or Cranelisp's local \
         Copilot, hook, Principle, or first-read wiring disagrees. Re-check with:\n\
         \x20   python3 {SCRIPT}\n\n{}",
        run.output,
    );
}

// The capability fence uses independent scratch copies so one fault cannot mask
// another. The shared-check plant also proves ordering: its failure returns
// before the local summary can be printed.
//
// spec: CLAUDE.md §Assurance — §"Records are claims too" (instrument detection
//       proof; both polarities)
#[test]
fn role_wiring_gate_detects_shared_and_local_faults_and_clears_a_sound_copy() {
    let target = Path::new(workspace_root()).join("target");
    fs::create_dir_all(&target).expect("target/ must be creatable");
    let scratch =
        tempfile::TempDir::new_in(&target).expect("scratch dir under target/ must be creatable");
    let base = scratch.path();

    let clean = scratch_copy(base, "clean");
    let run = run_gate(&clean);
    assert_eq!(
        run.code,
        Some(0),
        "NEGATIVE LEG FAILED — an unmodified copy reported drift.\n\n{}",
        run.output,
    );
    for evidence in [
        "conformant: 11 dispatched roles, checked-in adapters",
        "11 subordinate roles",
        "11 Copilot adapters",
        "26 principles",
        "4 first-read roles",
        "0 local finding(s)",
    ] {
        assert!(
            run.output.contains(evidence),
            "NEGATIVE LEG IS VACUOUS — clean output does not prove it inspected \
             `{evidence}`.\n\n{}",
            run.output,
        );
    }

    // Shared integration and ordering — the coordinator is invalid in the
    // subordinate declaration. A simultaneous local fault would be present if
    // local checks ran, but the shared failure must be the entire report.
    let shared_fault = scratch_copy(base, "shared-consumer-fault");
    rewrite_once(
        &shared_fault.join(".agents-consumer.toml"),
        "\"training\"]",
        "\"training\", \"sprint\"]",
        "shared checker",
    );
    fs::remove_file(shared_fault.join(".github/agents/docs.agent.md"))
        .expect("plant masked local fault");
    let run = run_gate(&shared_fault);
    assert_eq!(
        run.code,
        Some(1),
        "shared checker fault passed\n\n{}",
        run.output
    );
    assert!(
        run.output.contains("declaration-value-invalid")
            && run.output.contains("coordinator")
            && !run.output.contains("local finding")
            && !run.output.contains("=== W1"),
        "SHARED CHECKER DID NOT RUN FIRST — expected its coordinator fault and \
         no local report.\n\n{}",
        run.output,
    );

    // W1a — prose and machine declaration diverge.
    let prose_drift = scratch_copy(base, "prose-role-drift");
    let claude = prose_drift.join("CLAUDE.md");
    let body = fs::read_to_string(&claude).expect("read CLAUDE.md plant target");
    let stripped = body
        .lines()
        .filter(|line| !line.starts_with("| `docs` |"))
        .collect::<Vec<_>>()
        .join("\n");
    assert_ne!(body, stripped, "PLANT DID NOT APPLY (W1 prose)");
    fs::write(&claude, stripped).expect("write prose plant");
    let run = run_gate(&prose_drift);
    assert_eq!(run.code, Some(1), "W1 prose fault passed\n\n{}", run.output);
    assert!(
        run.output.contains("W1")
            && run
                .output
                .contains(".agents-consumer.toml dispatches `docs`")
            && run.output.contains("CLAUDE.md §Roles"),
        "W1 prose fault fired for the wrong reason.\n\n{}",
        run.output,
    );

    // W1b — Copilot loses one declared role while shared Claude wiring stays sound.
    let missing_copilot = scratch_copy(base, "missing-copilot-adapter");
    fs::remove_file(missing_copilot.join(".github/agents/docs.agent.md"))
        .expect("remove Copilot plant target");
    let run = run_gate(&missing_copilot);
    assert_eq!(
        run.code,
        Some(1),
        "W1 Copilot fault passed\n\n{}",
        run.output
    );
    assert!(
        run.output.contains("W1") && run.output.contains("docs.agent.md"),
        "W1 Copilot fault fired for the wrong reason.\n\n{}",
        run.output,
    );

    // W2 — Copilot adapter identity differs from its filename and contract slot.
    let wrong_name = scratch_copy(base, "wrong-copilot-name");
    rewrite_once(
        &wrong_name.join(".github/agents/spec.agent.md"),
        "name: spec",
        "name: specification",
        "W2",
    );
    let run = run_gate(&wrong_name);
    assert_eq!(run.code, Some(1), "W2 fault passed\n\n{}", run.output);
    assert!(
        run.output.contains("W2")
            && run.output.contains(".github/agents/spec.agent.md")
            && run.output.contains("specification"),
        "W2 fault fired for the wrong reason.\n\n{}",
        run.output,
    );

    // W3a — one lifecycle event calls another real package tool.
    let wrong_telemetry = scratch_copy(base, "wrong-telemetry-hook");
    let settings = wrong_telemetry.join(".claude/settings.json");
    let body = fs::read_to_string(&settings).expect("read settings plant target");
    let at = body
        .find("\"SubagentStop\"")
        .expect("SubagentStop hook exists");
    let (head, tail) = body.split_at(at);
    let rewritten = tail.replacen("subagent_telemetry.py", "codex_role.py", 1);
    assert_ne!(tail, rewritten, "PLANT DID NOT APPLY (W3 telemetry)");
    fs::write(&settings, format!("{head}{rewritten}")).expect("write hook plant");
    let run = run_gate(&wrong_telemetry);
    assert_eq!(
        run.code,
        Some(1),
        "W3 telemetry fault passed\n\n{}",
        run.output
    );
    assert!(
        run.output.contains("W3") && run.output.contains("SubagentStop"),
        "W3 telemetry fault fired for the wrong reason.\n\n{}",
        run.output,
    );

    // W3b — the required provider-routing guard is filtered to one tool name.
    let filtered_guard = scratch_copy(base, "filtered-dispatch-guard");
    let settings = filtered_guard.join(".claude/settings.json");
    rewrite_once(
        &settings,
        "\"PreToolUse\": [\n      {\n        \"hooks\"",
        "\"PreToolUse\": [\n      {\n        \"matcher\": \"Task\",\n        \"hooks\"",
        "W3 guard",
    );
    let run = run_gate(&filtered_guard);
    assert_eq!(run.code, Some(1), "W3 guard fault passed\n\n{}", run.output);
    assert!(
        run.output.contains("W3")
            && run.output.contains("PreToolUse")
            && run.output.contains("filtered"),
        "W3 guard fault fired for the wrong reason.\n\n{}",
        run.output,
    );

    // W4 — a Principle exists on disk but is absent from the canonical index.
    let orphan = scratch_copy(base, "orphan-principle");
    fs::write(
        orphan.join("design/arch/principles/27-planted-orphan-principle.md"),
        "---\nnumber: 27\ntitle: Planted orphan\n---\n",
    )
    .expect("write Principle plant");
    let run = run_gate(&orphan);
    assert_eq!(run.code, Some(1), "W4 fault passed\n\n{}", run.output);
    assert!(
        run.output.contains("W4") && run.output.contains("27-planted-orphan-principle.md"),
        "W4 fault fired for the wrong reason.\n\n{}",
        run.output,
    );

    // W5 — a required host adapter drops the repository's first-read instruction.
    let dropped_first_read = scratch_copy(base, "adapter-drops-first-read");
    let adapter = dropped_first_read.join(".claude/agents/dev.md");
    let body = fs::read_to_string(&adapter).expect("read adapter plant target");
    let stripped: String = body
        .lines()
        .filter(|line| !line.contains("design/arch/principles.md"))
        .map(|line| format!("{line}\n"))
        .collect();
    assert_ne!(body, stripped, "PLANT DID NOT APPLY (W5)");
    fs::write(&adapter, stripped).expect("write first-read plant");
    let run = run_gate(&dropped_first_read);
    assert_eq!(run.code, Some(1), "W5 fault passed\n\n{}", run.output);
    assert!(
        run.output.contains("W5") && run.output.contains(".claude/agents/dev.md"),
        "W5 fault fired for the wrong reason.\n\n{}",
        run.output,
    );
}
