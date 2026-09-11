//! Standing gate for the repository's declared document inventory and local
//! references.
//!
//! The shared package owns the checker. Cranelisp owns
//! `standing-documents.toml`, invokes the checker directly, and carries no
//! baseline. The project gate therefore stays red while unresolved findings
//! remain. The independent scratch-project test proves the same invocation can
//! distinguish a clean source citation from a newly planted stale symbol.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

const CHECKER: &str = ".agents/tools/check_documents.py";
const CONFIG: &str = "standing-documents.toml";

fn workspace_root() -> &'static str {
    env!("CARGO_MANIFEST_DIR")
}

struct GateRun {
    code: Option<i32>,
    output: String,
}

impl GateRun {
    fn passed(&self) -> bool {
        self.code == Some(0)
    }
}

fn require_prerequisites() {
    let python = Command::new("python3").arg("--version").output();
    assert!(
        python.is_ok(),
        "DOCUMENT GATE CANNOT RUN — `python3` is not on PATH"
    );
    for path in [CHECKER, CONFIG] {
        assert!(
            Path::new(workspace_root()).join(path).is_file(),
            "DOCUMENT GATE CANNOT RUN — required input `{path}` is absent"
        );
    }
}

fn run_checker(root: &Path, config: &Path, extra_args: &[&str]) -> GateRun {
    require_prerequisites();
    let checker = Path::new(workspace_root()).join(CHECKER);
    let out = Command::new("python3")
        .arg(checker)
        .arg("--root")
        .arg(root)
        .arg("--config")
        .arg(config)
        .args(extra_args)
        .current_dir(workspace_root())
        .output()
        .expect("python3 must be spawnable — require_prerequisites() checked this");

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

fn run_project_gate(extra_args: &[&str]) -> GateRun {
    require_prerequisites();
    let out = Command::new("python3")
        .args([CHECKER, "--root", ".", "--config", CONFIG])
        .args(extra_args)
        .current_dir(workspace_root())
        .output()
        .expect("python3 must be spawnable — require_prerequisites() checked this");

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

fn initialize_git(root: &Path) {
    let output = Command::new("git")
        .args(["init", "--quiet"])
        .current_dir(root)
        .output()
        .expect("git must be spawnable for the checker fixture");
    assert!(
        output.status.success(),
        "fixture Git initialization failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

fn scratch_project(base: &Path) -> PathBuf {
    let root = base.join("project");
    fs::create_dir_all(root.join("docs")).expect("create fixture documents");
    fs::create_dir_all(root.join("src")).expect("create fixture source");
    initialize_git(&root);

    fs::write(
        root.join("CLAUDE.md"),
        "# Fixture guidance\n\n[Guide](docs/guide.md) records the source claim. \
         [The declaration](standing-documents.toml) defines the inventory.\n",
    )
    .expect("write fixture root memory");
    fs::write(
        root.join("docs/guide.md"),
        "# Guide\n\nThe implementation is src/lib.rs::present_symbol.\n",
    )
    .expect("write fixture guide");
    fs::write(root.join("src/lib.rs"), "pub fn present_symbol() {}\n")
        .expect("write fixture source");
    fs::write(
        root.join(CONFIG),
        r#"[inventory]
version = 1
root_memory = "CLAUDE.md"
owners = ["test"]

[references]
source_roots = ["src"]
symbol_roots = ["src"]

[[document]]
path = "CLAUDE.md"
kind = "root-memory"
owner = "test"
purpose = "Fixture guidance and inventory."

[[document]]
path = "docs/guide.md"
kind = "standing"
owner = "test"
purpose = "Records the source claim."
established_by = "CLAUDE.md"

[[document]]
path = "standing-documents.toml"
kind = "standing"
owner = "test"
purpose = "Defines the fixture document inventory."
established_by = "CLAUDE.md"
"#,
    )
    .expect("write fixture declaration");
    root
}

fn corpus_contains(report: &str, path: &str) -> bool {
    report.contains(&format!("\"path\": \"{path}\""))
}

// The real project invocation is the gate. It must not reinterpret exit 1 as
// success: unresolved findings stay visible until their owners repair or
// explicitly disposition them.
//
// spec: CLAUDE.md §Assurance — §"Records are claims too"
#[test]
fn project_documents_conform_to_the_checked_in_declaration() {
    let run = run_project_gate(&[]);
    assert_ne!(
        run.code,
        Some(2),
        "DOCUMENT GATE COULD NOT INSPECT THE PROJECT — invalid invocation, \
         configuration, or input:\n\n{}",
        run.output,
    );
    assert!(
        run.passed(),
        "DOCUMENT GATE FOUND UNRESOLVED CLAIMS (exit {:?}). Repair the cited \
         document or obtain a specific approved disposition; this project gate \
         has no baseline. Re-run with:\n\n    python3 {CHECKER} --root . --config {CONFIG}\n\n{}",
        run.code,
        run.output,
    );
}

// The shared invocation must distinguish a sound source-symbol claim from the
// same document after its symbol is made stale. Empty findings are asserted on
// the clean leg so exit 0 cannot come from an uninspected fixture.
//
// spec: CLAUDE.md §Assurance — §"Records are claims too" (instrument detection)
#[test]
fn project_document_gate_detects_a_planted_source_symbol_and_clears_its_control() {
    let target = Path::new(workspace_root()).join("target");
    fs::create_dir_all(&target).expect("target/ must be creatable");
    let temporary = tempfile::TempDir::new_in(&target).expect("create fixture root under target/");
    let root = scratch_project(temporary.path());
    let config = root.join(CONFIG);

    let clean = run_checker(&root, &config, &["--format", "json"]);
    assert_eq!(
        clean.code,
        Some(0),
        "clean fixture failed:\n{}",
        clean.output
    );
    assert!(
        clean.output.contains("\"findings\": []")
            && corpus_contains(&clean.output, "docs/guide.md")
            && clean.output.contains("\"source-symbol\""),
        "clean fixture did not prove both discovery and the source-symbol rule:\n{}",
        clean.output,
    );

    fs::write(
        root.join("docs/guide.md"),
        "# Guide\n\nThe implementation is src/lib.rs::totally_fictional_symbol.\n",
    )
    .expect("plant stale source symbol");
    let planted = run_checker(&root, &config, &["--format", "json"]);
    assert_eq!(
        planted.code,
        Some(1),
        "planted finding must produce checker exit 1:\n{}",
        planted.output,
    );
    assert!(
        planted.output.contains("\"rule\": \"source-symbol\"")
            && planted.output.contains("totally_fictional_symbol")
            && planted.output.contains("\"source\": \"docs/guide.md\""),
        "planted run failed for the wrong reason:\n{}",
        planted.output,
    );
}

// Discovery remains independent of declarations: the real project manifest
// includes current scheduling, host, review, and declaration products while the
// separately owned `.agents` Gitlink stays outside the project corpus.
//
// spec: CLAUDE.md §Assurance — shared document discovery and ownership boundary
#[test]
fn project_document_discovery_covers_owned_surfaces_and_the_package_boundary() {
    let run = run_project_gate(&["--list-docs", "--format", "json"]);
    assert_eq!(
        run.code,
        Some(0),
        "project discovery could not run:\n{}",
        run.output,
    );
    for path in [
        "sprints/METHOD.md",
        ".claude/agents/qa.md",
        ".github/agents/qa.agent.md",
        ".github/copilot-instructions.md",
        "design/review/CLAUDE.md",
        "design/review/sprint-61-final.md",
        "standing-documents.toml",
        "tests/plan/s122-document-checker-reconciliation/README.md",
    ] {
        assert!(
            corpus_contains(&run.output, path),
            "project discovery omitted `{path}`:\n{}",
            run.output,
        );
    }
    assert!(
        !run.output.contains("\"path\": \".agents/"),
        "project discovery descended into the separately owned `.agents` Gitlink:\n{}",
        run.output,
    );

    let declaration = fs::read_to_string(Path::new(workspace_root()).join(CONFIG))
        .expect("read checked-in project declaration");
    assert!(
        declaration.contains("name = \"frozen-review-records\"")
            && declaration.contains("patterns = [\"design/review/*.md\"]")
            && declaration.contains("reference_policy = \"historical-record\"")
            && declaration.contains("path = \".agents\""),
        "project declaration lost the approved review-history or package-boundary policy",
    );
}
