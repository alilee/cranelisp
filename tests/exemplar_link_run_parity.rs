//! Standing `--link`-then-run vs `--run` parity gate for the showcase project.
//!
//! Replaces FIXME 0875 ("`--link` of the exemplar fails"), which `/qa` CLOSED
//! at S118 P6 as not reproducible at HEAD (`tests/plan/s118-test-plan.md`
//! §11.8.2): a bounded replay linked cleanly and produced byte-identical
//! output, so there was no symptom left to attribute. What the episode DID
//! expose is that nothing in the suite would have caught a recurrence — the
//! failure surfaced in a Phase-6 manual replay, not in CI. This cell is that
//! missing guard.
//!
//! It is an ordinary coverage cell, not a repro: it carries no `// defect:`
//! line, because nothing attributable was ever reproduced.
//!
//! Shape (the S118 P6 replay, mechanised): a fresh scratch copy of
//! `exemplar/*.cl` per mode so neither child can hit a cache the other
//! populated, `--run` the stdio entry in one, `--link` it in the other and exec
//! the produced executable, then compare. Both must exit 0 and their stdout
//! must be byte-identical — a REPL/`--run`/`--link` divergence is always a
//! defect (root `CLAUDE.md`).
//!
//! Cost is two full cold compiles of the showcase (~3s each). That is the
//! price of an application-scale link gate; the `--link` path links five
//! workspace members it has no Cargo dependency edge to, and only a real link
//! exercises them (`tests/CLAUDE.md` §"`--link` / platform prerequisites" — the
//! nextest setup script builds them before any test runs).
//!
//! The exemplar is one of the two sanctioned stdlib touchpoints (root
//! `CLAUDE.md` §"Stdlib separation"): the showcase depends on `stdlib/` by
//! design, so `CRANELISP_LIB` points at the workspace tree here.

use std::path::{Path, PathBuf};
use std::process::Command;

/// The stdio showcase entry: one-shot solve-and-print, terminating. (`main.cl`
/// is the WEB entry and serves until killed — not a parity subject.)
const ENTRY: &str = "user.cl";
/// The executable `--link` produces beside the source: the entry's stem.
const PRODUCED: &str = "user";

fn workspace_root() -> PathBuf {
    // read-only on project_root
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

/// A scratch project holding a copy of every top-level `exemplar/*.cl` source.
/// Sub-libraries resolve through `CRANELISP_LIB` exactly as they do for the
/// showcase. The durable test never writes into or executes from `exemplar/`.
fn exemplar_scratch() -> tempfile::TempDir {
    let td = tempfile::tempdir().expect("tempdir");
    for entry in std::fs::read_dir(workspace_root().join("exemplar")).expect("read exemplar") {
        let path = entry.expect("dir entry").path();
        if path.extension().and_then(|x| x.to_str()) == Some("cl") {
            std::fs::copy(&path, td.path().join(path.file_name().unwrap()))
                .expect("copy exemplar source");
        }
    }
    td
}

/// `cranelisp` (or the produced executable) in `dir`, with the showcase's
/// environment and nothing else inherited. `PATH` is passed because `--link`
/// shells out to `cc`.
fn spawn(program: &Path, dir: &Path, args: &[&str]) -> std::process::Output {
    let root = workspace_root();
    Command::new(program)
        .current_dir(dir)
        .args(args)
        .env_clear()
        .env("PATH", std::env::var("PATH").unwrap_or_default())
        .env("CRANELISP_LIB", root.join("stdlib"))
        .env("CRANELISP_PLATFORM_PATH", root.join("target/debug"))
        .output()
        .unwrap_or_else(|e| panic!("spawn {}: {e}", program.display()))
}

// spec: spec/10-io.md §10.6.3 — Mode-Output Equivalence, at application scale:
// the linked executable's stdout must match `--run`'s exactly.
#[test]
fn exemplar_linked_binary_matches_run_output_byte_for_byte() {
    let compiler = workspace_root().join("target/debug/cranelisp");
    assert!(
        compiler.exists(),
        "compiler binary not built at {}: build before running this gate",
        compiler.display()
    );

    // --run, in its own cold tree.
    let run_tree = exemplar_scratch();
    let run = spawn(&compiler, run_tree.path(), &["--run", ENTRY]);
    assert!(
        run.status.success(),
        "`--run {ENTRY}` on a fresh exemplar copy MUST succeed; exit={:?}\nstderr:\n{}",
        run.status.code(),
        String::from_utf8_lossy(&run.stderr)
    );
    assert!(
        !run.stdout.is_empty(),
        "`--run {ENTRY}` produced no stdout — the parity comparison below would \
         be vacuous"
    );

    // --link, in a second cold tree, then exec what it produced.
    let link_tree = exemplar_scratch();
    let link = spawn(&compiler, link_tree.path(), &["--link", ENTRY]);
    assert!(
        link.status.success(),
        "`--link {ENTRY}` on a fresh exemplar copy MUST succeed (FIXME 0875's \
         symptom); exit={:?}\nstderr:\n{}",
        link.status.code(),
        String::from_utf8_lossy(&link.stderr)
    );
    let produced = link_tree.path().join(PRODUCED);
    assert!(
        produced.exists(),
        "`--link {ENTRY}` reported success but produced no `{PRODUCED}` \
         executable in {}",
        link_tree.path().display()
    );
    let linked = spawn(&produced, link_tree.path(), &[]);
    assert!(
        linked.status.success(),
        "the linked exemplar MUST run cleanly; exit={:?}\nstderr:\n{}",
        linked.status.code(),
        String::from_utf8_lossy(&linked.stderr)
    );

    assert_eq!(
        String::from_utf8_lossy(&linked.stdout),
        String::from_utf8_lossy(&run.stdout),
        "linked exemplar stdout MUST be byte-identical to `--run` stdout \
         ({} vs {} bytes) — a mode divergence is always a defect",
        linked.stdout.len(),
        run.stdout.len()
    );
}
