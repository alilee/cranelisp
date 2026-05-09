// public_api_relocations.rs — Sprint 66 Phase 5 Stage 1 (FIXME 0100).
//
// Authored failing-not-ignored at Phase-5 Stage-1 open per /qa Phase-5
// obligation. This is the structural conformance gate for the type-
// relocation FIXME (single-consumer types move from `cranelisp-types`
// into the consumer crate that owns them):
//   - `CheckResult`, `CheckError`, `FormCheckResult`, `CheckPass`,
//     `CheckState`, `TypeCheckEnv`, `ModuleCheckAccumulator`,
//     `ReplSnapshot` move into `cranelisp-typecheck` (FIXME 0100 Phase 1).
//   - `CompilationError`, `GotEvent`, `GotEventTag`, `GotProvenance`,
//     `GotObserver` move into `cranelisp-backend` (FIXME 0100 Phase 2).
//
// Implementation: subprocess-runs `cargo +nightly public-api --diff …`
// per crate against the committed `crates/{crate}/public-api.txt`
// baseline. Drift produces a non-zero exit + diff in stderr.
//
// At Phase-5 Stage 1 this test fails because:
//   (a) baselines for `cranelisp-primitives` + `cranelisp-intrinsics`
//       don't exist (Wave 2 scaffolds them);
//   (b) `cranelisp-types` baseline currently includes the to-be-relocated
//       types — those move out in Wave 2;
//   (c) `cranelisp-typecheck` + `cranelisp-backend` baselines don't yet
//       reflect the in-bound relocations.
//
// FIXME(/dev — every per-crate workstream that lands a facade-conformant
// change must regenerate the affected baseline per the triad pattern in
// `tests/CLAUDE.md §"Public-API enforcement"`).

#![allow(dead_code)]

use std::path::{Path, PathBuf};
use std::process::Command;

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

/// Crates whose public surface S66 governs by binding facade.
/// `cranelisp-runtime` is included transit-state; it retires by S66 close.
fn crates_with_baselines() -> &'static [&'static str] {
    &[
        "cranelisp-types",
        "cranelisp-frontend",
        "cranelisp-typecheck",
        "cranelisp-backend",
        "cranelisp-runtime",
        "cranelisp-platform",
        // Live in S66 per /arch Option A — D43 binds:
        "cranelisp-primitives",
        "cranelisp-intrinsics",
    ]
}

// spec: tests/CLAUDE.md §"Public-API enforcement" (structural test, no
// language-spec section — this is a conformance gate for facade adoption).
// FIXME(/dev — multi: every crate with a facade-conformant landing in
// S66 must commit its `public-api.txt` baseline per /qa slice §1.1).
#[test]
fn public_api_check_runs_against_all_eight_crates() {
    // Skip if cargo-public-api is not installed; emit instructions.
    let probe = Command::new("cargo")
        .args(["+nightly", "public-api", "--version"])
        .output();
    let probe_ok = matches!(&probe, Ok(o) if o.status.success());
    if !probe_ok {
        panic!(
            "cargo +nightly public-api unavailable. Install per tests/CLAUDE.md \
             §\"Public-API enforcement\":\n\
             rustup toolchain install nightly\n\
             cargo +nightly install cargo-public-api"
        );
    }

    let root = workspace_root();
    let mut missing_baseline: Vec<&str> = Vec::new();
    let mut missing_crate: Vec<&str> = Vec::new();
    let mut drifted: Vec<(String, String)> = Vec::new();

    for crate_name in crates_with_baselines() {
        let crate_dir = root.join("crates").join(crate_name);
        if !crate_dir.exists() {
            missing_crate.push(crate_name);
            continue;
        }
        let baseline = crate_dir.join("public-api.txt");
        if !baseline.exists() {
            missing_baseline.push(crate_name);
            continue;
        }
        // Generate current public-api and diff against baseline.
        let cur = Command::new("cargo")
            .args([
                "+nightly",
                "public-api",
                "--simplified",
                "--manifest-path",
            ])
            .arg(crate_dir.join("Cargo.toml"))
            .output();
        let cur = match cur {
            Ok(o) if o.status.success() => o.stdout,
            Ok(o) => {
                drifted.push((
                    crate_name.to_string(),
                    format!(
                        "cargo public-api failed: {}\nstderr:\n{}",
                        o.status,
                        String::from_utf8_lossy(&o.stderr)
                    ),
                ));
                continue;
            }
            Err(e) => {
                drifted.push((crate_name.to_string(), format!("spawn: {e}")));
                continue;
            }
        };
        let actual = String::from_utf8_lossy(&cur).into_owned();
        let expected = std::fs::read_to_string(&baseline)
            .unwrap_or_else(|e| panic!("read {}: {e}", baseline.display()));
        if normalise(&actual) != normalise(&expected) {
            drifted.push((
                crate_name.to_string(),
                diff_summary(&expected, &actual),
            ));
        }
    }

    if !missing_crate.is_empty() || !missing_baseline.is_empty() || !drifted.is_empty() {
        let mut msg = String::from("public-api conformance check failed:\n");
        if !missing_crate.is_empty() {
            msg.push_str(&format!(
                "  missing crates (D43 not yet executed): {:?}\n",
                missing_crate
            ));
        }
        if !missing_baseline.is_empty() {
            msg.push_str(&format!(
                "  missing baselines (run `cargo +nightly public-api > crates/{{crate}}/public-api.txt`): {:?}\n",
                missing_baseline
            ));
        }
        for (c, d) in &drifted {
            msg.push_str(&format!("  drift in {c}:\n{d}\n"));
        }
        panic!("{msg}");
    }
}

fn normalise(s: &str) -> String {
    s.lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| l.trim_end())
        .collect::<Vec<_>>()
        .join("\n")
}

fn diff_summary(expected: &str, actual: &str) -> String {
    let exp: std::collections::HashSet<&str> = expected.lines().collect();
    let act: std::collections::HashSet<&str> = actual.lines().collect();
    let added: Vec<&&str> = act.difference(&exp).collect();
    let removed: Vec<&&str> = exp.difference(&act).collect();
    let mut out = String::new();
    let cap = 20usize;
    if !added.is_empty() {
        out.push_str(&format!("    +{} additions (showing up to {}):\n", added.len(), cap));
        for s in added.iter().take(cap) {
            out.push_str(&format!("      + {s}\n"));
        }
    }
    if !removed.is_empty() {
        out.push_str(&format!("    -{} removals (showing up to {}):\n", removed.len(), cap));
        for s in removed.iter().take(cap) {
            out.push_str(&format!("      - {s}\n"));
        }
    }
    out
}

// Suppress unused warning when test is disabled.
#[allow(dead_code)]
fn _path_unused(_: &Path) {}
