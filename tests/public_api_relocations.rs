// Compares the seven library API baselines with the default-feature surface.
// The disposable-crate proof exercises the same generator and drift check.

use std::path::{Path, PathBuf};
use std::process::Command;

const MIN_PUBLIC_API_VERSION: (u64, u64) = (0, 52);

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

/// Library crates governed by the public-API baseline discipline.
fn crates_with_baselines() -> &'static [&'static str] {
    &[
        "cranelisp-types",
        "cranelisp-frontend",
        "cranelisp-typecheck",
        "cranelisp-backend",
        "cranelisp-platform",
        "cranelisp-primitives",
        "cranelisp-intrinsics",
    ]
}

// spec: tests/AGENTS.md §"Public-API enforcement" — repository surface drift.
#[test]
fn public_api_check_runs_against_all_seven_crates() {
    let probe = Command::new("cargo")
        .args(["+nightly", "public-api", "--version"])
        .output();
    let probe = match probe {
        Ok(output) if output.status.success() => output,
        _ => panic!(
            "cargo +nightly public-api unavailable. Install per tests/AGENTS.md \
             §\"Public-API enforcement\":\n\
             rustup toolchain install nightly\n\
             cargo +nightly install cargo-public-api"
        ),
    };
    let version = String::from_utf8_lossy(&probe.stdout);
    require_supported_public_api_version(&version).unwrap_or_else(|reason| {
        panic!(
            "unsupported cargo-public-api for committed baselines: {reason}\n\
             Install version 0.52 or newer per tests/AGENTS.md \
             §\"Public-API enforcement\""
        )
    });

    // read-only on project_root; cargo writes only regenerable build artifacts.
    check_public_api(&workspace_root(), crates_with_baselines());
}

fn check_public_api(root: &Path, crate_names: &[&str]) {
    let mut missing_baseline: Vec<&str> = Vec::new();
    let mut missing_crate: Vec<&str> = Vec::new();
    let mut drifted: Vec<(String, String)> = Vec::new();

    for crate_name in crate_names {
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
        let actual = match generate_public_api(root, crate_name) {
            Ok(actual) => actual,
            Err(error) => {
                drifted.push((crate_name.to_string(), error));
                continue;
            }
        };
        let expected = std::fs::read_to_string(&baseline)
            .unwrap_or_else(|e| panic!("read {}: {e}", baseline.display()));
        if normalise(&actual) != normalise(&expected) {
            drifted.push((crate_name.to_string(), diff_summary(&expected, &actual)));
        }
    }

    if !missing_crate.is_empty() || !missing_baseline.is_empty() || !drifted.is_empty() {
        let mut msg = String::from("public-api conformance check failed:\n");
        if !missing_crate.is_empty() {
            msg.push_str(&format!("  missing crates: {:?}\n", missing_crate));
        }
        if !missing_baseline.is_empty() {
            msg.push_str(&format!(
                "  missing baselines (run `cargo +nightly public-api -s --omit auto-derived-impls --omit auto-trait-impls -p <crate> > crates/<crate>/public-api.txt`): {:?}\n",
                missing_baseline
            ));
        }
        for (c, d) in &drifted {
            msg.push_str(&format!("  drift in {c}:\n{d}\n"));
        }
        panic!("{msg}");
    }
}

// Keep these flags identical to the baseline command in tests/AGENTS.md.
fn generate_public_api(root: &Path, crate_name: &str) -> Result<String, String> {
    let output = Command::new("cargo")
        .current_dir(root)
        .args([
            "+nightly",
            "public-api",
            "--simplified",
            "--omit",
            "auto-derived-impls",
            "--omit",
            "auto-trait-impls",
            "-p",
            crate_name,
        ])
        .output()
        .map_err(|error| format!("spawn: {error}"))?;
    if !output.status.success() {
        return Err(format!(
            "cargo public-api failed: {}\nstderr:\n{}",
            output.status,
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    Ok(String::from_utf8_lossy(&output.stdout).into_owned())
}

// spec: tests/AGENTS.md §"Public-API enforcement" — generated auto-traits
// are omitted; a public-item change still fails the executing drift guard.
#[test]
fn public_api_detection_proof_catches_public_item_and_accepts_clean_surface() {
    let fixture = tempfile::tempdir().expect("private API proof workspace");
    let root = fixture.path();
    let crate_dir = root.join("crates/api-proof");
    std::fs::create_dir_all(crate_dir.join("src")).unwrap();
    std::fs::write(
        root.join("Cargo.toml"),
        "[workspace]\nmembers = [\"crates/api-proof\"]\nresolver = \"2\"\n",
    )
    .unwrap();
    std::fs::write(
        crate_dir.join("Cargo.toml"),
        "[package]\nname = \"api-proof\"\nversion = \"0.1.0\"\nedition = \"2021\"\n",
    )
    .unwrap();
    let source = crate_dir.join("src/lib.rs");
    let clean = "pub struct Surface;\n";
    std::fs::write(&source, clean).unwrap();
    let baseline = generate_public_api(root, "api-proof").expect("generate proof baseline");
    assert!(baseline.contains("pub struct api_proof::Surface"));
    assert!(
        !baseline.contains("impl core::marker::Send for api_proof::Surface"),
        "new baseline format must omit generated auto-trait implementations\n{baseline}"
    );
    std::fs::write(crate_dir.join("public-api.txt"), baseline).unwrap();
    check_public_api(root, &["api-proof"]);

    std::fs::write(
        &source,
        format!("{clean}pub fn planted_public_item() {{}}\n"),
    )
    .unwrap();
    // catch_unwind keeps the expected failure inside the proof while the panic
    // hook emits the guard's real diagnostic to stderr.
    let failure = std::panic::catch_unwind(|| check_public_api(root, &["api-proof"]))
        .expect_err("guard must reject the planted public function");
    let diagnostic = failure.downcast_ref::<String>().expect("guard diagnostic");
    assert!(diagnostic.contains("public-api conformance check failed:"));
    assert!(diagnostic.contains("drift in api-proof:"));
    assert!(diagnostic.contains("+1 additions"));
    assert!(diagnostic.contains("+ pub fn api_proof::planted_public_item()"));
    assert!(!diagnostic.contains("cargo public-api failed"));

    std::fs::write(&source, clean).unwrap();
    check_public_api(root, &["api-proof"]);
}

fn require_supported_public_api_version(output: &str) -> Result<(), String> {
    let version = output
        .split_whitespace()
        .nth(1)
        .ok_or_else(|| format!("could not parse version output {output:?}"))?;
    let mut components = version.split('.');
    let major = components
        .next()
        .and_then(|part| part.parse::<u64>().ok())
        .ok_or_else(|| format!("could not parse version output {output:?}"))?;
    let minor = components
        .next()
        .and_then(|part| part.parse::<u64>().ok())
        .ok_or_else(|| format!("could not parse version output {output:?}"))?;

    if (major, minor) < MIN_PUBLIC_API_VERSION {
        return Err(format!(
            "found {major}.{minor}; require >= {}.{}",
            MIN_PUBLIC_API_VERSION.0, MIN_PUBLIC_API_VERSION.1
        ));
    }
    Ok(())
}

// spec: tests/AGENTS.md §"Public-API enforcement" — the committed format
// changed at cargo-public-api 0.52 and an older generator must be rejected.
#[test]
fn public_api_version_floor_rejects_pre_052_generator() {
    let error = require_supported_public_api_version("cargo-public-api 0.51.0")
        .expect_err("0.51 would generate parameter-name churn");
    assert!(error.contains("require >= 0.52"));
}

// spec: tests/AGENTS.md §"Public-API enforcement" — the floor admits the
// baseline-producing version and later compatible generators.
#[test]
fn public_api_version_floor_accepts_052_and_newer_generators() {
    for output in [
        "cargo-public-api 0.52.0",
        "cargo-public-api 0.53.1",
        "cargo-public-api 1.0.0",
    ] {
        require_supported_public_api_version(output).expect("supported generator");
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
        out.push_str(&format!(
            "    +{} additions (showing up to {}):\n",
            added.len(),
            cap
        ));
        for s in added.iter().take(cap) {
            out.push_str(&format!("      + {s}\n"));
        }
    }
    if !removed.is_empty() {
        out.push_str(&format!(
            "    -{} removals (showing up to {}):\n",
            removed.len(),
            cap
        ));
        for s in removed.iter().take(cap) {
            out.push_str(&format!("      - {s}\n"));
        }
    }
    out
}
