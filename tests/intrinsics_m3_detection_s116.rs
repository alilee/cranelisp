// Sprint 116 M3 production compiler-child wiring. The private plant protocol is
// closed and exact; tests never call allocator internals or counter setters.

use std::process::{Command, Output};

fn child(fault: Option<&str>) -> Output {
    let td = tempfile::tempdir().expect("tempdir");
    let source = td.path().join("user.cl");
    std::fs::write(
        &source,
        "(import [primitives [Pure str-len sub-i64]])\n\
         (defn main [] (let [s \"owned-local\"] (Pure (sub-i64 (str-len s) 11))))\n",
    )
    .expect("write source");
    let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let binary = root.join("target/debug/cranelisp");
    let mut cmd = Command::new(binary);
    cmd.env_clear()
        .current_dir(td.path())
        .args(["--run", "user.cl", "--no-cache"])
        .env("CRANELISP_LIB", root.join("stdlib"))
        .env("CRANELISP_PLATFORM_PATH", root.join("target/debug"))
        .env("CRANELISP_ALLOC_PARITY", "1");
    if let Some(plant) = fault {
        cmd.env("CRANELISP_TEST_FAULTS", "s116-detection-proof-v1")
            .env("CRANELISP_TEST_FAULT", plant);
    }
    cmd.output().expect("run compiler child")
}

// RED — one suppressed production discharge reaches the real always-on
// counters, atexit report, then abnormal termination. Removing M3 must make this
// assertion fail rather than false-green.
// spec: design/intrinsics/diagnostic-modes.md §7.3 — M3 compiler-child
// counter→atexit→report→abort proof using the exact closed plant protocol.
// defect: class=detection-gap locus=cranelisp-intrinsics diagnostics production wiring — M3Leak plant/e2e atexit proof absent (0848 R-1) found=S115 owner=/dev
#[test]
fn m3_parity_catches_injected_imbalance() {
    let out = child(Some("M3Leak"));
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        !out.status.success(),
        "M3 leak child MUST abort non-zero; stderr:\n{stderr}"
    );
    assert!(
        stderr.contains("M3Leak")
            && stderr.contains("alloc")
            && stderr.contains("dealloc")
            && (stderr.contains("parity") || stderr.contains("imbalance")),
        "atexit report MUST name plant and alloc/dealloc imbalance; stderr:\n{stderr}"
    );
}

// GREEN control — parity enabled without a plant uses the same binary/program
// and exits normally with no test-fault or imbalance report.
// spec: design/intrinsics/diagnostic-modes.md §7.3 — clean M3 child control.
#[test]
fn m3_parity_clean_child_exits_normally_control() {
    let out = child(None);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        out.status.success(),
        "clean M3 child MUST succeed; stderr:\n{stderr}"
    );
    assert!(
        !stderr.contains("M3Leak") && !stderr.contains("imbalance"),
        "stderr:\n{stderr}"
    );
}
