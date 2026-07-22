// Sprint 116 application-scale acceptance guard for the ownership-composition
// class. This intentionally copies the showcase sources into a scratch project;
// the durable compiler test never writes into or executes from exemplar/.

use std::process::Command;

fn residue(stderr: &str) -> i64 {
    let line = stderr
        .lines()
        .rev()
        .find(|line| line.contains("[RC_STATS]"))
        .unwrap_or_else(|| panic!("missing RC_STATS:\n{stderr}"));
    let field = |key: &str| -> i64 {
        line.split_whitespace()
            .find_map(|word| word.strip_prefix(key)?.parse().ok())
            .unwrap_or_else(|| panic!("missing {key} in {line}"))
    };
    field("allocs=") - field("deallocs=")
}

// RED — after the 0810 wrapper leak is fixed, the warm serial Sudoku solve is
// bounded by the independently measured composition residue (~1,312). A partial
// fix leaving the current ~11,820 objects cannot pass.
// spec: spec/12-runtime.md §12.3.1 — unreachable heap ownership is released;
// application-scale quantitative acceptance for the transitive-discharge class.
// defect: class=rc-miscount locus=backend owned match temporary + nested TCO composition — warm Sudoku solve retains materially above bounded residual (FIXME 0840) found=S115 owner=/dev
#[test]
fn sudoku_warm_serial_solve_residue_at_most_1400() {
    let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let td = tempfile::tempdir().expect("tempdir");
    for entry in std::fs::read_dir(root.join("exemplar")).expect("read exemplar") {
        let entry = entry.expect("dir entry");
        let path = entry.path();
        if path.extension().and_then(|x| x.to_str()) == Some("cl") {
            std::fs::copy(&path, td.path().join(path.file_name().unwrap()))
                .expect("copy exemplar source");
        }
    }
    let run = || {
        Command::new(root.join("target/debug/cranelisp"))
            .current_dir(td.path())
            .args(["--run", "solver.cl"])
            .env("CRANELISP_LIB", root.join("stdlib"))
            .env("CRANELISP_PLATFORM_PATH", root.join("target/debug"))
            .env("CRANELISP_NO_LENIENT", "1")
            .env("CRANELISP_RC_STATS", "1")
            .output()
            .expect("run copied solver")
    };
    let cold = run();
    assert!(
        cold.status.success(),
        "cold compile/run failed:\n{}",
        String::from_utf8_lossy(&cold.stderr)
    );
    let warm = run();
    let stderr = String::from_utf8_lossy(&warm.stderr);
    assert!(warm.status.success(), "warm run failed:\n{stderr}");
    let retained = residue(&stderr);
    assert!(
        retained <= 1_400,
        "warm serial Sudoku residue MUST be <=1400 after complete 0810/transitive \
         discharge; got {retained}. A value materially above ~2000 is a partial fix.\n{stderr}"
    );
}
