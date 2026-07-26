// Sprint 116 application-scale acceptance guard for the ownership-composition
// class. This intentionally copies the showcase sources into a scratch project;
// the durable compiler test never writes into or executes from exemplar/.
//
// WHY AN ABSOLUTE NUMBER LIVES HERE AT ALL (tests/CLAUDE.md §"Allocator balance
// is measured MARGINALLY" bans absolute thresholds for the prelude-loading
// class). The ban's premise is an ambient, program-independent compile-time
// residual (1143 allocations at S118 HEAD — FIXME 0889's macro-turn marshal
// boundary) that an absolute cell would be measuring instead of the behaviour
// it is named after. That premise is FALSE for a WARM cache-hit child, and
// `/qa` measured it so (`tests/plan/s118-test-plan.md` §11.3): a cache hit
// skips macro expansion entirely, so two independent warm controls report
// residual EXACTLY 0 (allocs=1 / deallocs=1). The 1143 term appears only in
// COLD / `--no-cache` children. The warm subject's residue is therefore pure
// runtime retention, and the absolute bound below is an honest instrument —
// but only for as long as that premise holds, which is why the second cell in
// this file executes the premise continuously instead of trusting this comment.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

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

fn workspace_root() -> PathBuf {
    // read-only on project_root
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

/// A scratch project holding a copy of every top-level `exemplar/*.cl` source.
/// Sub-libraries (`collections/`, `num/`, `text/`, …) resolve through
/// `CRANELISP_LIB` — the stdlib tree — exactly as they do for the showcase.
fn exemplar_scratch() -> tempfile::TempDir {
    let td = tempfile::tempdir().expect("tempdir");
    for entry in std::fs::read_dir(workspace_root().join("exemplar")).expect("read exemplar") {
        let entry = entry.expect("dir entry");
        let path = entry.path();
        if path.extension().and_then(|x| x.to_str()) == Some("cl") {
            std::fs::copy(&path, td.path().join(path.file_name().unwrap()))
                .expect("copy exemplar source");
        }
    }
    td
}

/// Run `entry` in `dir` twice under the SAME environment — cold (populates the
/// module cache), then warm (the cache-hit child this file measures) — and
/// return the warm child's `[RC_STATS]` residual. Both runs must exit clean: a
/// failed child has no balance verdict to give.
fn warm_residue_of(dir: &Path, entry: &str) -> (i64, String) {
    let root = workspace_root();
    let run = || -> Output {
        Command::new(root.join("target/debug/cranelisp"))
            .current_dir(dir)
            .args(["--run", entry])
            .env("CRANELISP_LIB", root.join("stdlib"))
            .env("CRANELISP_PLATFORM_PATH", root.join("target/debug"))
            .env("CRANELISP_NO_LENIENT", "1")
            .env("CRANELISP_RC_STATS", "1")
            .output()
            .expect("run copied exemplar entry")
    };
    let cold = run();
    assert!(
        cold.status.success(),
        "cold compile/run of {entry} failed:\n{}",
        String::from_utf8_lossy(&cold.stderr)
    );
    let warm = run();
    let stderr = String::from_utf8_lossy(&warm.stderr).into_owned();
    assert!(
        warm.status.success(),
        "warm run of {entry} failed:\n{stderr}"
    );
    (residue(&stderr), stderr)
}

// RED — the warm serial Sudoku solve must be bounded by the independently
// measured composition residue (~1,312). The current ~12,431 retained objects
// are pure runtime retention (the warm ambient term is 0 — see the second cell
// and the header), and no partial fix can pass.
// spec: spec/12-runtime.md §12.3.1 — unreachable heap ownership is released;
// application-scale quantitative acceptance for the transitive-discharge class.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/fn_compiler.rs::protect_return_value found=S115 owner=/dev
//   — FIXME 0917: an unbalanced `NULLARY_TAG_THRESHOLD`-guarded protect inc at
//   the match-result return seam. A nullary `ConstrADT` arm classifies non-Fresh
//   in the `value_provenance`/`is_fresh_construction` join, so ONE `None` arm —
//   never taken at runtime — flips the whole match result to protect-eligible,
//   and nothing balances the inc: the returned tree strands at rc=1 per
//   iteration. That is the `eliminate` shape the backtracking solver runs per
//   cell per pass, and it accounts for 100% of the 12,431
//   (`tests/plan/s118-test-plan.md` §11.8.1; probe-backed subject/control
//   4406/4 vs 4406/4406, repro pair `tests/nullary_arm_beside_boxed_arm_0917.rs`).
//   Two superseded attributions, kept so neither is re-tried: the 0810/0840 pair
//   this cell was born under (S118 W2b+W3 landed those fixes and the residue
//   survived them), and the §11.3 lead pointing at 0903's two censused families
//   via `grid/Grid.cells` — FALSIFIED by `/port`'s direct experiment (the
//   exemplar never calls that accessor) and by the 0917 reduction. This cell is
//   NOT 0903's acceptance witness; it flips when 0917's fix lands.
#[test]
fn sudoku_warm_serial_solve_residue_at_most_1400() {
    let td = exemplar_scratch();
    let (retained, stderr) = warm_residue_of(td.path(), "solver.cl");
    assert!(
        retained <= 1_400,
        "warm serial Sudoku residue MUST be <=1400 after complete 0810/transitive \
         discharge; got {retained}. A value materially above ~2000 is a partial fix.\n{stderr}"
    );
}

// The PREMISE LEG of the cell above, and the reason its absolute bound means
// anything (`tests/plan/s118-test-plan.md` §11.3, `/qa`'s disposition of FIXME
// 0890). The control is the same scratch project, the same environment, the
// same cold-then-warm sequence, and the same instrument — it differs from the
// subject in exactly ONE thing: the entry program does no solve work, while
// still importing `solver` so the exemplar modules' own compilation is present
// in both children.
//
// Its warm residual is EXACTLY 0 (allocs=1 / deallocs=1) at S118 HEAD. That is
// the fact that makes the subject's 12,431 attributable to runtime retention
// rather than to an ambient compile-time term: if this cell ever goes nonzero,
// the ambient term has returned and the subject cell's bound has silently
// changed meaning — re-derive it (marginally) before reading the subject again.
// Exact, not a threshold: any movement must flip this cell and force the record
// to be updated, which is the whole point. This is the marginal-accounting
// principle of tests/CLAUDE.md carried onto the cold/warm axis §11.3 flagged:
// the control/subject pair here differs by the workload, and the quantity
// asserted is the control side of it.
// spec: spec/12-runtime.md §12.3.1 — unreachable heap ownership is released
#[test]
fn warm_cache_hit_control_carries_no_ambient_residual() {
    let td = exemplar_scratch();
    std::fs::write(
        td.path().join("warm_control.cl"),
        // Same platform + prelude surface as solver.cl, same module graph
        // (importing `solve` compiles the whole exemplar tree), zero solve work.
        "(platform stdio)\n\
         (import [primitives [Pure]])\n\
         (import [solver [solve]])\n\
         (defn main [] (Pure 0))\n",
    )
    .expect("write warm control entry");
    let (retained, stderr) = warm_residue_of(td.path(), "warm_control.cl");
    assert_eq!(
        retained, 0,
        "a WARM cache-hit child that does no solve work MUST retain nothing \
         (measured 0 — allocs=1/deallocs=1 — at S118 HEAD, tests/plan/\
         s118-test-plan.md §11.3); got {retained}. Nonzero means the ambient \
         compile-time term (FIXME 0889's 1143, or a new one) is back in the WARM \
         path, so `sudoku_warm_serial_solve_residue_at_most_1400` is no longer \
         measuring runtime retention and its bound must be re-derived.\n{stderr}"
    );
}
