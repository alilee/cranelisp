// Sprint 116 transitive-discharge cells not represented by the fixed-depth
// 0760 repro: a recursive type must compile finitely and release finite values.
//
// FIXED — S118 W3 slice S1, `c6234398`. The cell is GREEN and is now a
// regression guard. The fixed-depth fallback it names is gone entirely
// (`MAX_DROP_GLUE_DEPTH` and `FnCompiler::drop_glue_depth` deleted, grep-zero
// fenced by `drop_glue_legacy_emitter_fence.rs`); the canonical registry in
// `crates/cranelisp-backend/src/drop_glue.rs` carries no cutoff and satisfies
// the declare-before-compiling-body requirement by construction, which is what
// makes the recursive definition terminate.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

fn balance(src: &str) -> (i64, i64, String) {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .env("CRANELISP_RC_STATS", "1")
        .env("CRANELISP_NO_LENIENT", "1")
        .user(src)
        .run("user.cl")
        .output();
    assert_eq!(
        out.status.code(),
        Some(0),
        "stdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
    let line = out
        .stderr
        .lines()
        .rev()
        .find(|l| l.contains("[RC_STATS]"))
        .unwrap_or_else(|| panic!("missing RC_STATS:\n{}", out.stderr));
    let field = |key: &str| -> i64 {
        line.split_whitespace()
            .find_map(|p| p.strip_prefix(key)?.parse().ok())
            .unwrap_or_else(|| panic!("missing {key}: {line}"))
    };
    (field("allocs="), field("deallocs="), out.stderr)
}

const RECURSIVE: &str = "(deftype List Nil (Cons [:String head :List tail]))\n\
     (defn build [n xs] (if (eq-i64 n 0) xs (build (sub-i64 n 1) (Cons \"x\" xs))))\n\
     (defn main [] (let [empty (build 0 Nil) one (build 1 Nil) many (build 9 Nil)] (Pure 0)))\n";

// Named/per-concrete glue generation must terminate on the recursive definition,
// while runtime recursion follows and releases each finite chain.
// spec: spec/12-runtime.md §12.3.1 — all unreachable transitive heap ownership
// is released, including finite values of recursive types.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/rc_emission.rs::MAX_DROP_GLUE_DEPTH — the fixed-depth fallback in the backend's recursive type-directed glue generation stranded recursive payloads; the replacement had to declare before compiling the body (read `drop_glue.rs`'s registry today) found=S116 fixed=S118/c6234398 owner=/dev
#[test]
fn finite_recursive_values_zero_one_many_terminate_and_balance() {
    let (allocs, deallocs, stderr) = balance(RECURSIVE);
    assert_eq!(
        allocs, deallocs,
        "recursive finite chains MUST balance; {allocs}/{deallocs}\n{stderr}"
    );
}
