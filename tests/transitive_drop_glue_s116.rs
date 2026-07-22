// Sprint 116 transitive-discharge cells not represented by the fixed-depth
// 0760 repro: a recursive type must compile finitely and release finite values.

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

// RED — named/per-concrete glue generation must terminate on the recursive
// definition, while runtime recursion follows and releases each finite chain.
// spec: spec/12-runtime.md §12.3.1 — all unreachable transitive heap ownership
// is released, including finite values of recursive types.
// defect: class=rc-miscount locus=backend recursive type-directed drop-glue generation — fixed-depth fallback strands recursive payloads; replacement must declare before compiling body found=S116 owner=/dev
#[test]
fn finite_recursive_values_zero_one_many_terminate_and_balance() {
    let (allocs, deallocs, stderr) = balance(RECURSIVE);
    assert_eq!(
        allocs, deallocs,
        "recursive finite chains MUST balance; {allocs}/{deallocs}\n{stderr}"
    );
}
