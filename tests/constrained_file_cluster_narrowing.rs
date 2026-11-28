mod helpers;
use helpers::e2e::{Cranelisp, PreludeVariant};

fn file_cluster_float_repl(int_use: bool) {
    let source = format!(
        "(defn g [:a x] (+ x x))\n{}",
        if int_use {
            "(defn int-use [] (g 3))\n"
        } else {
            ""
        }
    );
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::TestStandard)
        .user(&source)
        .cli_flag("--no-cache")
        .stdin("(g 1.5)\n")
        .output()
        .assert_ok();
    assert!(
        out.stdout.contains(":primitives/Float 3.0"),
        "file-checked constrained g accepts Float and gives 3.0 (Int use={int_use}):\n{}\n{}",
        out.stdout,
        out.stderr
    );
}

fn file_cluster_float_run(int_use: bool) {
    let source = format!("(defn g [:a x] (+ x x))\n{}(defn main [] (primitives/pure (if (primitives/eq-f64 (g 1.5) 3.0) 0 1)))\n",
        if int_use { "(defn int-use [] (g 3))\n" } else { "" });
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::TestStandard)
        .file("main.cl", &source)
        .cli_flag("--no-cache")
        .run("main.cl")
        .output();
    assert_eq!(
        out.status.code(),
        Some(0),
        "--run must accept g at Float and observe exactly 3.0 (Int use={int_use}):\n{}\n{}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/03-types.md §3.3.2; spec/05-definitions.md §5.13.1 — T-NARROW, a caller cannot narrow the file's constrained scheme.
// defect: class=wrong-reject locus=crates/cranelisp-typecheck found=S125 owner=/dev — provisional: cluster generalisation
#[test]
fn s125_t_narrow_file_int_use_preserves_float_repl() {
    file_cluster_float_repl(true);
}

// spec: spec/03-types.md §3.3.2; spec/05-definitions.md §5.13.1 — T-NARROW without the Int caller.
#[test]
fn s125_t_narrow_file_without_int_use_float_repl_control() {
    file_cluster_float_repl(false);
}

// spec: spec/03-types.md §3.3.2; spec/05-definitions.md §5.13.1 — T-NARROW also applies under --run.
// defect: class=wrong-reject locus=crates/cranelisp-typecheck found=S125 owner=/dev — provisional: cluster generalisation
#[test]
fn s125_t_narrow_file_int_use_preserves_float_run() {
    file_cluster_float_run(true);
}

// spec: spec/03-types.md §3.3.2; spec/05-definitions.md §5.13.1 — T-NARROW --run without the Int caller.
#[test]
fn s125_t_narrow_file_without_int_use_float_run_control() {
    file_cluster_float_run(false);
}
