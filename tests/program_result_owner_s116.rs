// Sprint 116 typed-context exit matrix. Successful owning results are observed
// first and then released exactly once through the same concrete drop glue.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

fn counts(stderr: &str) -> (i64, i64) {
    let line = stderr
        .lines()
        .rev()
        .find(|line| line.contains("[RC_STATS]"))
        .unwrap_or_else(|| panic!("missing RC_STATS line:\n{stderr}"));
    let field = |key: &str| {
        line.split_whitespace()
            .find_map(|word| word.strip_prefix(key)?.parse().ok())
            .unwrap_or_else(|| panic!("missing {key} in {line}"))
    };
    (field("allocs="), field("deallocs="))
}

const NESTED_MAIN: &str = "(deftype Leaf [:String text])\n\
     (deftype Branch [:(Vec Leaf) leaves])\n\
     (defn main [] (Pure (Branch [(Leaf \"seen-before-release\")])))\n";

// RED — run observes a non-Int `Pure` payload as exit 0, then releases the
// nested ADT→Vec→ADT→String graph. Both analysis polarities are exact.
// spec: spec/10-io.md §10.1 and spec/12-runtime.md §12.3.1 — `Pure` transfers
// its payload to the program-result owner; non-Int conversion precedes release.
// defect: class=rc-miscount locus=src program-result typed-context exit — entry result is observed but never released (0745/R15) found=S114 owner=/dev
#[test]
fn run_nested_pure_payload_observed_then_released_both_toggles() {
    for off in [false, true] {
        let mut c = Cranelisp::new()
            .with_prelude(PreludeVariant::PrimitivesOnly)
            .user(NESTED_MAIN)
            .run("user.cl")
            .env("CRANELISP_RC_STATS", "1")
            .env("CRANELISP_NO_LENIENT", "1");
        if off {
            c = c.env("CRANELISP_NO_OWNERSHIP", "1");
        }
        let out = c.output();
        assert_eq!(
            out.status.code(),
            Some(0),
            "stdout:\n{}\nstderr:\n{}",
            out.stdout,
            out.stderr
        );
        let (a, d) = counts(&out.stderr);
        assert_eq!(
            a, d,
            "run result owner MUST release nested payload exactly once ({a}/{d})"
        );
    }
}

// RED — linked startup performs the same non-Int conversion and transitive
// release before process exit; this proves relocation, not link success alone.
// spec: spec/10-io.md §10.1 and spec/12-runtime.md §12.3.1.
// defect: class=rc-miscount locus=cranelisp-exe-bundle linked startup result owner — linked successful result lacks type-directed final release found=S116 owner=/dev
#[test]
fn linked_nested_pure_payload_converts_then_releases() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .user(NESTED_MAIN)
        .link_then_run("user.cl")
        .env("CRANELISP_RC_STATS", "1")
        .env("CRANELISP_NO_LENIENT", "1")
        .output();
    assert_eq!(
        out.status.code(),
        Some(0),
        "stdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
    let (a, d) = counts(&out.stderr);
    assert_eq!(
        a, d,
        "linked result owner MUST release nested payload ({a}/{d})"
    );
}

// RED — REPL rendering must finish while the owning value is live, after which
// the turn releases it before the next prompt/process exit.
// spec: repl/spec.md §5.1 and spec/12-runtime.md §12.3.1 — value feedback is
// useful and complete before exact-once release at the typed exit.
// defect: class=rc-miscount locus=src REPL result owner — displayed owning expression result leaks after formatting found=S116 owner=/dev
#[test]
fn repl_nested_heap_value_displays_before_exact_release() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .repl()
        .stdin(
            "(deftype Leaf [:String text])\n\
             (deftype Branch [:(Vec Leaf) leaves])\n\
             (Branch [(Leaf \"seen-before-release\")])\n",
        )
        .env("CRANELISP_RC_STATS", "1")
        .env("CRANELISP_NO_LENIENT", "1")
        .output();
    assert!(
        out.stdout.contains("seen-before-release"),
        "value must be observed before release:\n{}",
        out.stdout
    );
    let (a, d) = counts(&out.stderr);
    assert_eq!(
        a, d,
        "REPL result owner MUST release after display ({a}/{d})"
    );
}

// GREEN control — scalar results require no glue and retain ordinary exit-code
// conversion in both run and link modes.
// spec: spec/10-io.md §10.1 — `Pure Int` becomes the process exit code.
#[test]
fn scalar_pure_result_exit_conversion_control_green() {
    let src = "(defn main [] (Pure 7))\n";
    for linked in [false, true] {
        let c = Cranelisp::new()
            .with_prelude(PreludeVariant::PrimitivesOnly)
            .user(src);
        let out = if linked {
            c.link_then_run("user.cl").output()
        } else {
            c.run("user.cl").output()
        };
        assert_eq!(
            out.status.code(),
            Some(7),
            "stdout:\n{}\nstderr:\n{}",
            out.stdout,
            out.stderr
        );
    }
}
