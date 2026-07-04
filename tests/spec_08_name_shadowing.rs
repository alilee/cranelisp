// spec_08_name_shadowing.rs — §8.6.4 name-shadowing matrix (S102, FIXME 0514).
//
// The final, no-exception ruling (user, 2026-07-04; scribed `a953de0`):
//   It is ALWAYS a compile-time error to redefine or shadow a name in scope
//   via `import` (private), `export` (public), OR the implicit prelude — no
//   exceptions, order-independent, all import shapes, all visibilities, and
//   UNIFORM across REPL / `--run` / `--link`. The remedy is the
//   fully-qualified reference (§8.6.6). Legal (NOT shadowing): not loading the
//   prelude (empty/reduced/suppressed → name out of scope → define freely),
//   reuse-by-re-export (same terminal source dedups, §8.6.4/§8.4.0), and
//   lexical `let`/`fn`/`match` bindings (§8.6.3, layer 1).
//
// SIGNAL WIRING (current impl `e1fe4a8` state):
//   The rejection landed on the REPL (Additive) commit-gate ONLY, and covers
//   inner-table `import`/`export` only — NOT the batch (`--run`/`--link`,
//   Replace) path and NOT the implicit prelude (outer scope). Therefore:
//     * The REPL def-over-{import,export} negatives PASS today (green anchors
//       — the REPL leg is already correct).
//     * Every `--run`/`--link` negative, the mode-parity test, and every
//       def-over-PRELUDE negative FAIL today — that failure IS the signal of
//       FIXME 0514 (move the check to the shared typecheck two-scope seam and
//       add the prelude arm). Failing-not-ignored per
//       `memory/feedback_failing_not_ignored.md`; they flip GREEN when 0514
//       lands. Ledger: `tests/plan/ledger.md` §"Sprint 102 name-shadowing
//       matrix (FIXME 0514)".
//   The POSITIVE (legal) tests are GREEN today and MUST stay green under the
//   rule — they guard the escape hatches (FQ reference, not-loading, dedup,
//   lexical binding) the rule explicitly preserves.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, CrOutput, PreludeVariant};

// A prelude that re-exports primitives (so bare `Pure`/`vec-len`/`add-i64`
// resolve) and defines a sentinel prelude-provided function `gulp`.
const PRELUDE_GULP: &str = "\
(export [primitives [*]])
(defn gulp [x] (add-i64 x 1))
";

// A bare primitives re-export prelude (no sentinel), for the explicit
// import/export collision shapes (they contest a local module name, not a
// prelude name).
const PRELUDE_PRIMS: &str = "(export [primitives [*]])\n";

fn combined(out: &CrOutput) -> String {
    format!("stdout:\n{}\nstderr:\n{}", out.stdout, out.stderr)
}

/// A §8.6.4/§8.6.5 collision diagnostic is present (def-over-name-in-scope, or
/// a distinct-terminal poison). Substring set covers the landed REPL wording
/// ("conflicts with the explicit import/export") and the ambiguity wording.
fn has_collision_diagnostic(out: &CrOutput) -> bool {
    let c = combined(out).to_lowercase();
    c.contains("conflict") || c.contains("ambiguous")
}

/// Batch (`--run` / `--link`) rejection: the collision diagnostic is present
/// AND the shadowing definition did not run to its exit code (no effect).
fn assert_batch_rejected(out: &CrOutput, shadow_exit: i32) {
    assert!(
        has_collision_diagnostic(out),
        "expected a §8.6.4/§8.6.5 collision (conflict/ambiguous) diagnostic; {}",
        combined(out)
    );
    assert_ne!(
        out.status.code(),
        Some(shadow_exit),
        "the rejected definition MUST have no effect (must not run to exit {}); {}",
        shadow_exit,
        combined(out)
    );
}

/// REPL rejection: the collision diagnostic is present, the shadow value never
/// appears, and the in-scope binding remains the resolution.
fn assert_repl_rejected(out: &CrOutput, shadow_marker: &str) {
    assert!(
        has_collision_diagnostic(out),
        "expected a §8.6.4 collision diagnostic in the REPL; {}",
        combined(out)
    );
    assert!(
        !out.stdout.contains(shadow_marker),
        "the rejected definition MUST have no effect (found shadow marker '{}'); {}",
        shadow_marker,
        combined(out)
    );
}

// =============================================================================
// 1. NEGATIVE — def-over-explicit-import (specific shape)
// =============================================================================

// spec: spec/08-modules.md §8.6.4 — a `defn` over a specifically-imported name
// is a compile-time error at the REPL. GREEN anchor: the REPL commit-gate
// already rejects (the mode that is currently correct).
#[test]
fn def_over_import_repl_rejected() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file("util.cl", "(defn measure [v] (vec-len v))\n")
        .stdin(
            "(import [util [measure]])\n\
             (measure [1 2 3])\n\
             (defn measure [v] 99)\n\
             (measure [1 2 3])\n",
        )
        .output();
    assert_repl_rejected(&out, ":primitives/Int 99");
    // The import remains the binding before AND after the rejected def.
    assert_eq!(
        out.stdout.matches(":primitives/Int 3").count(),
        2,
        "the import must remain the binding across the rejected def; {}",
        combined(&out)
    );
}

// spec: spec/08-modules.md §8.6.4 — the SAME rejection MUST hold in `--run`.
// RED signal (FIXME 0514): batch Replace path accepts (def wins, exit 99).
#[test]
fn def_over_import_run_rejected() {
    let out = Cranelisp::new()
        .prelude(PRELUDE_PRIMS)
        .file("util.cl", "(defn measure [v] (vec-len v))\n")
        .file(
            "main.cl",
            "(import [util [measure]])\n\
             (defn measure [v] 99)\n\
             (defn main [] (Pure (measure [1 2 3])))\n",
        )
        .run("main.cl")
        .output();
    assert_batch_rejected(&out, 99);
}

// spec: spec/08-modules.md §8.6.4 — the SAME rejection MUST hold in `--link`.
// RED signal (FIXME 0514): batch Replace path accepts (def wins, exit 99).
#[test]
fn def_over_import_link_rejected() {
    let out = Cranelisp::new()
        .prelude(PRELUDE_PRIMS)
        .file("util.cl", "(defn measure [v] (vec-len v))\n")
        .file(
            "main.cl",
            "(import [util [measure]])\n\
             (defn measure [v] 99)\n\
             (defn main [] (Pure (measure [1 2 3])))\n",
        )
        .link_then_run("main.cl")
        .output();
    assert_batch_rejected(&out, 99);
}

// spec: spec/08-modules.md §8.6.4 — symmetric direction: an `import` that binds
// a bare name already bound by a module-local definition is ALSO the error
// (order-independent). RED signal (FIXME 0514): batch accepts (exit 99).
#[test]
fn import_over_def_run_rejected() {
    let out = Cranelisp::new()
        .prelude(PRELUDE_PRIMS)
        .file("util.cl", "(defn measure [v] (vec-len v))\n")
        .file(
            "main.cl",
            "(defn measure [v] 99)\n\
             (import [util [measure]])\n\
             (defn main [] (Pure (measure [1 2 3])))\n",
        )
        .run("main.cl")
        .output();
    assert_batch_rejected(&out, 99);
}

// =============================================================================
// 2. NEGATIVE — def-over-explicit-import (glob shape) — NO glob exemption
// =============================================================================

// spec: spec/08-modules.md §8.6.4 — a `defn` over a name a GLOB import would
// bring in is the SAME error (no glob-exemption). RED signal (FIXME 0514):
// batch accepts (exit 99).
#[test]
fn def_over_glob_import_run_rejected() {
    let out = Cranelisp::new()
        .prelude(PRELUDE_PRIMS)
        .file("util.cl", "(defn measure [v] (vec-len v))\n")
        .file(
            "main.cl",
            "(import [util [*]])\n\
             (defn measure [v] 99)\n\
             (defn main [] (Pure (measure [1 2 3])))\n",
        )
        .run("main.cl")
        .output();
    assert_batch_rejected(&out, 99);
}

// =============================================================================
// 3. NEGATIVE — def-over-export (§8.4.0 public brings into scope)
// =============================================================================

// spec: spec/08-modules.md §8.4.0/§8.6.4 — a `defn` over an EXPORTED (public,
// in-scope) name is the same error as over an imported one. GREEN anchor: the
// REPL commit-gate already rejects export-brought collisions.
#[test]
fn def_over_export_repl_rejected() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file("util.cl", "(defn measure [v] (vec-len v))\n")
        .stdin(
            "(export [util [measure]])\n\
             (defn measure [v] 99)\n\
             (measure [1 2 3])\n",
        )
        .output();
    assert_repl_rejected(&out, ":primitives/Int 99");
}

// spec: spec/08-modules.md §8.4.0/§8.6.4 — the SAME export-collision rejection
// MUST hold in `--run`. RED signal (FIXME 0514): batch accepts (exit 99).
#[test]
fn def_over_export_run_rejected() {
    let out = Cranelisp::new()
        .prelude(PRELUDE_PRIMS)
        .file("util.cl", "(defn measure [v] (vec-len v))\n")
        .file(
            "main.cl",
            "(export [util [measure]])\n\
             (defn measure [v] 99)\n\
             (defn main [] (Pure (measure [1 2 3])))\n",
        )
        .run("main.cl")
        .output();
    assert_batch_rejected(&out, 99);
}

// =============================================================================
// 4. NEGATIVE — def-over-PRELUDE-name (the no-exception case)
// =============================================================================

// spec: spec/08-modules.md §8.6.4/§8.8.1 — the prelude is just an implicit
// `(import [prelude [*]])`; a `defn` over a prelude-PROVIDED name is the same
// compile-time error. RED signal (FIXME 0514, prelude arm): today the local
// def silently wins over the prelude (outer scope not checked). REPL leg.
#[test]
fn def_over_prelude_repl_rejected() {
    let out = Cranelisp::new()
        .repl()
        .prelude(PRELUDE_GULP)
        .stdin(
            "(gulp 10)\n\
             (defn gulp [x] (add-i64 x 100))\n\
             (gulp 10)\n",
        )
        .output();
    assert_repl_rejected(&out, ":primitives/Int 110");
}

// spec: spec/08-modules.md §8.6.4/§8.8.1 — def-over-prelude in `--run`.
// RED signal (FIXME 0514, prelude arm): today the local def wins (exit 105).
#[test]
fn def_over_prelude_run_rejected() {
    let out = Cranelisp::new()
        .prelude(PRELUDE_GULP)
        .file(
            "main.cl",
            "(defn gulp [x] (add-i64 x 100))\n\
             (defn main [] (Pure (gulp 5)))\n",
        )
        .run("main.cl")
        .output();
    assert_batch_rejected(&out, 105);
}

// spec: spec/08-modules.md §8.6.4/§8.8.1 — def-over-prelude in `--link`.
// RED signal (FIXME 0514, prelude arm): today the local def wins (exit 105).
#[test]
fn def_over_prelude_link_rejected() {
    let out = Cranelisp::new()
        .prelude(PRELUDE_GULP)
        .file(
            "main.cl",
            "(defn gulp [x] (add-i64 x 100))\n\
             (defn main [] (Pure (gulp 5)))\n",
        )
        .link_then_run("main.cl")
        .output();
    assert_batch_rejected(&out, 105);
}

// =============================================================================
// 5. NEGATIVE — MODE-PARITY (the normative MUST: same rejection all 3 modes)
// =============================================================================

// spec: spec/08-modules.md §8.6.4 "Definition-Over-Import: Order-Independent,
// All Modes" — "[S102 — mode-parity test owed: /qa to author a test asserting
// the SAME rejection for one colliding binding set across REPL, --run, and
// --link]". ONE binding set (def-over-import), asserted rejected identically
// in all three modes. RED signal (FIXME 0514): the REPL leg rejects, but
// `--run`/`--link` accept — that divergence IS the defect this test pins.
#[test]
fn mode_parity_def_over_import_same_rejection_all_modes() {
    // REPL leg.
    let repl = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file("util.cl", "(defn measure [v] (vec-len v))\n")
        .stdin(
            "(import [util [measure]])\n\
             (defn measure [v] 99)\n\
             (measure [1 2 3])\n",
        )
        .output();
    assert!(
        has_collision_diagnostic(&repl),
        "REPL leg MUST reject the def-over-import; {}",
        combined(&repl)
    );

    // --run leg — MUST reject identically.
    let run = Cranelisp::new()
        .prelude(PRELUDE_PRIMS)
        .file("util.cl", "(defn measure [v] (vec-len v))\n")
        .file(
            "main.cl",
            "(import [util [measure]])\n\
             (defn measure [v] 99)\n\
             (defn main [] (Pure (measure [1 2 3])))\n",
        )
        .run("main.cl")
        .output();
    assert!(
        has_collision_diagnostic(&run),
        "--run leg MUST reject the def-over-import identically to REPL \
         (mode-parity §8.6.4 is normative); {}",
        combined(&run)
    );

    // --link leg — MUST reject identically.
    let link = Cranelisp::new()
        .prelude(PRELUDE_PRIMS)
        .file("util.cl", "(defn measure [v] (vec-len v))\n")
        .file(
            "main.cl",
            "(import [util [measure]])\n\
             (defn measure [v] 99)\n\
             (defn main [] (Pure (measure [1 2 3])))\n",
        )
        .link_then_run("main.cl")
        .output();
    assert!(
        has_collision_diagnostic(&link),
        "--link leg MUST reject the def-over-import identically to REPL \
         (mode-parity §8.6.4 is normative); {}",
        combined(&link)
    );
}

// =============================================================================
// 6. POSITIVE (legal) — the escape hatches the rule PRESERVES
// =============================================================================

// spec: spec/08-modules.md §8.6.6/§8.8.3 — the FQ reference reaches the
// shadowed prelude name: suppress the prelude, define your OWN `gulp`, and
// reach the prelude's `gulp` via `prelude/gulp`. GREEN today, stays green.
#[test]
fn fq_reference_reaches_shadowed_prelude_name() {
    Cranelisp::new()
        .prelude(PRELUDE_GULP)
        .file(
            "main.cl",
            "(import [prelude []])\n\
             (import [primitives [Pure add-i64]])\n\
             (defn gulp [x] (add-i64 x 100))\n\
             (defn main [] (Pure (prelude/gulp 5)))\n",
        )
        .run("main.cl")
        .output()
        .assert_exit(6); // prelude/gulp = (+1); (prelude/gulp 5) = 6
}

// spec: spec/08-modules.md §8.8.3 — "not loading" is legal (NOT shadowing): a
// suppressed prelude leaves the name out of scope, so a local def of that name
// compiles freely. GREEN today, stays green (the Optional-prelude escape).
#[test]
fn suppressed_prelude_allows_local_def_of_prelude_name() {
    Cranelisp::new()
        .prelude(PRELUDE_GULP)
        .file(
            "main.cl",
            "(import [prelude []])\n\
             (import [primitives [Pure add-i64]])\n\
             (defn gulp [x] (add-i64 x 100))\n\
             (defn main [] (Pure (gulp 5)))\n",
        )
        .run("main.cl")
        .output()
        .assert_exit(105); // local gulp = (+100); (gulp 5) = 105
}

// spec: spec/08-modules.md §8.8.3 — with NO prelude at all, a name that a
// prelude WOULD have provided is out of scope and free to define. GREEN today.
#[test]
fn no_prelude_allows_local_def_of_would_be_prelude_name() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(import [primitives [Pure add-i64]])\n\
             (defn gulp [x] (add-i64 x 100))\n\
             (defn main [] (Pure (gulp 5)))\n",
        )
        .run("main.cl")
        .output()
        .assert_exit(105);
}

// spec: spec/08-modules.md §8.4.0/§8.6.4 — reuse-by-re-export: an
// `(import [m [X]])` + `(export [m [X]])` for the same terminal DEDUPS (same
// terminal source), it does NOT collide. GREEN today, stays green.
#[test]
fn reuse_by_reexport_same_terminal_dedups() {
    Cranelisp::new()
        .prelude(PRELUDE_PRIMS)
        .file("libc.cl", "(defn helper [x] (add-i64 x 1))\n")
        .file(
            "main.cl",
            "(import [libc [helper]])\n\
             (export [libc [helper]])\n\
             (defn main [] (Pure (helper 41)))\n",
        )
        .run("main.cl")
        .output()
        .assert_exit(42);
}

// spec: spec/08-modules.md §8.6.3 — a lexical `let` binding of a
// prelude-provided name is layer-1 scoping, NOT a module-local redefinition;
// it is allowed. GREEN today, stays green.
#[test]
fn lexical_let_binding_of_prelude_name_allowed() {
    Cranelisp::new()
        .prelude(PRELUDE_GULP)
        .file("main.cl", "(defn main [] (let [gulp 7] (Pure gulp)))\n")
        .run("main.cl")
        .output()
        .assert_exit(7);
}

// spec: spec/08-modules.md §8.6.3 — a lexical `fn` PARAMETER named after a
// prelude-provided name is layer-1 scoping, allowed. GREEN today, stays green.
#[test]
fn lexical_fn_param_of_prelude_name_allowed() {
    Cranelisp::new()
        .prelude(PRELUDE_GULP)
        .file(
            "main.cl",
            "(defn use-it [gulp] (add-i64 gulp 1))\n\
             (defn main [] (Pure (use-it 41)))\n",
        )
        .run("main.cl")
        .output()
        .assert_exit(42);
}
