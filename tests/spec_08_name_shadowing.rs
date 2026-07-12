// spec_08_name_shadowing.rs — §8.6.4 name-shadowing matrix (S102; the 0514/0516
// def-over-name-in-scope defect cluster, now RESOLVED).
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
// HISTORY (0514/0516 defect cluster — FIXED). The def-over-name-in-scope
// rejection was once wired on the REPL (Additive) commit-gate ONLY, covering
// inner-table `import`/`export` — NOT the batch (`--run`/`--link`, Replace)
// path and NOT the implicit prelude. The §1–§5 negatives below reproduced that
// cluster: the `--run`/`--link` legs (class=mode-divergence) and the
// def-over-PRELUDE legs (class=prelude-scope-miss) were the RED guards. The fix
// moved the check to the shared typecheck seam
// (`checker.rs::reject_def_over_binding`) and added the prelude-fallback arm;
// all §1–§6 rows are GREEN on HEAD (verified 2026-07-12). They remain as
// regression guards and carry `// defect:` notation for defect-class analysis
// (a fixed repro keeps contributing to class-frequency/hotspot signals).
//
// The §6 POSITIVE (legal) tests guard the escape hatches (FQ reference,
// not-loading, dedup, lexical binding) the rule explicitly preserves.
//
// §7 (deftrait/defmacro/trait-method over name-in-scope) and §8 (deftype/defn-
// legs) are the S109 prelude≡explicit-import matrix rows (PLAN.md §II/§III);
// §7 carries the live RED acceptance-spec rows for the resolution convergence.

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

// A prelude re-exporting primitives and providing a sentinel trait `Show`
// (for the deftrait-over-prelude rows R2/R3 and import-over-local-deftrait R8).
const PRELUDE_SHOW: &str = "\
(export [primitives [*]])
(deftrait Show (shw [x] Int))
";

// A prelude re-exporting primitives and providing a sentinel type `Zed`
// (for the deftype-over-prelude row G7).
const PRELUDE_ZED: &str = "\
(export [primitives [*]])
(deftype Zed (ZedC [:Int n]))
";

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

/// §8.6.4 definition-over-name-in-scope rejection family, broadened beyond
/// `has_collision_diagnostic` to also accept the trait-registry `already
/// defined` wording. The R2 explicit-arm control rejects a redefined trait with
/// `trait Show already defined` today; the resolution convergence folds it into
/// the §8.6.4 `conflicts with '<name>' already in scope` wording (the landed
/// `defn`/`deftype` legs already use it — see G7/G8). Both contain a
/// recognisable rejection token, so the predicate matches across the transition.
fn has_def_conflict_diagnostic(out: &CrOutput) -> bool {
    let c = combined(out).to_lowercase();
    c.contains("conflict") || c.contains("ambiguous") || c.contains("already")
}

/// Batch (`--run` / `--link`) def-conflict rejection: a §8.6.4 def-conflict
/// diagnostic is present AND the offending definition did not run to its
/// `shadow_exit` (no effect). `shadow_exit` is the exit code the program would
/// produce if the shadowing definition were silently accepted (e.g. the macro's
/// identity result, the private def's value, or `0` for a declaration with no
/// runtime value — a rejection never exits 0).
fn assert_def_conflict_rejected(out: &CrOutput, shadow_exit: i32) {
    assert!(
        has_def_conflict_diagnostic(out),
        "expected a §8.6.4 definition-over-name-in-scope rejection \
         (conflict/already/ambiguous); {}",
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
// is a compile-time error at the REPL. The REPL leg was the always-correct
// anchor of the 0514 def-over-import cluster (the batch legs below were the RED
// arms); GREEN on HEAD.
// defect: class=mode-divergence locus=crates/cranelisp-typecheck/src/checker.rs::reject_def_over_binding found=S102 owner=/dev
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
// Was a 0514 RED arm (the batch Replace path accepted, def won, exit 99); the
// check moved to the shared typecheck seam and this is GREEN on HEAD.
// defect: class=mode-divergence locus=crates/cranelisp-typecheck/src/checker.rs::reject_def_over_binding found=S102 owner=/dev
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
// Was a 0514 RED arm (the batch Replace path accepted, def won, exit 99);
// GREEN on HEAD after the check moved to the shared typecheck seam.
// defect: class=mode-divergence locus=crates/cranelisp-typecheck/src/checker.rs::reject_def_over_binding found=S102 owner=/dev
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
// (order-independent). Was a 0514 RED arm (batch accepted, exit 99); GREEN on
// HEAD.
// defect: class=mode-divergence locus=crates/cranelisp-typecheck/src/checker.rs::reject_def_over_binding found=S102 owner=/dev
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
// bring in is the SAME error (no glob-exemption). Was a 0514 RED arm (batch
// accepted, exit 99); GREEN on HEAD.
// defect: class=mode-divergence locus=crates/cranelisp-typecheck/src/checker.rs::reject_def_over_binding found=S102 owner=/dev
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
// in-scope) name is the same error as over an imported one. The REPL leg was
// the always-correct anchor of the 0514 cluster; GREEN on HEAD.
// defect: class=mode-divergence locus=crates/cranelisp-typecheck/src/checker.rs::reject_def_over_binding found=S102 owner=/dev
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
// MUST hold in `--run`. Was a 0514 RED arm (batch accepted, exit 99); GREEN on
// HEAD.
// defect: class=mode-divergence locus=crates/cranelisp-typecheck/src/checker.rs::reject_def_over_binding found=S102 owner=/dev
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
// compile-time error. Was a 0514 prelude-arm RED (the local def silently won
// over the prelude — the outer scope was not checked); GREEN on HEAD after the
// prelude-fallback arm landed at the shared seam. REPL leg.
// defect: class=prelude-scope-miss locus=crates/cranelisp-typecheck/src/checker.rs::reject_def_over_binding found=S102 owner=/dev
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
// Was a 0514 prelude-arm RED (the local def won, exit 105); GREEN on HEAD.
// defect: class=prelude-scope-miss locus=crates/cranelisp-typecheck/src/checker.rs::reject_def_over_binding found=S102 owner=/dev
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
// Was a 0514 prelude-arm RED (the local def won, exit 105); GREEN on HEAD.
// defect: class=prelude-scope-miss locus=crates/cranelisp-typecheck/src/checker.rs::reject_def_over_binding found=S102 owner=/dev
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
// in all three modes. Was a 0514 RED (the REPL leg rejected, but `--run`/
// `--link` accepted — that divergence was the defect); GREEN on HEAD, pinning
// mode parity through the fix.
// defect: class=mode-divergence locus=crates/cranelisp-typecheck/src/checker.rs::reject_def_over_binding found=S102 owner=/dev
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

// spec: spec/08-modules.md §8.6.4 "Definition-Over-Import: Order-Independent,
// All Modes" — the #8 residual mode-divergence (FIXME 0516 Issue 2). The
// SYMMETRIC companion of def-over-import: an `import` (or `export`) that brings
// a bare name already bound by a LOCAL `def` in the current module MUST be
// rejected identically — order-independent, all modes. Batch (same cluster)
// already rejects it; the REPL, when the `import` arrives in a SEPARATE later
// turn than the `def`, does NOT — no def is registered in the import's cluster,
// so the def-registration seam never fires and the import installer skips.
// That REPL/batch divergence IS the #8 hole; this test pins it.
//
// Was a 0516-Issue-2 RED (the batch leg rejected, but the REPL separate-turn
// leg accepted the turn-2 import silently over the turn-1 def); GREEN on HEAD
// after the fix rejected an import/export whose bare name already resolves to a
// local `Def`, extended to the cross-cluster REPL case.
// defect: class=mode-divergence locus=crates/cranelisp-typecheck/src/checker.rs::reject_def_over_binding found=S102 owner=/dev
#[test]
fn import_over_def_repl_separate_turn_rejected() {
    // Batch leg (import-over-def, single cluster) — GREEN anchor: already
    // rejected. Establishes the shape the REPL leg must match.
    let batch = Cranelisp::new()
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
    assert!(
        has_collision_diagnostic(&batch),
        "batch leg MUST reject the import-over-def (§8.6.4 is order-independent); {}",
        combined(&batch)
    );

    // REPL leg — the def in turn 1, the import in a SEPARATE later turn. MUST
    // reject with mode-parity. RED today: the #8 hole silently accepts it.
    let repl = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file("util.cl", "(defn measure [v] (vec-len v))\n")
        .stdin(
            "(defn measure [v] 99)\n\
             (import [util [measure]])\n\
             (measure [1 2 3])\n",
        )
        .output();
    assert!(
        has_collision_diagnostic(&repl),
        "REPL separate-turn import-over-def MUST reject with mode-parity to \
         batch (§8.6.4 all-modes; FIXME 0516 Issue 2 — the #8 residual); {}",
        combined(&repl)
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

// =============================================================================
// 7. NEGATIVE — the forgotten-fallback definition forms (PLAN.md §II R2–R8)
//
// §8.6.4 lists `deftrait`, `defmacro`, and the private `-` variants alongside
// `defn`/`deftype` as definition forms that MUST be rejected over a name in
// scope — INCLUDING a prelude-provided name (§8.8.1: the prelude is just an
// implicit `(import [prelude [*]])`). The `defn`/`deftype` legs land through the
// §8.6.4 seam (`reject_def_over_binding`); `deftrait` (trait name AND method
// names) and `defmacro` bypass it. These rows are the acceptance spec for the
// resolution convergence [S109]: every definition form routes through the ONE
// §8.6.4 seam so no form can silently register over an in-scope name.
//
// Twin shape: where a row has an explicit-import companion (R2↔control,
// R4↔R5, R6↔R7), the two arms differ ONLY in the contested name's provenance
// (explicit `(import [prelude [X]])` vs implicit prelude) and MUST reject
// identically. `defmacro`/trait-method miss the seam on BOTH arms, so both are
// RED; `deftrait` over an explicit import is caught by the trait registry's
// duplicate check today, so THAT arm is a GREEN control.
// =============================================================================

// spec: spec/08-modules.md §8.6.4 — a `deftrait` whose name is already in scope
// via an EXPLICIT import is a compile-time error. GREEN control: the trait
// registry's duplicate-name check rejects it today (`trait Show already
// defined`). Twin companion of the prelude-arm row below.
#[test]
fn deftrait_over_explicitly_imported_trait_rejected_neg() {
    let out = Cranelisp::new()
        .prelude(PRELUDE_SHOW)
        .file(
            "main.cl",
            "(import [prelude [Show Pure]])\n\
             (deftrait Show (shw2 [x] Int))\n\
             (defn main [] (Pure 0))\n",
        )
        .run("main.cl")
        .output();
    assert_def_conflict_rejected(&out, 0);
}

// spec: spec/08-modules.md §8.6.4/§8.8.1 — a `deftrait` whose name a loaded
// prelude PROVIDES is the SAME compile-time error as over an explicit import.
// RED signal (R2): today the local `deftrait Show` silently registers
// `user/Show` over the prelude's `Show` (probed REPL + --run 2026-07-12); the
// trait registry's duplicate check is current-module-only and
// `TopLevel::TraitDecl` skips `reject_def_over_binding`.
// defect: class=prelude-scope-miss locus=crates/cranelisp-typecheck/src/traits/registry.rs::register_trait_decl (lookup_trait_decl_with_state is current-module-only; TopLevel::TraitDecl skips reject_def_over_binding) found=S108 owner=/dev
#[test]
fn deftrait_over_prelude_provided_trait_rejected_neg() {
    let out = Cranelisp::new()
        .prelude(PRELUDE_SHOW)
        .file(
            "main.cl",
            "(deftrait Show (shw2 [x] Int))\n\
             (defn main [] (Pure 0))\n",
        )
        .run("main.cl")
        .output();
    assert_def_conflict_rejected(&out, 0);
}

// spec: spec/08-modules.md §8.6.4 — mode parity for the deftrait-over-prelude
// rejection: it MUST be identical in REPL, `--run`, and `--link` (the §8.6.4
// all-modes MUST). RED signal (R3): all three legs SILENTLY ACCEPT today, so
// the gap is mode-uniform — this pins parity through the convergence fix.
// defect: class=prelude-scope-miss locus=crates/cranelisp-typecheck/src/traits/registry.rs::register_trait_decl (deftrait bypasses the §8.6.4 seam in every mode) found=S108 owner=/dev
#[test]
fn deftrait_over_prelude_mode_parity_all_modes() {
    // REPL leg — MUST reject the deftrait-over-prelude.
    let repl = Cranelisp::new()
        .repl()
        .prelude(PRELUDE_SHOW)
        .stdin("(deftrait Show (shw2 [x] Int))\n")
        .output();
    assert!(
        has_def_conflict_diagnostic(&repl),
        "REPL leg MUST reject the deftrait-over-prelude (§8.6.4 all-modes); {}",
        combined(&repl)
    );

    // --run leg — MUST reject identically.
    let run = Cranelisp::new()
        .prelude(PRELUDE_SHOW)
        .file(
            "main.cl",
            "(deftrait Show (shw2 [x] Int))\n\
             (defn main [] (Pure 0))\n",
        )
        .run("main.cl")
        .output();
    assert!(
        has_def_conflict_diagnostic(&run),
        "--run leg MUST reject the deftrait-over-prelude identically to REPL \
         (mode-parity §8.6.4 is normative); {}",
        combined(&run)
    );

    // --link leg — MUST reject identically.
    let link = Cranelisp::new()
        .prelude(PRELUDE_SHOW)
        .file(
            "main.cl",
            "(deftrait Show (shw2 [x] Int))\n\
             (defn main [] (Pure 0))\n",
        )
        .link_then_run("main.cl")
        .output();
    assert!(
        has_def_conflict_diagnostic(&link),
        "--link leg MUST reject the deftrait-over-prelude identically to REPL \
         (mode-parity §8.6.4 is normative); {}",
        combined(&link)
    );
}

// spec: spec/08-modules.md §8.6.4/§8.8.1 — a `defmacro` over a PRELUDE-provided
// name is the same compile-time error. RED signal (R4): today it is silently
// accepted AND the identity macro WINS at expansion — bare `(gulp 3)` expands
// to `3` (exit 3) instead of the prelude `gulp`'s `(+1)` = 4. The macro
// registration never consults the §8.6.4 seam.
// defect: class=silent-accept locus=src/expander.rs (macro registration never consults the §8.6.4 reject_def_over_binding seam) found=S108 owner=/dev
#[test]
fn defmacro_over_prelude_provided_name_rejected_neg() {
    let out = Cranelisp::new()
        .prelude(PRELUDE_GULP)
        .file(
            "main.cl",
            "(defmacro gulp [x] x)\n\
             (defn main [] (Pure (gulp 3)))\n",
        )
        .run("main.cl")
        .output();
    // The identity macro must NOT silently win (would expand `(gulp 3)` -> 3).
    assert_def_conflict_rejected(&out, 3);
}

// spec: spec/08-modules.md §8.6.4 — the EXPLICIT-import arm of R4: `(import
// [prelude [gulp]])` + `(defmacro gulp …)` MUST be rejected. RED signal (R5):
// accepted today — `defmacro` misses the §8.6.4 seam on BOTH arms, not only the
// prelude one (the identity macro wins, exit 3).
// defect: class=silent-accept locus=src/expander.rs (macro registration never consults the §8.6.4 reject_def_over_binding seam) found=S108 owner=/dev
#[test]
fn defmacro_over_explicit_import_rejected_neg() {
    let out = Cranelisp::new()
        .prelude(PRELUDE_GULP)
        .file(
            "main.cl",
            "(import [prelude [gulp Pure add-i64]])\n\
             (defmacro gulp [x] x)\n\
             (defn main [] (Pure (gulp 3)))\n",
        )
        .run("main.cl")
        .output();
    assert_def_conflict_rejected(&out, 3);
}

// spec: spec/08-modules.md §8.6.4 — a `deftrait` METHOD name contesting an
// in-scope name is a definition over a name in scope (a trait method is a fresh
// module-scope binding with a fresh terminal — it can never dedup). A
// `(deftrait Zork (gulp …))` under a prelude providing `gulp` MUST be rejected.
// RED signal (R6): silently accepted today (exit 0); `register_trait_method`
// has no §8.6.4 seam.
// defect: class=silent-accept locus=crates/cranelisp-typecheck/src/traits/registry.rs::register_trait_method (no §8.6.4 seam) found=S108 owner=/dev
#[test]
fn deftrait_method_name_over_prelude_provided_name_rejected_neg() {
    let out = Cranelisp::new()
        .prelude(PRELUDE_GULP)
        .file(
            "main.cl",
            "(deftrait Zork (gulp [x] Int))\n\
             (defn main [] (Pure 0))\n",
        )
        .run("main.cl")
        .output();
    assert_def_conflict_rejected(&out, 0);
}

// spec: spec/08-modules.md §8.6.4 — the EXPLICIT-import arm of R6: `(import
// [prelude [gulp]])` + `(deftrait Zork (gulp …))` MUST be rejected. RED signal
// (R7): accepted today — the trait-method seam misses on BOTH arms (exit 0).
// defect: class=silent-accept locus=crates/cranelisp-typecheck/src/traits/registry.rs::register_trait_method (no §8.6.4 seam) found=S108 owner=/dev
#[test]
fn deftrait_method_name_over_explicit_import_rejected_neg() {
    let out = Cranelisp::new()
        .prelude(PRELUDE_GULP)
        .file(
            "main.cl",
            "(import [prelude [gulp Pure]])\n\
             (deftrait Zork (gulp [x] Int))\n\
             (defn main [] (Pure 0))\n",
        )
        .run("main.cl")
        .output();
    assert_def_conflict_rejected(&out, 0);
}

// spec: spec/08-modules.md §8.6.4 (order-independence, symmetric direction) — an
// `import` whose bare name is already bound by a LOCAL `deftrait` MUST be
// rejected symmetrically. GREEN (reconciliation): probed RED-expected but is
// REJECTED today — the trait registry's duplicate-name check fires when the
// import brings a second `Show` alongside the local trait (`trait Show already
// defined`). Kept as a pin; the symmetric-macro sibling below is RED.
#[test]
fn import_over_local_deftrait_rejected_neg() {
    let out = Cranelisp::new()
        .prelude(PRELUDE_SHOW)
        .file(
            "main.cl",
            "(deftrait Show (shw-local [x] Int))\n\
             (import [prelude [Show Pure]])\n\
             (defn main [] (Pure 0))\n",
        )
        .run("main.cl")
        .output();
    assert_def_conflict_rejected(&out, 0);
}

// spec: spec/08-modules.md §8.6.4 (order-independence, symmetric direction) — an
// `import` whose bare name is already bound by a LOCAL `defmacro` MUST be
// rejected symmetrically (the later-arriving import is the rejected form). RED
// signal (R8, macro leg): accepted today — the import-over-local §8.6.4
// predicate reads `Def` entries; the local macro binding is invisible to it, so
// the identity macro wins (exit 3).
// defect: class=silent-accept locus=src/expander.rs (local macro binding invisible to the import-over-local §8.6.4 predicate) found=S108 owner=/dev
#[test]
fn import_over_local_defmacro_rejected_neg() {
    let out = Cranelisp::new()
        .prelude(PRELUDE_GULP)
        .file(
            "main.cl",
            "(defmacro gulp [x] x)\n\
             (import [prelude [gulp Pure]])\n\
             (defn main [] (Pure (gulp 3)))\n",
        )
        .run("main.cl")
        .output();
    assert_def_conflict_rejected(&out, 3);
}

// =============================================================================
// 8. NEGATIVE — the landed def-over-prelude legs, pinned (PLAN.md §III G7–G8)
//
// The `defn` leg of def-over-prelude is pinned above (§4); these pin the
// `deftype` and private `defn-` legs, which route through the same §8.6.4 seam
// and reject with the landed `conflicts with '<name>' already in scope via the
// implicit prelude` diagnostic. GREEN today; they guard the convergence refactor
// (behaviour preservation) and make the NEXT forgotten-fallback site fail loud.
// =============================================================================

// spec: spec/08-modules.md §8.6.4 — a `deftype` over a prelude-provided TYPE
// name is the §8.6.4 def-over-name-in-scope error, exactly as the `defn` leg.
// GREEN (probed): rejected with the implicit-prelude conflict diagnostic.
#[test]
fn deftype_over_prelude_provided_type_rejected_neg() {
    let out = Cranelisp::new()
        .prelude(PRELUDE_ZED)
        .file(
            "main.cl",
            "(deftype Zed (Other [:Int m]))\n\
             (defn main [] (Pure 0))\n",
        )
        .run("main.cl")
        .output();
    assert_def_conflict_rejected(&out, 0);
    // Pin the landed §8.6.4 wording (behaviour-preservation for the convergence).
    assert!(
        combined(&out).to_lowercase().contains("conflict"),
        "the deftype-over-prelude rejection MUST carry the §8.6.4 conflict \
         wording; {}",
        combined(&out)
    );
}

// spec: spec/08-modules.md §8.6.4/§8.7.2 — the PRIVATE variant: a `defn-` over a
// prelude-provided name is the SAME rejection (visibility of the definition does
// not exempt it). GREEN (probed): rejected with the §8.6.4 conflict diagnostic.
#[test]
fn private_defn_over_prelude_provided_name_rejected_neg() {
    let out = Cranelisp::new()
        .prelude(PRELUDE_GULP)
        .file(
            "main.cl",
            "(defn- gulp [x] (add-i64 x 100))\n\
             (defn main [] (Pure (gulp 5)))\n",
        )
        .run("main.cl")
        .output();
    // The private local `gulp` = (+100); (gulp 5) = 105 if it silently won.
    assert_def_conflict_rejected(&out, 105);
    assert!(
        combined(&out).to_lowercase().contains("conflict"),
        "the defn-over-prelude rejection MUST carry the §8.6.4 conflict wording; {}",
        combined(&out)
    );
}
