// spec_08_name_shadowing.rs — §8.6.4 registration and §8.6.5 use-site
// selection matrix.
//
// Distinct canonical declarations may expose the same module-scope spelling.
// Registration is order- and mode-independent; it neither rejects the later
// declaration nor makes either candidate shadow the other. Each use first
// filters by syntactic role and then by ordinary HM constraints. One surviving
// candidate is selected; several are a located ambiguity naming their canonical
// identities. Lexical bindings remain the only shadowing layer (§8.6.3).
//
// Several test function names retain their historical `_rejected` suffix because
// durable coverage citations refer to those identifiers. Their assertions now
// distinguish registration success from a later ambiguous use. The macro,
// trait, type, and trait-method rows additionally pin syntactic-role filtering.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{CrOutput, Cranelisp, PreludeVariant};

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

/// A §8.6.5 use-site ambiguity diagnostic is present.
fn has_ambiguity_diagnostic(out: &CrOutput) -> bool {
    let c = combined(out).to_lowercase();
    c.contains("ambiguous")
}

/// Batch (`--run` / `--link`) unresolved use: registration succeeded, but the
/// ambiguous call did not run to either candidate's distinguishing exit code.
fn assert_batch_use_ambiguous(out: &CrOutput, candidate_exit: i32) {
    assert!(
        has_ambiguity_diagnostic(out),
        "expected a §8.6.5 use-site ambiguity diagnostic; {}",
        combined(out)
    );
    assert_ne!(
        out.status.code(),
        Some(candidate_exit),
        "the ambiguous use must not run to candidate exit {}; {}",
        candidate_exit,
        combined(out)
    );
}

/// REPL unresolved use: the ambiguity diagnostic is present and no candidate
/// result is silently selected.
fn assert_repl_use_ambiguous(out: &CrOutput, candidate_marker: &str) {
    assert!(
        has_ambiguity_diagnostic(out),
        "expected a §8.6.5 use-site ambiguity diagnostic in the REPL; {}",
        combined(out)
    );
    assert!(
        !out.stdout.contains(candidate_marker),
        "the ambiguous use must not select candidate marker '{}'; {}",
        candidate_marker,
        combined(out)
    );
}

// =============================================================================
// 1. Selective imports and local definitions
// =============================================================================

// spec: spec/08-modules.md §8.6.4–§8.6.5 — an import and local defn with
// distinct canonical identities both register. A use before the defn has one
// candidate; a later equally compatible use is ambiguous and lists both.
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
    let c = combined(&out);
    assert!(
        c.contains("ambiguous bare name 'measure'")
            && c.contains("user/measure")
            && c.contains("util/measure"),
        "the post-registration use must list both compatible candidates; {c}"
    );
    assert!(!out.stdout.contains(":primitives/Int 99"));
    // Before the local declaration registers, the import is the sole candidate.
    assert_eq!(
        out.stdout.matches(":primitives/Int 3").count(),
        1,
        "the pre-registration call must use the sole imported candidate; {}",
        combined(&out)
    );
}

// spec: spec/08-modules.md §8.6.4–§8.6.5 — the same candidate set and
// ambiguous-use result holds in `--run`.
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
    assert_batch_use_ambiguous(&out, 99);
}

// spec: spec/08-modules.md §8.6.4–§8.6.5 — the same candidate set and
// ambiguous-use result holds in `--link`.
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
    assert_batch_use_ambiguous(&out, 99);
}

// spec: spec/08-modules.md §8.6.4–§8.6.5 — reversing registration order
// yields the same candidate set and ambiguous use.
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
    assert_batch_use_ambiguous(&out, 99);
}

// =============================================================================
// 2. Glob imports are registration peers
// =============================================================================

// spec: spec/08-modules.md §8.6.4–§8.6.5 — glob and selective imports are
// peers; the same compatible local candidate makes the call ambiguous.
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
    assert_batch_use_ambiguous(&out, 99);
}

// =============================================================================
// 3. Re-exported names are registration peers
// =============================================================================

// spec: spec/08-modules.md §8.4.0/§8.6.4–§8.6.5 — a re-export and local
// declaration both register; an equally compatible bare use is ambiguous.
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
    assert_repl_use_ambiguous(&out, ":primitives/Int 99");
}

// spec: spec/08-modules.md §8.4.0/§8.6.4–§8.6.5 — batch mode observes the
// same re-export/local candidate ambiguity.
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
    assert_batch_use_ambiguous(&out, 99);
}

// =============================================================================
// 4. Prelude candidates are registration peers
// =============================================================================

// spec: spec/08-modules.md §8.6.4/§8.8.1 — prelude and local candidates are
// merged; neither silently shadows the other.
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
    assert_repl_use_ambiguous(&out, ":primitives/Int 110");
}

// spec: spec/08-modules.md §8.6.4/§8.8.1 — the same merge holds in `--run`.
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
    assert_batch_use_ambiguous(&out, 105);
}

// spec: spec/08-modules.md §8.6.4/§8.8.1 — the same merge holds in `--link`.
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
    assert_batch_use_ambiguous(&out, 105);
}

// =============================================================================
// 5. Mode and registration-order parity
// =============================================================================

// spec: spec/08-modules.md §8.6.4–§8.6.5 — one candidate set produces the
// same use-site ambiguity in REPL, `--run`, and `--link`.
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
        has_ambiguity_diagnostic(&repl),
        "REPL leg must report the ambiguous use; {}",
        combined(&repl)
    );

    // --run leg — same use-site result.
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
        has_ambiguity_diagnostic(&run),
        "--run leg must report the same ambiguity as REPL; {}",
        combined(&run)
    );

    // --link leg — same use-site result.
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
        has_ambiguity_diagnostic(&link),
        "--link leg must report the same ambiguity as REPL; {}",
        combined(&link)
    );
}

// spec: spec/08-modules.md §8.6.4–§8.6.5 — reversing arrival order, including
// separate REPL turns, preserves both candidates and the same ambiguous use.
#[test]
fn import_over_def_repl_separate_turn_rejected() {
    // Batch leg (import-over-def, single cluster).
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
        has_ambiguity_diagnostic(&batch),
        "batch leg must report the ambiguous use; {}",
        combined(&batch)
    );

    // REPL leg — the def and import arrive in separate turns.
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
        has_ambiguity_diagnostic(&repl),
        "REPL separate-turn import-over-def must report the same ambiguity; {}",
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
// 7. Syntactic-role filtering across declaration kinds
//
// Trait, macro, trait-method, and ordinary value candidates may share an
// unqualified spelling. Registration succeeds. A syntactic role that leaves
// exactly one candidate selects it before HM filtering; explicit qualification
// still reaches the other canonical declaration.
// =============================================================================

// spec: spec/08-modules.md §8.6.4 — explicit-import and local trait candidates
// with distinct canonical identities both register.
#[test]
fn deftrait_over_explicitly_imported_trait_rejected_neg() {
    Cranelisp::new()
        .prelude(PRELUDE_SHOW)
        .file(
            "main.cl",
            "(import [prelude [Show Pure]])\n\
             (deftrait Show (shw2 [x] Int))\n\
             (defn main [] (Pure 0))\n",
        )
        .run("main.cl")
        .output()
        .assert_exit(0);
}

// spec: spec/08-modules.md §8.6.4/§8.8.1 — implicit-prelude and local
// trait candidates follow the same registration rule.
#[test]
fn deftrait_over_prelude_provided_trait_rejected_neg() {
    Cranelisp::new()
        .prelude(PRELUDE_SHOW)
        .file(
            "main.cl",
            "(deftrait Show (shw2 [x] Int))\n\
             (defn main [] (Pure 0))\n",
        )
        .run("main.cl")
        .output()
        .assert_exit(0);
}

// spec: spec/08-modules.md §8.6.4 — trait candidate registration has mode
// parity across REPL, `--run`, and `--link`.
#[test]
fn deftrait_over_prelude_mode_parity_all_modes() {
    // REPL leg — registration is accepted and identifies the local trait.
    let repl = Cranelisp::new()
        .repl()
        .prelude(PRELUDE_SHOW)
        .stdin("(deftrait Show (shw2 [x] Int))\n")
        .output();
    assert!(
        repl.stdout.contains(":user/Show ; deftrait"),
        "REPL must register the local canonical trait without replacing the \
         prelude candidate; {}",
        combined(&repl)
    );

    // --run and --link accept the same declaration set.
    Cranelisp::new()
        .prelude(PRELUDE_SHOW)
        .file(
            "main.cl",
            "(deftrait Show (shw2 [x] Int))\n\
             (defn main [] (Pure 0))\n",
        )
        .run("main.cl")
        .output()
        .assert_exit(0);

    Cranelisp::new()
        .prelude(PRELUDE_SHOW)
        .file(
            "main.cl",
            "(deftrait Show (shw2 [x] Int))\n\
             (defn main [] (Pure 0))\n",
        )
        .link_then_run("main.cl")
        .output()
        .assert_exit(0);
}

// spec: spec/08-modules.md §8.6.4–§8.6.6 — a local macro and prelude
// function both register. Macro-head syntax selects the macro; qualification
// selects the prelude function.
#[test]
fn defmacro_over_prelude_provided_name_rejected_neg() {
    Cranelisp::new()
        .prelude(PRELUDE_GULP)
        .file(
            "main.cl",
            "(defmacro gulp [x] x)\n\
             (defn main [] (Pure (add-i64 (gulp 3) (prelude/gulp 3))))\n",
        )
        .run("main.cl")
        .output()
        .assert_exit(7);
}

// spec: spec/08-modules.md §8.6.4–§8.6.6 — the same role filtering holds
// when the function candidate was imported explicitly.
#[test]
fn defmacro_over_explicit_import_rejected_neg() {
    Cranelisp::new()
        .prelude(PRELUDE_GULP)
        .file(
            "main.cl",
            "(import [prelude [gulp Pure add-i64]])\n\
             (defmacro gulp [x] x)\n\
             (defn main [] (Pure (add-i64 (gulp 3) (prelude/gulp 3))))\n",
        )
        .run("main.cl")
        .output()
        .assert_exit(7);
}

// spec: spec/08-modules.md §8.6.4 — a trait method and prelude function may
// expose the same spelling as distinct canonical candidates.
#[test]
fn deftrait_method_name_over_prelude_provided_name_rejected_neg() {
    Cranelisp::new()
        .prelude(PRELUDE_GULP)
        .file(
            "main.cl",
            "(deftrait Zork (gulp [x] Int))\n\
             (defn main [] (Pure 0))\n",
        )
        .run("main.cl")
        .output()
        .assert_exit(0);
}

// spec: spec/08-modules.md §8.6.4 — the same trait-method registration rule
// holds for an explicitly imported function candidate.
#[test]
fn deftrait_method_name_over_explicit_import_rejected_neg() {
    Cranelisp::new()
        .prelude(PRELUDE_GULP)
        .file(
            "main.cl",
            "(import [prelude [gulp Pure]])\n\
             (deftrait Zork (gulp [x] Int))\n\
             (defn main [] (Pure 0))\n",
        )
        .run("main.cl")
        .output()
        .assert_exit(0);
}

// spec: spec/08-modules.md §8.6.4 — registration remains order-independent
// when the local trait precedes the imported trait.
#[test]
fn import_over_local_deftrait_rejected_neg() {
    Cranelisp::new()
        .prelude(PRELUDE_SHOW)
        .file(
            "main.cl",
            "(deftrait Show (shw-local [x] Int))\n\
             (import [prelude [Show Pure]])\n\
             (defn main [] (Pure 0))\n",
        )
        .run("main.cl")
        .output()
        .assert_exit(0);
}

// spec: spec/08-modules.md §8.6.4–§8.6.6 — registration remains
// order-independent when the local macro precedes the imported function;
// syntactic role and qualification still select the two candidates.
#[test]
fn import_over_local_defmacro_rejected_neg() {
    Cranelisp::new()
        .prelude(PRELUDE_GULP)
        .file(
            "main.cl",
            "(defmacro gulp [x] x)\n\
             (import [prelude [gulp Pure add-i64]])\n\
             (defn main [] (Pure (add-i64 (gulp 3) (prelude/gulp 3))))\n",
        )
        .run("main.cl")
        .output()
        .assert_exit(7);
}

// =============================================================================
// 8. Type and private-definition candidates
// =============================================================================

// spec: spec/08-modules.md §8.6.4 — local and prelude type candidates with
// distinct canonical identities both register.
#[test]
fn deftype_over_prelude_provided_type_rejected_neg() {
    Cranelisp::new()
        .prelude(PRELUDE_ZED)
        .file(
            "main.cl",
            "(deftype Zed (Other [:Int m]))\n\
             (defn main [] (Pure 0))\n",
        )
        .run("main.cl")
        .output()
        .assert_exit(0);
}

// spec: spec/08-modules.md §8.6.4/§8.7.2 — private visibility does not give a
// local candidate precedence over an equally compatible prelude candidate.
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
    let c = combined(&out);
    assert!(
        c.contains("ambiguous bare name 'gulp'")
            && c.contains("main/gulp")
            && c.contains("prelude/gulp"),
        "the unresolved bare call must list both canonical candidates; {c}"
    );
    assert!(!out.stdout.contains(":primitives/Int 105"));
}
