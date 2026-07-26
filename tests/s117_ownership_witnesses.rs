//! Sprint 117 R-2 production-path ownership witnesses.
//!
//! These tests compile ordinary Cranelisp source through the public binary.
//! They use normal `/clif` output plus Run/Link/REPL behavior. They add no
//! runtime trace, allocator hook, fault injection, or detector mode.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant, run_through_all_modes};

fn clif(forms: &str, name: &str, ownership_off: bool) -> String {
    let mut run = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(&format!("{forms}\n/clif {name}\n"));
    if ownership_off {
        run = run.env("CRANELISP_NO_OWNERSHIP", "1");
    } else {
        run = run.env_remove("CRANELISP_NO_OWNERSHIP");
    }
    let out = run.output();
    assert!(
        out.stdout.contains(&format!("; clif ir for {name}")),
        "ordinary /clif did not expose wrapper {name}; stdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
    out.stdout
}

/// How many **canonical glue releases** the emitted CLIF performs.
///
/// A release is a direct call to the colocated void drop-glue symbol
/// (`fnN = colocated u0:NN sig(i64)` + `call fnN(ptr)`). Before the S118 W3
/// consumer migration (`2df95c41..966d298e`) the same release was emitted
/// INLINE as `atomic_rmw.i64 sub` + a conditional free, and these oracles
/// grepped for that text; the migration collapsed every release site onto the
/// glue call, so the text disappeared while the ownership behaviour was
/// unchanged (FIXME 0910, `tests/fixtures/clif_baseline/MANIFEST.md`
/// §Re-baselines S118 drift class 1). Counting the glue call is the spelling
/// of "a release happens here" that survives that collapse.
///
/// `call_indirect` (the GOT-indirect primitive/user call shape) is deliberately
/// NOT matched: the substring is `call fn`, and an indirect call reads
/// `call_indirect sigN, vN(...)`.
fn glue_releases(ir: &str) -> usize {
    ir.matches("call fn").count()
}

// spec: design/typecheck/ownership-inference.md §9.1 — Borrowed scalar-result
// facts affect normal lowering: the live String owner remains with its scope,
// whereas conservative all-Owned lowering emits the final owner release.
#[test]
fn r2_borrowed_scalar_result_has_production_clif_polarity() {
    let src = "(defn borrowed-live [s] (add-i64 (str-len s) (str-len s)))";
    let precise = clif(src, "borrowed-live", false);
    let conservative = clif(src, "borrowed-live", true);
    assert!(
        precise.matches("atomic_rmw.i64 add").count() >= 2,
        "live owner must be retained across both consuming primitive calls:\n{precise}"
    );
    assert_eq!(
        glue_releases(&precise),
        0,
        "Borrowed precision MUST elide the wrapper's final owner release \
         entirely — no glue call on the return path:\n{precise}"
    );
    assert_eq!(
        glue_releases(&conservative),
        1,
        "conservative all-Owned lowering MUST still release the owner exactly \
         once (one canonical glue call), so the precision difference this cell \
         exists to pin stays visible:\n{conservative}"
    );
}

// spec: design/typecheck/ownership-inference.md §9.1 — Borrowed scalar-result
// behavior preserves a live source and accepts a temporary in every mode.
#[test]
fn r2_borrowed_scalar_result_live_and_temporary_all_modes() {
    let src = "(import [primitives [*]])\n\
               (defn main []\n\
                 (let [s \"abc\"]\n\
                   (Pure (add-i64 (str-len s)\n\
                                  (add-i64 (str-len s)\n\
                                           (str-len (str-concat \"a\" \"b\")))))))\n";
    run_through_all_modes(src, PreludeVariant::None).assert_all_equal(8);
}

// spec: design/typecheck/ownership-inference.md §9.1 — AliasOf(0) keeps the
// return-protect/argument-transfer pair in emitted production CLIF.
#[test]
fn r2_alias_of_string_identity_has_production_clif_transfer() {
    let ir = clif("(defn alias [s] (string-identity s))", "alias", false);
    assert!(
        ir.contains("store notrap aligned"),
        "AliasOf(0) wrapper MUST protect the returned alias:\n{ir}"
    );
    assert_eq!(
        glue_releases(&ir),
        1,
        "AliasOf(0) wrapper MUST release the transferred argument exactly once \
         (one canonical glue call):\n{ir}"
    );
}

// spec: design/typecheck/ownership-inference.md §9.1 — source and returned
// AliasOf(0) value remain usable with distinct scope uses in all modes.
#[test]
fn r2_alias_of_string_identity_source_and_alias_all_modes() {
    let src = "(import [primitives [*]])\n\
               (defn main []\n\
                 (let [s \"abc\" a (string-identity s)]\n\
                   (Pure (add-i64 (str-len a) (str-len s)))))\n";
    run_through_all_modes(src, PreludeVariant::None).assert_all_equal(6);
}

// spec: design/typecheck/ownership-inference.md §9.3 — ProjectionOf(0)
// materializes ownership for a heap element; the scalar-element control does
// not emit heap RC materialization.
#[test]
fn r2_projection_of_heap_element_has_production_clif_materialization() {
    let heap = clif(
        "(defn project-string [:(Vec String) v] (vec-get v 0))",
        "project-string",
        false,
    );
    let scalar = clif(
        "(defn project-int [:(Vec Int) v] (vec-get v 0))",
        "project-int",
        false,
    );
    assert!(
        heap.contains("atomic_rmw.i64 add"),
        "heap projection MUST materialize one owned element result:\n{heap}"
    );
    assert!(
        !scalar.contains("atomic_rmw.i64 add"),
        "scalar projection control MUST NOT materialize heap ownership:\n{scalar}"
    );
}

// spec: design/typecheck/ownership-inference.md §9.3 — a projected String and
// its source Vec remain usable in both relative-use orders across all modes.
#[test]
fn r2_projection_of_heap_element_and_root_all_modes() {
    let src = "(import [primitives [*]])\n\
               (defn main []\n\
                 (let [v [\"abc\"] x (vec-get v 0)]\n\
                   (Pure (add-i64 (str-len x) (str-len (vec-get v 0))))))\n";
    run_through_all_modes(src, PreludeVariant::None).assert_all_equal(6);
}

// spec: design/typecheck/ownership-inference.md §9.3 — MayAliasOf(0) COW
// lowering contains both the unique in-place and shared copy/release branches.
#[test]
fn r2_may_alias_vec_set_has_both_production_clif_cow_branches() {
    let ir = clif("(defn cow [:(Vec Int) v] (vec-set v 0 9))", "cow", false);

    // The protect/escape gate reads the source Vec's strong count and admits
    // the in-place arm only for the unique owner.
    assert!(
        ir.contains(
            "v6 = load.i64 notrap aligned v1+8\n\
             \x20   v7 = iconst.i64 1\n\
             \x20   v8 = icmp eq v6, v7  ; v7 = 1\n\
             \x20   brif v8, block2, block3"
        ),
        "MayAliasOf(0) vec-set MUST retain its source-count protect/escape \
         gate and dispatch unique versus shared sources:\n{ir}"
    );

    // The unique branch mutates the source allocation and returns that exact
    // allocation without releasing it.
    assert!(
        ir.contains(
            "block2:\n\
             \x20   v10 = load.i64 notrap aligned v1+32\n"
        ) && ir.contains(
            "store.i64 notrap aligned v3, v13  ; v3 = 9\n\
             \x20   jump block4(v1)"
        ),
        "the unique COW branch MUST mutate and return the original Vec without \
         a source release:\n{ir}"
    );

    // The shared branch calls the copying helper, releases the owned source at
    // its strong-count slot, conditionally destroys it, and returns the copy.
    assert!(
        ir.contains(
            "block3:\n\
             \x20   v15 = call fn0(v1, v2, v3, v4)"
        ) && ir.contains(
            "v16 = iadd_imm.i64 v1, 8\n\
             \x20   v17 = iconst.i64 1\n\
             \x20   v18 = atomic_rmw.i64 sub v16, v17"
        ) && ir.contains(
            "brif v19, block6, block5\n\n\
             block6:\n\
             \x20   fence \n\
             \x20   call fn1(v1, v5)"
        ) && ir.contains("jump block4(v15)"),
        "the shared COW branch MUST return its copied Vec after the exact \
         owned-source release/destruction gate:\n{ir}"
    );

    assert!(
        ir.contains(
            "block4(v9: i64):\n\
             \x20   return v9"
        ) && ir.matches("atomic_rmw.i64 sub").count() == 1,
        "the original and copied Vec branches MUST converge at one result, \
         with the source release confined to the shared branch:\n{ir}"
    );
}

// spec: design/typecheck/ownership-inference.md §9.3 — MayAliasOf(0) reaches
// the backend's producer-side result-summary consumer. Joining a vec-set
// result with a fresh Vec keeps the function result non-Fresh, so the merged
// return receives a protect increment. A false Fresh declaration removes this
// exact increment; vec-set's specialised COW body remains independently
// guarded above.
#[test]
fn r2_may_alias_summary_protects_control_flow_merged_return() {
    let ir = clif(
        "(defn cow-branch [:(Vec Int) v :Bool b]\n\
           (if b (vec-set v 0 9) [1]))",
        "cow-branch",
        false,
    );

    assert!(
        ir.contains(
            "block4(v4: i64):\n\
             \x20   v26 = iadd_imm v4, 8\n\
             \x20   v27 = iconst.i64 1\n\
             \x20   v28 = atomic_rmw.i64 add v26, v27"
        ),
        "the non-Fresh MayAliasOf summary MUST protect the control-flow-merged \
         return at the producer boundary:\n{ir}"
    );
    assert_eq!(
        ir.matches("atomic_rmw.i64 add").count(),
        2,
        "one add belongs to vec-set's unique COW branch and one to the \
         producer-side merged-return protect:\n{ir}"
    );
}

// spec: design/typecheck/ownership-inference.md §9.3 — unique and shared
// MayAliasOf(0) branches return correct values while the shared old Vec
// remains unchanged, uniformly through Run/Link/REPL.
#[test]
fn r2_may_alias_vec_set_unique_and_shared_all_modes() {
    let src = "(import [primitives [*]])\n\
               (defn main []\n\
                 (let [u (vec-set [1 2] 0 9)\n\
                       old [1 2]\n\
                       alias old\n\
                       changed (vec-set alias 0 9)]\n\
                   (Pure (add-i64 (vec-get u 0)\n\
                           (add-i64 (vec-get old 0) (vec-get changed 0))))))\n";
    run_through_all_modes(src, PreludeVariant::None).assert_all_equal(19);
}
