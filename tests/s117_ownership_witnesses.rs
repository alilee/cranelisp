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

// spec: design/typecheck/ownership-inference.md §9.1 — Borrowed scalar-result
// behavior preserves a live source and accepts a temporary in every mode.
#[test]
fn r2_borrowed_scalar_result_live_and_temporary_all_modes() {
    let src = "(import [primitives [*]])\n\
               (defn main []\n\
                 (let [s \"abc\"]\n\
                   (primitives/pure (add-i64 (str-len s)\n\
                                  (add-i64 (str-len s)\n\
                                           (str-len (str-concat \"a\" \"b\")))))))\n";
    run_through_all_modes(src, PreludeVariant::None).assert_all_equal(8);
}

// spec: design/typecheck/ownership-inference.md §9.1 — source and returned
// AliasOf(0) value remain usable with distinct scope uses in all modes.
#[test]
fn r2_alias_of_string_identity_source_and_alias_all_modes() {
    let src = "(import [primitives [*]])\n\
               (defn main []\n\
                 (let [s \"abc\" a (string-identity s)]\n\
                   (primitives/pure (add-i64 (str-len a) (str-len s)))))\n";
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
                   (primitives/pure (add-i64 (str-len x) (str-len (vec-get v 0))))))\n";
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
            "v13 = load.i64 notrap aligned v1+8\n\
             \x20   v14 = iconst.i64 1\n\
             \x20   v15 = icmp eq v13, v14  ; v14 = 1\n\
             \x20   brif v15, block4, block5"
        ),
        "MayAliasOf(0) vec-set MUST retain its source-count protect/escape \
         gate and dispatch unique versus shared sources:\n{ir}"
    );

    // The unique branch mutates the source allocation and returns that exact
    // allocation without releasing it.
    assert!(
        ir.contains(
            "block4:\n\
             \x20   v17 = load.i64 notrap aligned v1+32\n"
        ) && ir.contains(
            "store.i64 notrap aligned v3, v20  ; v3 = 9\n\
             \x20   jump block6(v1)"
        ),
        "the unique COW branch MUST mutate and return the original Vec without \
         a source release:\n{ir}"
    );

    // The shared branch calls the copying helper, releases the owned source at
    // its strong-count slot, conditionally destroys it, and returns the copy.
    assert!(
        ir.contains(
            "block5:\n\
             \x20   v22 = call fn1(v1, v2, v3, v4)"
        ) && ir.contains(
            "v23 = iadd_imm.i64 v1, 8\n\
             \x20   v24 = iconst.i64 1\n\
             \x20   v25 = atomic_rmw.i64 sub v23, v24"
        ) && ir.contains(
            "brif v26, block8, block7\n\n\
             block8:\n\
             \x20   fence \n\
             \x20   call fn2(v1, v5)"
        ) && ir.contains("jump block6(v22)"),
        "the shared COW branch MUST return its copied Vec after the exact \
         owned-source release/destruction gate:\n{ir}"
    );

    assert!(
        ir.contains(
            "block6(v16: i64):\n\
             \x20   return v16"
        ) && ir.matches("atomic_rmw.i64 sub").count() == 1,
        "the original and copied Vec branches MUST converge at one result, \
         with the source release confined to the shared branch:\n{ir}"
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
                   (primitives/pure (add-i64 (vec-get u 0)\n\
                           (add-i64 (vec-get old 0) (vec-get changed 0))))))\n";
    run_through_all_modes(src, PreludeVariant::None).assert_all_equal(19);
}
