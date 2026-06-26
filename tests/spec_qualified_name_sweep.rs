// spec_qualified_name_sweep.rs — qualified-AND-bare name-position sweep (Sprint
// 91, Thread B, FIXME 0434).
//
// The S90 Phase-6 live smoke surfaced D-qual-impl-target: a module-qualified type
// path in IMPL-TARGET position is re-rooted under the current module to a phantom
// (`user/primitives/Int`, `user/user/Widget`), so dispatch never matches — while
// the BARE target works. The two impl-target repros live in
// `tests/spec_07_traits.rs` (the 2 known S90-close reds; they flip green with the
// Wave-1 frontend `type_ref_from_name`/`trait_ref_from_name` fix).
//
// FIXME 0434 generalises the guard: for EVERY name-position the REPL displays
// qualified, a qualified reference MUST be interchangeable with the bare reference
// (qualified = canonical, spec §8.5; no re-rooting). This file is that proactive
// coverage class — qualified-AND-bare pairs across:
//   - type-annotation position (`:primitives/Int x` ≡ `:Int x`)
//   - deftype field type-ref (`(deftype Box [:primitives/Int v])` ≡ bare)
//   - deftrait method type-ref
//   - qualified constructor pattern in `match`
//   - import/(mod) target path resolution
//
// POSTURE (per the plan): each row is authored RED-first. Whether the OTHER
// name-positions already canonicalise correctly is UNKNOWN until the run — the
// D-qual fix is at the impl-target seam only. Any row that passes green-on-HEAD
// becomes a floor (the position already canonicalises — the sweep PROVES it,
// closing the blind spot). Any row that goes RED surfaces a fresh D-qual-shaped
// defect at that position → handed to /frontend with the repro as the brief.
//
// Free-standing: PrimitivesOnly prelude; current REPL module is `user`, so a
// type/ctor defined at the prompt is `user/`-qualified.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

fn repl_prims(lines: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(lines)
        .output()
}

// spec: spec/08-modules.md §8.5 — type-annotation position: a qualified type
// annotation `:primitives/Int x` pins the SAME type as the bare `:Int x`. Both
// `(defn f [:primitives/Int x] x)` and `(defn g [:Int x] x)` accept an Int and
// return it → both `(f 7)` and `(g 7)` yield 7.
#[test]
fn annotation_qualified_type_equals_bare_typecheck() {
    repl_prims(
        "(defn f [:primitives/Int x] x)\n\
         (defn g [:Int x] x)\n\
         (f 7)\n\
         (g 7)\n",
    )
    // Both forms must accept the Int and return it — the qualified annotation
    // canonicalises identically to the bare one.
    .assert_stdout_contains_all(&[":primitives/Int 7"]);
}

// spec: spec/08-modules.md §8.5 — NEG: a qualified type annotation
// `:primitives/Int` MUST NOT re-root to a phantom `user/primitives/Int` in any
// diagnostic or display. The well-typed program produces no such phantom.
#[test]
fn annotation_qualified_type_neg_no_reroot() {
    repl_prims("(defn f [:primitives/Int x] x)\n(f 7)\n")
        .assert_stdout_does_not_contain("user/primitives/Int");
}

// spec: spec/08-modules.md §8.5 — deftype field type-ref: a qualified field type
// `(deftype Box [:primitives/Int v])` is equivalent to the bare
// `(deftype Box [:Int v])` — the accessor types identically and `(v (Box 5))`
// yields 5.
#[test]
fn deftype_field_qualified_type_ref_equals_bare() {
    repl_prims(
        "(deftype Box [:primitives/Int v])\n\
         (v (Box 5))\n",
    )
    .assert_stdout_contains(":primitives/Int 5")
    .assert_stdout_does_not_contain("user/primitives/Int");
}

// spec: spec/08-modules.md §8.5 — deftrait method type-ref: a `deftrait` method
// signature using a qualified `primitives/Int` is equivalent to the bare `Int`.
// The impl over `Int` dispatches and `(scale 4)` → 8.
#[test]
fn deftrait_method_qualified_type_ref_equals_bare() {
    repl_prims(
        "(deftrait Scaler (scale [:primitives/Int x] :primitives/Int))\n\
         (impl Scaler Int (defn scale [x] (add-i64 x x)))\n\
         (scale 4)\n",
    )
    .assert_stdout_contains(":primitives/Int 8")
    .assert_stdout_does_not_contain("user/primitives/Int");
}

// spec: spec/08-modules.md §8.5 — qualified constructor pattern in `match`: a
// `user/`-qualified constructor pattern `(user/Some x)` matches identically to
// the bare `(Some x)` (the type lives in the current `user` module). Both bind
// the payload → 10.
#[test]
fn match_qualified_constructor_pattern_equals_bare() {
    repl_prims(
        "(deftype Maybe Nope (Yep [:primitives/Int v]))\n\
         (match (Yep 10) [(user/Yep x) x Nope 0])\n\
         (match (Yep 10) [(Yep x) x Nope 0])\n",
    )
    .assert_stdout_contains_all(&[":primitives/Int 10"]);
}

// spec: spec/08-modules.md §8.5 — NEG: a qualified constructor pattern MUST NOT
// re-root the type name to `user/user/...` in any diagnostic or display.
#[test]
fn match_qualified_constructor_neg_no_reroot() {
    repl_prims(
        "(deftype Maybe Nope (Yep [:primitives/Int v]))\n\
         (match (Yep 10) [(user/Yep x) x Nope 0])\n",
    )
    .assert_stdout_does_not_contain("user/user/");
}

// spec: spec/08-modules.md §8.5 — import/(mod) target path resolution: a
// qualified call `(util/helper)` to an imported sibling module resolves to the
// canonical module (no double-rooting). `(util/helper)` → 99.
#[test]
fn import_qualified_target_resolves() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n\
             (import [util [helper]])\n\
             (defn main [] (Pure (util/helper)))",
        )
        .file("util.cl", "(defn helper [] 99)")
        .run("main.cl")
        .output()
        .assert_exit(99);
}
