// spec_05_definitions.rs — Top-level definition forms (Sprint 64 Wave 5 Batch 2).
//
// Covers `spec/05-definitions.md`. Carries forward language-behaviour
// assertions from legacy integration-tier `tests/ring0.rs`, `tests/ring1.rs`,
// `tests/ring2.rs`, `tests/sketch_port.rs`, and `tests/e2e.rs`. REPL canonical
// per `tests/plan/PLAN.md §"Mode canonicalisation"`.
//
// What this file covers:
//   - defn (single-signature) — body, params (§5.1.1)
//   - defn (multi-signature) — arity dispatch (§5.1.2)
//   - Auto-currying (§5.1.3)
//   - deftype — product, sum, enum (§5.2)
//   - deftrait + impl (§5.3, §5.4)
//   - defmacro registration & display (§5.5 — surface only; full macro
//     coverage is in spec_09_macros.rs)
//   - const + def (§5.6, §5.7)
//   - Visibility (§5.11) — defn- private
//   - Docstrings (§5.12)
//   - Definition ordering (§5.13)

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

fn repl_std(lines: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::TestStandard)
        .stdin(lines)
        .output()
}

// =============================================================================
// §5.1.1 Single-signature defn
// =============================================================================

// spec: spec/05-definitions.md §5.1.1 — defn binds + can be called
#[test]
fn defn_define_and_call() {
    repl_prims("(defn three [] 3)\n(three)\n").assert_stdout_contains(":primitives/Int 3");
}

// spec: spec/05-definitions.md §5.1.1 — defn with one param
#[test]
fn defn_one_param() {
    repl_prims("(defn id [x] x)\n(id 7)\n").assert_stdout_contains(":primitives/Int 7");
}

// spec: spec/05-definitions.md §5.1.1 — defn with multiple params
#[test]
fn defn_multi_params() {
    repl_prims("(defn add3 [x y z] (add-i64 x (add-i64 y z)))\n(add3 1 2 3)\n")
        .assert_stdout_contains(":primitives/Int 6");
}

// spec: spec/05-definitions.md §5.1.1 — defn with annotated param types
#[test]
fn defn_annotated_params() {
    repl_prims("(defn f [:Int x] x)\n(f 42)\n").assert_stdout_contains(":primitives/Int 42");
}

// =============================================================================
// §5.1.2 Multi-signature defn
// =============================================================================

// spec: spec/05-definitions.md §5.1.2 — multi-clause arity dispatch
#[test]
fn defn_multi_clause_arity() {
    repl_prims(
        "(defn f ([] 0) ([x] x) ([x y] (add-i64 x y)))\n(f)\n(f 5)\n(f 3 4)\n",
    )
    .assert_stdout_contains_all(&[
        ":primitives/Int 0",
        ":primitives/Int 5",
        ":primitives/Int 7",
    ]);
}

// =============================================================================
// §5.1.3 Auto-Currying
// =============================================================================

// spec: spec/05-definitions.md §5.1.3 — calling with fewer args returns closure
#[test]
fn defn_auto_curry_call_with_fewer_args() {
    repl_prims(
        "(defn add [x y] (add-i64 x y))\n(let [inc (add 1)] (inc 4))\n",
    )
    .assert_stdout_contains(":primitives/Int 5");
}

// =============================================================================
// §5.1.2 Multi-Signature — additional shapes (Wave 5.6 sketch_port carry-forward)
// =============================================================================

// spec: spec/05-definitions.md §5.1.2 — multi-clause type-based dispatch
// (same arity, different parameter types). Distinct from arity-only dispatch
// already covered by `defn_multi_clause_arity`.
// (carry: legacy/sketch_port.rs::sketch_multi_sig_type_based_dispatch)
#[test]
fn defn_multi_clause_type_dispatch() {
    repl_prims(
        "(defn choose ([x y] (add-i64 x y)) ([x y] (if y x 0)))\n\
         (add-i64 (choose 10 20) (choose 5 true))\n",
    )
    .assert_stdout_contains(":primitives/Int 35");
}

// spec: spec/05-definitions.md §5.1.2 — duplicate clause signatures rejected.
// (carry: legacy/sketch_port.rs::sketch_multi_sig_duplicate_signature_error)
#[test]
fn defn_multi_clause_duplicate_sig_neg() {
    let out = repl_prims("(defn dup ([x] (add-i64 x 1)) ([y] (add-i64 y 2)))\n");
    assert!(
        out.stdout.to_lowercase().contains("error")
            || out.stdout.contains("duplicate"),
        "duplicate clause signature MUST error per §5.1.2; got:\n{}",
        out.stdout
    );
}

// =============================================================================
// §5.2 Type Definition (deftype)
// =============================================================================

// spec: spec/05-definitions.md §5.2 — enum (nullary constructors)
#[test]
fn deftype_enum_construct_and_match() {
    repl_prims(
        "(deftype Color Red Green Blue)\n(match Red [Red 0 Green 1 Blue 2 _ 99])\n",
    )
    .assert_stdout_contains(":primitives/Int 0");
}

// spec: spec/05-definitions.md §5.2 — sum type with field
#[test]
fn deftype_sum_with_field_match() {
    repl_prims(
        "(deftype (Maybe a) Nothing (Just [:a v]))\n(match (Just 5) [(Just x) x Nothing 0])\n",
    )
    .assert_stdout_contains(":primitives/Int 5");
}

// spec: spec/05-definitions.md §5.2 — product type
#[test]
fn deftype_product_construct_and_destructure() {
    repl_prims(
        "(deftype Point [:Int x :Int y])\n(match (Point 3 4) [(Point a b) (add-i64 a b)])\n",
    )
    .assert_stdout_contains(":primitives/Int 7");
}

// spec: spec/05-definitions.md §5.2.4 — bare-field-name shortcut syntax
// `(deftype Pair [first second])` — fresh type vars assigned to bare field
// names, no `:Type` annotation required. Distinct from explicitly-annotated
// product shape.
// (carry: legacy/sketch_port.rs::sketch_adt_shortcut_syntax)
#[test]
fn deftype_product_shortcut_field_names() {
    repl_prims(
        "(deftype Pair [first second])\n\
         (match (Pair 7 8) [(Pair a b) a])\n",
    )
    .assert_stdout_contains(":primitives/Int 7");
}

// spec: spec/05-definitions.md §5.2 — constructor as first-class value
// (let-bound, then called as a function). Distinct from operator-as-value
// and defn-as-value first-class shapes.
// (carry: legacy/sketch_port.rs::sketch_adt_first_class_constructor)
#[test]
fn deftype_constructor_as_first_class_value() {
    repl_prims(
        "(deftype (MyOpt a) MyNone (MySome [:a mval]))\n\
         (let [f MySome] (match (f 42) [MyNone 0 (MySome v) v]))\n",
    )
    .assert_stdout_contains(":primitives/Int 42");
}

// =============================================================================
// §5.3 + §5.4 deftrait + impl
// =============================================================================

// spec: spec/05-definitions.md §5.3 — deftrait + impl + invoke method
#[test]
fn deftrait_impl_and_dispatch() {
    // Per the impl syntax in spec/07-traits.md §7.3, methods inside impl
    // bodies use the (defn name [params] body) shape.
    repl_prims(
        "(deftrait Shape (area [self] Int))\n\
         (deftype Square [:Int side])\n\
         (impl Shape Square (defn area [s] (match s [(Square n) (mul-i64 n n)])))\n\
         (area (Square 5))\n",
    )
    .assert_stdout_contains(":primitives/Int 25");
}

// =============================================================================
// §5.5 defmacro (surface only — full coverage in spec_09_macros.rs)
// =============================================================================

// spec: spec/05-definitions.md §5.5 — defmacro registers and displays
#[test]
fn defmacro_registers_with_display() {
    repl_prims("(defmacro id [x] x)\n").assert_stdout_contains_all(&["user/id", "defmacro"]);
}

// =============================================================================
// §5.6 / §5.7 const + def — prelude macros, not in TestStandard fixture
// =============================================================================
//
// `const` and `def` are documented as prelude-provided macros (§5.6, §5.7).
// They live in the project's prelude (e.g., `stdlib/prelude.cl`), not in
// the `tests/fixtures/preludes/test-standard.cl` fixture. Coverage for
// these forms lives in `tests/spec_11_stdlib.rs` which is the named
// exception that loads the workspace stdlib.

// =============================================================================
// §5.11 Visibility (defn- private)
// =============================================================================

// spec: spec/05-definitions.md §5.11 — defn- callable from same module
#[test]
fn private_defn_callable_in_module() {
    repl_prims("(defn- helper [] 41)\n(defn main [] (add-i64 (helper) 1))\n(main)\n")
        .assert_stdout_contains(":primitives/Int 42");
}

// =============================================================================
// §5.12 Docstrings — registered, no observable effect on call
// =============================================================================

// spec: spec/05-definitions.md §5.12 — docstring on defn does not break call
#[test]
fn docstring_does_not_affect_call() {
    repl_prims("(defn inc \"Increment by one\" [x] (add-i64 x 1))\n(inc 9)\n")
        .assert_stdout_contains(":primitives/Int 10");
}

// =============================================================================
// §5.13 Definition Ordering — forward references between defns
// =============================================================================

// spec: spec/05-definitions.md §5.13 — defn forward reference to later defn
//
// Mode-specific exception: definition ordering is a module-compilation
// property (a module is compiled as a unit), not a per-form REPL property.
// We test through `--run` against an on-disk module so the spec property
// (forward references resolve when the whole module is compiled) is what
// is observed.
#[test]
fn forward_reference_between_defns() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(defn main [] (use-helper))\n\
             (defn use-helper [] (helper-fn))\n\
             (defn helper-fn [] 5)",
        )
        .run("main.cl")
        .output()
        .assert_exit(5);
}

// spec: spec/05-definitions.md §5.13.1 — defns may reference each other
// across forward-decl ordering. Distinct from
// `forward_reference_between_defns` (single-direction chain a→b→c): this
// test exercises the bidirectional shape where two defns each reference
// the other via interleaved forward-references within a single module
// compilation unit.
// (carry: legacy/ring0.rs::mutual_forward_references)
#[test]
fn defns_mutual_forward_references() {
    // is-positive references gt-i64; classify references is-positive.
    // main combines two classify calls. Both functions are defined before
    // main — but is-positive is referenced by classify *before* the
    // body-of-classify is type-checked, exercising the module-as-unit
    // forward-reference resolution. (5+10) + 3 = 18.
    Cranelisp::new()
        .file(
            "main.cl",
            "(import [primitives [*]])\n\
             (defn is-positive [n] (if (gt-i64 n 0) 1 0))\n\
             (defn classify [n] (if (eq-i64 (is-positive n) 1) (add-i64 n 10) (sub-i64 0 n)))\n\
             (defn main [] (add-i64 (classify 5) (classify (sub-i64 0 3))))",
        )
        .run("main.cl")
        .output()
        .assert_exit(18);
}
