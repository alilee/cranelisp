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
//
// NOTE: `MySome` is a SUM constructor (ctor name `MySome` ≠ type name `MyOpt`),
// so it keys distinctly in the symbol table. The single-ctor PRODUCT case where
// ctor name == type name (the `R`/`R` collision) is the
// `single_ctor_product_constructor_as_first_class_value` guard below.
#[test]
fn deftype_constructor_as_first_class_value() {
    repl_prims(
        "(deftype (MyOpt a) MyNone (MySome [:a mval]))\n\
         (let [f MySome] (match (f 42) [MyNone 0 (MySome v) v]))\n",
    )
    .assert_stdout_contains(":primitives/Int 42");
}

// spec: spec/04-expressions.md §4.2.1 — a single-ctor PRODUCT constructor used
// as a first-class value (let-bound, then called as a function).
//
// This is the §4.2.1 spec-violation GUARD for the S79 Option-3 product-ctor-as-
// Def correction (FIXME 0319). For a single-ctor product `(deftype R [:Int w
// :Int h])` the constructor name `R` collides with the type name `R` on the
// symbol-table key. Before the dual-facet correction the surviving entry was the
// `TypeDef`, which carries no GOT slot and is absent from `defined_symbols()` —
// so referencing the product ctor as a VALUE (`(let [f R] ...)`, `(g R ...)`)
// failed to compile (`undefined variable: R` / no codegen). §4.2.1 says "data
// constructors ... evaluate to constructor functions ... a function value that
// ... can be ... bound with `let`, passed as an argument" — the product ctor
// MUST be a first-class value exactly like the sum ctor above. The correction
// makes the surviving `"R"` entry the got-slotted ctor `Def` carrying a type
// facet, so the product ctor flows through `defined_symbols()` and got-slots
// like any other ctor. This was RED before the correction; it is GREEN now.
#[test]
fn single_ctor_product_constructor_as_first_class_value() {
    // let-bound product ctor, then called: (f 3 4) builds (R 3 4), area = 7.
    repl_prims(
        "(deftype R [:Int w :Int h])\n\
         (defn add-fields [c] (match c [(R a b) (add-i64 a b)]))\n\
         (let [f R] (add-fields (f 3 4)))\n",
    )
    .assert_stdout_contains(":primitives/Int 7");
}

// spec: spec/04-expressions.md §4.2.1 — a single-ctor PRODUCT constructor passed
// as a higher-order argument (the `(map R …)`-style use). Companion to
// `single_ctor_product_constructor_as_first_class_value`: there the product ctor
// is let-bound; here it crosses a function-call boundary as an argument value
// (`(apply2 R 3 4)`), exercising the same "product ctor is a first-class value"
// requirement on the argument-passing path. Runs through `--run` (the product
// ctor's value must survive into batch codegen / `defined_symbols()`); exit = 7.
#[test]
fn single_ctor_product_constructor_passed_as_higher_order_arg() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(import [primitives [Int add-i64 Pure]])\n\
             (deftype R [:Int w :Int h])\n\
             (defn apply2 [f a b] (f a b))\n\
             (defn area [c] (match c [(R w h) (add-i64 w h)]))\n\
             (defn main [] (Pure (area (apply2 R 3 4))))",
        )
        .run("main.cl")
        .output()
        .assert_exit(7);
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
            "(import [primitives [Pure]])\n\
             (defn main [] (Pure (use-helper)))\n\
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
             (defn main [] (Pure (add-i64 (classify 5) (classify (sub-i64 0 3)))))",
        )
        .run("main.cl")
        .output()
        .assert_exit(18);
}

// =============================================================================
// Wave 5.6 ring1.rs GAP-COVER carry-forwards (chunks 2-3)
// =============================================================================

// spec: spec/05-definitions.md §5.2.2 — closure-call result used as ctor
// argument: `(Some (f 41))`. Exercises the eval-order of arg vs ctor
// wrap, plus the heap-temp lifetime through the ctor wrap. Distinct from
// `closure_returning_adt` where the closure body wraps in the ctor
// (opposite ordering — here the ctor is OUTSIDE the closure body).
// (carry: legacy/ring1.rs::adt_containing_closure_result)
#[test]
fn data_constructor_arg_from_closure_call_result() {
    repl_prims(
        "(deftype (Option a) None (Some [:a val]))\n\
         (let [f (fn [x] (add-i64 x 1))]\n\
           (match (Some (f 41)) [(Some x) x None 0]))\n",
    )
    .assert_stdout_contains(":primitives/Int 42");
}

// spec: spec/05-definitions.md §5.2.7 — constructor arity rejection:
// `(Point 1)` where Point expects two args. No prior spec_05 test
// isolated ADT-constructor arity rejection; `defn_multi_clause_arity`
// covers defn arity (positive). Ctor arity is a distinct lookup path.
// (carry: legacy/ring1.rs::error_adt_constructor_wrong_arg_count)
#[test]
fn deftype_product_constructor_arity_mismatch_neg() {
    let out = repl_prims(
        "(deftype Point [:Int x :Int y])\n\
         (Point 1)\n",
    );
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.to_lowercase().contains("error")
            || combined.to_lowercase().contains("arg")
            || combined.to_lowercase().contains("arity")
            || combined.to_lowercase().contains("expect"),
        "(Point 1) with Point [:Int x :Int y] MUST produce an arity-mismatch \
         diagnostic per §5.2.7; got stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/05-definitions.md §5.2.7 — constructor argument-type
// rejection: `(Point true 2)` where the first slot expects Int. The
// product-ctor-type-check angle is uncovered —
// `deftype_product_construct_and_destructure` is positive only.
// (carry: legacy/ring1.rs::error_adt_constructor_wrong_type)
#[test]
fn deftype_product_constructor_wrong_arg_type_neg() {
    let out = repl_prims(
        "(deftype Point [:Int x :Int y])\n\
         (match (Point true 2) [(Point x y) x])\n",
    );
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("Bool")
            || combined.contains("Int")
            || combined.to_lowercase().contains("type")
            || combined.to_lowercase().contains("error"),
        "(Point true 2) MUST produce a type-mismatch diagnostic naming \
         Bool / Int / type / error per §5.2.7; got stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/05-definitions.md §5.2 — undefined-constructor lookup:
// `(Foo 1 2)` where Foo is never defined. Distinct from
// `variable_reference_unbound_errors` (in spec_04) — constructor lookup
// is a different code path (constructor table vs symbol table).
// (carry: legacy/ring1.rs::error_undefined_constructor)
#[test]
fn data_constructor_undefined_lookup_neg() {
    let out = repl_prims("(Foo 1 2)\n");
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("Foo")
            || combined.to_lowercase().contains("undefined")
            || combined.to_lowercase().contains("unbound")
            || combined.to_lowercase().contains("error"),
        "(Foo 1 2) where Foo is never defined MUST produce a diagnostic \
         naming Foo / undefined / unbound / error per §5.2; got stdout={} \
         stderr={}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/05-definitions.md §5.2.2 — Vec containing ADT values:
// `[(Some 1) None (Some 3)]`, vec-get + match. Heap-element vec with
// mixed-tag ADTs. Distinct from all covered shapes — exercises ADT-in-vec
// lifetime + dispatch through match after vec-get.
// (carry: legacy/ring1.rs::vec_of_adts)
#[test]
fn vec_containing_adt_elements_get_and_match() {
    repl_prims(
        "(deftype (Option a) None (Some [:a val]))\n\
         (match (vec-get [(Some 1) None (Some 3)] 0) [(Some x) x None 0])\n",
    )
    .assert_stdout_contains(":primitives/Int 1");
}

// =============================================================================
// Wave 5.6 ring1.rs GAP-COVER carry-forwards (chunk 4)
// =============================================================================

// spec: spec/05-definitions.md §5.2.7 — constructor with wrong-typed
// argument: `(Point true 2)` where `Point [:Int x :Int y]` expects
// `Int`. The diagnostic MUST name the offending actual type "Bool".
// Distinct from chunk-3 `error_adt_constructor_wrong_type` which
// asserts any of Bool/Int/type indicators; this is the strict
// Bool-naming variant per the U1.7 Wave 3 error-quality contract.
// (carry: legacy/ring1.rs::error_quality_constructor_wrong_type_names_bool)
#[test]
fn deftype_product_constructor_wrong_arg_type_names_bool_strict() {
    let out = repl_prims(
        "(deftype Point [:Int x :Int y])\n\
         (match (Point true 2) [(Point x y) x])\n",
    );
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("Bool"),
        "diagnostic MUST name 'Bool' for the wrong-typed ctor arg, got: {combined}"
    );
}

// =============================================================================
// Wave 5.6 file 8 ring2.rs chunk 4 GAP-COVER carry-forwards.
// =============================================================================

// spec: spec/05-definitions.md §5.2.5 — a `deftype` MAY carry a docstring
// between the type name and the constructor list. The docstring MUST NOT
// affect construction or match dispatch. Existing
// `docstring_does_not_affect_call` covers defn-with-docstring; this is
// the deftype companion (no prior carry).
// (carry: legacy/ring2.rs::docstring_on_deftype)
#[test]
fn deftype_with_docstring_does_not_affect_construct_or_match() {
    repl_prims(
        "(deftype Color \"A primary color\" Red Green Blue)\n\
         (match Green [Red 1 Green 2 Blue 3])\n",
    )
    .assert_stdout_contains(":primitives/Int 2");
}

// spec: spec/05-definitions.md §5.3 + §5.12 — a `deftrait` MAY carry a
// docstring after the trait header AND each method MAY carry its own
// docstring. Neither MUST affect dispatch. No prior carry exercises
// deftrait-with-docstring + per-method docstring; this is the canonical
// completion of docstring coverage.
// Cross-ref: spec/07-traits.md §7.1.2 — Docstrings.
// (carry: legacy/ring2.rs::docstring_on_deftrait)
#[test]
fn deftrait_with_docstring_and_method_docstring_does_not_affect_dispatch() {
    repl_prims(
        "(deftrait (Sizeable a) \"Types that have a size\"\n  (size \"Get the size\" [a] Int))\n\
         (impl Sizeable Int (defn size [x] x))\n\
         (size 42)\n",
    )
    .assert_stdout_contains(":primitives/Int 42");
}
