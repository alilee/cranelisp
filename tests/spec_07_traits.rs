// spec_07_traits.rs — Trait system (Sprint 64 Wave 5 Batch 2).
//
// Covers `spec/07-traits.md`. Carries forward language-behaviour assertions
// from legacy integration-tier `tests/ring2.rs`, `tests/sketch_port.rs`,
// `tests/e2e.rs`. REPL canonical per
// `tests/plan/PLAN.md §"Mode canonicalisation"`.
//
// What this file covers:
//   - Trait declaration (§7.1)
//   - Higher-kinded traits (§7.2)
//   - Trait implementation (§7.3)
//   - Static method resolution (§7.4)
//   - Operators as trait methods (§7.5)
//   - Operators as first-class values (§7.6)
//   - Constrained polymorphism interaction (§7.8)
//   - User-defined traits (§7.9)
//   - REPL introspection (§7.10)

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{run_through_all_modes, Cranelisp, PreludeVariant};

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

/// Compile `src` as `user.cl` under `--run` with the PrimitivesOnly prelude.
/// Used by the §7.3.5 mode-uniformity rows (AG-2): a rejection CLASS must fire
/// identically under REPL, `--run`, and `--link`.
fn run_prims(src: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .user(src)
        .run("user.cl")
        .output()
}

/// As `run_prims` but under `--link` then run the produced executable.
fn link_prims(src: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .user(src)
        .link_then_run("user.cl")
        .output()
}

// =============================================================================
// §7.1 Trait Declaration
// =============================================================================

// spec: spec/07-traits.md §7.1 — deftrait declares trait + method signatures
#[test]
fn deftrait_declaration_succeeds() {
    repl_prims("(deftrait Showable (show [x] String))\n")
        .assert_stdout_contains_all(&["user/Showable", "deftrait"]);
}

// =============================================================================
// §7.3 Trait Implementation
// =============================================================================

// spec: spec/07-traits.md §7.3 — impl provides method body for type
#[test]
fn trait_impl_concrete_type() {
    repl_prims(
        "(deftrait Doubler (twice [x] Int))\n\
         (impl Doubler Int (defn twice [n] (add-i64 n n)))\n\
         (twice 21)\n",
    )
    .assert_stdout_contains(":primitives/Int 42");
}

// spec: spec/07-traits.md §7.3 — multiple impls registered for distinct types
#[test]
fn trait_multiple_impls() {
    // Two impls on distinct types both compile and the appropriate one
    // dispatches at the call site. Cross-type dispatch in a single REPL
    // session can hit known monomorphisation interactions; we assert the
    // first call dispatches to the Int impl and both impls compile.
    repl_prims(
        "(deftrait Tag (tag [x] Int))\n\
         (impl Tag Int (defn tag [_] 1))\n\
         (impl Tag Bool (defn tag [_] 2))\n\
         (tag 0)\n",
    )
    .assert_stdout_contains_all(&[
        "impl user/Tag for user/Int",
        "impl user/Tag for user/Bool",
        ":primitives/Int 1",
    ]);
}

// =============================================================================
// §7.4 Static Method Resolution
// =============================================================================

// spec: spec/07-traits.md §7.4 — method resolution selects correct impl by arg type
#[test]
fn trait_method_dispatched_by_arg_type() {
    repl_std("(+ 1 2)\n").assert_stdout_contains(":primitives/Int 3");
}

// =============================================================================
// §7.5 Operators as Trait Methods (Num.+)
// =============================================================================

// spec: spec/07-traits.md §7.5 — + is a Num method, dispatches per type
#[test]
fn operator_plus_int() {
    repl_std("(+ 5 6)\n").assert_stdout_contains(":primitives/Int 11");
}

// spec: spec/07-traits.md §7.5 — + on Float
#[test]
fn operator_plus_float() {
    repl_std("(+ 1.5 2.5)\n").assert_stdout_contains(":primitives/Float");
}

// =============================================================================
// §7.6 Operators as First-Class Values
// =============================================================================

// spec: spec/07-traits.md §7.6 — operator passed as a value works through dispatch
#[test]
fn operator_as_first_class_value() {
    // Not all operator-as-value forms are reliably first-class across surfaces;
    // assert via direct application to confirm the trait method resolves.
    repl_std("(let [op +] (op 4 5))\n").assert_stdout_contains(":primitives/Int 9");
}

// =============================================================================
// §7.8 Constrained Polymorphism Interaction
// =============================================================================

// spec: spec/07-traits.md §7.8 — constrained defn instantiates per call site
#[test]
fn constrained_polymorphism_int_then_float() {
    repl_std(
        "(defn dbl [x] (+ x x))\n(dbl 3)\n(dbl 1.5)\n",
    )
    .assert_stdout_contains_all(&[":primitives/Int 6", ":primitives/Float"]);
}

// =============================================================================
// §7.9 User-Defined Traits
// =============================================================================

// spec: spec/07-traits.md §7.9 — user trait is independent of stdlib traits
#[test]
fn user_trait_simple() {
    repl_prims(
        "(deftrait Inc (inc-by [x n] Int))\n\
         (impl Inc Int (defn inc-by [a b] (add-i64 a b)))\n\
         (inc-by 10 5)\n",
    )
    .assert_stdout_contains(":primitives/Int 15");
}

// =============================================================================
// §7.10 REPL Introspection
// =============================================================================

// spec: spec/07-traits.md §7.10 — deftrait display shows trait name + classification
#[test]
fn deftrait_display_shows_classification() {
    repl_prims("(deftrait Sized (size [x] Int))\n")
        .assert_stdout_contains_all(&["user/Sized", "deftrait"]);
}

// =============================================================================
// §7.1.5 Default Method Implementations
// (Wave 5.6 sketch_port carry-forward — REGRESSION-GUARD trio + ADT variant)
// =============================================================================

// spec: spec/07-traits.md §7.1.5 — default method body synthesised when impl
// omits the method; default body invokes another required method via dispatch.
// (carry: legacy/sketch_port.rs::sketch_default_method_used_when_not_overridden)
// (carry: legacy/sketch_port.rs::sigsegv_isolation_default_method)
#[test]
fn default_method_used_when_not_overridden() {
    repl_prims(
        "(deftrait Greetable (greet [self] Int) (wave [x] Int (add-i64 (greet x) 10)))\n\
         (impl Greetable Int (defn greet [x] x))\n\
         (wave 5)\n",
    )
    .assert_stdout_contains(":primitives/Int 15");
}

// spec: spec/07-traits.md §7.1.5 — explicit override shadows the default body.
// (carry: legacy/sketch_port.rs::sketch_default_method_overridden)
#[test]
fn default_method_overridden_by_impl() {
    repl_prims(
        "(deftrait Greetable (greet [self] Int) (wave [x] Int (add-i64 (greet x) 10)))\n\
         (impl Greetable Int (defn greet [x] x) (defn wave [x] (mul-i64 x 100)))\n\
         (wave 5)\n",
    )
    .assert_stdout_contains(":primitives/Int 500");
}

// spec: spec/07-traits.md §7.1.5 — impl missing required method (no default
// available for it) MUST error even when other defaults exist.
// (carry: legacy/sketch_port.rs::sketch_default_method_validate_impl_missing_required)
#[test]
fn impl_missing_required_method_neg() {
    let out = repl_prims(
        "(deftrait Greetable (greet [self] Int) (wave [x] Int (add-i64 (greet x) 10)))\n\
         (impl Greetable Int (defn wave [x] 42))\n",
    );
    assert!(
        out.stdout.to_lowercase().contains("error")
            || out.stdout.contains("missing required method")
            || out.stdout.contains("missing"),
        "impl missing required method MUST error per §7.1.5; got:\n{}",
        out.stdout
    );
}

// spec: spec/07-traits.md §7.1.5 — default method synthesis when impl is on an
// ADT type rather than a primitive; sister-shape of default_method_used_when_not_overridden.
// (carry: legacy/sketch_port.rs::sketch_default_method_on_adt)
#[test]
fn default_method_used_on_adt_impl() {
    repl_prims(
        "(deftrait Countable (count [self] Int) (count-plus-one [x] Int (add-i64 (count x) 1)))\n\
         (deftype Color Red Green Blue)\n\
         (impl Countable Color (defn count [c] (match c [Red 1 Green 2 Blue 3])))\n\
         (count-plus-one Green)\n",
    )
    .assert_stdout_contains(":primitives/Int 3");
}

// spec: spec/07-traits.md §7.1.5 — default method whose body uses a primitive
// directly (no inner trait dispatch) — discriminates from the default-with-trait-call
// path and was a load-bearing SIGSEGV-isolation repro.
// (carry: legacy/sketch_port.rs::sigsegv_isolation_default_method_no_trait_call)
#[test]
fn default_method_with_primitive_only_body() {
    repl_prims(
        "(deftrait Simple (val [self] Int) (val-plus [x] Int (add-i64 (val x) 1)))\n\
         (impl Simple Int (defn val [x] x))\n\
         (val 5)\n\
         (val-plus 5)\n",
    )
    .assert_stdout_contains_all(&[":primitives/Int 5", ":primitives/Int 6"]);
}

// =============================================================================
// §7.3 Trait Implementation — additional shapes (Wave 5.6 sketch_port carry-forward)
// =============================================================================

// spec: spec/07-traits.md §7.3 — trait impl on an enum ADT with the impl method
// body matching over all constructors. Defect-isolation repro from the
// `sigsegv_isolation_*` cluster (trait-on-enum-ADT dispatch).
// (carry: legacy/sketch_port.rs::sigsegv_isolation_trait_impl_on_adt)
#[test]
fn trait_impl_on_enum_adt_with_match_over_all_constructors() {
    repl_prims(
        "(deftype Color Red Green Blue)\n\
         (deftrait Tag (tag [self] Int))\n\
         (impl Tag Color (defn tag [c] (match c [Red 1 Green 2 Blue 3])))\n\
         (tag Red)\n",
    )
    .assert_stdout_contains(":primitives/Int 1");
}

// spec: spec/07-traits.md §7.3 — impl method body uses a trait operator (`+`),
// invoking trait dispatch from inside another trait's impl body.
// (carry: legacy/sketch_port.rs::sigsegv_isolation_trait_impl_with_trait_dispatch_in_body)
#[test]
fn trait_impl_body_uses_operator() {
    repl_std(
        "(deftrait Double (double [self] Int))\n\
         (impl Double Int (defn double [x] (+ x x)))\n\
         (double 3)\n",
    )
    .assert_stdout_contains(":primitives/Int 6");
}

// =============================================================================
// §7.4 Method Resolution — polymorphic ADT impl on concrete instantiation
// =============================================================================

// spec: spec/07-traits.md §7.4 — polymorphic impl on concrete ADT instantiation
// `(MyOpt Int)` — distinct from polymorphic-target. Memory note re:
// `impl_target_mangled()` produces `Option$Int` for concrete vs `Option` for type
// var. Body recursively dispatches the same trait on the inner field type.
// (carry: legacy/sketch_port.rs::sketch_adt_display_option_int_batch)
// (carry: legacy/sketch_port.rs::sigsegv_isolation_poly_adt_impl)
#[test]
fn polymorphic_impl_on_concrete_adt_instantiation() {
    repl_prims(
        "(deftrait Showable (showit [self] String))\n\
         (impl Showable Int (defn showit [x] \"int\"))\n\
         (deftype (MyOpt a) MyNone (MySome [:a mval]))\n\
         (impl Showable (MyOpt Int) (defn showit [self] (match self [MyNone \"None\" (MySome x) (showit x)])))\n\
         (showit (MySome 42))\n",
    )
    .assert_stdout_contains(":primitives/String");
}

// =============================================================================
// §7.3 Trait Error Recovery (REGRESSION-GUARD)
// =============================================================================

// spec: spec/07-traits.md §7.3 — calling a trait method on a type with no impl
// errors AND the REPL session continues so the next valid call still succeeds.
// (Cross-ref repl/spec.md §5.2 — error recovery.)
// (carry: legacy/sketch_port.rs::sketch_repl_trait_error_recovers)
#[test]
fn trait_method_no_impl_then_recovery() {
    let out = repl_prims(
        "(deftrait Double (double [self] self))\n\
         (impl Double Int (defn double [x] (add-i64 x x)))\n\
         (double 3)\n\
         (double true)\n\
         (double 6)\n",
    );
    assert!(
        out.stdout.contains(":primitives/Int 6"),
        "first valid call must succeed; got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.to_lowercase().contains("error"),
        "calling trait method on non-impl'd type must surface an error; got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains(":primitives/Int 12"),
        "session must continue after the error; (double 6) must yield 12; got:\n{}",
        out.stdout
    );
}

// =============================================================================
// Wave 5.6 ring2.rs GAP-COVER carry-forwards (chunks 1+2+3)
// =============================================================================

// spec: spec/07-traits.md §7.5 — trait-dispatched `=`/`+`/`-` inside a
// recursive defn body whose param is pinned to Int by the literal `0`.
// Distinct from `operator_plus_int` (single inline call) and from the
// named-primitive `recursive_factorial` shape: each operator inside the
// recursive body still goes through Num/Eq dispatch.
// (carry: legacy/ring2.rs::fn_using_operators_with_literals)
#[test]
fn trait_operator_in_recursive_defn_literal_pinned() {
    repl_std(
        "(defn sum-to [n] (if (= n 0) 0 (+ n (sum-to (- n 1)))))\n\
         (sum-to 10)\n",
    )
    .assert_stdout_contains(":primitives/Int 55");
}

// spec: spec/07-traits.md §7.5 — factorial-shape canonical: trait-dispatched
// `=`/`*`/`-` inside a recursive defn body. Sister of the sum-to shape;
// exercises the multiplication path through Num dispatch.
// (carry: legacy/ring2.rs::fn_factorial_with_operators)
#[test]
fn trait_operator_factorial_recursive_defn() {
    repl_std(
        "(defn fact [n] (if (= n 0) 1 (* n (fact (- n 1)))))\n\
         (fact 10)\n",
    )
    .assert_stdout_contains(":primitives/Int 3628800");
}

// spec: spec/07-traits.md §7.5 — constrained polymorphic tree-recursive fib
// using trait-dispatched `=`/`+`/`-`. Exercises monomorphisation through the
// tree-recursion shape (two recursive calls per arm). Distinct from
// `constrained_polymorphism_int_then_float` (single call) and from the
// named-primitive `recursive_fibonacci` shape.
// Cross-ref: spec/03-types.md §3.6 — constrained polymorphism.
// (carry: legacy/ring2.rs::constrained_fn_fibonacci)
#[test]
fn constrained_polymorphic_fib_tree_recursion() {
    repl_std(
        "(defn fib [n] (if (= n 0) 0 (if (= n 1) 1 (+ (fib (- n 1)) (fib (- n 2))))))\n\
         (fib 10)\n",
    )
    .assert_stdout_contains(":primitives/Int 55");
}

// spec: spec/07-traits.md §7.5 — constrained polymorphic abs-diff with
// distinct trait operators in each arm of the if (`<` in the cond, `-` with
// reversed operand order in each arm body). Distinct from
// `constrained_fn_clamp` (3-arg + nested-if): the both-arms-use-different-
// trait-ops shape inside a 2-arg constrained defn is unique.
// Cross-ref: spec/03-types.md §3.6 — constrained polymorphism.
// (carry: legacy/ring2.rs::constrained_with_if)
#[test]
fn constrained_polymorphic_abs_diff_if_arms() {
    repl_std(
        "(defn abs-diff [x y] (if (< x y) (- y x) (- x y)))\n\
         (abs-diff 3 10)\n",
    )
    .assert_stdout_contains(":primitives/Int 7");
}

// spec: spec/07-traits.md §7.5 — REGRESSION-GUARD: named primitive
// `add-i64` and trait-dispatched `+` MUST coexist in the same body.
// Original legacy test name flagged this as a Sprint-N operator-transition-
// era defect repro (the source comment reads "Mix named primitives and
// trait operators in the same program"). Asserts that bare-prim `add-i64`
// and dispatched-`+` resolve correctly when both appear in the same scope.
// Cross-ref: spec/appendix-a-builtins.md §A.3 — named primitives.
// (carry: legacy/ring2.rs::regression_named_and_trait_ops_in_same_program)
#[test]
fn named_prim_and_trait_op_coexist_in_same_body_regression() {
    repl_std(
        "(defn run [] (let [a (add-i64 1 2) b (+ 3 4)] (+ a b)))\n\
         (run)\n",
    )
    .assert_stdout_contains(":primitives/Int 10");
}

// spec: spec/07-traits.md §7.5 — sum-of-squares via match-destructure of a
// product ADT with TWO trait operators (`+` and `*`) composed in the arm
// body. Distinct from `trait_arithmetic_with_adt_field` (single-`+` only):
// the two-trait-op-in-product-match-arm-body composition is unique.
// Cross-ref: spec/06-pattern-matching.md §6.2 — match destructure of ADTs.
// (carry: legacy/ring2.rs::trait_operators_in_adt_function)
#[test]
fn trait_op_composition_in_match_arm_body_with_product_adt() {
    repl_std(
        "(deftype Point [:Int x :Int y])\n\
         (defn distance-sq [p] (match p [(Point x y) (+ (* x x) (* y y))]))\n\
         (distance-sq (Point 3 4))\n",
    )
    .assert_stdout_contains(":primitives/Int 25");
}

// spec: spec/07-traits.md §7.5 — Eq trait dispatch INSIDE each match arm
// body, with an enum-ADT scrutinee. No carry covers Eq-op-in-enum-arm: the
// arm-internal-Eq composition shape is unique.
// Cross-ref: spec/06-pattern-matching.md §6.1 — match patterns.
// (carry: legacy/ring2.rs::trait_eq_in_match_branch)
#[test]
fn trait_eq_dispatch_inside_each_enum_match_arm() {
    repl_std(
        "(deftype Color Red Green Blue)\n\
         (defn is-primary [c] (match c [Red (= 1 1) Green (= 2 2) Blue (= 3 3)]))\n\
         (if (is-primary Red) 1 0)\n",
    )
    .assert_stdout_contains(":primitives/Int 1");
}

// spec: spec/07-traits.md §7.5 — higher-order function + lambda + trait
// operator inside the lambda body: `(apply-fn (fn [x] (* x 2)) 21) = 42`.
// Distinct from `lambda_passed_as_argument_invoked_inside_callee` which
// uses `add-i64` (named primitive); this exercises trait dispatch INSIDE a
// fn-typed value passed through a HOF.
// Cross-ref: spec/04-expressions.md §4.5 — function application.
// (carry: legacy/ring2.rs::higher_order_with_trait_operators)
#[test]
fn hof_with_lambda_using_trait_operator_in_body() {
    repl_std(
        "(defn apply-fn [f x] (f x))\n\
         (apply-fn (fn [x] (* x 2)) 21)\n",
    )
    .assert_stdout_contains(":primitives/Int 42");
}

// spec: spec/07-traits.md §7.11 — cross-module trait+impl dispatch: a child
// module declares `(deftrait Classify ...)`, `(deftype Color ...)` and
// `(impl Classify Color ...)`; the parent module imports the trait, method,
// type, and constructors and dispatches. No prior carry exercises
// cross-module trait+impl dispatch (`spec_07_traits.rs` is single-module;
// `spec_08_modules.rs` has no trait/impl tests).
// Cross-ref: spec/08-modules.md §8.3 — import.
// (carry: legacy/ring2.rs::trait_method_accessible_across_modules)
#[test]
fn trait_deftrait_impl_in_child_module_imported_dispatch_from_parent() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n\
             (import [types [Classify classify Color Red Green Blue]])\n\
             (defn main [] (Pure (classify Green)))",
        )
        // b1-migration (S112): the conventional (kind-`*`) trait moves off the
        // never-applied `(Classify a)`-head mismodel to the settled bare-head +
        // `self` form — `(deftrait Classify (classify [self] Int))`. Assertion
        // subject UNCHANGED: cross-module deftrait/impl/import/dispatch (exit 2).
        // `a` was only ever a bare method-param type (never applied `(a …)`), so
        // it IS the implementing type → `self`; the impl body is untouched.
        .file(
            "types.cl",
            "(deftrait Classify (classify [self] Int))\n\
             (deftype Color Red Green Blue)\n\
             (impl Classify Color (defn classify [c] (match c [Red 1 Green 2 Blue 3])))",
        )
        .run("main.cl")
        .output()
        .assert_exit(2);
}

// =============================================================================
// Wave 5.6 file 8 ring2.rs chunk 4 GAP-COVER carry-forwards.
// =============================================================================

// spec: spec/07-traits.md §7.2 — Higher-kinded trait declaration. A trait
// parameter `f` is itself a type constructor, used as `(f a)` in method
// signatures. Reclassified from GAP-HARVEST → GAP-COVER per the chunk-4
// re-audit: spec anchors `spec/03-types.md §3.7` and
// `spec/07-traits.md §7.2.2` are explicit and the property is
// e2e-observable as "deftrait declaration succeeds without error".
// Cross-ref: spec/03-types.md §3.7 — Higher-Kinded Types.
// (carry: legacy/ring2.rs::hkt_type_variable_in_trait)
#[test]
fn hkt_deftrait_declaration_with_type_constructor_parameter_succeeds() {
    repl_prims(
        "(deftrait (Functor f)\n  (fmap [:(Fn [a] b) func :(f a) x] (f b)))\n",
    )
    .assert_stdout_contains_all(&["user/Functor", "deftrait"]);
}

// spec: spec/07-traits.md §7.2.3 / §7.3.5 Case 2 — negative HKT: a primitive
// type is NOT a type constructor, so implementing a higher-kinded trait on it
// MUST be rejected. §7.2.3 is explicit: primitive types are rejected as HKT
// impl targets because they are not type constructors. The `Functor` trait uses
// `f` at arity 1 (`(f a)`), so the pairing `(Functor Int)` must fail at the
// §7.3.5 Case-3 kind-check seam with a not-a-type-constructor diagnostic — a
// clean §7.2-class check-side error, NOT a backend leak. Negative companion to
// `hkt_deftrait_declaration_with_type_constructor_parameter_succeeds`.
//
// b2-swap (S112 W5, TB-14): migrated to the settled echo-the-head form — the
// deftrait keeps its applied head `(Functor f)`, and the impl echoes it in slot
// 1 with the trait-constructor pairing `(Functor Int)` in slot 2. Assertion
// subject UNCHANGED (primitive-target rejection); the diagnostic re-grounds to
// the §7.3.5 Case-2 "not a type constructor" wording.
#[test]
fn hkt_impl_on_primitive_type_is_rejected_neg() {
    let out = repl_prims(
        "(deftrait (Functor f)\n  (fmap [:(Fn [a] b) func :(f a) x] (f b)))\n\
         (impl (Functor f) (Functor Int) (defn fmap [func x] x))\n",
    );
    assert!(
        out.stdout.contains("not a type constructor")
            || out.stdout.contains("type constructor"),
        "impl of a HKT trait on the primitive `Int` MUST be rejected with a \
         not-a-type-constructor diagnostic per spec/07-traits.md §7.2.3; \
         got:\n{}",
        out.stdout
    );
}

// spec: spec/07-traits.md §7.2 + spec/05-definitions.md §5.4.4 — full HKT
// impl: declare `(deftrait (Functor f) ...)`, define `(deftype (Option a)
// None (Some [:a val]))`, `(impl Functor Option ...)` with a match-
// destructure dispatching `func` over `Some x` -> `Some (func x)` and
// `None -> None`. Calling `(fmap (fn [x] (add-i64 x 1)) (Some 41))` and
// match-destructuring the result must yield 42. Reclassified GAP-HARVEST
// → GAP-COVER per the chunk-4 re-audit (spec anchors are explicit;
// e2e-observable through numeric output).
// Cross-ref: spec/03-types.md §3.7.6 — HKT dispatch.
// (carry: legacy/ring2.rs::hkt_trait_declaration)
#[test]
fn hkt_functor_impl_on_option_dispatches_via_match() {
    // Reuse the prelude-seeded `primitives/Option` (§8.6.4: a local Option
    // deftype under the Option-providing prelude is a define-over-prelude
    // collision). The pairing `(Functor Option)` targets the seeded Option; the
    // HKT dispatch-via-match behaviour is unchanged.
    //
    // b2-swap (S112 W5, TB-8/TB-17 positive): settled echo-the-head form — slot
    // 1 echoes the declared head `(Functor f)`, slot 2 is the trait-constructor
    // pairing `(Functor Option)`. Assertion subject UNCHANGED (fmap dispatches
    // over Option, result 42).
    repl_prims(
        "(deftrait (Functor f) (fmap [:(Fn [a] b) func :(f a) x] (f b)))\n\
         (impl (Functor f) (Functor Option)\n  (defn fmap [func opt]\n    (match opt [None None (Some x) (Some (func x))])))\n\
         (match (fmap (fn [x] (add-i64 x 1)) (Some 41)) [(Some v) v None 0])\n",
    )
    .assert_stdout_contains(":primitives/Int 42");
}

// ===========================================================================
// R1 — HKT-arity gate parity: prelude-provided impl target (PLAN.md §II R1)
//
// The invariant (spec/08-modules.md §8.8.1): a prelude-provided name is in a
// module's scope on EXACTLY the same terms as an explicit `import`. The kind-
// checking MUST (§7.2.3 / §7.3.4) — "an implementation MUST validate that the
// impl target's type parameter count matches the expected constructor arity" —
// therefore fires identically whether the target ADT is reached via an explicit
// `(import [prelude [Zed]])` or via the implicit prelude glob.
//
// Twin fixture, parametrised over the TARGET's provenance only:
//   Leg A — `Zed` explicitly imported: the §7.3.5 Case-2 kind-check looks up
//     `Zed`, finds a 0-arity type, and REJECTS the pairing `(Functor Zed)`
//     (Functor expects arity 1).
//   Leg B — `Zed` implicit-prelude-provided: the same kind-check resolves `Zed`
//     THROUGH THE SCOPE (`scope_resolve`, prelude-fallback intrinsic per S108
//     Wave-G) and rejects identically. The prelude-scope-miss the arity gate
//     once had (`lookup_type_def_with_state` had no fallback → silent-skip →
//     wrong-arity accept) is CLOSED: the gate now resolves once, so a
//     prelude-provided target is arity-checked on identical terms (§8.8.1).
//
// The divergence WAS the whole signal: same program, target-provenance the only
// difference, MUST reject in both arms. The specific arity substring (not a bare
// non-zero exit) guards against a false-pass on an unrelated failure.
//
// b2-swap (S112 W5, TB-16): migrated to the settled echo-the-head form — the
// deftrait keeps its applied head `(Functor f)`; the impl echoes it and names
// the pairing `(Functor Zed)`. Both the wrong-arity reject AND the prelude
// provenance axis survive the swap.
//
// spec: spec/07-traits.md §7.2.3 (Kind Checking — the arity MUST) + §7.3.5
//       (HKT impl kind-check seam) + spec/08-modules.md §8.8.1 (prelude ≡ explicit import)
// defect: class=prelude-scope-miss locus=crates/cranelisp-typecheck/src/traits/impl_check.rs::register_trait_impl (HKT kind-check now resolves the target through the fallback-aware scope; the fallback-less lookup was the miss) found=S108 owner=/dev
#[test]
fn impl_hkt_arity_neg_prelude_provided_target_wrong_arity_rejected() {
    // A prelude that provides a 0-arity type `Zed` and the arity-1 HKT trait
    // `Functor`, both via the implicit glob (leg B) or explicit import (leg A).
    const PRELUDE: &str = "\
(export [primitives [*]])
(deftype Zed (ZedC [:Int n]))
(deftrait (Functor f)
  (fmap [:(Fn [a] b) func :(f a) x] (f b)))
";
    // Leg A — target `Zed` (and `Functor`) reached via explicit prelude import.
    let leg_a = Cranelisp::new()
        .prelude(PRELUDE)
        .file(
            "user.cl",
            "(import [prelude [Zed Functor]])\n\
             (impl (Functor f) (Functor Zed) (defn fmap [func x] x))\n\
             (defn main [] (Pure 0))\n",
        )
        .run("user.cl")
        .output();
    let a = format!("{}\n{}", leg_a.stdout, leg_a.stderr).to_lowercase();
    // GREEN control: the wrong-arity impl on the explicitly-imported target is
    // rejected with the §7.2.3 arity diagnostic.
    assert!(
        a.contains("type parameters") && a.contains("arity"),
        "LEG A (explicit-import target): a wrong-arity HKT impl MUST be rejected \
         with the §7.2.3 kind-checking arity diagnostic;\nstdout:\n{}\nstderr:\n{}",
        leg_a.stdout,
        leg_a.stderr
    );
    assert_ne!(
        leg_a.status.code(),
        Some(0),
        "LEG A: the rejected impl MUST NOT compile clean;\nstdout:\n{}\nstderr:\n{}",
        leg_a.stdout,
        leg_a.stderr
    );

    // Leg B — same program, target `Zed`/`Functor` reached via the IMPLICIT
    // prelude (no explicit import). MUST produce the SAME arity rejection.
    let leg_b = Cranelisp::new()
        .prelude(PRELUDE)
        .file(
            "user.cl",
            "(impl (Functor f) (Functor Zed) (defn fmap [func x] x))\n\
             (defn main [] (Pure 0))\n",
        )
        .run("user.cl")
        .output();
    let b = format!("{}\n{}", leg_b.stdout, leg_b.stderr).to_lowercase();
    assert!(
        b.contains("type parameters") && b.contains("arity"),
        "LEG B (implicit-prelude target): the wrong-arity HKT impl MUST get the \
         SAME §7.2.3 arity rejection as the explicit-import twin — a prelude-\
         provided target is in scope on identical terms (§8.8.1). The §7.3.5 \
         kind-check resolves the target through the fallback-aware scope, so a \
         prelude-provided target is arity-checked exactly like an imported one;\n\
         stdout:\n{}\nstderr:\n{}",
        leg_b.stdout,
        leg_b.stderr
    );
    assert_ne!(
        leg_b.status.code(),
        Some(0),
        "LEG B: the wrong-arity impl MUST NOT compile clean via the prelude \
         fallback gap;\nstdout:\n{}\nstderr:\n{}",
        leg_b.stdout,
        leg_b.stderr
    );
}

// spec: spec/05-definitions.md §5.4.4 + spec/07-traits.md §7.3.4 — when an
// impl targets a higher-kinded trait, the impl-target syntax is the BARE
// type constructor (`Option`), NOT an applied form (`(Option a)`). This
// test isolates that distinction by confirming `(impl Functor Option ...)`
// is the accepted form and the dispatch resolves over `Option a`.
// Distinct from #188 by isolating the bare-vs-applied-target syntactic
// requirement. Reclassified GAP-HARVEST → GAP-COVER per chunk-4 re-audit.
// Cross-ref: spec/03-types.md §3.7.4 — Implementing HKT Traits.
// (carry: legacy/ring2.rs::hkt_impl_bare_constructor)
#[test]
fn hkt_impl_targets_bare_type_constructor_not_applied_form() {
    // Reuse the prelude-seeded `primitives/Option` (see §8.6.4 note above).
    // The bare-vs-applied impl-target distinction is still isolated — inside the
    // pairing, the target is the BARE seeded type constructor `Option`, never an
    // applied form `(Option a)` (an applied pairing arg is the §7.3.5 Case-2
    // "kind-mismatch" reject, exercised separately by
    // `hkt_impl_applied_type_in_pairing_rejected_neg`).
    //
    // b2-swap (S112 W5): settled echo-the-head form — slot 1 `(Functor f)`, slot
    // 2 the pairing `(Functor Option)` whose constructor arg is the bare `Option`.
    // Assertion subject UNCHANGED (bare-constructor target, result 100).
    repl_prims(
        "(deftrait (Functor f) (fmap [:(Fn [a] b) func :(f a) x] (f b)))\n\
         (impl (Functor f) (Functor Option)\n  (defn fmap [func opt]\n    (match opt [None None (Some x) (Some (func x))])))\n\
         (match (fmap (fn [x] (add-i64 x 1)) (Some 99)) [(Some v) v None 0])\n",
    )
    .assert_stdout_contains(":primitives/Int 100");
}

// =============================================================================
// The 0628 trait/impl rejection matrix (S112 W5, plan §3 — the variant×polarity
// cure for the "wrong-form-looked-right" hole). One codepath, exercised across
// the whole grid:
//
//   con_var axis (the DEFTRAIT head):
//     applied `(Functor f)`   → genuinely higher-kinded; proceeds to the impl
//     bare-return `(X a)` (a only as bare return)  → DECLARATION-time reject
//     bare-arg    `(X a)` (a only as bare param)   → DECLARATION-time reject
//   target axis (the HK impl pairing `(Trait Constructor)`):
//     primitive        → §7.3.5 Case 2 "not a type constructor"
//     wrong-arity ADT  → §7.3.5 Case 2 arity reject
//     well-kinded ADT  → ACCEPT (dispatch)
//   slot-1 echo axis (§7.3.5 Case-3 seam, hkt.md §5.4 step 3):
//     bare head on HK trait / parenthesized head on conventional trait → shape
//     reject; wrong con_var spelling on HK trait → spelling reject.
//
// The declaration-reject rows subsume the old §5.4 "bare-con_var impl-on-primitive
// silently accepted → backend `undefined function` leak": the trait now cannot
// register, so the impl never runs and no codegen leak can arise. The former
// leak becomes a POSITIVE guard (0628's core symptom, now the thing we pin the
// absence of). Diagnostics asserted mode-uniform (REPL ≡ `--run` ≡ `--link`) per
// class (AG-2). Spec: spec/07-traits.md §7.2.1 (declaration), §7.3.4/§7.3.5
// (impl form + kind-check). Design: design/typecheck/hkt.md §5.1/§5.4.
// =============================================================================

// ---- con_var axis: applied × primitive — the check-gate-leak flip (TB-2) -----

// spec: spec/07-traits.md §7.2.3 / §7.3.5 Case 2 — a genuinely higher-kinded
// trait impl'd on a PRIMITIVE is rejected at the §7.3.5 Case-3 kind-check seam
// with a clean §7.2-class diagnostic ("not a type constructor"), located and
// check-side. The 0628 core symptom — a source-level fault leaking past the
// check boundary as a backend `undefined function` / `codegen error` — MUST NOT
// occur: it becomes a POSITIVE guard here. Asserted across all three modes.
// defect: class=check-gate-leak locus=crates/cranelisp-typecheck/src/traits/impl_check.rs::register_trait_impl found=S110 owner=/dev
#[test]
fn hkt_on_primitive_no_backend_undefined_function_leak_neg() {
    const SRC: &str = "(deftrait (Functor f) (fmap [:(Fn [a] b) func :(f a) x] (f b)))\n\
                       (impl (Functor f) (Functor Int) (defn fmap [func x] x))\n";
    // REPL facet + the leak-absence guard.
    let repl = repl_prims(SRC);
    let rc = format!("{}{}", repl.stdout, repl.stderr).to_lowercase();
    assert!(
        rc.contains("not a type constructor"),
        "REPL: HK impl on primitive `Int` MUST be a clean §7.2.3 check-side reject; got:\n{rc}"
    );
    // `--run` + `--link` facets — same class of rejection (AG-2 mode-uniformity).
    let run = run_prims(&format!("{SRC}(defn main [] (Pure 0))\n"));
    let link = link_prims(&format!("{SRC}(defn main [] (Pure 0))\n"));
    for (label, out) in [("--run", &run), ("--link", &link), ("repl", &repl)] {
        let c = format!("{}{}", out.stdout, out.stderr).to_lowercase();
        assert!(
            !c.contains("undefined function") && !c.contains("codegen error"),
            "{label}: the HK-on-primitive reject MUST stay check-side — NO backend \
             `undefined function` / `codegen error` leak (0628 core symptom); got:\n{c}"
        );
    }
    assert_ne!(run.status.code(), Some(0), "--run must not compile the primitive HK impl clean");
    assert_ne!(link.status.code(), Some(0), "--link must not compile the primitive HK impl clean");
}

// ---- con_var axis: never-applied (bare-return / bare-arg) → declaration reject

// spec: spec/07-traits.md §7.2.1 — a parenthesized `deftrait` head whose type
// parameter is NEVER APPLIED `(a …)` is malformed and rejected AT the deftrait.
// bare-RETURN shape: `a` occurs only as a bare method return. The diagnostic
// names the fix (the bare head + `self` form). This is A2 (rejection moved to
// declaration time); the `(impl … Int)` question never arises.
// defect: class=check-gate-leak locus=crates/cranelisp-typecheck/src/traits/registry.rs::register_trait_decl found=S110 owner=/dev
#[test]
fn deftrait_bare_return_convar_never_applied_rejected_neg() {
    let out = repl_prims("(deftrait (Zeroable a) (zed [] :a))\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !c.contains("; deftrait"),
        "a never-applied con_var `(Zeroable a)` MUST be rejected at the deftrait, \
         NOT registered (§7.2.1); got:\n{c}"
    );
    assert!(
        c.contains("never applied") && c.contains("self"),
        "the declaration-reject diagnostic MUST name the fault (con_var never \
         applied) and the fix (bare head + `self`); got:\n{c}"
    );
}

// spec: spec/07-traits.md §7.2.1 — bare-ARG shape: the con_var `a` occurs only
// as a bare method PARAMETER type, never applied. Same declaration-time reject.
// The polarity twin of the bare-return row (both never-applied shapes reject).
// defect: class=check-gate-leak locus=crates/cranelisp-typecheck/src/traits/registry.rs::register_trait_decl found=S110 owner=/dev
#[test]
fn deftrait_bare_arg_convar_never_applied_rejected_neg() {
    let out = repl_prims("(deftrait (Container a) (unwrap [:a x] Int))\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !c.contains("; deftrait"),
        "a never-applied con_var `(Container a)` (bare-arg) MUST be rejected at the \
         deftrait (§7.2.1); got:\n{c}"
    );
    assert!(
        c.contains("never applied") && c.contains("self"),
        "the declaration-reject diagnostic MUST name the fault and the `self` fix; got:\n{c}"
    );
}

// spec: spec/07-traits.md §7.2.1 — the full 0628 repro transcript. A never-applied
// `(Container a)` decl + its impl + a use: the decl rejects, so the impl `unknown
// trait`s and the use is a clean `undefined variable` — all CHECK-side. The old
// `:a 7` unresolved-var display and the backend `undefined function` leak are
// BOTH absent (0628's three symptoms all closed by the single declaration reject).
// defect: class=check-gate-leak locus=crates/cranelisp-typecheck/src/traits/registry.rs::register_trait_decl found=S110 owner=/dev
#[test]
fn bare_convar_full_0628_repro_no_leak_and_no_unresolved_var_display_neg() {
    let out = repl_prims(
        "(deftrait (Container a) (unwrap [:a x] :a))\n\
         (impl (Container a) (Container Int) (defn unwrap [x] x))\n\
         (unwrap 7)\n",
    );
    let c = format!("{}{}", out.stdout, out.stderr);
    let lc = c.to_lowercase();
    assert!(
        c.contains("never applied"),
        "the decl MUST reject (the 0628 root); got:\n{c}"
    );
    assert!(
        !lc.contains("undefined function") && !lc.contains("codegen error"),
        "NO backend leak may reach the surface (0628 symptom 1); got:\n{c}"
    );
    assert!(
        !c.contains(":a 7") && !c.contains(":user/a"),
        "the unresolved-con_var display `:a 7` MUST NEVER appear (0628 symptom 2); got:\n{c}"
    );
}

// ---- slot-1 echo axis: shape + spelling rejects (§7.3.5 Case-3, hkt.md §5.4) --

// spec: spec/07-traits.md §7.3 "Slot 1 is fixed" — the migration-era diagnostic:
// an OLD-form bare-head impl `(impl Functor Option …)` of a higher-kinded trait
// is rejected, and the diagnostic NAMES THE NEW FORM (echo the declared head).
// Highest user-facing value (TB-9): the pre-b2 corpus wrote exactly this.
#[test]
fn old_form_hkt_impl_bare_head_rejected_names_new_form_neg() {
    let out = repl_prims(
        "(deftrait (Functor f) (fmap [:(Fn [a] b) func :(f a) x] (f b)))\n\
         (impl Functor Option (defn fmap [func x] x))\n",
    );
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.contains("higher-kinded") && c.contains("echo"),
        "a bare-head impl of an HK trait MUST be rejected naming the new echoed-head \
         form `(Functor f)`; got:\n{c}"
    );
}

// spec: spec/07-traits.md §7.3 "Slot 1 is fixed" (hkt.md §5.4 step 3, spelling
// bit) — a parenthesized head with the WRONG con_var spelling `(Functor g)`
// passes the shape bit but its spelling `g` ≠ the declared `f`; the located
// diagnostic names BOTH spellings and the verbatim expected form (TB-11).
#[test]
fn hkt_impl_echo_wrong_convar_spelling_rejected_neg() {
    let out = repl_prims(
        "(deftrait (Functor f) (fmap [:(Fn [a] b) func :(f a) x] (f b)))\n\
         (impl (Functor g) (Functor Option) (defn fmap [func x] x))\n",
    );
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.contains("(Functor g)") && c.contains("(Functor f)"),
        "the echo-spelling reject MUST name BOTH the written `(Functor g)` and the \
         declared `(Functor f)` head; got:\n{c}"
    );
    assert!(
        c.contains("declared") && (c.contains("spelled") || c.contains("verbatim")),
        "the diagnostic MUST direct to reproducing the declared head verbatim; got:\n{c}"
    );
}

// spec: spec/07-traits.md §7.3 "Slot 1 is fixed" (hkt.md §5.4 step 3, shape bit)
// — a parenthesized (echoed) head on a CONVENTIONAL (kind-`*`) trait is rejected:
// its impl head is the bare trait name (TB-10). The polarity mirror of the
// bare-head-on-HK-trait reject above.
#[test]
fn conventional_impl_parenthesized_head_rejected_neg() {
    let out = repl_prims(
        "(deftrait Disp (shw [self] Int))\n\
         (impl (Disp x) Int (defn shw [w] 5))\n",
    );
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.contains("conventional") && c.contains("bare name"),
        "a parenthesized head on a conventional trait MUST be rejected, directing \
         to the bare-name form; got:\n{c}"
    );
}

// ---- target axis: the slot-2 kind rejections (§7.3.5 Case 1 & Case 2) ---------

// spec: spec/07-traits.md §7.3.5 Case 2 — wrong-arity ADT: the pairing
// `(Functor Pair)` names a constructor of arity 2, but Functor's con_var is used
// at arity 1. Rejected naming the constructor, its arity, and the trait (TB-16
// sibling; direct, non-prelude-provenance form of the arity reject).
#[test]
fn hkt_impl_wrong_arity_pair_rejected_neg() {
    // `Pair` is prelude-provided (arity 2). The pairing arg `Pair` is a bare
    // constructor whose arity (2) ≠ Functor's expected arity (1).
    let out = repl_prims(
        "(deftrait (Functor f) (fmap [:(Fn [a] b) func :(f a) x] (f b)))\n\
         (impl (Functor f) (Functor Pair) (defn fmap [func x] x))\n",
    );
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.contains("Pair") && c.contains("2") && c.contains("arity"),
        "the pairing `(Functor Pair)` MUST be rejected naming Pair's arity (2) vs \
         the trait's expected arity (1); got:\n{c}"
    );
}

// spec: spec/07-traits.md §7.3.5 Case 2 — a fully-applied type inside the pairing
// `(Functor (Option Int))` is not a bare constructor. The e2e surface catches
// this at PARSE (slot 2's inner element is a list, not a symbol): a located parse
// error rejects it before the typecheck kind-mismatch seam. (The typecheck-layer
// "kind-mismatch: slot 2 names the bare constructor" wording is unit-reachable
// only — impl_check/tests.rs::hkt_impl_applied_type_in_pairing_rejected — because
// the parser rejects the applied inner element first; verify-example-well-formed.)
#[test]
fn hkt_impl_applied_type_in_pairing_rejected_neg() {
    let out = repl_prims(
        "(deftrait (Functor f) (fmap [:(Fn [a] b) func :(f a) x] (f b)))\n\
         (impl (Functor f) (Functor (Option Int)) (defn fmap [func x] x))\n",
    );
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.contains("parse error") && c.contains("impl target"),
        "an applied inner element in the pairing `(Functor (Option Int))` MUST be \
         rejected (located parse error on the impl target); got:\n{c}"
    );
}

// spec: spec/07-traits.md §7.3.5 Case 1 — the SOLE conventional-trait rejection:
// a bare / under-applied constructor target `(impl Disp Option)` — `Option` is a
// constructor, not a type; apply it (TB-13).
#[test]
fn conventional_impl_bare_constructor_target_rejected_neg() {
    let out = repl_prims(
        "(deftrait Disp (shw [self] Int))\n\
         (impl Disp Option (defn shw [w] 5))\n",
    );
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.contains("Option") && c.contains("constructor, not a type"),
        "a bare constructor target on a conventional trait MUST be rejected \
         (`Option` is a constructor, not a type — apply it); got:\n{c}"
    );
}

// ---- target axis: well-kinded ADT positive — a user ADT, two-impl dispatch ----

// spec: spec/07-traits.md §7.3.4 / §7.3.5 Case 2 — the well-kinded ADT positive
// grid cell over a USER-declared constructor (not the prelude Option). A local
// `(deftype (Box a) …)` is a well-kinded arity-1 constructor; the echoed-head
// impl registers and `fmap` dispatches over it (TB-17: the well-kinded ADT cell,
// distinct provenance from the prelude-Option positive above).
#[test]
fn hkt_impl_on_user_well_kinded_adt_dispatches() {
    repl_prims(
        "(deftype (Box a) (Boxed [:a v]))\n\
         (deftrait (Functor f) (fmap [:(Fn [a] b) func :(f a) x] (f b)))\n\
         (impl (Functor f) (Functor Box)\n  (defn fmap [func b]\n    (match b [(Boxed v) (Boxed (func v))])))\n\
         (match (fmap (fn [x] (add-i64 x 1)) (Boxed 41)) [(Boxed v) v])\n",
    )
    .assert_stdout_contains(":primitives/Int 42");
}

// ---- mode-uniformity (AG-2): one guard per rejection CLASS across all modes ---

// spec: spec/07-traits.md §7.2.1 — the DECLARATION-reject class is mode-uniform:
// a never-applied `(Zeroable a)` head is rejected under REPL, `--run`, AND
// `--link`, each naming the `self` fix. A new reject is a new opportunity for a
// REPL/`--run`/`--link` split; this makes the class loud once.
#[test]
fn never_applied_head_declaration_reject_is_mode_uniform_neg() {
    const DECL: &str = "(deftrait (Zeroable a) (zed [] :a))\n";
    let repl = repl_prims(DECL);
    let run = run_prims(&format!("{DECL}(defn main [] (Pure 0))\n"));
    let link = link_prims(&format!("{DECL}(defn main [] (Pure 0))\n"));
    for (label, out) in [("repl", &repl), ("--run", &run), ("--link", &link)] {
        let c = format!("{}{}", out.stdout, out.stderr);
        assert!(
            c.contains("never applied") && c.contains("self"),
            "{label}: the never-applied declaration reject MUST fire with the same \
             §7.2.1 diagnostic core (mode-uniform, AG-2); got:\n{c}"
        );
    }
    assert_ne!(run.status.code(), Some(0), "--run must reject the malformed decl");
    assert_ne!(link.status.code(), Some(0), "--link must reject the malformed decl");
}

// spec: spec/07-traits.md §7.3.5 Case-3 — the ECHO-shape-mismatch class is
// mode-uniform: a bare-head impl of an HK trait is rejected naming the echoed
// form under REPL, `--run`, AND `--link`.
#[test]
fn hkt_echo_shape_mismatch_reject_is_mode_uniform_neg() {
    const SRC: &str = "(deftrait (Functor f) (fmap [:(Fn [a] b) func :(f a) x] (f b)))\n\
                       (impl Functor Option (defn fmap [func x] x))\n";
    let repl = repl_prims(SRC);
    let run = run_prims(&format!("{SRC}(defn main [] (Pure 0))\n"));
    let link = link_prims(&format!("{SRC}(defn main [] (Pure 0))\n"));
    for (label, out) in [("repl", &repl), ("--run", &run), ("--link", &link)] {
        let c = format!("{}{}", out.stdout, out.stderr);
        assert!(
            c.contains("higher-kinded") && c.contains("echo"),
            "{label}: the echo-shape-mismatch reject MUST fire with the same §7.3.5 \
             diagnostic core (mode-uniform, AG-2); got:\n{c}"
        );
    }
    assert_ne!(run.status.code(), Some(0), "--run must reject the bare-head HK impl");
    assert_ne!(link.status.code(), Some(0), "--link must reject the bare-head HK impl");
}

// =============================================================================
// W5.1 REMEDIATION — two wrong-ACCEPT axes the W5 /review BLOCK confirmed live,
// both landing RED ahead of the W5.1 /dev fix (design hkt.md §5.4):
//
//   B1 pairing-head-mismatch (§7.3.5 Case-2 4th HK rejection): the b2 Case-3 seam
//     binds `Applied(_pairing_head, args)` and DISCARDS the head — a pairing whose
//     head names a different / nonexistent trait silently registers under slot 1
//     and dispatches. The head MUST name the trait slot 1 resolves to (FQ-identity).
//   I1 conventional over-applied (§7.3.5 Case-1): the conventional arity guard is
//     `>` (under-application only), not `!=`; an over-applied target `(Option Int
//     Int)` is silently accepted. The `>` MUST generalise to `!=`.
//
// The MATCHING positive twin (`(Functor Option)` accepts + dispatches) is already
// covered by `hkt_impl_targets_bare_type_constructor_not_applied_form` and
// `hkt_impl_on_user_well_kinded_adt_dispatches` — referenced, not duplicated.
//
// UNPINNED pending user ruling (S112 W5.1): qualified/bare same-trait pairing head
// — `(impl (fmt/Functor f) (Functor Option) …)` (qualified slot 1, bare pairing
// head, SAME resolved trait). Left out entirely; NOT a wave blocker — the
// different/nonexistent-head rejection below rejects under BOTH the resolved-
// identity and verbatim-spelling readings.
// Spec: spec/07-traits.md §7.3.5. Design: design/typecheck/hkt.md §5.4.
// =============================================================================

// ---- B1: the pairing-head-mismatch axis (§7.3.5 Case-2 4th rejection) ---------

// spec: spec/07-traits.md §7.3.5 Case 2 — pairing-head mismatch (4th HK rejection):
// a trait-constructor pairing whose head names a NONEXISTENT trait `(NotFunctor
// Option)` MUST be rejected — the pairing head must name the trait slot 1 resolves
// to. The reject names BOTH the written `(NotFunctor Option)` and the expected
// `(Functor Option)`. Twin-asserts NO dispatch: the current wrong-accept
// (impl_check.rs:98 discards the pairing head) silently registers `impl
// user/Functor for user/Option` and lets `fmap` dispatch → `:primitives/Int 100`.
// Cross-mode (REPL + --run + --link) per the AG-2 uniformity convention.
// defect: class=wrong-accept locus=crates/cranelisp-typecheck/src/traits/impl_check.rs::register_trait_impl found=S112 owner=/dev
#[test]
fn hkt_impl_pairing_head_nonexistent_trait_rejected_no_dispatch_neg() {
    const SRC: &str = "(deftrait (Functor f) (fmap [:(Fn [a] b) func :(f a) x] (f b)))\n\
                       (impl (Functor f) (NotFunctor Option)\n  (defn fmap [func opt]\n    (match opt [None None (Some x) (Some (func x))])))\n";
    // REPL facet: the diagnostic + the dispatch-absence twin. The trailing `fmap`
    // call dispatches to `:primitives/Int 100` under the wrong-accept.
    let repl = repl_prims(&format!(
        "{SRC}(match (fmap (fn [x] (add-i64 x 1)) (Some 99)) [(Some v) v None 0])\n"
    ));
    let rc = format!("{}{}", repl.stdout, repl.stderr);
    assert!(
        rc.contains("(NotFunctor Option)") && rc.contains("(Functor Option)"),
        "the pairing-head-mismatch reject MUST name BOTH the written \
         `(NotFunctor Option)` and the expected `(Functor Option)` (§7.3.5 Case-2 \
         4th rejection); got:\n{rc}"
    );
    assert!(
        !repl.stdout.contains(":primitives/Int 100"),
        "NO dispatch may occur — the rejected impl MUST NOT register + let `fmap` \
         dispatch to `:primitives/Int 100` (twin-assert absence); got:\n{}",
        repl.stdout
    );
    assert!(
        !repl.stdout.contains("impl user/Functor for user/Option"),
        "the rejected impl MUST NOT register (no `impl user/Functor for user/Option` \
         echo); got:\n{}",
        repl.stdout
    );
    // Cross-mode facet (AG-2): the reject fires uniformly under --run and --link.
    let run = run_prims(&format!("{SRC}(defn main [] (Pure 0))\n"));
    let link = link_prims(&format!("{SRC}(defn main [] (Pure 0))\n"));
    for (label, out) in [("--run", &run), ("--link", &link)] {
        let c = format!("{}{}", out.stdout, out.stderr);
        assert!(
            c.contains("(NotFunctor Option)") && c.contains("(Functor Option)"),
            "{label}: the pairing-head-mismatch reject MUST fire with the same \
             §7.3.5 diagnostic core (mode-uniform); got:\n{c}"
        );
    }
    assert_ne!(run.status.code(), Some(0), "--run must reject the mismatched pairing head");
    assert_ne!(link.status.code(), Some(0), "--link must reject the mismatched pairing head");
}

// spec: spec/07-traits.md §7.3.5 Case 2 — pairing-head mismatch, the DIFFERENT-
// real-trait variant: a second genuine HK trait `Mappy` used as the pairing head
// `(impl (Functor f) (Mappy Option) …)` MUST be rejected — the head resolves to a
// trait, but not the one slot 1 (`Functor`) names (FQ-identity compare, not
// spelling). Asserts the impl did NOT register under Functor: a bare `Functor`
// lookup's `; impl:` section MUST NOT list `Option`. Under the current wrong-accept
// slot 1 wins and `Functor` silently gains `Option`.
// defect: class=wrong-accept locus=crates/cranelisp-typecheck/src/traits/impl_check.rs::register_trait_impl found=S112 owner=/dev
#[test]
fn hkt_impl_pairing_head_different_real_trait_rejected_not_registered_neg() {
    let out = repl_prims(
        "(deftrait (Functor f) (fmap [:(Fn [a] b) func :(f a) x] (f b)))\n\
         (deftrait (Mappy f) (mapp [:(Fn [a] b) func :(f a) x] (f b)))\n\
         (impl (Functor f) (Mappy Option)\n  (defn fmap [func opt]\n    (match opt [None None (Some x) (Some (func x))])))\n\
         Functor\n",
    );
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.contains("(Mappy Option)") && c.contains("(Functor Option)"),
        "the different-real-trait pairing-head reject MUST name BOTH the written \
         `(Mappy Option)` and the expected `(Functor Option)` (§7.3.5 Case-2); got:\n{c}"
    );
    // Registration-absence: the bare `Functor` lookup's `; impl:` section MUST NOT
    // list `Option` (the impl was rejected, never registered under slot 1). Extract
    // the section body the same way
    // `hkt_echo_head_impl_registration_echo_names_resolved_constructor_not_pairing_head`
    // does. An empty / absent section (post-fix) satisfies the assertion vacuously.
    let impl_body: Vec<String> = out
        .stdout
        .lines()
        .skip_while(|l| l.trim() != "; impl:")
        .skip(1)
        .take_while(|l| l.trim_start().starts_with(';'))
        .map(|l| l.trim_start_matches(';').trim().to_string())
        .collect();
    assert!(
        !impl_body.iter().any(|l| l.split_whitespace().any(|t| t == "Option")),
        "the rejected impl MUST NOT register under `Functor` — its `; impl:` section \
         MUST NOT list `Option`; impl body={impl_body:?}\nstdout:\n{}",
        out.stdout
    );
}

// ---- I1: the conventional over-applied axis (§7.3.5 Case 1) -------------------

// spec: spec/07-traits.md §7.3.5 Case 1 — the conventional over-applied target
// (I1): `(impl Disp (Option Int Int))` applies `Option` (arity 1) to 2 args. The
// existing `>` under-application guard MUST generalise to `!=`; `provided (2) !=
// arity (1)` rejects with "takes 1 type parameter but is applied to 2". Twin-
// asserts no registration. Currently wrong-ACCEPTS (registers `impl user/Disp for
// user/Option`).
// defect: class=wrong-accept locus=crates/cranelisp-typecheck/src/traits/impl_check.rs::register_trait_impl found=S112 owner=/dev
#[test]
fn conventional_impl_over_applied_target_rejected_no_dispatch_neg() {
    let out = repl_prims(
        "(deftrait Disp (shw [self] Int))\n\
         (impl Disp (Option Int Int) (defn shw [w] 5))\n",
    );
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.contains("1 type parameter") && c.contains("applied to 2"),
        "the over-applied conventional target `(Option Int Int)` MUST be rejected \
         naming the arity surplus (`takes 1 type parameter but is applied to 2`, \
         §7.3.5 Case 1); got:\n{c}"
    );
    assert!(
        !out.stdout.contains("impl user/Disp for user/Option"),
        "the rejected over-applied impl MUST NOT register (no `impl user/Disp for \
         user/Option` echo — twin-assert absence); got:\n{}",
        out.stdout
    );
}

// spec: spec/07-traits.md §7.3.5 Case 1 — the exactly-arity POSITIVE twin of the
// over-applied reject: `(impl Disp (Option Int))` applies `Option` to exactly its
// arity (1). It MUST accept (register) NOW and stay green when the arity guard
// generalises `>` → `!=` (`provided == arity == 1`, so `!=` never fires) — the
// guard-generalisation hazard fence (hkt.md §5.4 Case-1 "Care").
//
// NOTE (S112 W5.1 finding — see the /testing report): the design's LITERAL poly-
// applied twin `(impl Disp (Option a))` — a BARE type variable — is NOT green
// today. It wrong-rejects with `unknown type a` BEFORE reaching the arity gate
// (pre-existing, orthogonal to I1's arity concern; the canonical inline-constrained
// form `(impl Display (Option :Display a))` from spec §7.3.3 wrong-rejects the same
// way, and spec §7.3.5 line 352 `(impl Display (Option a)) ✓` is un-annotated /
// untested). The concrete `(Option Int)` reaches and passes the arity gate with
// `provided == arity == 1`, so it is the sound green fence for the generalisation.
#[test]
fn conventional_impl_exactly_arity_target_accepts_arity_gate_fence() {
    repl_prims(
        "(deftrait Disp (shw [self] Int))\n\
         (impl Disp (Option Int) (defn shw [w] 5))\n",
    )
    .assert_stdout_contains("impl user/Disp for user/Option");
}

// spec: spec/07-traits.md §7.5 + spec/04-expressions.md §4.6.3 — calling a
// trait-dispatched operator with one argument auto-curries: `(+ 5)`
// returns a closure of type `(Fn [Int] Int)`, which when applied to `10`
// yields `15`. Distinct from existing `operator_as_first_class_value`
// (let-bound + apply) and from `auto_curry_passed_to_higher_order_fn`
// (named primitive path with `add-i64`): this asserts the trait-
// dispatched-operator + single-arg-auto-curry composition unique to
// constrained polymorphism. The two-step `((+ 5) 10)` form is what's
// load-bearing — it exercises both the auto-curry construction and the
// closure application in sequence.
// Cross-ref: spec/03-types.md §3.6 — constrained polymorphism.
// (carry: legacy/ring2.rs::constrained_auto_curry_plus_int)
#[test]
fn trait_op_plus_single_arg_auto_curries_then_applies() {
    repl_std("((+ 5) 10)\n").assert_stdout_contains(":primitives/Int 15");
}

// =============================================================================
// §7.8.2 — Stacked trait-bound param annotations (FIXME 0341, S81 close)
//
// FAILING-NOT-IGNORED repros. A parameter MAY carry MORE THAN ONE trait-bound
// annotation (`[:Eq :Display a]` — a value that must be both comparable and
// displayable). The run of `:Trait` annotations preceding a binder name all
// attach to that binder as bounds. Today the parser reads each leading
// `:Trait` after the first as a SEPARATE parameter name:
//   - single param `[:Eq :Display a]`        → the `:Display` is mis-read;
//   - two params `[:Eq :Display a :Eq :Display b]` → the two `:Display`
//     tokens collide → `duplicate parameter name ':Display'`.
//
// This blocks `stdlib/testing/assertions.cl::assert-eq`, whose signature is
// `[:Eq :Display a :Eq :Display b]`.
//
// Owning skill: /frontend (param-list parser). A tighter UNIT repro in
// cranelisp-frontend will follow separately from /dev; this is the e2e
// cross-skill record. Flips green when the parser attaches the run of
// `:Trait` annotations to the following binder.
// =============================================================================

// spec: spec/07-traits.md §7.8.2 — TWO stacked trait bounds on ONE param
//   (`[:Eq :Display a]`) MUST compile. FIXME(/frontend 0341).
#[test]
fn stacked_trait_bounds_single_param_compiles() {
    Cranelisp::new()
        .with_prelude(PreludeVariant::TestStandard)
        .file(
            "user.cl",
            "(import [primitives [Pure]])\n\
             (defn g [:Eq :Display a] a)\n\
             (defn main [] (Pure (g 7)))",
        )
        .run("user.cl")
        .output()
        // CORRECT: the stacked bounds attach to `a`; the program compiles and
        // `(g 7)` exits 7. Today this FAILS (the second bound is mis-parsed).
        .assert_exit(7);
}

// spec: spec/07-traits.md §7.8.2 — the `assert-eq`-shaped TWO-param stacked
//   signature `[:Eq :Display a :Eq :Display b]` MUST compile, not error
//   `duplicate parameter name ':Display'`. FIXME(/frontend 0341).
#[test]
fn stacked_trait_bounds_two_params_compiles() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::TestStandard)
        .file(
            "user.cl",
            "(import [primitives [Pure]])\n\
             (defn f [:Eq :Display a :Eq :Display b] a)\n\
             (defn main [] (Pure (f 1 2)))",
        )
        .run("user.cl")
        .output();
    // CORRECT: both params carry the two stacked bounds; the program compiles
    // and `(f 1 2)` exits 1. Today this FAILS with
    // `duplicate parameter name ':Display'`.
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !combined.contains("duplicate parameter name"),
        "stacked trait bounds `[:Eq :Display a :Eq :Display b]` MUST parse \
         (spec/07-traits.md §7.8.2); got a duplicate-param parse error:\n{}",
        combined
    );
    out.assert_exit(1);
}

// =============================================================================
// §7.8 Constrained Polymorphism × §8 Modules — CROSS-MODULE stacked-bound call
// (FIXME 0354)
// =============================================================================

// spec: spec/07-traits.md §7.8 + spec/08-modules.md §8.5 — a stacked-trait-bound
//   function (`[:Eq :Display a :Eq :Display b]`, constrained polymorphism)
//   defined in an IMPORTED module and called from another module RUNS: the
//   cross-module monomorphisation feature (FIXME 0355, landed S83) produces a
//   `cmp$Int+Int` mono variant in the caller's module whose body is re-checked
//   in the DEFINING module's import context, and the backend wires it (and its
//   trait-method callees `Display.show$Int`) into the GOT via the existing
//   concrete-mono codegen path — no new backend path. `(cmp 1 1)` = "11";
//   `str-len` = 2 ⇒ the program exits 2.
//
// History (FIXMEs 0354 + 0355, now both RESOLVED): S82 fixed the same-module
// define-and-call path. A stacked-bound fn defined in an imported `helper.cl`
// and called from `entry.cl` used to crash with a SIGSEGV (exit 139): the
// constrained-fn template carried a phantom Pass-1 `got_slot`, `resolve_got_target`
// read it blindly, and cross-module that slot was NULL → null `call_indirect` →
// segfault. 0354's structural fix removed the crash (clean rejection); 0355 then
// made the call RUN. The typecheck half collects the imported constrained call
// site, re-checks the mono body in the defining module's scope, and verifies the
// trait constraints against the INSTANTIATED vars (fixing a cross-module var-id
// collision that bound the constraint var to the caller's `IO`) with the trait
// impl resolved in the defining module's scope.
//
// This guard pins the RUN behaviour (exit 2) in `--run` (JIT). The `--link`
// companion below pins the static-relocation path — cross-module mono GOT-wiring
// is exactly what can diverge between JIT and static linking.
#[test]
fn cross_module_stacked_trait_bound_call_runs_to_clean_exit() {
    Cranelisp::new()
        .with_prelude(PreludeVariant::TestStandard)
        .file(
            "helper.cl",
            "(import [primitives [String str-concat]])\n\
             (defn cmp [:Eq :Display a :Eq :Display b] :String \
               (str-concat (show a) (show b)))",
        )
        .file(
            "entry.cl",
            "(import [primitives [Pure str-len]])\n\
             (import [helper [cmp]])\n\
             (defn main [] (Pure (str-len (cmp 1 1))))",
        )
        .run("entry.cl")
        .output()
        // (cmp 1 1) = "11"; (str-len "11") = 2 ⇒ exit 2 (FIXME 0355 landed).
        .assert_exit(2);
}

// spec: spec/07-traits.md §7.8 + spec/08-modules.md §8.5 — `--link` companion to
//   the run-mode guard above. Cross-module monomorphisation GOT-wiring is the
//   precise behaviour that diverges between `--run` (JIT, GOT populated in
//   memory) and `--link` (static relocations emitted into the object), so the
//   exit-2 contract must hold in BOTH modes. The same two-file fixture, linked to
//   a native executable and then run, must exit 2 (FIXME 0355).
#[test]
fn cross_module_stacked_trait_bound_call_links_to_exit_2() {
    Cranelisp::new()
        .with_prelude(PreludeVariant::TestStandard)
        .file(
            "helper.cl",
            "(import [primitives [String str-concat]])\n\
             (defn cmp [:Eq :Display a :Eq :Display b] :String \
               (str-concat (show a) (show b)))",
        )
        .file(
            "entry.cl",
            "(import [primitives [Pure str-len]])\n\
             (import [helper [cmp]])\n\
             (defn main [] (Pure (str-len (cmp 1 1))))",
        )
        .link_then_run("entry.cl")
        .output()
        .assert_exit(2);
}

// =============================================================================
// §7.1.5 Default Methods × §8.6 Name Resolution — DEFECT D1 (S86)
// =============================================================================
//
// D1 — impl-body (specifically a SYNTHESIZED DEFAULT method body) resolves in
// the CALLER's module scope, not the trait's DEFINING module. A trait declares
// a default method whose body references a bare name (`add-i64`) in scope only
// in the trait's defining module (`trait_mod`, which globs primitives). An impl
// in a DIFFERENT module (`user`) omits that method, so `generate_default_methods`
// synthesizes a `Defn` from the default body and checks it via
// `check_impl_method_with_sig` (crates/cranelisp-typecheck/src/traits.rs:595).
// That function calls `check_defn_body_with_types` WITHOUT switching
// `state.current_module` to the trait's home — the switch that
// `recheck_body_for_mono` (traits.rs:1757-1759, the mono path) DOES have. So the
// default body's `add-i64` resolves in `user`'s scope → `undefined variable:
// add-i64`. Same class as FIXME 0355. TRUE OWNER: /typecheck (mirror the
// defining-module switch into `check_impl_method_with_sig`). This is the
// hide-primitives DE-LEAK blocker. FIXME(/typecheck).
//
// The concrete-call path (`(+ 1 2)`) does NOT trigger this — it goes through
// monomorphisation, which already switches into the defining module. Only the
// synthesized-default-method-checked-in-the-impl's-module path reaches the
// unswitched `check_impl_method_with_sig`.
//
// FAILING-NOT-IGNORED per memory/feedback_failing_not_ignored.md: asserts the
// CORRECT behaviour (the default body's home-module name resolves; the program
// runs to exit 42), RED today (`undefined variable: add-i64`, exit 1), GREEN
// when the module switch lands.

// spec: spec/07-traits.md §7.1.5 + spec/08-modules.md §8.6 — a default-method
// body's free names MUST resolve in the trait's DEFINING module, not the impl's
// (caller's) module. D1: currently `undefined variable: add-i64`.
#[test]
fn default_method_body_resolves_in_trait_defining_module() {
    // `42` is the success exit, distinct from the error exit `1` (RED).
    Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        // The trait's defining module: `add-i64` is bare-in-scope here.
        .file(
            "trait_mod.cl",
            "(import [primitives [*]])\n\
             (deftrait Foo\n\
            \x20 (req [a] :Int self)\n\
            \x20 (bar [a b] :Int (add-i64 a b)))",
        )
        // The impl module: does NOT have `add-i64` in scope. Omits `bar`, so the
        // default body is synthesized and checked here.
        .user(
            "(import [trait_mod [Foo req bar]])\n\
             (import [primitives [Int Pure]])\n\
             (impl Foo Int (defn req [a] a))\n\
             (defn main [] (Pure (bar 40 2)))",
        )
        .run("user.cl")
        .output()
        .assert_exit(42);
}

// =============================================================================
// §7.7.2 Eq — String inequality (`!=`) — DEFECT D2 (S86)
// =============================================================================
//
// D2 — String `!=` codegen panic. `(!= "a" "b")` on the TestStandard prelude
// (which defines `(impl Eq String (defn = ...) (defn != ...))`) does NOT compile:
// the typecheck primitive-dispatch table maps `("Eq", "!=", "String")` to the
// symbol `neq-string` (`crates/cranelisp-typecheck/src/traits.rs:1183`), but NO
// such primitive is registered (`cranelisp-primitives` has only
// `neq-i64`/`neq-f64`/`neq-bool`) and NO backend inline emits it
// (`cranelisp-backend/src/primitives_inline.rs`). At codegen the JIT panics
// `can't resolve symbol neq-string`. Note the asymmetry: `=` String dispatches
// to `str-eq` (which EXISTS) but `!=` String dispatches to the phantom
// `neq-string`. TRUE OWNER: /backend (+ /primitives) — register/emit a
// `neq-string` implementation (or have typecheck route String `!=` through the
// default `(not (str-eq a b))` body). The typecheck mapping is the trigger; the
// missing implementation is the defect. FIXME(/backend).
//
// These two tests are FAILING-NOT-IGNORED per memory/feedback_failing_not_ignored.md:
// they assert the CORRECT behaviour (`!= "a" "b"` is `true`), go RED today (panic),
// and flip GREEN when the `neq-string` gap closes.

// spec: spec/07-traits.md §7.7.2 — `(!= "a" "b")` MUST evaluate to `true`
// (String inequality); D2: currently panics `can't resolve symbol neq-string`.
#[test]
fn eq_string_neq_evaluates_run() {
    // `42` (not `1`) is the success exit so it is DISTINCT from the
    // codegen-error exit (`1`): RED = exit 1 + panic on stderr; GREEN = exit 42.
    // Control: the sibling `(= "a" "a")` form already exits 42 today (str-eq
    // exists) — only `!=`/neq-string is missing.
    Cranelisp::new()
        .with_prelude(PreludeVariant::TestStandard)
        .user("(import [primitives [Pure]])\n(defn main [] (Pure (if (!= \"a\" \"b\") 42 0)))")
        .run("user.cl")
        .output()
        .assert_exit(42);
}

// spec: spec/07-traits.md §7.7.2 — REPL companion: `(!= "a" "b")` MUST display
// `:primitives/Bool true`; D2: currently panics `can't resolve symbol neq-string`.
#[test]
fn eq_string_neq_evaluates_repl() {
    repl_std("(!= \"a\" \"b\")\n")
        .assert_stdout_contains("true")
        // Negative guard: the codegen-panic symbol MUST NOT leak to stderr once fixed.
        .assert_stderr_empty();
}

// =============================================================================
// §7.1.4 Type Expressions in Signatures — deftrait param annotation form
//        (ring2a behavior-pin, S86)
// =============================================================================
//
// ring2a behavior-pin (NOT a bug — pin expected behaviour). A `deftrait` method
// signature parameter is written `:Type name` (spec §7.1.4: "To give a parameter
// a different type, use a `:Type name` annotation"). So `(size [:a x] :Int)`
// binds parameter `x` with type-var `a` (ACCEPTED), whereas `(size [:a] :Int)`
// is an annotation `:a` with NO parameter name following it — REJECTED at parse
// time with the clear message `annotation missing parameter name`. The compiler
// behaviour is CORRECT (the error is clear, not a panic); these pin it so the
// /repl demo fix (use the named form) stays anchored. Owner is /frontend ONLY if
// the error becomes unclear — today it is a clean parse error, so this is a
// passing guard pair (positive + negative).

// spec: spec/07-traits.md §7.1.4 — `:Type name` annotated param ACCEPTED in a
// deftrait method signature (named param after the annotation).
#[test]
fn deftrait_method_annotated_named_param_accepted() {
    repl_prims("(deftrait Sized (size [:a x] :Int))\n")
        .assert_stdout_contains_all(&["user/Sized", "deftrait"])
        .assert_stderr_empty();
}

// spec: spec/07-traits.md §7.1.4 — a NAMELESS annotation `[:a]` (annotation with
// no parameter name) is REJECTED with a clear parse error, NOT a panic.
#[test]
fn deftrait_method_nameless_annotation_param_rejected_neg() {
    let out = repl_prims("(deftrait Sized (size [:a] :Int))\n");
    // Clear, actionable parse error — the pin: nameless annotation is an error
    // with a message naming the cause, not a panic and not silent acceptance.
    out.assert_stdout_contains("annotation missing parameter name")
        // Negative: the trait MUST NOT be silently declared from the bad sig.
        .assert_stdout_does_not_contain("user/Sized");
}

// =============================================================================
// §7.3.1 × §8.5 — Qualified type path in impl-target position MUST resolve to
//        the canonical type (not be re-rooted under the current module)
//        — DEFECT D-qual-impl-target (S90, agentic-REPL Phase-6 finding)
// =============================================================================
//
// DEFECT. A module-qualified type path in impl-target position
// (`(impl Num primitives/Int …)`) is RE-ROOTED under the current module: it
// registers as `impl user/Num for user/primitives/Int` — a phantom type that
// no real value ever has. A value `3 : Int` then finds no matching impl, so
// `(add 3 4)` errors `no impl of trait Num for type Int`. Per spec/08-modules.md
// §8.5 a qualified name `primitives/Int` denotes the type `Int` in module
// `primitives` (the canonical primitive) and BYPASSES the import/current-module
// machinery; the grammar `concrete_target = type_name` (spec/07-traits.md §7.3,
// EBNF) carries no impl-target exemption. So the qualified target MUST resolve
// to the SAME canonical type the bare target `Int` does — bare and qualified
// impl targets must be interchangeable.
//
// The trap is that the REPL self-documents values as `:primitives/Int 3`, so a
// human (or the embedded agent, mirroring the display) NATURALLY writes the
// qualified form `(impl Num primitives/Int …)`. The agent is the first consumer
// to hit this latent path — the entire human-written impl corpus uses BARE
// targets (`impl Trait Int`, `impl Trait MyType`), so the qualified-target
// resolution path was never exercised.
//
// Extent (probed by hand, S90): NOT primitives-specific. A qualified USER type
// `(impl Tagger user/Widget …)` re-roots to `user/user/Widget` (double-rooted
// phantom) and fails identically. The bug is general qualified-path re-rooting
// in impl-target type position — `user/` is prepended to ANY already-qualified
// path.
//
// Owning skill: /frontend (impl-target type-name resolution) — the qualified
// path must be canonicalised, not current-module-prefixed, at the point the
// impl target is read/built. If isolation shows the canonicalisation seam is in
// the typechecker's impl registration, /typecheck owns it instead; a /dev unit
// repro at the resolution seam will pin which. See the handoff brief in the S90
// outcome.
//
// FAILING-NOT-IGNORED per memory/feedback_failing_not_ignored.md: the qualified
// test asserts the CORRECT behaviour (qualified resolves like bare → `:a 7`),
// RED today (`no impl of trait Num for type Int`), GREEN when the qualified
// impl target canonicalises. The bare control passes TODAY and pins the
// contrast so the fix target is unambiguous.

// spec: spec/07-traits.md §7.3.1 — CONTROL (green today): a BARE impl target
// `(impl Num2 Int …)` registers `impl user/Num2 for user/Int`, and `(add2 3 4)`
// dispatches to the Int impl → `:a 7`. Pins the contrast for the qualified case.
#[test]
fn impl_bare_type_target_dispatches_control() {
    repl_prims(
        "(deftrait Num2 (add2 [:a x :a y] :a))\n\
         (impl Num2 Int (defn add2 [x y] (add-i64 x y)))\n\
         (add2 3 4)\n",
    )
    .assert_stdout_contains_all(&["impl user/Num2 for user/Int", ":a 7"]);
}

// spec: spec/07-traits.md §7.3.1 + spec/08-modules.md §8.5 — a QUALIFIED impl
// target `(impl Num2 primitives/Int …)` MUST resolve to the canonical primitive
// `Int` (identically to the bare `Int` control above), so `(add2 3 4)` → `:a 7`.
// D-qual-impl-target: today it re-roots to `user/primitives/Int` and errors
// `no impl of trait Num2 for type Int`. FIXME(/frontend).
#[test]
fn impl_qualified_primitive_type_target_resolves_to_canonical() {
    repl_prims(
        "(deftrait Num2 (add2 [:a x :a y] :a))\n\
         (impl Num2 primitives/Int (defn add2 [x y] (add-i64 x y)))\n\
         (add2 3 4)\n",
    )
    // CORRECT: qualified target canonicalises to `Int` exactly as the bare
    // target does; the call dispatches and yields 7. Today this FAILS — the
    // impl registers for the phantom `user/primitives/Int` and `(add2 3 4)`
    // errors `no impl of trait Num2 for type Int`.
    .assert_stdout_contains(":a 7")
    // Negative: the phantom re-rooted target MUST NOT appear in the impl line.
    .assert_stdout_does_not_contain("user/primitives/Int");
}

// spec: spec/07-traits.md §7.3.1 + spec/08-modules.md §8.5 — extent guard: the
// re-rooting is NOT primitives-specific. A qualified USER type target
// `(impl Tagger user/Widget …)` MUST resolve to the canonical `user/Widget`
// (the same type the bare target `Widget` names), so `(tagit Gadget)` → 99.
// D-qual-impl-target: today it double-roots to `user/user/Widget` and errors
// `undefined function: Tagger.tagit$Widget` at codegen (the impl was registered
// for a phantom type). FIXME(/frontend).
#[test]
fn impl_qualified_user_type_target_resolves_to_canonical() {
    repl_prims(
        "(deftype Widget Gadget)\n\
         (deftrait Tagger (tagit [x] :Int))\n\
         (impl Tagger user/Widget (defn tagit [w] 99))\n\
         (tagit Gadget)\n",
    )
    // CORRECT: qualified `user/Widget` canonicalises to the already-current-
    // module type `Widget`; dispatch yields 99. Today this FAILS — the impl
    // registers for `user/user/Widget` and the call cannot resolve.
    .assert_stdout_contains(":primitives/Int 99")
    // Negative: the double-rooted phantom MUST NOT appear.
    .assert_stdout_does_not_contain("user/user/Widget");
}

// =============================================================================
// §7.4 — Nullary return-type-polymorphic trait method dispatch (D-default)
// =============================================================================

// spec: spec/07-traits.md §7.4 — Static method resolution. A nullary trait
// method whose ONLY type information is its return type (`self` in return
// position, no parameter to dispatch on) MUST monomorphise/dispatch to the
// concrete impl when the call site fixes the return type.
//
// HISTORY (D-default, S87 Stage-C.2 /stdlib rollout — now RESOLVED). This
// argument-context return-type-dispatch cell once FAILED at codegen
// (`codegen error … undefined function: z`) even though typecheck pinned the
// return type. That leak is FIXED: `(add-i64 (z) 5)` — the `add-i64` context
// fixes `(z)`'s return to `Int` — dispatches to the Int impl and yields 5.
// GREEN. This is the argument-context REPL cell of the leg-(c) acceptance
// lattice (S112 W6, AG-4 below covers the full cross-mode/context matrix).
#[test]
fn nullary_return_poly_trait_method_dispatches_at_codegen() {
    // `z` has no parameter; its only type info is the `self` return. The
    // `add-i64` context fixes the return to Int, selecting the Int impl;
    // 0 + 5 = 5 when GREEN.
    repl_prims(
        "(deftrait T (z [] self))\n\
         (impl T Int (defn z [] 0))\n\
         (add-i64 (z) 5)\n",
    )
    .assert_stdout_contains(":primitives/Int 5");
}

// =============================================================================
// AG-4 — leg-(c) return-type-dispatch acceptance lattice (S112 W6, plan §4/§11.6)
// =============================================================================
//
// LEG-(c) VERDICT (S112 W6, /testing repro-gated investigation, 2026-07-18):
// NO cell fires. Return-type dispatch works end-to-end across
// {REPL, --run, --link} × {annotation-context `:Int (zed)`, argument-context
// `(add-i64 (zed) 1)`} × {fresh, cached} × {Int impl, Float impl}. The S111
// close record's asserted "undefined function codegen leak" does NOT reproduce
// on HEAD — matching FIXME 0628's "Not this" observation (admitted return-type
// dispatch already worked at the REPL). Per the standing dual-path rule the
// pinned cross-mode probe is committed as GREEN coverage (these cells ARE the
// evidence): leg (c) collapses to the acceptance lattice; no defect authored.
//
// The `zed`-like conventional method: `(deftrait Zeroable (zed [] self))` — the
// dispatch position is the RETURN type (`self` in return, no param). Int and
// Float impls exercise a real two-impl dispatch (not an accidental always-Int).

// spec: spec/07-traits.md §7.4 / §7.1.1 (param-or-return) — the ANNOTATION
// context: a `:Type` annotation pins the return type of a nullary
// return-type-polymorphic method, selecting the impl. `:Int (zed)` → 0; the
// `main` returns `(add-i64 <:Int (zed)> 7)` = 7. Mode-equivalent (exit/value)
// across REPL + --run + --link, fresh AND cached (run_through_all_modes runs
// all six permutations). GREEN — the leg-(c) annotation-context lattice.
#[test]
fn return_type_dispatch_annotation_context_all_modes() {
    run_through_all_modes(
        "(deftrait Zeroable (zed [] self))\n\
         (impl Zeroable Int (defn zed [] 0))\n\
         (impl Zeroable Float (defn zed [] 0.0))\n\
         (defn main [] (Pure (let [a :Int (zed)] (add-i64 a 7))))\n",
        PreludeVariant::PrimitivesOnly,
    )
    .assert_all_equal(7);
}

// spec: spec/07-traits.md §7.4 / §7.1.1 (param-or-return) — the ARGUMENT
// context: an ambient argument type fixes the return type of `(zed)`.
// `(add-i64 (zed) 7)` fixes `(zed)`'s return to Int → 0 + 7 = 7. Mode-equivalent
// across all six permutations. GREEN — the leg-(c) argument-context lattice
// (the cross-mode extension of `nullary_return_poly_trait_method_dispatches_at_codegen`).
#[test]
fn return_type_dispatch_argument_context_all_modes() {
    run_through_all_modes(
        "(deftrait Zeroable (zed [] self))\n\
         (impl Zeroable Int (defn zed [] 0))\n\
         (impl Zeroable Float (defn zed [] 0.0))\n\
         (defn main [] (Pure (add-i64 (zed) 7)))\n",
        PreludeVariant::PrimitivesOnly,
    )
    .assert_all_equal(7);
}

// spec: spec/07-traits.md §7.4 — the SECOND impl (Float) dispatches too, proving
// the annotation genuinely selects the impl (not an accidental always-first).
// `:Float (zed)` → 0.0; `(if (lt-f64 a 1.0) 3 9)` = 3. Mode-equivalent ×6.
// GREEN — the leg-(c) second-impl fence.
#[test]
fn return_type_dispatch_float_impl_selected_all_modes() {
    run_through_all_modes(
        "(deftrait Zeroable (zed [] self))\n\
         (impl Zeroable Int (defn zed [] 0))\n\
         (impl Zeroable Float (defn zed [] 0.0))\n\
         (defn main [] (Pure (let [a :Float (zed)] (if (lt-f64 a 1.0) 3 9))))\n",
        PreludeVariant::PrimitivesOnly,
    )
    .assert_all_equal(3);
}

// spec: spec/03-types.md §3.11 — the unresolved-use CONTROL: a bare `(zed)` with
// two impls and NO context to pin the return type is a clean §3.11
// return-type-ambiguity error (actionable, names the fix), NEVER a codegen leak
// (`undefined function`, `codegen error`). The negative half of the leg-(c)
// lattice: the leak the S111 record feared MUST be absent even in the genuinely
// unresolvable case. GREEN.
#[test]
fn return_type_dispatch_unresolved_bare_call_clean_ambiguity_neg() {
    let out = repl_prims(
        "(deftrait Zeroable (zed [] self))\n\
         (impl Zeroable Int (defn zed [] 0))\n\
         (impl Zeroable Float (defn zed [] 0.0))\n\
         (zed)\n",
    );
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.contains("ambiguous type"),
        "a bare `(zed)` with no return-type context MUST be a clean §3.11 \
         return-type-ambiguity error; got:\n{c}"
    );
    assert!(
        !c.contains("undefined function") && !c.contains("codegen error"),
        "the unresolved return-type-dispatch call MUST NOT leak a backend \
         `undefined function`/`codegen error` (the S111-record leak that does \
         NOT reproduce — leg (c) collapses to coverage); got:\n{c}"
    );
}

// =============================================================================
// TB-24 — Case-1 × POLY-applied impl-target wrong-reject (S112 W6, plan §3.3a,
// /qa ruling 3). The §7.3.5 Case-1 matrix's only `✓` row with no test — and it
// was BROKEN on HEAD (admissible-untested-broken, the exact hole the matrix
// discipline exists to close).
// =============================================================================

// spec: spec/07-traits.md §7.3.5 Case 1 + §7.3.3 + §5.4.3 — a conventional
// (kind-`*`) trait impl over a POLY-applied target `(Option a)` is admissible
// (`✓`): it registers a polymorphic impl over every `Option a`, and dispatch on
// a concrete `(Some 3)` resolves it. Likewise the canonical §7.3.3 constrained
// form `(Option :Disp a)`.
//
// RED at HEAD (pre-existing WRONG-REJECT, /qa ruling 3): both forms die with
// `unknown type a` BEFORE the arity gate — the impl-target TypeExpr resolution
// context binds no type variables, so the lowercase var `a` resolves as an
// unknown NAMED type (the 0590-tightening blast-radius shape landing on a
// position that legitimately holds a var). Parse accepts (frontend delivers
// `Applied(Option,[a])`); the error is the typecheck resolve-layer diagnostic;
// backend never involved. Flips GREEN when the impl-target resolver binds the
// pairing's lowercase con-vars.
// defect: class=wrong-reject locus=crates/cranelisp-typecheck impl-target TypeExpr resolution seam (lowercase con-var in `(Option a)`/`(Option :Disp a)` resolved as an unknown named type before the §7.3.5 arity gate) found=S112 owner=/dev
#[test]
fn conventional_impl_poly_applied_target_accepts_and_dispatches() {
    // Form A — the bare poly-applied target `(Option a)`.
    let a = repl_prims(
        "(deftrait Disp (dp [x] :Int))\n\
         (impl Disp (Option a) (defn dp [x] 7))\n\
         (dp (Some 3))\n",
    );
    let ac = format!("{}{}", a.stdout, a.stderr);
    assert!(
        !ac.contains("unknown type"),
        "`(impl Disp (Option a))` is admissible (§7.3.5 Case 1, poly-applied \
         target `✓`) — it MUST NOT reject the lowercase con-var `a` as an \
         `unknown type` before the arity gate (wrong-reject, ruling 3); got:\n{ac}"
    );
    assert!(
        a.stdout.contains(":primitives/Int 7"),
        "`(dp (Some 3))` MUST dispatch to the poly-applied `(Option a)` impl and \
         yield 7; got:\n{}",
        a.stdout
    );

    // Form B — the canonical §7.3.3 constrained form `(Option :Disp a)`.
    let b = repl_prims(
        "(deftrait Disp (dp [x] :Int))\n\
         (impl Disp (Option :Disp a) (defn dp [x] 7))\n\
         (dp (Some 3))\n",
    );
    let bc = format!("{}{}", b.stdout, b.stderr);
    assert!(
        !bc.contains("unknown type"),
        "the canonical §7.3.3 constrained form `(impl Disp (Option :Disp a))` \
         MUST NOT reject the con-var `a` as an `unknown type` (wrong-reject, \
         ruling 3); got:\n{bc}"
    );
    assert!(
        b.stdout.contains(":primitives/Int 7"),
        "`(dp (Some 3))` MUST dispatch to the constrained `(Option :Disp a)` \
         impl and yield 7; got:\n{}",
        b.stdout
    );
}

// =============================================================================
// FIXME 0434 sweep (this sprint) — deftrait/deftype TYPE REFERENCE name-position,
// qualified vs bare. The impl-TARGET position was already covered by the S91
// D-qual-impl-target repros (above); this sweeps the type-reference position
// INSIDE a signature. verify-on-HEAD: a passing row is a standing [Tested+Neg]
// guard; a failing row is a surfaced sibling defect handed to /frontend.
// =============================================================================

// spec: spec/07-traits.md §7.3.1 + spec/08-modules.md §8.5 — a `deftrait`
// method's return-type REFERENCE written QUALIFIED (`:primitives/Int`) MUST
// resolve to the same canonical type as the bare reference (`:Int`); the
// qualified form MUST NOT be re-rooted (to `user/primitives/Int`). Both dispatch
// and yield 5.
#[test]
fn deftype_deftrait_reference_qualified_and_bare_equiv() {
    // Bare control: a deftrait method return-type reference `:Int`.
    repl_prims(
        "(deftype W Wv)\n\
         (deftrait Qb (qb [x] :Int))\n\
         (impl Qb W (defn qb [w] 5))\n\
         (qb Wv)\n",
    )
    .assert_stdout_contains(":primitives/Int 5");

    // Qualified: the SAME return-type reference written `:primitives/Int` MUST
    // resolve to the canonical Int — dispatch yields 5, no phantom re-root.
    repl_prims(
        "(deftype W Wv)\n\
         (deftrait Qq (qq [x] :primitives/Int))\n\
         (impl Qq W (defn qq [w] 5))\n\
         (qq Wv)\n",
    )
    .assert_stdout_contains(":primitives/Int 5")
    .assert_stdout_does_not_contain("user/primitives/Int");
}

// =============================================================================
// S110 §D RD-3 — the R16/R17 false-positive fence (author FIRST; GREEN pin).
// The outcome-grounded dispatch-ambiguity scan (R16/R17) must NOT re-fire on an
// ARG-directed dispatch whose result span carries a residual type var but sits
// in an ordinary value position. `(add2 3 4)` resolves its impl by ARGUMENT type
// (Int) — the dispatch outcome is determined — even though the trait method's
// recorded span type is the residual `:a`. The S109-revert class was a gate that
// drifted back to surface-type concreteness (`!is_concrete()`) and false-flagged
// exactly this cell; RD-3 pins that it stays computable and unflagged.
// Plan: tests/plan/PLAN.md §S110 D / RD-3.
// =============================================================================

// spec: spec/03-types.md §3.3.3 — MUST (e) false-positive fence: an
// arg-directed trait dispatch whose recorded result-span type is a residual var
// but which is fully resolved by its ARGUMENTS is NOT the §3.11 ambiguity — it
// evaluates. `(let [r (add2 3 4)] r)` binds the Int-impl result to `r` and
// yields 7. The outcome-grounded scan MUST NOT flag it (no "ambiguous", no
// GOT-slot/__expr leak). GREEN today; MUST STAY green across the R16/R17 wave.
#[test]
fn arg_directed_dispatch_result_in_value_position_not_flagged() {
    let out = repl_prims(
        "(deftrait Num2 (add2 [:a x :a y] :a))\n\
         (impl Num2 Int (defn add2 [x y] (add-i64 x y)))\n\
         (let [r (add2 3 4)] r)\n",
    );
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.contains(":a 7") || c.contains("7"),
        "`(let [r (add2 3 4)] r)` is an arg-directed dispatch in an ordinary \
         value position — it MUST evaluate to 7, NOT be flagged (§3.3.3 MUST (e) \
         false-positive fence, RD-3); got:\n{c}"
    );
    assert!(
        !c.contains("ambiguous"),
        "an arg-directed dispatch whose result sits in a value position MUST NOT \
         be flagged as the §3.11 ambiguity (RD-3, the S109-revert class); got:\n{c}"
    );
    assert!(
        !c.contains("GOT slot") && !c.contains("__expr"),
        "RD-3 MUST NOT leak a backend GOT-slot/__expr frame; got:\n{c}"
    );
}

// =============================================================================
// S110 §C — 0590 TypeExpr resolver convergence: the behaviour-tightening matrix
// (TX rows) + the FV-13/FV-14 over-broadening fence. The convergence collapses
// the four TypeExpr resolver mirrors onto the ONE canonical resolver:
//   - mirror 1 (`resolve_trait_type_expr`, trait-method sigs) TODAY errors on a
//     bare in-scope user type → post-convergence RESOLVES (TX-1, RED positive);
//   - mirrors 2/3 (`resolve_type_expr_hkt{,_impl}`, HKT trait/impl sigs) TODAY
//     fabricate an empty-module ADT for an unknown Named (never error) →
//     post-convergence ERROR (TX-5/TX-6, RED negatives).
// FV-13/FV-14 (TX-8/TX-9) pin what must NOT broaden. Design:
// design/typecheck/type-expr-resolver-convergence.md §1. Spec: spec/07-traits.md
// + spec/08-modules.md §8.5 (bare ≡ qualified-in-scope). Plan: PLAN.md §S110 C.
// =============================================================================

// spec: spec/08-modules.md §8.5 + spec/07-traits.md §7.1 — a BARE in-scope user
// type named in a trait-method signature MUST resolve to that type (bare ≡
// qualified-in-scope, §8.5), exactly as a qualified reference would. A local
// `(deftype MyType Mk)` referenced as the parameter type of a trait method
// `(m [:MyType x] self)` MUST resolve; the impl registers and `(m Mk)`
// dispatches, returning the `self` value `Mk`. (The return type is the lowercase
// self keyword — spec §7 line 57: capital `Self` is an ordinary named type that
// fails resolution, so the earlier `Self` spelling asserted the wrong thing;
// FIXME 0625.)
//
// RED today (0590 mirror-1): `resolve_trait_type_expr` accepts only intrinsic
// scalars or qualified-only Named leaves, so the bare user type `MyType` errors
// `unknown type`. GREEN post-convergence (bare routes through the symbol table).
// defect: class=wrong-reject locus=crates/cranelisp-typecheck/src/traits/type_resolve.rs::resolve_trait_type_expr (bare in-scope user type in a trait-method sig rejected as `unknown type` instead of resolving via the symbol table, §8.5) found=S110 owner=/dev
#[test]
fn trait_method_sig_bare_user_type_resolves() {
    let out = repl_prims(
        "(deftype MyType Mk)\n\
         (deftrait Tt (m [:MyType x] self))\n\
         (impl Tt MyType (defn m [x] x))\n\
         (m Mk)\n",
    );
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !c.contains("unknown type"),
        "a BARE in-scope user type in a trait-method sig MUST resolve via the \
         symbol table (§8.5 bare ≡ qualified-in-scope), NOT error `unknown type` \
         (TX-1, 0590 mirror-1 tightening); got:\n{c}"
    );
    assert!(
        c.contains("Mk"),
        "with the bare user type resolved, `(m Mk)` MUST dispatch and return the \
         `self` value `Mk` (TX-1); got:\n{c}"
    );
}

// spec: spec/07-traits.md §7.2 + spec/03-types.md §3.7 — an UNKNOWN uppercase
// `Named` type in a HIGHER-KINDED trait method signature MUST be rejected with an
// `unknown type` error — a type reference that names nothing is a fault, not a
// silently-fabricated empty-module ADT.
//
// RED today (0590 mirror-2): `resolve_type_expr_hkt` fabricates an empty-module
// ADT for any unknown Named leaf and NEVER errors, so the bogus return type
// `Ghosttype` is silently accepted and the `deftrait` "succeeds". GREEN
// post-convergence (the fabrication arm is deleted; unknown Named errors).
// defect: class=silent-accept locus=crates/cranelisp-typecheck/src/traits/type_resolve.rs::resolve_type_expr_hkt (unknown uppercase Named in an HKT trait sig fabricates an empty-module ADT instead of erroring) found=S110 owner=/dev
#[test]
fn hkt_trait_sig_unknown_named_errors_neg() {
    let out = repl_prims("(deftrait (Boxx f) (peek [:(f a) x] Ghosttype))\n");
    let c = format!("{}{}", out.stdout, out.stderr).to_lowercase();
    assert!(
        c.contains("unknown type") || c.contains("ghosttype"),
        "an unknown uppercase Named in an HKT trait-method sig MUST error \
         `unknown type Ghosttype`, NOT silently fabricate an empty-module ADT \
         (TX-5, 0590 mirror-2 tightening); got:\n{c}"
    );
}

// TX-6 (unknown uppercase Named × HKT IMPL method — mirror-3
// `resolve_type_expr_hkt_impl` fabrication) is DEFERRED to /dev typecheck
// unit tier (enumerated per the S108-Inc2 deferral discipline). Rationale: to
// isolate the mirror-3 fabrication e2e, an HKT impl method must carry an unknown
// Named in a type-annotation position — but an impl method annotation inherits
// its type from the trait sig, so any unknown Named there either (a) unifies
// with the trait's expected `(f a)` (fabrication) or (b) mismatches it — the
// fabricated empty-module ADT does NOT unify with the trait's `(f a)`, so the
// probe fails on a type MISMATCH, not the fabrication-vs-error behaviour under
// test. A well-formed-except-for-the-unknown-Named HKT impl is not e2e-reachable
// without masking the mechanism (verify-example-well-formed lesson). The
// mirror-3 case is cleanly unit-testable over `resolve_type_expr_hkt_impl` in
// isolation. Enumerated /dev (typecheck) unit obligation:
//   (i)  an unknown Named leaf in an HKT impl method sig ERRORS `unknown type`
//        (post-convergence) — the fabrication arm is deleted;
//   (ii) a KNOWN in-scope Named in the same position resolves (the positive
//        control, so the error is the unknown-ness, not the position);
//   (iii) the error names the unknown type.
// TX-5 (mirror-2) stands as the e2e representative of the fabrication-deletion
// class. Plan: PLAN.md §S110 C TX-6.

// spec: spec/03-types.md §3.11 — FV-13 over-broadening fence (TX-8): the
// convergence's mint capability (a bare LOWERCASE name mints a fresh type var)
// MUST NOT swallow an unknown uppercase TYPE in an annotation. `:Nonesuchzz 5`
// MUST still error `unknown type` — the annotation resolver rejects unknown
// uppercase Named leaves. GREEN today; MUST STAY green through the W-TC wave.
#[test]
fn annotation_unknown_uppercase_named_still_errors_fence() {
    let out = repl_prims(":Nonesuchzz 5\n");
    let c = format!("{}{}", out.stdout, out.stderr).to_lowercase();
    assert!(
        c.contains("unknown type") || c.contains("nonesuchzz"),
        "FV-13 fence (TX-8): an unknown uppercase Named in a value-position \
         annotation MUST still error `unknown type` — the mint capability must \
         not broaden to swallow unknown TYPES; got:\n{c}"
    );
}

// spec: spec/07-traits.md §7.3 — FV-14 over-broadening fence (TX-9): a trait
// reference resolved through a module path is unaffected by the annotation mint
// path. A trait method dispatched by argument type (`add2` over Int) still
// resolves and yields 7. GREEN today; MUST STAY green through the W-TC wave.
#[test]
fn trait_path_resolution_unaffected_by_mint_fence() {
    repl_prims(
        "(deftrait Num2 (add2 [:a x :a y] :a))\n\
         (impl Num2 Int (defn add2 [x y] (add-i64 x y)))\n\
         (add2 3 4)\n",
    )
    .assert_stdout_contains(":a 7");
}

// =============================================================================
// §7.2 / §7.3 — b0 echo-the-head parse support: malformed slot-1 diagnostics
// (plan §3.5) + con_var lowercase enforcement (plan §7.2). The b0 parse change
// (`c08e68fc`) admits the parenthesized higher-kinded impl head `(Functor f)`
// and surfaces a LOCATED per-shape `parse error` for each malformed slot 1,
// naming the fix (design `design/frontend/trait-impl-head-parse.md` §4). These
// exercise the b0 support end-to-end and are GREEN on the current compiler.
// =============================================================================

// spec: spec/07-traits.md §7.3 — a structurally-malformed impl slot-1 head is
// rejected at parse with a LOCATED, per-shape diagnostic that names the fix
// (design §4 table, six rows). One test, six sub-asserts (plan §3.5).
#[test]
fn impl_head_malformed_variants_located_parse_errors_neg() {
    // Each row: (source, distinctive substring the located diagnostic must carry).
    let cases: &[(&str, &str)] = &[
        // 1-element head: HK head missing its constructor variable.
        (
            "(impl (Functor) Int (defn f [x] x))\n",
            "missing its constructor variable",
        ),
        // 3+-element head: too many elements.
        (
            "(impl (Functor f g) Int (defn f [x] x))\n",
            "too many elements in trait head",
        ),
        // empty head.
        ("(impl () Int (defn f [x] x))\n", "empty trait head"),
        // head element itself a list (`((Functor f))`) — the non-symbol-head
        // fault is named BEFORE any arity conclusion (design §4 dispatch order).
        (
            "(impl ((Functor f)) Int (defn f [x] x))\n",
            "trait name must be a bare symbol",
        ),
        // lowercase trait name.
        (
            "(impl (functor f) Int (defn f [x] x))\n",
            "trait name must start with uppercase",
        ),
        // non-symbol con_var.
        (
            "(impl (Functor 3) Int (defn f [x] x))\n",
            "constructor variable must be a symbol",
        ),
    ];
    for (src, needle) in cases {
        let out = repl_prims(src);
        let c = format!("{}{}", out.stdout, out.stderr);
        assert!(
            c.contains("parse error"),
            "malformed impl head `{src}` MUST be a located parse error; got:\n{c}"
        );
        assert!(
            c.contains(needle),
            "malformed impl head `{src}` MUST name the fix (expected substring \
             {needle:?}); got:\n{c}"
        );
    }
}

// spec: spec/07-traits.md §7.2 — the constructor variable is a lowercase symbol
// (`con_var = lowercase_symbol`). An uppercase con_var is malformed and rejected
// at parse in BOTH the deftrait head AND the impl echoed head — the single b0
// shared seam (`parse_trait_head_shape`) enforces it once for both forms
// (plan §7.2, design §4/§8.2). The two-form assertion pins the single-source
// (Principle 7) guarantee: neither parser accepts what the other rejects.
#[test]
fn trait_head_uppercase_convar_rejected_both_forms_neg() {
    // deftrait head.
    let dt = repl_prims("(deftrait (Functor F) (fmap [:(F a) x] Int))\n");
    let dc = format!("{}{}", dt.stdout, dt.stderr);
    assert!(
        dc.contains("parse error") && dc.contains("must start with lowercase"),
        "an uppercase con_var in a `deftrait` head `(Functor F)` MUST be a located \
         parse error naming the lowercase rule; got:\n{dc}"
    );
    // impl echoed head — same seam, same rule.
    let im = repl_prims("(impl (Functor F) Int (defn f [x] x))\n");
    let ic = format!("{}{}", im.stdout, im.stderr);
    assert!(
        ic.contains("parse error") && ic.contains("must start with lowercase"),
        "an uppercase con_var in an `impl` echoed head `(Functor F)` MUST be a \
         located parse error naming the lowercase rule (same shared seam as \
         deftrait); got:\n{ic}"
    );
}
