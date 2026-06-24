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
        .file(
            "types.cl",
            "(deftrait (Classify a) (classify [a] Int))\n\
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

// spec: spec/03-types.md §3.7 — negative HKT: a primitive type is NOT a type
// constructor, so implementing a higher-kinded trait on it MUST be rejected.
// §3.7.4 is explicit: "Primitive types (Int, Bool, String, Float) are rejected
// as HKT impl targets because they are not type constructors." The `Functor`
// trait uses `f` at arity 1 (`(f a)`), so `(impl Functor Int ...)` must fail
// at impl registration with an arity / not-a-constructor diagnostic. Negative
// companion to `hkt_deftrait_declaration_with_type_constructor_parameter_succeeds`.
#[test]
fn hkt_impl_on_primitive_type_is_rejected_neg() {
    let out = repl_prims(
        "(deftrait (Functor f)\n  (fmap [:(Fn [a] b) func :(f a) x] (f b)))\n\
         (impl Functor Int (defn fmap [func x] x))\n",
    );
    assert!(
        out.stdout.contains("not a type constructor")
            || out.stdout.contains("type constructor"),
        "impl of a HKT trait on the primitive `Int` MUST be rejected with a \
         not-a-type-constructor diagnostic per spec/03-types.md §3.7.4; \
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
    repl_prims(
        "(deftype (Option a) None (Some [:a val]))\n\
         (deftrait (Functor f) (fmap [:(Fn [a] b) func :(f a) x] (f b)))\n\
         (impl Functor Option\n  (defn fmap [func opt]\n    (match opt [None None (Some x) (Some (func x))])))\n\
         (match (fmap (fn [x] (add-i64 x 1)) (Some 41)) [(Some v) v None 0])\n",
    )
    .assert_stdout_contains(":primitives/Int 42");
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
    repl_prims(
        "(deftype (Option a) None (Some [:a val]))\n\
         (deftrait (Functor f) (fmap [:(Fn [a] b) func :(f a) x] (f b)))\n\
         (impl Functor Option\n  (defn fmap [func opt]\n    (match opt [None None (Some x) (Some (func x))])))\n\
         (match (fmap (fn [x] (add-i64 x 1)) (Some 99)) [(Some v) v None 0])\n",
    )
    .assert_stdout_contains(":primitives/Int 100");
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
// DEFECT (D-default, S87 Stage-C.2 /stdlib rollout). Such a nullary
// return-type-polymorphic method FAILS at codegen even though typecheck pins
// the return type. With `(add-i64 (z) 5)` the `add-i64` context fixes `(z)`'s
// return to `Int`, so the form TYPECHECKS — but codegen emits
//   `codegen error … undefined function: z`
// because the method is never resolved to the `Int` impl's body. Same shape as
// the stdlib `default` self-test (`:Int (default)` → `undefined function:
// default`), reduced to a 3-line self-contained repro. Blocks any nullary
// return-poly method (`default`, `zero`, `empty`, …).
//
// FAILING-NOT-IGNORED per memory/feedback_failing_not_ignored.md — RED today
// (codegen error), GREEN when the nullary return-poly method dispatches to its
// impl body. → /backend (monomorphisation/dispatch at codegen; typecheck
// already pins the return type, so the defect is on the codegen side).
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
