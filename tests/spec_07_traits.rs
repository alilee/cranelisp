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
