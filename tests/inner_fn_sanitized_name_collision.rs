//! Instances of one generic template whose type names differ only in
//! characters that inner-function name sanitizing collapses (`A-B` / `A_B`).
//!
//! The control pair (`A-B` / `A-C`) differs after sanitizing, so it isolates
//! the collapsed-character difference from generic capture itself.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{PreludeVariant, run_through_all_modes};

fn program(second_type: &str) -> String {
    format!(
        "(import [primitives [*]])\n\
         (deftype A-B [:primitives/Int p])\n\
         (deftype {second_type} [:primitives/Int q])\n\
         (defn f [v] (let [g (fn [] v)] (g)))\n\
         (defn main []\n\
           (Pure (add-i64 (p (f (A-B 3))) (q (f ({second_type} 4))))))\n"
    )
}

// spec: spec/01-lexical.md §1.4.1 Simple Symbols — `-` and `_` are distinct symbol characters
// spec: spec/04-expressions.md §4.5.1 Free Variable Capture
// defect: class=wrong-reject locus=crates/cranelisp-backend/src/compiler/resolution.rs::inner_fn_discriminator_for found=S122 owner=/dev
// Reproduced before the S122 fix: every mode rejected with `Duplicate definition of identifier:
// __lambda__user_f__user_A_B__user_A_B___…` — both instances' lambda bodies
// received one name. The injective encoding now keeps them distinct.
#[test]
fn generic_capturing_lambda_at_hyphen_and_underscore_type_names_runs_in_all_modes() {
    run_through_all_modes(&program("A_B"), PreludeVariant::None).assert_all_equal(7);
}

// spec: spec/04-expressions.md §4.5.1 Free Variable Capture
#[test]
fn generic_capturing_lambda_at_names_distinct_after_sanitizing_runs_in_all_modes() {
    run_through_all_modes(&program("A-C"), PreludeVariant::None).assert_all_equal(7);
}
