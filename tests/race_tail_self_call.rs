//! U-18: tail-position races must retain self-call operands as effects.

mod helpers;

use helpers::e2e::{PreludeVariant, run_through_all_modes};

fn assert_immediate_winner(body: &str) {
    let program = format!(
        "(import [primitives [*]])\n\
         (defn g [n] (bind (sleep 1000) (fn [u] (Pure 7))))\n\
         (defn f [n] (if (eq-i64 n 0)\n\
           (bind (sleep 1000) (fn [u] (Pure 7)))\n\
           {body}))\n\
         (defn main [] (f 1))\n"
    );
    let outcomes = run_through_all_modes(&program, PreludeVariant::None);
    println!("U-18 {body}: {outcomes:#?}");
    outcomes.assert_all_equal(99);
}

// spec: spec/10-io.md §10.12.8 — the first completed race branch supplies the value.
// defect: class=tail-context-leak locus=crates/cranelisp-backend/src/compiler/apply.rs::compile_builtin_fn_call found=S123 owner=/dev fixed=S123/3bdf398e
// U-18: the self-call jumped to the enclosing loop before the race could be
// built (exit 7 instead of 99).
#[test]
fn race_with_self_call_first_returns_the_immediate_winner() {
    assert_immediate_winner("(race (f (add-i64 n -1)) (Pure 99))");
}

// spec: spec/10-io.md §10.12.8 — either race operand can be the first to complete.
// defect: class=tail-context-leak locus=crates/cranelisp-backend/src/compiler/apply.rs::compile_builtin_fn_call found=S123 owner=/dev fixed=S123/3bdf398e
// U-18 also affected the second operand; a correction confined to the first
// operand would miss this case.
#[test]
fn race_with_self_call_second_returns_the_immediate_winner() {
    assert_immediate_winner("(race (Pure 99) (f (add-i64 n -1)))");
}

// spec: spec/10-io.md §10.12.8 — a tail-position race returns its winning value.
#[test]
fn race_with_non_self_call_returns_the_immediate_winner() {
    assert_immediate_winner("(race (g (add-i64 n -1)) (Pure 99))");
}

// spec: spec/10-io.md §10.12.8 — a let-bound recursive effect participates in race.
#[test]
fn race_with_let_bound_self_call_returns_the_immediate_winner() {
    assert_immediate_winner("(let [slow (f (add-i64 n -1))] (race slow (Pure 99)))");
}
