// Integration tests verifying that example programs compile and
// produce expected results.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::*;

fn run_example(filename: &str) -> i64 {
    let path = format!(
        "{}/examples/{}",
        env!("CARGO_MANIFEST_DIR"),
        filename
    );
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("cannot read {path}: {e}"));
    compile_and_run_simple(&source)
}

#[test]
fn example_01_integers() {
    // 7 + 7 + 42 + 3 + 17 + (-7) = 69
    assert_eq!(run_example("01-integers.cl"), 69);
}

#[test]
fn example_02_booleans() {
    // eq=1, neq=1, lt=1, gt=1, le=1, ge=0, sign(42)=1, sign(0)=0, sign(-7)=-1 = 5
    assert_eq!(run_example("02-booleans.cl"), 5);
}

#[test]
fn example_03_let_bindings() {
    // 6 + 9 + 30 + 20 + 25 + 7 = 97
    assert_eq!(run_example("03-let-bindings.cl"), 97);
}

#[test]
fn example_04_functions() {
    // 42 + 7 + 25 + 40 + 6 + 7 + 3 + 5 = 135
    assert_eq!(run_example("04-functions.cl"), 135);
}

#[test]
fn example_05_recursion() {
    // 120 + 3628800 + 55 + 6 + 5050 + 1024 = 3635055
    assert_eq!(run_example("05-recursion.cl"), 3635055);
}

#[test]
fn example_06_enums() {
    // 2 + 0 + 1 + 1 + 1 + 99 = 104
    assert_eq!(run_example("06-enums.cl"), 104);
}

#[test]
fn example_07_polymorphism() {
    // 42+10+10+20+7+30 = 119
    assert_eq!(run_example("07-polymorphism.cl"), 119);
}

#[test]
fn example_08_floats() {
    // 1+1+1+1+1+1+1+0+1+1 = 9
    assert_eq!(run_example("08-floats.cl"), 9);
}

// Ring 1 examples: strings, ADTs, destructuring, closures, higher-order

#[test]
fn example_09_strings() {
    // 5+0+11+3+1+0+2+4+12+16+1 = 55
    assert_eq!(run_example("09-strings.cl"), 55);
}

#[test]
fn example_10_adts() {
    // 7+60+42+99+7+0+30+20 = 265
    assert_eq!(run_example("10-adts.cl"), 265);
}

#[test]
fn example_11_destructuring() {
    // 4+7+1+15+2+35+5 = 69
    assert_eq!(run_example("11-destructuring.cl"), 69);
}

#[test]
fn example_12_closures() {
    // 6+42+42+6+42+10+42+42+10+10+11 = 263
    assert_eq!(run_example("12-closures.cl"), 263);
}

#[test]
fn example_13_higher_order() {
    // 42+2+5+54+45+12+21+15+7 = 203
    assert_eq!(run_example("13-higher-order.cl"), 203);
}

#[test]
fn example_14_vecs() {
    // 5+60+99+6+3+6+300+62 = 541
    assert_eq!(run_example("14-vecs.cl"), 541);
}

// Ring 2A examples: traits, operator dispatch

#[test]
fn example_15_traits() {
    // Num(7+7+42+5+30) + Float(1+1) + Eq(1+1+1+1+0) + Ord(1+1+0)
    // + fact(1) + sum(1) + closure(42) + ADT(25) + named(25)
    // + constrained(42+49+25) + default(1+1+1+1+0+1+0) = 314
    assert_eq!(run_example("15-traits.cl"), 314);
}
