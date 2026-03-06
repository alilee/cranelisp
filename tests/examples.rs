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

// spec: 04-expressions §4.1.1 — integer literal arithmetic
#[test]
fn example_01_integers() {
    // 7 + 7 + 42 + 3 + 17 + (-7) = 69
    assert_eq!(run_example("01-integers.cl"), 69);
}

// spec: 04-expressions §4.1.3 — boolean literals and comparisons
#[test]
fn example_02_booleans() {
    // eq=1, neq=1, lt=1, gt=1, le=1, ge=0, sign(42)=1, sign(0)=0, sign(-7)=-1 = 5
    assert_eq!(run_example("02-booleans.cl"), 5);
}

// spec: 04-expressions §4.3 — let expression
#[test]
fn example_03_let_bindings() {
    // 6 + 9 + 30 + 20 + 25 + 7 = 97
    assert_eq!(run_example("03-let-bindings.cl"), 97);
}

// spec: 05-definitions §5.1 — function definition and application
#[test]
fn example_04_functions() {
    // 42 + 7 + 25 + 40 + 6 + 7 + 3 + 5 = 135
    assert_eq!(run_example("04-functions.cl"), 135);
}

// spec: 12-runtime §12.5 — tail call optimization and recursion
#[test]
fn example_05_recursion() {
    // 120 + 3628800 + 55 + 6 + 5050 + 1024 = 3635055
    assert_eq!(run_example("05-recursion.cl"), 3635055);
}

// spec: 05-definitions §5.2.3 — enum ADT definition
#[test]
fn example_06_enums() {
    // 2 + 0 + 1 + 1 + 1 + 99 = 104
    assert_eq!(run_example("06-enums.cl"), 104);
}

// spec: 03-types §3.3 — type variables and let-polymorphism
#[test]
fn example_07_polymorphism() {
    // 42+10+10+20+7+30 = 119
    assert_eq!(run_example("07-polymorphism.cl"), 119);
}

// spec: 03-types §3.1 — Float primitive type
#[test]
fn example_08_floats() {
    // 1+1+1+1+1+1+1+0+1+1 = 9
    assert_eq!(run_example("08-floats.cl"), 9);
}

// Ring 1 examples: strings, ADTs, destructuring, closures, higher-order

// spec: 03-types §3.1 — String primitive type and operations
#[test]
fn example_09_strings() {
    // 5+0+11+3+1+0+2+4+12+16+1 = 55
    assert_eq!(run_example("09-strings.cl"), 55);
}

// spec: 05-definitions §5.2 — algebraic data type definitions
#[test]
fn example_10_adts() {
    // 7+60+42+99+7+0+30+20 = 265
    assert_eq!(run_example("10-adts.cl"), 265);
}

// spec: 06-pattern-matching §6.2 — pattern kinds in match
#[test]
fn example_11_destructuring() {
    // 4+7+1+15+2+35+5 = 69
    assert_eq!(run_example("11-destructuring.cl"), 69);
}

// spec: 04-expressions §4.5.1 — free variable capture in lambdas
#[test]
fn example_12_closures() {
    // 6+42+42+6+42+10+42+42+10+10+11 = 263
    assert_eq!(run_example("12-closures.cl"), 263);
}

// spec: 04-expressions §4.6 — function application and higher-order functions
#[test]
fn example_13_higher_order() {
    // 42+2+5+54+45+12+21+15+7 = 203
    assert_eq!(run_example("13-higher-order.cl"), 203);
}

// spec: 03-types §3.2.4 — Vec type operations
#[test]
fn example_14_vecs() {
    // 5+60+99+6+3+6+300+62 = 541
    assert_eq!(run_example("14-vecs.cl"), 541);
}

// Ring 2A examples: traits, operator dispatch

// spec: 07-traits §7.1 — trait declaration, implementation, and dispatch
#[test]
fn example_15_traits() {
    // Num(7+7+42+5+30) + Float(1+1) + Eq(1+1+1+1+0) + Ord(1+1+0)
    // + fact(1) + sum(1) + closure(42) + ADT(25) + named(25)
    // + constrained(42+49+25) + default(1+1+1+1+0+1+0) = 314
    assert_eq!(run_example("15-traits.cl"), 314);
}
