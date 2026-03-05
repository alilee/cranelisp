// Integration tests verifying that Ring 0 example programs compile and
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
