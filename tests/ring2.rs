// Ring 2A integration tests: traits, operator dispatch, constrained polymorphism.
//
// Tests the full pipeline from source text to execution result.
// Organized by category per tests/plan/ring2.md (Ring 2A items only).
//
// Ring 2A introduces trait-based operator dispatch:
//   Num trait: +, -, *, / for Int and Float
//   Eq trait:  =   for Int, Float, Bool, String
//   Ord trait: <   for Int, Float
// Default methods (!=, >, <=, >=) are registered but codegen not yet wired.
// Named primitives (add-i64, eq-i64, etc.) remain available (accretive).
//
// Since Decision 17 eliminated compiler-seeded traits, tests that use
// trait-dispatched operators must define traits inline.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::*;
use cranelisp::repl::ReplSession;
use cranelisp_types::Type;

// ---------------------------------------------------------------------------
// Trait prelude helpers — inline trait definitions for tests
// ---------------------------------------------------------------------------

fn num_trait_prelude() -> &'static str {
    r#"(deftrait Num (+ [self self] self) (- [self self] self) (* [self self] self) (/ [self self] self))
(impl Num Int (defn + [a b] (add-i64 a b)) (defn - [a b] (sub-i64 a b)) (defn * [a b] (mul-i64 a b)) (defn / [a b] (div-i64 a b)))
(impl Num Float (defn + [a b] (add-f64 a b)) (defn - [a b] (sub-f64 a b)) (defn * [a b] (mul-f64 a b)) (defn / [a b] (div-f64 a b)))"#
}

fn eq_trait_prelude() -> &'static str {
    r#"(deftrait Eq (= [self self] Bool) (!= [self self] Bool))
(impl Eq Int (defn = [a b] (eq-i64 a b)) (defn != [a b] (not (eq-i64 a b))))
(impl Eq Float (defn = [a b] (eq-f64 a b)) (defn != [a b] (not (eq-f64 a b))))
(impl Eq String (defn = [a b] (str-eq a b)) (defn != [a b] (not (str-eq a b))))
(impl Eq Bool (defn = [a b] (eq-bool a b)) (defn != [a b] (not (eq-bool a b))))"#
}

fn ord_trait_prelude() -> &'static str {
    r#"(deftrait Ord (< [self self] Bool) (> [self self] Bool) (<= [self self] Bool) (>= [self self] Bool))
(impl Ord Int (defn < [a b] (lt-i64 a b)) (defn > [a b] (gt-i64 a b)) (defn <= [a b] (le-i64 a b)) (defn >= [a b] (ge-i64 a b)))
(impl Ord Float (defn < [a b] (lt-f64 a b)) (defn > [a b] (gt-f64 a b)) (defn <= [a b] (le-f64 a b)) (defn >= [a b] (ge-f64 a b)))"#
}

/// All core trait definitions combined.
fn all_traits_prelude() -> String {
    format!("{}\n{}\n{}", num_trait_prelude(), eq_trait_prelude(), ord_trait_prelude())
}

/// Prepend all core trait definitions to a batch source string.
fn with_traits(src: &str) -> String {
    format!("{}\n{}", all_traits_prelude(), src)
}

/// Load all core trait definitions into a REPL session.
/// Each form is eval'd separately since the REPL processes one top-level form at a time.
fn load_traits(session: &mut cranelisp::repl::ReplSession) {
    // Num trait
    session.eval("(deftrait Num (+ [self self] self) (- [self self] self) (* [self self] self) (/ [self self] self))").unwrap_or_else(|e| panic!("failed to load Num deftrait: {e}"));
    session.eval("(impl Num Int (defn + [a b] (add-i64 a b)) (defn - [a b] (sub-i64 a b)) (defn * [a b] (mul-i64 a b)) (defn / [a b] (div-i64 a b)))").unwrap_or_else(|e| panic!("failed to load Num impl Int: {e}"));
    session.eval("(impl Num Float (defn + [a b] (add-f64 a b)) (defn - [a b] (sub-f64 a b)) (defn * [a b] (mul-f64 a b)) (defn / [a b] (div-f64 a b)))").unwrap_or_else(|e| panic!("failed to load Num impl Float: {e}"));
    // Eq trait (with !=)
    session.eval("(deftrait Eq (= [self self] Bool) (!= [self self] Bool))").unwrap_or_else(|e| panic!("failed to load Eq deftrait: {e}"));
    session.eval("(impl Eq Int (defn = [a b] (eq-i64 a b)) (defn != [a b] (not (eq-i64 a b))))").unwrap_or_else(|e| panic!("failed to load Eq impl Int: {e}"));
    session.eval("(impl Eq Float (defn = [a b] (eq-f64 a b)) (defn != [a b] (not (eq-f64 a b))))").unwrap_or_else(|e| panic!("failed to load Eq impl Float: {e}"));
    session.eval(r#"(impl Eq String (defn = [a b] (str-eq a b)) (defn != [a b] (not (str-eq a b))))"#).unwrap_or_else(|e| panic!("failed to load Eq impl String: {e}"));
    session.eval("(impl Eq Bool (defn = [a b] (eq-bool a b)) (defn != [a b] (not (eq-bool a b))))").unwrap_or_else(|e| panic!("failed to load Eq impl Bool: {e}"));
    // Ord trait (with >, <=, >=)
    session.eval("(deftrait Ord (< [self self] Bool) (> [self self] Bool) (<= [self self] Bool) (>= [self self] Bool))").unwrap_or_else(|e| panic!("failed to load Ord deftrait: {e}"));
    session.eval("(impl Ord Int (defn < [a b] (lt-i64 a b)) (defn > [a b] (gt-i64 a b)) (defn <= [a b] (le-i64 a b)) (defn >= [a b] (ge-i64 a b)))").unwrap_or_else(|e| panic!("failed to load Ord impl Int: {e}"));
    session.eval("(impl Ord Float (defn < [a b] (lt-f64 a b)) (defn > [a b] (gt-f64 a b)) (defn <= [a b] (le-f64 a b)) (defn >= [a b] (ge-f64 a b)))").unwrap_or_else(|e| panic!("failed to load Ord impl Float: {e}"));
}

// =============================================================================
// Trait: Num operator dispatch — Int (spec: 07-traits)
// =============================================================================

// spec: 07-traits §7.5 — Num + operator Int dispatch
#[test]
fn trait_plus_int() {
    let src = &with_traits("(defn main [] (+ 1 2))");
    assert_eq!(compile_and_run_simple(src), 3);
}

// spec: 07-traits §7.5 — Num - operator Int dispatch
#[test]
fn trait_minus_int() {
    let src = &with_traits("(defn main [] (- 10 3))");
    assert_eq!(compile_and_run_simple(src), 7);
}

// spec: 07-traits §7.5 — Num * operator Int dispatch
#[test]
fn trait_multiply_int() {
    let src = &with_traits("(defn main [] (* 6 7))");
    assert_eq!(compile_and_run_simple(src), 42);
}

// spec: 07-traits §7.5 — Num / operator Int dispatch
#[test]
fn trait_divide_int() {
    let src = &with_traits("(defn main [] (/ 20 4))");
    assert_eq!(compile_and_run_simple(src), 5);
}

// spec: 07-traits §7.5 — Num + operator negative operand
#[test]
fn trait_plus_negative() {
    let src = &with_traits("(defn main [] (+ -3 5))");
    assert_eq!(compile_and_run_simple(src), 2);
}

// spec: 07-traits §7.5 — Num - operator negative result
#[test]
fn trait_minus_negative_result() {
    let src = &with_traits("(defn main [] (- 3 10))");
    assert_eq!(compile_and_run_simple(src), -7);
}

// spec: 07-traits §7.5 — Num + operator with zero
#[test]
fn trait_plus_zero() {
    let src = &with_traits("(defn main [] (+ 0 42))");
    assert_eq!(compile_and_run_simple(src), 42);
}

// =============================================================================
// Trait: Num operator dispatch — Float (spec: 07-traits)
// =============================================================================

// spec: 07-traits §7.5 — Num + operator Float dispatch
#[test]
fn trait_plus_float() {
    let src = &with_traits("(defn main [] (+ 1.5 2.5))");
    let (value, ty) = compile_and_run_typed(src);
    assert_eq!(ty, Type::Float);
    let f = f64::from_bits(value as u64);
    assert!((f - 4.0).abs() < f64::EPSILON);
}

// spec: 07-traits §7.5 — Num - operator Float dispatch
#[test]
fn trait_minus_float() {
    let src = &with_traits("(defn main [] (- 10.0 3.5))");
    let (value, _) = compile_and_run_typed(src);
    let f = f64::from_bits(value as u64);
    assert!((f - 6.5).abs() < f64::EPSILON);
}

// spec: 07-traits §7.5 — Num * operator Float dispatch
#[test]
fn trait_multiply_float() {
    let src = &with_traits("(defn main [] (* 3.0 4.0))");
    let (value, _) = compile_and_run_typed(src);
    let f = f64::from_bits(value as u64);
    assert!((f - 12.0).abs() < f64::EPSILON);
}

// spec: 07-traits §7.5 — Num / operator Float dispatch
#[test]
fn trait_divide_float() {
    let src = &with_traits("(defn main [] (/ 10.0 2.0))");
    let (value, _) = compile_and_run_typed(src);
    let f = f64::from_bits(value as u64);
    assert!((f - 5.0).abs() < f64::EPSILON);
}

// =============================================================================
// Trait: Num nested/compound expressions (spec: 07-traits)
// =============================================================================

// spec: 07-traits §7.5 — nested Num operator expressions
#[test]
fn trait_plus_nested() {
    let src = &with_traits("(defn main [] (+ (+ 1 2) (+ 3 4)))");
    assert_eq!(compile_and_run_simple(src), 10);
}

// spec: 07-traits §7.5 — mixed arithmetic operator expression
#[test]
fn trait_mixed_arithmetic_expr() {
    let src = &with_traits("(defn main [] (* (+ 2 3) (- 10 4)))");
    assert_eq!(compile_and_run_simple(src), 30);
}

// spec: 07-traits §7.5 — trait operators in let expression
#[test]
fn trait_arithmetic_in_let() {
    let src = &with_traits("
        (defn main []
          (let [x (+ 3 4)
                y (* 2 3)]
            (+ x y)))
    ");
    assert_eq!(compile_and_run_simple(src), 13);
}

// spec: 07-traits §7.5 — trait operators in if expression
#[test]
fn trait_arithmetic_in_if() {
    let src = &with_traits("
        (defn main []
          (if (= 1 1) (+ 10 20) (- 10 20)))
    ");
    assert_eq!(compile_and_run_simple(src), 30);
}

// spec: 07-traits §7.5 — trait operators as function argument
#[test]
fn trait_arithmetic_as_function_arg() {
    // Using an annotated param avoids constrained poly — type is concrete.
    let src = &with_traits("
        (defn double [:Int x] (+ x x))
        (defn main [] (double (+ 10 11)))
    ");
    assert_eq!(compile_and_run_simple(src), 42);
}

// =============================================================================
// Trait: Eq operator dispatch (spec: 07-traits)
// =============================================================================

// spec: 07-traits §7.5 — Eq = operator Int true
#[test]
fn trait_eq_int_true() {
    let src = &with_traits("(defn main [] (if (= 5 5) 1 0))");
    assert_eq!(compile_and_run_simple(src), 1);
}

// spec: 07-traits §7.5 — Eq = operator Int false
#[test]
fn trait_eq_int_false() {
    let src = &with_traits("(defn main [] (if (= 5 3) 1 0))");
    assert_eq!(compile_and_run_simple(src), 0);
}

// spec: 07-traits §7.5 — Eq = operator Float
#[test]
fn trait_eq_float() {
    let src = &with_traits("(defn main [] (if (= 3.14 3.14) 1 0))");
    assert_eq!(compile_and_run_simple(src), 1);
}

// spec: 07-traits §7.5 — Eq = operator Float false
#[test]
fn trait_eq_float_false() {
    let src = &with_traits("(defn main [] (if (= 3.14 2.71) 1 0))");
    assert_eq!(compile_and_run_simple(src), 0);
}

// spec: 07-traits §7.5 — Eq = operator Bool true
#[test]
fn trait_eq_bool_true() {
    let src = &with_traits("(defn main [] (if (= true true) 1 0))");
    assert_eq!(compile_and_run_simple(src), 1);
}

// spec: 07-traits §7.5 — Eq = operator Bool false
#[test]
fn trait_eq_bool_false() {
    let src = &with_traits("(defn main [] (if (= true false) 1 0))");
    assert_eq!(compile_and_run_simple(src), 0);
}

// spec: 07-traits §7.5 — Eq = operator String
#[test]
fn trait_eq_string() {
    let src = &with_traits(r#"(defn main [] (if (= "hello" "hello") 1 0))"#);
    assert_eq!(compile_and_run_simple(src), 1);
}

// spec: 07-traits §7.5 — Eq = operator String false
#[test]
fn trait_eq_string_false() {
    let src = &with_traits(r#"(defn main [] (if (= "hello" "world") 1 0))"#);
    assert_eq!(compile_and_run_simple(src), 0);
}

// =============================================================================
// Trait: Ord operator dispatch — < (spec: 07-traits)
// =============================================================================

// spec: 07-traits §7.5 — Ord < operator Int true
#[test]
fn trait_lt_int_true() {
    let src = &with_traits("(defn main [] (if (< 3 5) 1 0))");
    assert_eq!(compile_and_run_simple(src), 1);
}

// spec: 07-traits §7.5 — Ord < operator Int false
#[test]
fn trait_lt_int_false() {
    let src = &with_traits("(defn main [] (if (< 5 3) 1 0))");
    assert_eq!(compile_and_run_simple(src), 0);
}

// spec: 07-traits §7.5 — Ord < operator Int equal
#[test]
fn trait_lt_int_equal() {
    let src = &with_traits("(defn main [] (if (< 5 5) 1 0))");
    assert_eq!(compile_and_run_simple(src), 0);
}

// spec: 07-traits §7.5 — Ord < operator Float
#[test]
fn trait_lt_float() {
    let src = &with_traits("(defn main [] (if (< 1.0 2.0) 1 0))");
    assert_eq!(compile_and_run_simple(src), 1);
}

// spec: 07-traits §7.5 — Ord < operator Float false
#[test]
fn trait_lt_float_false() {
    let src = &with_traits("(defn main [] (if (< 2.0 1.0) 1 0))");
    assert_eq!(compile_and_run_simple(src), 0);
}

// =============================================================================
// Default methods — >, <=, >= (spec: 07-traits)
// =============================================================================

// spec: 07-traits §7.1.5 — default method > Int
#[test]
fn default_method_gt_int() {
    let src = &with_traits("(defn main [] (if (> 5 3) 1 0))");
    assert_eq!(compile_and_run_simple(src), 1);
}

// spec: 07-traits §7.1.5 — default method > Int false
#[test]
fn default_method_gt_int_false() {
    let src = &with_traits("(defn main [] (if (> 3 5) 1 0))");
    assert_eq!(compile_and_run_simple(src), 0);
}

// spec: 07-traits §7.1.5 — default method <= Int
#[test]
fn default_method_le_int() {
    let src = &with_traits("(defn main [] (if (<= 3 5) 1 0))");
    assert_eq!(compile_and_run_simple(src), 1);
}

// spec: 07-traits §7.1.5 — default method <= Int equal
#[test]
fn default_method_le_int_equal() {
    let src = &with_traits("(defn main [] (if (<= 5 5) 1 0))");
    assert_eq!(compile_and_run_simple(src), 1);
}

// spec: 07-traits §7.1.5 — default method <= Int false
#[test]
fn default_method_le_int_false() {
    let src = &with_traits("(defn main [] (if (<= 5 3) 1 0))");
    assert_eq!(compile_and_run_simple(src), 0);
}

// spec: 07-traits §7.1.5 — default method >= Int
#[test]
fn default_method_ge_int() {
    let src = &with_traits("(defn main [] (if (>= 5 3) 1 0))");
    assert_eq!(compile_and_run_simple(src), 1);
}

// spec: 07-traits §7.1.5 — default method >= Int equal
#[test]
fn default_method_ge_int_equal() {
    let src = &with_traits("(defn main [] (if (>= 5 5) 1 0))");
    assert_eq!(compile_and_run_simple(src), 1);
}

// spec: 07-traits §7.1.5 — default method >= Int false
#[test]
fn default_method_ge_int_false() {
    let src = &with_traits("(defn main [] (if (>= 3 5) 1 0))");
    assert_eq!(compile_and_run_simple(src), 0);
}

// != requires reader support for ! as operator char.
// spec: 07-traits §7.1.5 — default method != Int
#[test]
fn default_method_neq_int() {
    let src = &with_traits("(defn main [] (if (!= 3 5) 1 0))");
    assert_eq!(compile_and_run_simple(src), 1);
}

// spec: 07-traits §7.1.5 — default method != Int equal
#[test]
fn default_method_neq_int_equal() {
    let src = &with_traits("(defn main [] (if (!= 5 5) 1 0))");
    assert_eq!(compile_and_run_simple(src), 0);
}

// spec: 07-traits §7.1.5 — default method != String (different strings)
#[test]
fn default_method_neq_string() {
    let src = &with_traits(r#"(defn main [] (if (!= "hello" "world") 1 0))"#);
    assert_eq!(compile_and_run_simple(src), 1);
}

// spec: 07-traits §7.1.5 — default method != String (equal strings)
#[test]
fn default_method_neq_string_equal() {
    let src = &with_traits(r#"(defn main [] (if (!= "same" "same") 1 0))"#);
    assert_eq!(compile_and_run_simple(src), 0);
}

// =============================================================================
// Constrained polymorphism (spec: 03-types, 07-traits)
// Functions that use operators with type-variable args become constrained.
// Monomorphisation codegen not yet wired (empty resolutions).
// =============================================================================

// Functions that use operators with literal operands (unified to Int within body)
// are NOT constrained — the operators resolve during type inference.
// Functions whose operator operands are ALL type-variable params become constrained.
// spec: 07-traits §7.5 — inline operator in main
#[test]
fn inline_operator_in_main() {
    // Operators used directly in main with literals — always works.
    let src = &with_traits("
        (defn main []
          (if (= 0 0) (+ 10 20) (- 10 20)))
    ");
    assert_eq!(compile_and_run_simple(src), 30);
}

// spec: 07-traits §7.5 — function using operators with literals
#[test]
fn fn_using_operators_with_literals() {
    // n is unified to Int by literal 0, so this is NOT constrained.
    let src = &with_traits("
        (defn sum-to [n]
          (if (= n 0) 0 (+ n (sum-to (- n 1)))))
        (defn main [] (sum-to 10))
    ");
    assert_eq!(compile_and_run_simple(src), 55);
}

// spec: 07-traits §7.5 — factorial with trait operators
#[test]
fn fn_factorial_with_operators() {
    // n unified to Int by literal 0.
    let src = &with_traits("
        (defn fact [n]
          (if (= n 0) 1 (* n (fact (- n 1)))))
        (defn main [] (fact 10))
    ");
    assert_eq!(compile_and_run_simple(src), 3628800);
}

// Functions where operators only act on type-variable params are constrained.
// These need monomorphisation which isn't fully wired.
// spec: 03-types §3.6 — constrained polymorphic fibonacci
#[test]
fn constrained_fn_fibonacci() {
    let mut session = repl_session();
    load_traits(&mut session);
    repl_eval(&mut session, "(defn fib [n] (if (= n 0) 0 (if (= n 1) 1 (+ (fib (- n 1)) (fib (- n 2))))))");
    assert_eq!(repl_eval(&mut session, "(fib 10)"), 55);
}

// spec: 03-types §3.6 — constrained polymorphic clamp
#[test]
fn constrained_fn_clamp() {
    let mut session = repl_session();
    load_traits(&mut session);
    repl_eval(&mut session, "(defn clamp [x lo hi] (if (< x lo) lo (if (< hi x) hi x)))");
    assert_eq!(repl_eval(&mut session, "(clamp 5 0 10)"), 5);
}

// spec: 03-types §3.6 — constrained poly clamp low
#[test]
fn constrained_fn_clamp_low() {
    let mut session = repl_session();
    load_traits(&mut session);
    repl_eval(&mut session, "(defn clamp [x lo hi] (if (< x lo) lo (if (< hi x) hi x)))");
    assert_eq!(repl_eval(&mut session, "(clamp -5 0 10)"), 0);
}

// spec: 03-types §3.6 — constrained poly clamp high
#[test]
fn constrained_fn_clamp_high() {
    let mut session = repl_session();
    load_traits(&mut session);
    repl_eval(&mut session, "(defn clamp [x lo hi] (if (< x lo) lo (if (< hi x) hi x)))");
    assert_eq!(repl_eval(&mut session, "(clamp 15 0 10)"), 10);
}

// Truly constrained functions (params remain polymorphic) need monomorphisation.
// spec: 03-types §3.6.3 — constrained fn monomorphised at Int
#[test]
fn constrained_add_int() {
    let mut session = repl_session();
    load_traits(&mut session);
    repl_eval(&mut session, "(defn add [x y] (+ x y))");
    assert_eq!(repl_eval(&mut session, "(add 3 4)"), 7);
}

// spec: 03-types §3.6.3 — constrained fn monomorphised at Float
#[test]
fn constrained_add_float() {
    let mut session = repl_session();
    load_traits(&mut session);
    repl_eval(&mut session, "(defn add [x y] (+ x y))");
    let (value, ty) = repl_eval_typed(&mut session, "(add 1.5 2.5)");
    assert_eq!(ty, Type::Float);
    let f = f64::from_bits(value as u64);
    assert!((f - 4.0).abs() < f64::EPSILON);
}

// spec: 03-types §3.6.3 — constrained fn at both Int and Float
#[test]
fn constrained_add_both_types() {
    let mut session = repl_session();
    load_traits(&mut session);
    repl_eval(&mut session, "(defn add [x y] (+ x y))");
    assert_eq!(repl_eval(&mut session, "(add 3 4)"), 7);
}

// spec: 03-types §3.6 — constrained poly multiply
#[test]
fn constrained_multiply() {
    let mut session = repl_session();
    load_traits(&mut session);
    repl_eval(&mut session, "(defn square [x] (* x x))");
    assert_eq!(repl_eval(&mut session, "(square 7)"), 49);
}

// spec: 03-types §3.6 — constrained poly subtract
#[test]
fn constrained_subtract() {
    let mut session = repl_session();
    load_traits(&mut session);
    repl_eval(&mut session, "(defn diff [x y] (- x y))");
    assert_eq!(repl_eval(&mut session, "(diff 10 3)"), 7);
}

// spec: 03-types §3.6 — constrained poly comparison
#[test]
fn constrained_comparison() {
    let mut session = repl_session();
    load_traits(&mut session);
    repl_eval(&mut session, "(defn less-than [x y] (< x y))");
    assert_eq!(repl_eval(&mut session, "(if (less-than 3 5) 1 0)"), 1);
}

// spec: 03-types §3.6 — constrained poly equality
#[test]
fn constrained_equality() {
    let mut session = repl_session();
    load_traits(&mut session);
    repl_eval(&mut session, "(defn is-equal [x y] (= x y))");
    assert_eq!(repl_eval(&mut session, "(if (is-equal 5 5) 1 0)"), 1);
}

// spec: 03-types §3.6 — constrained poly multi-operator
#[test]
fn constrained_multi_op() {
    let mut session = repl_session();
    load_traits(&mut session);
    repl_eval(&mut session, "(defn compute [x y] (+ (* x x) (* y y)))");
    assert_eq!(repl_eval(&mut session, "(compute 3 4)"), 25);
}

// spec: 03-types §3.6 — constrained fn never called compiles
#[test]
fn constrained_never_called_ok() {
    // A constrained function that is never called should not error.
    let src = &with_traits("
        (defn unused-add [x y] (+ x y))
        (defn main [] 42)
    ");
    assert_eq!(compile_and_run_simple(src), 42);
}

// spec: 03-types §3.6 — constrained fn in let scope
#[test]
fn constrained_with_let() {
    let mut session = repl_session();
    load_traits(&mut session);
    repl_eval(&mut session, "(defn double [x] (+ x x))");
    assert_eq!(repl_eval(&mut session, "(let [n 21] (double n))"), 42);
}

// spec: 03-types §3.6 — constrained fn in if expression
#[test]
fn constrained_with_if() {
    let mut session = repl_session();
    load_traits(&mut session);
    repl_eval(&mut session, "(defn abs-diff [x y] (if (< x y) (- y x) (- x y)))");
    assert_eq!(repl_eval(&mut session, "(abs-diff 3 10)"), 7);
}

// =============================================================================
// Type annotations (spec: 03-types)
// =============================================================================

// spec: 04-expressions §4.9 — concrete Int annotation
#[test]
fn annotation_concrete_type_int() {
    let src = &with_traits("(defn inc [:Int x] (+ x 1)) (defn main [] (inc 5))");
    assert_eq!(compile_and_run_simple(src), 6);
}

// spec: 04-expressions §4.9 — concrete Float annotation
#[test]
fn annotation_concrete_type_float() {
    let src = &with_traits("(defn half [:Float x] (/ x 2.0)) (defn main [] (half 10.0))");
    let (value, _) = compile_and_run_typed(src);
    let f = f64::from_bits(value as u64);
    assert!((f - 5.0).abs() < f64::EPSILON);
}

// spec: 04-expressions §4.9 — annotation wrong type error
#[test]
fn annotation_wrong_type_error() {
    assert_type_error(&with_traits("(defn inc [:Int x] (+ x 1)) (defn main [] (inc 1.5))"), "");
}

// spec: 04-expressions §4.9 — Bool parameter annotation
#[test]
fn annotation_bool_param() {
    let src = "(defn to-int [:Bool b] (if b 1 0)) (defn main [] (to-int true))";
    assert_eq!(compile_and_run_simple(src), 1);
}

// spec: 04-expressions §4.9 — String parameter annotation
#[test]
fn annotation_string_param() {
    let src = r#"(defn len [:String s] (str-len s)) (defn main [] (len "hello"))"#;
    assert_eq!(compile_and_run_simple(src), 5);
}

// spec: 04-expressions §4.5.2 — annotated lambda parameter
#[test]
fn annotated_lambda() {
    let src = &with_traits("(defn main [] ((fn [:Int x] (+ x 1)) 5))");
    assert_eq!(compile_and_run_simple(src), 6);
}

// spec: 04-expressions §4.9 — mixed annotated and inferred
#[test]
fn annotation_mixed_annotated_and_inferred() {
    let src = &with_traits("
        (defn add-offset [:Int x y] (+ x y))
        (defn main [] (add-offset 10 20))
    ");
    assert_eq!(compile_and_run_simple(src), 30);
}

// spec: 04-expressions §4.9 — annotation constrains body type
#[test]
fn annotation_constrains_body() {
    // Annotating param as Int means body operators resolve concretely.
    let src = &with_traits("
        (defn square [:Int x] (* x x))
        (defn main [] (square 7))
    ");
    assert_eq!(compile_and_run_simple(src), 49);
}

// spec: 04-expressions §4.9 — annotation on both params
#[test]
fn annotation_on_both_params() {
    let src = &with_traits("
        (defn add [:Int a :Int b] (+ a b))
        (defn main [] (add 10 20))
    ");
    assert_eq!(compile_and_run_simple(src), 30);
}

// spec: 04-expressions §4.9 — annotation mismatch at call site
#[test]
fn annotation_mismatch_call_error() {
    // Float arg to Int-annotated param.
    assert_type_error(
        "(defn inc [:Int x] (+ x 1)) (defn main [] (inc 1.5))",
        "",
    );
}

// =============================================================================
// Operator transition regression: named primitives still work
// =============================================================================

// spec: none — regression: named primitive add-i64 still works
#[test]
fn regression_named_prim_add_i64() {
    let src = "(defn main [] (add-i64 3 4))";
    assert_eq!(compile_and_run_simple(src), 7);
}

// spec: none — regression: named primitive sub-i64 still works
#[test]
fn regression_named_prim_sub_i64() {
    let src = "(defn main [] (sub-i64 10 3))";
    assert_eq!(compile_and_run_simple(src), 7);
}

// spec: none — regression: named primitive mul-i64 still works
#[test]
fn regression_named_prim_mul_i64() {
    let src = "(defn main [] (mul-i64 6 7))";
    assert_eq!(compile_and_run_simple(src), 42);
}

// spec: none — regression: named primitive div-i64 still works
#[test]
fn regression_named_prim_div_i64() {
    let src = "(defn main [] (div-i64 20 4))";
    assert_eq!(compile_and_run_simple(src), 5);
}

// spec: none — regression: named primitive eq-i64 still works
#[test]
fn regression_named_prim_eq_i64() {
    let src = "(defn main [] (if (eq-i64 5 5) 1 0))";
    assert_eq!(compile_and_run_simple(src), 1);
}

// spec: none — regression: named primitive lt-i64 still works
#[test]
fn regression_named_prim_lt_i64() {
    let src = "(defn main [] (if (lt-i64 3 5) 1 0))";
    assert_eq!(compile_and_run_simple(src), 1);
}

// spec: none — regression: named primitive add-f64 still works
#[test]
fn regression_named_prim_add_f64() {
    let src = "(defn main [] (add-f64 1.5 2.5))";
    let (value, ty) = compile_and_run_typed(src);
    assert_eq!(ty, Type::Float);
    let f = f64::from_bits(value as u64);
    assert!((f - 4.0).abs() < f64::EPSILON);
}

// spec: none — regression: named primitive le-i64 still works
#[test]
fn regression_named_prim_le_i64() {
    let src = "(defn main [] (if (le-i64 3 3) 1 0))";
    assert_eq!(compile_and_run_simple(src), 1);
}

// spec: none — regression: named primitive ge-i64 still works
#[test]
fn regression_named_prim_ge_i64() {
    let src = "(defn main [] (if (ge-i64 5 3) 1 0))";
    assert_eq!(compile_and_run_simple(src), 1);
}

// spec: none — regression: named primitives and trait ops coexist
#[test]
fn regression_named_and_trait_ops_in_same_program() {
    // Mix named primitives and trait operators in the same program.
    let src = &with_traits("
        (defn main []
          (let [a (add-i64 1 2)
                b (+ 3 4)]
            (+ a b)))
    ");
    assert_eq!(compile_and_run_simple(src), 10);
}

// =============================================================================
// User-defined traits (spec: 07-traits)
// User-defined trait impl methods need pipeline wiring for batch compilation.
// =============================================================================

// spec: 07-traits §7.3.1 — user-defined trait simple impl
#[test]
fn user_trait_simple() {
    let src = "
        (deftrait (Sizeable a)
          (size [a] Int))
        (impl Sizeable Int
          (defn size [x] x))
        (defn main [] (size 42))
    ";
    assert_eq!(compile_and_run_simple(src), 42);
}

// spec: 07-traits §7.3.1 — user-defined trait on ADT
#[test]
fn user_trait_adt() {
    let src = "
        (deftrait (Sizeable a)
          (size [a] Int))
        (deftype Color Red Green Blue)
        (impl Sizeable Color
          (defn size [c] (match c [Red 1 Green 2 Blue 3])))
        (defn main [] (size Green))
    ";
    assert_eq!(compile_and_run_simple(src), 2);
}

// spec: 07-traits §7.3.1 — user-defined trait multiple impls
#[test]
fn user_trait_multiple_impls() {
    let src = &with_traits("
        (deftrait (Sizeable a)
          (size [a] Int))
        (impl Sizeable Int
          (defn size [x] x))
        (impl Sizeable Bool
          (defn size [b] (if b 1 0)))
        (defn main [] (+ (size 10) (size true)))
    ");
    assert_eq!(compile_and_run_simple(src), 11);
}

// =============================================================================
// Error cases (spec: 07-traits, 03-types)
// =============================================================================

// spec: 07-traits §7.5 — no Num impl for Bool (type mismatch)
// NOTE: Decision 17 (user-defined traits) doesn't enforce same-type constraint
// on `self`/`other` params, so `(+ 1 1.5)` no longer errors. Instead test
// that using a type with no Num impl at all fails.
// NOTE: In REPL mode, constrained polymorphic trait errors surface at the call
// site, not at defn time. These tests eval the expression directly to trigger
// the error at monomorphisation time.
// IGNORED: In REPL mode (form-by-form eval), trait constraint violations on
// bare expressions like (+ true true) are not caught because monomorphisation
// is deferred. These tests require batch-mode compilation where all forms are
// compiled together and constraints are checked eagerly.
#[test]
fn error_type_mismatch_plus() {
    assert_error(&with_traits("(defn main [] (+ true true))"), "");
}

// spec: 07-traits §7.5 — Eq with mismatched argument types
#[test]
fn error_type_mismatch_eq() {
    // = requires both args to be the same type (self, self). Passing Int and Bool
    // should produce a type mismatch error.
    assert_error(&with_traits("(= 1 true)"), "");
}

// spec: 07-traits §7.5 — no Num impl for Bool
// IGNORED: same REPL deferred-monomorphisation limitation.
#[test]
fn error_plus_bool() {
    assert_error(&with_traits("(defn main [] (+ true false))"), "");
}

// spec: 07-traits §7.5 — no Num impl for String
// IGNORED: same REPL deferred-monomorphisation limitation.
#[test]
fn error_plus_string() {
    assert_error(&with_traits(r#"(defn main [] (+ "a" "b"))"#), "");
}

// spec: 07-traits §7.5 — no Ord impl for Bool
// IGNORED: same REPL deferred-monomorphisation limitation.
#[test]
fn error_lt_bool() {
    assert_error(&with_traits("(defn main [] (< true false))"), "");
}

// spec: 07-traits §7.5 — no Ord impl for String
// IGNORED: same REPL deferred-monomorphisation limitation.
#[test]
fn error_lt_string() {
    assert_error(&with_traits(r#"(defn main [] (< "a" "b"))"#), "");
}

// spec: 07-traits §7.5 — no Num impl for String (mixed types)
// IGNORED: same REPL deferred-monomorphisation limitation.
#[test]
fn error_mixed_types_in_operator() {
    assert_error(&with_traits(r#"(defn main [] (+ "hello" "world"))"#), "");
}

// =============================================================================
// REPL: Trait operator dispatch (spec: 07-traits, 12-runtime)
// =============================================================================

// spec: 07-traits §7.5 — Num + Int in REPL
#[test]
fn repl_trait_plus_int() {
    let mut session = repl_session();
    load_traits(&mut session);
    assert_eq!(repl_eval(&mut session, "(+ 1 2)"), 3);
}

// spec: 07-traits §7.5 — Num - Int in REPL
#[test]
fn repl_trait_minus_int() {
    let mut session = repl_session();
    load_traits(&mut session);
    assert_eq!(repl_eval(&mut session, "(- 10 3)"), 7);
}

// spec: 07-traits §7.5 — Num * Int in REPL
#[test]
fn repl_trait_multiply_int() {
    let mut session = repl_session();
    load_traits(&mut session);
    assert_eq!(repl_eval(&mut session, "(* 6 7)"), 42);
}

// spec: 07-traits §7.5 — Num / Int in REPL
#[test]
fn repl_trait_divide_int() {
    let mut session = repl_session();
    load_traits(&mut session);
    assert_eq!(repl_eval(&mut session, "(/ 20 4)"), 5);
}

// spec: 07-traits §7.5 — Eq = Int in REPL
#[test]
fn repl_trait_eq_int() {
    let mut session = repl_session();
    load_traits(&mut session);
    assert_eq!(repl_eval(&mut session, "(if (= 5 5) 1 0)"), 1);
    assert_eq!(repl_eval(&mut session, "(if (= 5 3) 1 0)"), 0);
}

// spec: 07-traits §7.5 — Ord < Int in REPL
#[test]
fn repl_trait_lt_int() {
    let mut session = repl_session();
    load_traits(&mut session);
    assert_eq!(repl_eval(&mut session, "(if (< 3 5) 1 0)"), 1);
    assert_eq!(repl_eval(&mut session, "(if (< 5 3) 1 0)"), 0);
}

// spec: 07-traits §7.5 — Num + Float in REPL
#[test]
fn repl_trait_plus_float() {
    let mut session = repl_session();
    load_traits(&mut session);
    let (value, ty) = repl_eval_typed(&mut session, "(+ 1.5 2.5)");
    assert_eq!(ty, Type::Float);
    let f = f64::from_bits(value as u64);
    assert!((f - 4.0).abs() < f64::EPSILON);
}

// spec: 07-traits §7.5 — Eq = String in REPL
#[test]
fn repl_trait_eq_string() {
    let mut session = repl_session();
    load_traits(&mut session);
    assert_eq!(repl_eval(&mut session, r#"(if (= "abc" "abc") 1 0)"#), 1);
    assert_eq!(repl_eval(&mut session, r#"(if (= "abc" "xyz") 1 0)"#), 0);
}

// spec: 07-traits §7.5 — Eq = Bool in REPL
#[test]
fn repl_trait_eq_bool() {
    let mut session = repl_session();
    load_traits(&mut session);
    assert_eq!(repl_eval(&mut session, "(if (= true true) 1 0)"), 1);
    assert_eq!(repl_eval(&mut session, "(if (= true false) 1 0)"), 0);
}

// spec: 07-traits §7.5 — Ord < Float in REPL
#[test]
fn repl_trait_lt_float() {
    let mut session = repl_session();
    load_traits(&mut session);
    assert_eq!(repl_eval(&mut session, "(if (< 1.0 2.0) 1 0)"), 1);
}

// spec: 07-traits §7.5 — chained trait arithmetic in REPL
#[test]
fn repl_trait_arithmetic_chained() {
    let mut session = repl_session();
    load_traits(&mut session);
    assert_eq!(repl_eval(&mut session, "(+ (* 3 4) (- 10 2))"), 20);
}

// REPL: Default methods (same issues as batch)
// spec: 07-traits §7.1.5 — default != in REPL
#[test]
fn repl_trait_neq_default() {
    let mut session = repl_session();
    load_traits(&mut session);
    assert_eq!(repl_eval(&mut session, "(if (!= 3 5) 1 0)"), 1);
}

// spec: 07-traits §7.1.5 — default >= in REPL
#[test]
fn repl_trait_ge_default() {
    let mut session = repl_session();
    load_traits(&mut session);
    assert_eq!(repl_eval(&mut session, "(if (>= 5 3) 1 0)"), 1);
}

// spec: 07-traits §7.1.5 — default <= in REPL
#[test]
fn repl_trait_le_default() {
    let mut session = repl_session();
    load_traits(&mut session);
    assert_eq!(repl_eval(&mut session, "(if (<= 3 5) 1 0)"), 1);
}

// spec: 07-traits §7.1.5 — default > in REPL
#[test]
fn repl_trait_gt_default() {
    let mut session = repl_session();
    load_traits(&mut session);
    assert_eq!(repl_eval(&mut session, "(if (> 5 3) 1 0)"), 1);
}

// =============================================================================
// REPL: Constrained polymorphism
// =============================================================================

// spec: 03-types §3.6 — constrained fn Int in REPL
#[test]
fn repl_constrained_fn_int() {
    let mut session = repl_session();
    load_traits(&mut session);
    repl_eval(&mut session, "(defn add [x y] (+ x y))");
    assert_eq!(repl_eval(&mut session, "(add 3 4)"), 7);
}

// spec: 03-types §3.6 — constrained fn Float in REPL
#[test]
fn repl_constrained_fn_float() {
    let mut session = repl_session();
    load_traits(&mut session);
    repl_eval(&mut session, "(defn add [x y] (+ x y))");
    let (value, ty) = repl_eval_typed(&mut session, "(add 1.5 2.5)");
    assert_eq!(ty, Type::Float);
    let f = f64::from_bits(value as u64);
    assert!((f - 4.0).abs() < f64::EPSILON);
}

// =============================================================================
// REPL: User-defined trait
// =============================================================================

// spec: 07-traits §7.3.1 — user-defined trait in REPL
#[test]
fn repl_user_trait() {
    let mut session = repl_session();
    repl_eval(
        &mut session,
        "(deftrait (Sizeable a) (size [a] Int))",
    );
    repl_eval(
        &mut session,
        "(impl Sizeable Int (defn size [x] x))",
    );
    assert_eq!(repl_eval(&mut session, "(size 42)"), 42);
}

// =============================================================================
// REPL: Defn type finalization (spec: 03-types, 07-traits)
// Functions that use operators with concrete types work fine.
// =============================================================================

// spec: 07-traits §7.5 — defn with operators returns Int in REPL
#[test]
fn repl_defn_operator_returns_int() {
    let mut session = repl_session();
    load_traits(&mut session);
    // Using annotated param avoids constrained poly.
    repl_eval(&mut session, "(defn double [:Int x] (+ x x))");
    assert_eq!(repl_eval(&mut session, "(double 21)"), 42);
}

// spec: 07-traits §7.5 — defn with = returns Bool in REPL
#[test]
fn repl_defn_eq_returns_bool() {
    let mut session = repl_session();
    load_traits(&mut session);
    repl_eval(&mut session, "(defn is-zero [x] (= x 0))");
    let (value, ty) = repl_eval_typed(&mut session, "(is-zero 0)");
    assert_eq!(ty, Type::Bool);
    assert_eq!(value, 1);
}

// spec: 07-traits §7.5 — defn with comparison chain in REPL
#[test]
fn repl_defn_using_comparison_chain() {
    let mut session = repl_session();
    load_traits(&mut session);
    repl_eval(
        &mut session,
        "(defn clamp [x lo hi] (if (< x lo) lo (if (< hi x) hi x)))",
    );
    assert_eq!(repl_eval(&mut session, "(clamp 5 0 10)"), 5);
}

// spec: 07-traits §7.5 — defn with concrete comparison in REPL
#[test]
fn repl_defn_concrete_comparison() {
    // clamp called immediately with Int literals pins everything to Int.
    let mut session = repl_session();
    load_traits(&mut session);
    assert_eq!(
        repl_eval(
            &mut session,
            "(let [x 5 lo 0 hi 10] (if (< x lo) lo (if (< hi x) hi x)))"
        ),
        5
    );
}

// spec: repl/spec.md §5.2 — error recovery with trait operators
#[test]
fn repl_type_error_recovers() {
    let mut session = repl_session();
    load_traits(&mut session);
    // Type error: calling + with wrong arity (3 args instead of 2).
    let err = session.eval("(+ 1 2 3)");
    assert!(err.is_err());
    // Session should still work after error.
    assert_eq!(repl_eval(&mut session, "(+ 1 2)"), 3);
}

// =============================================================================
// Dual-mode parity (batch + interactive produce same results)
// =============================================================================

// spec: 07-traits §7.5 — dual-mode + parity
#[test]
fn dual_mode_trait_plus() {
    compile_both(&with_traits("(defn main [] (+ 3 4))"), 7);
}

// spec: 07-traits §7.5 — dual-mode - parity
#[test]
fn dual_mode_trait_minus() {
    compile_both(&with_traits("(defn main [] (- 10 3))"), 7);
}

// spec: 07-traits §7.5 — dual-mode * parity
#[test]
fn dual_mode_trait_multiply() {
    compile_both(&with_traits("(defn main [] (* 6 7))"), 42);
}

// spec: 07-traits §7.5 — dual-mode / parity
#[test]
fn dual_mode_trait_divide() {
    compile_both(&with_traits("(defn main [] (/ 20 4))"), 5);
}

// spec: 07-traits §7.5 — dual-mode = parity
#[test]
fn dual_mode_trait_eq() {
    compile_both(&with_traits("(defn main [] (if (= 5 5) 1 0))"), 1);
}

// spec: 07-traits §7.5 — dual-mode < parity
#[test]
fn dual_mode_trait_lt() {
    compile_both(&with_traits("(defn main [] (if (< 3 5) 1 0))"), 1);
}

// spec: 07-traits §7.5 — dual-mode nested arithmetic parity
#[test]
fn dual_mode_trait_nested_arithmetic() {
    compile_both(&with_traits("(defn main [] (* (+ 2 3) (- 10 4)))"), 30);
}

// spec: 07-traits §7.5 — dual-mode factorial with operators parity
#[test]
fn dual_mode_factorial_operators() {
    let src = &with_traits("
        (defn fact [n]
          (if (= n 0) 1 (* n (fact (- n 1)))))
        (defn main [] (fact 10))
    ");
    compile_both(src, 3628800);
}

// spec: 07-traits §7.5 — dual-mode sum-to with operators parity
#[test]
fn dual_mode_sum_to_with_operators() {
    let src = &with_traits("
        (defn sum-to [n]
          (if (= n 0) 0 (+ n (sum-to (- n 1)))))
        (defn main [] (sum-to 100))
    ");
    compile_both(src, 5050);
}

// Dual mode for default methods
// spec: 07-traits §7.1.5 — dual-mode default != parity
#[test]
fn dual_mode_default_neq() {
    compile_both(&with_traits("(defn main [] (if (!= 3 5) 1 0))"), 1);
}

// spec: 07-traits §7.1.5 — dual-mode default <= parity
#[test]
fn dual_mode_default_le() {
    compile_both(&with_traits("(defn main [] (if (<= 3 5) 1 0))"), 1);
}

// spec: 07-traits §7.1.5 — dual-mode default >= parity
#[test]
fn dual_mode_default_ge() {
    compile_both(&with_traits("(defn main [] (if (>= 5 3) 1 0))"), 1);
}

// =============================================================================
// Trait + ADT interaction
// =============================================================================

// spec: 07-traits §7.5 — trait operators in match body
#[test]
fn trait_operators_in_match_body() {
    let src = &with_traits("
        (deftype (Option a) None (Some [:a val]))
        (defn unwrap-or [opt default]
          (match opt
            [(Some x) x
             None default]))
        (defn main [] (+ (unwrap-or (Some 10) 0) (unwrap-or None 5)))
    ");
    assert_eq!(compile_and_run_simple(src), 15);
}

// spec: 07-traits §7.5 — trait operators with ADT function
#[test]
fn trait_operators_in_adt_function() {
    let src = &with_traits("
        (deftype Point [:Int x :Int y])
        (defn distance-sq [p]
          (match p
            [(Point x y) (+ (* x x) (* y y))]))
        (defn main [] (distance-sq (Point 3 4)))
    ");
    assert_eq!(compile_and_run_simple(src), 25);
}

// spec: 07-traits §7.5 — Eq = in match branch
#[test]
fn trait_eq_in_match_branch() {
    let src = &with_traits("
        (deftype Color Red Green Blue)
        (defn is-primary [c]
          (match c
            [Red (= 1 1)
             Green (= 2 2)
             Blue (= 3 3)]))
        (defn main [] (if (is-primary Red) 1 0))
    ");
    assert_eq!(compile_and_run_simple(src), 1);
}

// spec: 07-traits §7.5 — trait arithmetic with ADT field
#[test]
fn trait_arithmetic_with_adt_field() {
    let src = &with_traits("
        (deftype Pair [:Int first :Int second])
        (defn sum-pair [p]
          (match p [(Pair a b) (+ a b)]))
        (defn main [] (sum-pair (Pair 17 25)))
    ");
    assert_eq!(compile_and_run_simple(src), 42);
}

// =============================================================================
// Trait + Closure interaction
// =============================================================================

// spec: 07-traits §7.5 — closure using trait operators
#[test]
fn closure_using_trait_operators() {
    let src = &with_traits("
        (defn main []
          (let [n 10]
            ((fn [x] (+ n x)) 32)))
    ");
    assert_eq!(compile_and_run_simple(src), 42);
}

// spec: 07-traits §7.5 — higher-order with trait operators
#[test]
fn higher_order_with_trait_operators() {
    let src = &with_traits("
        (defn apply-fn [f x] (f x))
        (defn main [] (apply-fn (fn [x] (* x 2)) 21))
    ");
    assert_eq!(compile_and_run_simple(src), 42);
}

// spec: 07-traits §7.5 — closure with comparison operator
#[test]
fn closure_with_comparison() {
    let src = &with_traits("
        (defn main []
          (let [threshold 10]
            ((fn [x] (if (< x threshold) 0 1)) 15)))
    ");
    assert_eq!(compile_and_run_simple(src), 1);
}

// spec: 07-traits §7.5 — closure with equality operator
#[test]
fn closure_with_eq() {
    let src = &with_traits("
        (defn main []
          (let [target 42]
            ((fn [x] (if (= x target) 1 0)) 42)))
    ");
    assert_eq!(compile_and_run_simple(src), 1);
}

// =============================================================================
// Trait + TCO interaction
// =============================================================================

// spec: 12-runtime §12.5 — TCO countdown with trait operators
// IGNORED: constrained polymorphic self-recursion with TCO requires
// cross-eval monomorphisation that the REPL session doesn't support.
// The constrained fn definition and the call site are in separate eval calls,
// and the monomorphised variant GOT slot isn't available.
#[test]
fn tco_countdown_with_operators() {
    let src = &with_traits("
        (defn countdown [n]
          (if (= n 0) 0 (countdown (- n 1))))
        (defn main [] (countdown 1000000))
    ");
    assert_eq!(compile_and_run_simple(src), 0);
}

// spec: 12-runtime §12.5 — TCO accumulator with trait operators
// IGNORED: same cross-eval constrained poly limitation as above.
#[test]
fn tco_accumulator_with_operators() {
    let src = &with_traits("
        (defn sum-acc [n acc]
          (if (= n 0) acc (sum-acc (- n 1) (+ acc n))))
        (defn main [] (sum-acc 100 0))
    ");
    assert_eq!(compile_and_run_simple(src), 5050);
}

// =============================================================================
// U1.3 resolution: Nested heap ADT tests (deferred from Ring 1)
// =============================================================================

// spec: 05-definitions §5.2.2 — nested ADT with string field
#[test]
fn nested_adt_with_string() {
    let src = r#"
        (deftype (Option a) None (Some [:a val]))
        (defn main []
          (let [opt (Some "hello")]
            (match opt
              [(Some s) (str-len s)
               None 0])))
    "#;
    assert_eq!(compile_and_run_simple(src), 5);
}

// spec: 05-definitions §5.2.2 — nested Option of Option
#[test]
fn nested_adt_option_of_option() {
    let src = "
        (deftype (Option a) None (Some [:a val]))
        (defn main []
          (match (Some (Some 42))
            [(Some inner)
              (match inner
                [(Some x) x
                 None 0])
             None 0]))
    ";
    assert_eq!(compile_and_run_simple(src), 42);
}

// spec: 03-types §3.2.4 — Vec of strings in ADT context
#[test]
fn nested_adt_vec_of_strings() {
    let src = r#"
        (defn main []
          (str-len (vec-get ["hello" "world" "test"] 1)))
    "#;
    assert_eq!(compile_and_run_simple(src), 5);
}

// spec: 05-definitions §5.2.2 — Point inside Option
#[test]
fn nested_adt_point_in_option() {
    let src = &with_traits("
        (deftype Point [:Int x :Int y])
        (deftype (Option a) None (Some [:a val]))
        (defn main []
          (match (Some (Point 3 4))
            [(Some p) (match p [(Point x y) (+ x y)])
             None 0]))
    ");
    assert_eq!(compile_and_run_simple(src), 7);
}

// spec: 05-definitions §5.2.1 — string field in product type
#[test]
fn nested_adt_string_in_product() {
    let src = r#"
        (deftype Named [:String name :Int value])
        (defn main []
          (match (Named "test" 42)
            [(Named n v) v]))
    "#;
    assert_eq!(compile_and_run_simple(src), 42);
}

// =============================================================================
// U1.5 resolution: Closure capturing heap types (deferred from Ring 1)
// =============================================================================

// spec: 04-expressions §4.5.1 — closure capturing string
#[test]
fn closure_capturing_string() {
    let src = r#"
        (defn main []
          (let [s "hello"]
            ((fn [] (str-len s)))))
    "#;
    assert_eq!(compile_and_run_simple(src), 5);
}

// spec: 04-expressions §4.5.1 — closure capturing ADT
#[test]
fn closure_capturing_adt() {
    let src = "
        (deftype (Option a) None (Some [:a val]))
        (defn main []
          (let [opt (Some 42)]
            ((fn [] (match opt [(Some x) x None 0])))))
    ";
    assert_eq!(compile_and_run_simple(src), 42);
}

// spec: 04-expressions §4.5.1 — closure capturing Vec
#[test]
fn closure_capturing_vec() {
    let src = "
        (defn main []
          (let [v [1 2 3]]
            ((fn [] (vec-len v)))))
    ";
    assert_eq!(compile_and_run_simple(src), 3);
}

// spec: 04-expressions §4.5.1 — closure returning captured string
#[test]
fn closure_returning_captured_string() {
    let src = r#"
        (defn make-greeter [greeting]
          (fn [] greeting))
        (defn main [] (str-len ((make-greeter "hello"))))
    "#;
    assert_eq!(compile_and_run_simple(src), 5);
}

// spec: 04-expressions §4.5.1 — closure with string in HOF
#[test]
fn closure_capturing_string_in_higher_order() {
    let src = r#"
        (defn apply-fn [f] (f))
        (defn main []
          (let [s "test"]
            (apply-fn (fn [] (str-len s)))))
    "#;
    assert_eq!(compile_and_run_simple(src), 4);
}

// =============================================================================
// R2.1 — deftrait REPL display
// =============================================================================

// spec: repl/spec.md §1.3 — deftrait display shows `:module/TraitName`
#[test]
fn repl_deftrait_display_shows_trait_name() {
    let mut session = repl_session();
    let display = repl_eval_display(
        &mut session,
        "(deftrait (Sizeable a) (size [a] Int))",
    );
    // Universal format: `:user/Sizeable ; deftrait` + `; defn:` section with methods
    assert!(
        display.contains(":user/Sizeable ; deftrait"),
        "deftrait display should contain ':user/Sizeable ; deftrait', got: {display}"
    );
    assert!(
        display.contains("; defn:") && display.contains("size"),
        "deftrait display should show '; defn:' section with 'size', got: {display}"
    );
}

// =============================================================================
// R2.2 — constrained fn REPL display
// =============================================================================

// spec: repl/spec.md §1.3 — constrained fn display shows inline constraints
#[test]
fn repl_constrained_fn_shows_constraints() {
    let mut session = repl_session();
    load_traits(&mut session);
    let display = repl_eval_display(
        &mut session,
        "(defn double [x] (+ x x))",
    );
    // spec §1.3, §1.1: inline constraint notation + '; defn' classification.
    // `double` takes one Num-constrained param and returns the same type.
    assert!(
        display.contains(":(Fn [:Num a] a) user/double"),
        "constrained fn display should use inline constraint notation, got: {display}"
    );
    assert!(
        display.contains("; defn"),
        "constrained fn display should include '; defn' classification, got: {display}"
    );
}

// spec: repl/spec.md §1.3 — two-param constrained fn shows `:var` on subsequent occurrences
#[test]
fn repl_constrained_fn_two_params_shows_subsequent_colon_var() {
    let mut session = repl_session();
    load_traits(&mut session);
    let display = repl_eval_display(
        &mut session,
        "(defn add [x y] (+ x y))",
    );
    // spec: 03-types §3.5.1 — constrained type display repeats constraint prefix
    // on every occurrence: `(Fn [:Num a :Num a] a)`, NOT `[:Num a :a]` or `[:Num a a]`.
    assert!(
        display.contains(":(Fn [:Num a :Num a] a) user/add"),
        "constrained fn display must repeat :Num on both params per spec §3.5.1, got: {display}"
    );
    assert!(
        display.contains("; defn"),
        "constrained fn display should include '; defn' classification, got: {display}"
    );
}

// =============================================================================
// R2.3 — impl REPL display
// =============================================================================

// spec: repl/spec.md §1.3 — impl display shows `impl module/Trait for module/Type`
#[test]
fn repl_impl_display_shows_trait_for_type() {
    let mut session = repl_session();
    repl_eval(
        &mut session,
        "(deftrait (Sizeable a) (size [a] Int))",
    );
    repl_eval(
        &mut session,
        "(deftype MyType [:Int val])",
    );
    let display = repl_eval_display(
        &mut session,
        "(impl Sizeable MyType (defn size [self] 42))",
    );
    assert_eq!(
        display, "impl user/Sizeable for user/MyType",
        "impl display should be 'impl user/Sizeable for user/MyType'"
    );
}

// =============================================================================
// Trait implementation forms (spec: 07-traits §7.3)
// =============================================================================

// spec: 07-traits §7.3 — impl form provides method bodies for a concrete type
#[test]
fn trait_impl_concrete_type() {
    // Basic concrete impl: Display for a simple type.
    let src = r#"
        (deftrait (Showable a)
          (show-it [a] Int))
        (deftype Color Red Green Blue)
        (impl Showable Color
          (defn show-it [c]
            (match c [Red 1 Green 2 Blue 3])))
        (defn main [] (show-it Green))
    "#;
    assert_eq!(compile_and_run_simple(src), 2);
}

// =============================================================================
// Trait scope and visibility (spec: 07-traits §7.11)
// =============================================================================

// spec: 07-traits §7.11 — trait methods accessible via import across modules
#[test]
fn trait_method_accessible_across_modules() {
    let dir = create_test_project(&[
        ("main.cl", "(mod types)\n(import [main.types [Classify classify Color Red Green Blue]])\n(defn main [] (classify Green))"),
        ("types.cl", "(deftrait (Classify a) (classify [a] Int))\n(deftype Color Red Green Blue)\n(impl Classify Color (defn classify [c] (match c [Red 1 Green 2 Blue 3])))"),
    ]);
    let result = cranelisp::pipeline::compile_module_graph(
        &dir.path().join("main.cl"),
        &[],
    ).unwrap();
    assert_eq!(result.value, 2);
}

// =============================================================================
// Visibility (spec: 05-definitions §5.11, 02-grammar §2.6)
// =============================================================================

// spec: 05-definitions §5.11 — defn- creates private function
#[test]
fn visibility_private_defn_not_importable() {
    let dir = create_test_project(&[
        ("main.cl", "(mod util)\n(import [main.util [helper]])\n(defn main [] (helper))"),
        ("util.cl", "(defn- helper [] 42)"),
    ]);
    let result = cranelisp::pipeline::compile_module_graph(
        &dir.path().join("main.cl"),
        &[],
    );
    assert!(result.is_err(), "private defn should not be importable");
}

// spec: 05-definitions §5.11 — public defn accessible via import
#[test]
fn visibility_public_defn_importable() {
    let dir = create_test_project(&[
        ("main.cl", "(mod util)\n(import [main.util [helper]])\n(defn main [] (helper))"),
        ("util.cl", "(defn helper [] 42)"),
    ]);
    let result = cranelisp::pipeline::compile_module_graph(
        &dir.path().join("main.cl"),
        &[],
    ).unwrap();
    assert_eq!(result.value, 42);
}

// spec: 05-definitions §5.11 — deftype- creates private type
#[test]
fn visibility_private_deftype_not_importable() {
    let dir = create_test_project(&[
        ("main.cl", "(mod types)\n(import [main.types [Secret]])\n(defn main [] 1)"),
        ("types.cl", "(deftype- Secret [:Int val])"),
    ]);
    let result = cranelisp::pipeline::compile_module_graph(
        &dir.path().join("main.cl"),
        &[],
    );
    assert!(result.is_err(), "private deftype should not be importable");
}

// =============================================================================
// Docstrings (spec: 05-definitions §5.12, 02-grammar §2.7)
// =============================================================================

// spec: 05-definitions §5.12 — defn with docstring compiles and runs correctly
#[test]
fn docstring_on_defn() {
    let src = &with_traits(r#"
        (defn inc "Increment by one" [:Int x] (+ x 1))
        (defn main [] (inc 5))
    "#);
    assert_eq!(compile_and_run_simple(src), 6);
}

// spec: 05-definitions §5.12 — deftype with docstring
#[test]
fn docstring_on_deftype() {
    let src = r#"
        (deftype Color "A primary color" Red Green Blue)
        (defn main [] (match Green [Red 1 Green 2 Blue 3]))
    "#;
    assert_eq!(compile_and_run_simple(src), 2);
}

// spec: 05-definitions §5.12 — deftrait with docstring
#[test]
fn docstring_on_deftrait() {
    let src = r#"
        (deftrait (Sizeable a) "Types that have a size"
          (size "Get the size" [a] Int))
        (impl Sizeable Int
          (defn size [x] x))
        (defn main [] (size 42))
    "#;
    assert_eq!(compile_and_run_simple(src), 42);
}

// =============================================================================
// Export (spec: 08-modules §8.4)
// =============================================================================

// spec: 08-modules §8.4 — export re-exports names from submodule
// Note: Export parsing is tested at unit level in module_extract.rs.
// Full pipeline re-export resolution across nested modules is not yet
// implemented — this test is left as future work.
// #[test]
// fn export_re_exports_names() { ... }

// =============================================================================
// Module: prelude, synthetic modules, lib dir (spec: 08-modules §8.8, §8.9, §8.11)
// =============================================================================

// spec: 08-modules §8.9.1 — qualified access to synthetic primitives module
#[test]
fn synthetic_primitives_qualified_access() {
    // Qualified access `primitives/add-i64` MUST work per §8.9.1.
    // Uses ReplSession::new() — NOT repl_session() which auto-imports.
    let mut session = ReplSession::new();
    assert_eq!(repl_eval(&mut session, "(primitives/add-i64 2 3)"), 5);
}

// spec: 08-modules §8.9 — explicit selective import of primitives
#[test]
fn synthetic_primitives_explicit_import() {
    // §8.9.1 + §8.9.4: explicit (import [primitives [add-i64]]) MUST resolve.
    let mut session = ReplSession::new();
    repl_eval(&mut session, "(import [primitives [add-i64 sub-i64]])");
    assert_eq!(repl_eval(&mut session, "(add-i64 (sub-i64 10 3) 2)"), 9);
}

// spec: 08-modules §8.9.1 — bare primitive without import MUST NOT resolve (REPL)
#[test]
fn synthetic_primitives_bare_without_import_fails_repl() {
    // Bare `add-i64` with no import MUST fail in REPL.
    let mut session = ReplSession::new();
    let err = session.eval("(add-i64 2 3)");
    assert!(
        err.is_err(),
        "bare primitive without import MUST fail"
    );
}

// spec: 08-modules §8.9.1 — bare primitive without import MUST NOT resolve (batch)
#[test]
fn synthetic_primitives_bare_without_import_fails_batch() {
    // Bare `add-i64` with no import MUST fail in batch mode.
    let src = "(defn main [] (add-i64 2 3))";
    let result = cranelisp::pipeline::compile_and_run(src);
    assert!(
        result.is_err(),
        "bare primitive without import MUST fail"
    );
}

// spec: 08-modules §8.9 — glob import of primitives
#[test]
fn synthetic_primitives_glob_import() {
    // §8.9.4: glob import makes all primitive names available as bare.
    // This is what repl_session() and compile_and_run_simple() do automatically.
    let mut session = ReplSession::new();
    repl_eval(&mut session, "(import [primitives [*]])");
    assert_eq!(repl_eval(&mut session, "(add-i64 (mul-i64 3 4) 1)"), 13);
}

// =============================================================================
// Module-phase declarations (spec: 05-definitions §5.13.3)
// =============================================================================

// spec: 05-definitions §5.13.3 — mod/import extracted before compilation
#[test]
fn module_phase_declarations_order_independent() {
    // mod and import at top work correctly in compilation order.
    let dir = create_test_project(&[
        ("main.cl", "(mod helper)\n(import [main.helper [double]])\n(defn main [] (double 21))"),
        ("helper.cl", "(defn double [:Int x] (add-i64 x x))"),
    ]);
    let result = cranelisp::pipeline::compile_module_graph(
        &dir.path().join("main.cl"),
        &[],
    ).unwrap();
    assert_eq!(result.value, 42);
}

// =============================================================================
// Name resolution (spec: 08-modules §8.6)
// =============================================================================

// spec: 08-modules §8.6 — resolution layers: local > module > root
#[test]
fn name_resolution_local_shadows_module() {
    // Local let binding shadows module-level definition.
    let src = "
        (defn val [] 10)
        (defn main [] (let [val 42] val))
    ";
    assert_eq!(compile_and_run_simple(src), 42);
}

// =============================================================================
// Variable reference (spec: 04-expressions §4.2)
// =============================================================================

// spec: 04-expressions §4.2 — variable reference resolves in lexical scope
#[test]
fn variable_reference_lexical_scope() {
    let src = "
        (defn main []
          (let [x 10]
            (let [y (add-i64 x 5)]
              y)))
    ";
    assert_eq!(compile_and_run_simple(src), 15);
}

// spec: 04-expressions §4.2.2 — qualified reference to module function
#[test]
fn qualified_reference_to_module() {
    let dir = create_test_project(&[
        ("main.cl", "(mod math)\n(defn main [] (math/double 21))"),
        ("math.cl", "(defn double [:Int x] (add-i64 x x))"),
    ]);
    let result = cranelisp::pipeline::compile_module_graph(
        &dir.path().join("main.cl"),
        &[],
    ).unwrap();
    assert_eq!(result.value, 42);
}

// =============================================================================
// Module integration tests (spec: 08-modules)
// =============================================================================

use tempfile::TempDir;

/// Create a temporary project directory with the given files.
/// Each entry is (relative_path, content). Subdirectories are created automatically.
fn create_test_project(files: &[(&str, &str)]) -> TempDir {
    let dir = tempfile::tempdir().unwrap();
    for (path, content) in files {
        let full = dir.path().join(path);
        if let Some(parent) = full.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        std::fs::write(&full, content).unwrap();
    }
    dir
}

// spec: 08-modules §8.2 — single-file batch compilation via compile_module_graph
#[test]
fn single_file_via_run_project() {
    let dir = create_test_project(&[
        ("main.cl", "(defn main [] 42)"),
    ]);
    let result = cranelisp::pipeline::compile_module_graph(
        &dir.path().join("main.cl"),
        &[],
    ).unwrap();
    assert_eq!(result.value, 42);
    assert_eq!(result.ty, cranelisp_types::Type::Int);
}

// spec: 08-modules §8.2.5 — missing module file gives descriptive error
#[test]
fn module_missing_file_error() {
    let dir = create_test_project(&[
        ("main.cl", "(mod nonexistent)\n(defn main [] 1)"),
    ]);
    let result = cranelisp::pipeline::compile_module_graph(
        &dir.path().join("main.cl"),
        &[],
    );
    let msg = match result {
        Err(e) => e.message().to_string(),
        Ok(_) => panic!("expected error for missing module file"),
    };
    assert!(
        msg.contains("nonexistent"),
        "error should mention the missing module name, got: {msg}"
    );
}

// spec: 08-modules §8.2.6 — circular module dependency detected
#[test]
fn module_cycle_detection() {
    // We can't easily create a true filesystem cycle through (mod ...) since
    // submodule paths are hierarchical. Instead, test the toposort cycle
    // detection directly by constructing a graph with a cycle.
    use cranelisp::pipeline::{ModuleGraph, ModuleNode, toposort};
    use cranelisp_types::ModuleFullPath;
    use std::collections::HashMap;
    use std::path::PathBuf;

    let mut nodes = HashMap::new();
    nodes.insert(
        ModuleFullPath::from("a"),
        ModuleNode {
            path: ModuleFullPath::from("a"),
            file_path: PathBuf::from("a.cl"),
            dependencies: vec![ModuleFullPath::from("b")],
        },
    );
    nodes.insert(
        ModuleFullPath::from("b"),
        ModuleNode {
            path: ModuleFullPath::from("b"),
            file_path: PathBuf::from("b.cl"),
            dependencies: vec![ModuleFullPath::from("a")],
        },
    );
    let graph = ModuleGraph {
        nodes,
        entry: ModuleFullPath::from("a"),
        project_root: PathBuf::from("."),
        lib_dirs: Vec::new(),
    };

    let result = toposort(&graph);
    let msg = match result {
        Err(e) => e.message().to_string(),
        Ok(_) => panic!("expected cycle detection error"),
    };
    assert!(
        msg.contains("circular"),
        "error should mention circular dependency, got: {msg}"
    );
}

// spec: 08-modules §8.3 — qualified name resolution across modules
#[test]
fn module_qualified_name_resolution() {
    let dir = create_test_project(&[
        ("main.cl", "(mod util)\n(defn main [] (util/helper))"),
        ("util.cl", "(defn helper [] 42)"),
    ]);
    let result = cranelisp::pipeline::compile_module_graph(
        &dir.path().join("main.cl"),
        &[],
    ).unwrap();
    assert_eq!(result.value, 42);
}

// spec: 08-modules §8.4 — import specific names
#[test]
fn import_specific_names() {
    let dir = create_test_project(&[
        ("main.cl", "(mod util)\n(import [main.util [helper]])\n(defn main [] (helper))"),
        ("util.cl", "(defn helper [] 42)"),
    ]);
    let result = cranelisp::pipeline::compile_module_graph(
        &dir.path().join("main.cl"),
        &[],
    ).unwrap();
    assert_eq!(result.value, 42);
}

// spec: 08-modules §8.4 — glob import
#[test]
fn import_glob() {
    let dir = create_test_project(&[
        ("main.cl", "(mod util)\n(import [main.util [*]])\n(defn main [] (helper))"),
        ("util.cl", "(defn helper [] 42)"),
    ]);
    let result = cranelisp::pipeline::compile_module_graph(
        &dir.path().join("main.cl"),
        &[],
    ).unwrap();
    assert_eq!(result.value, 42);
}

// spec: 08-modules §8.4 — importing nonexistent name gives clear error
#[test]
fn import_nonexistent_name_errors() {
    let dir = create_test_project(&[
        ("main.cl", "(mod util)\n(import [main.util [nonexistent]])\n(defn main [] 1)"),
        ("util.cl", "(defn helper [] 42)"),
    ]);
    let result = cranelisp::pipeline::compile_module_graph(
        &dir.path().join("main.cl"),
        &[],
    );
    let msg = match result {
        Err(e) => e.message().to_string(),
        Ok(_) => panic!("expected error for nonexistent import"),
    };
    assert!(
        msg.contains("nonexistent"),
        "error should mention the missing name, got: {msg}"
    );
}

// =============================================================================
// D5: P1-HIGH Negative Coverage — Module Boundaries (Sprint 16)
// =============================================================================

// spec: 08-modules §8.7.3 — glob export MUST NOT include private names
#[test]
fn neg_glob_export_excludes_private() {
    // Module B has a public function and a private function.
    // Module A glob-imports from B. The private function MUST NOT be accessible.
    let dir = create_test_project(&[
        ("main.cl", "(mod util)\n(import [main.util [*]])\n(defn main [] (secret))"),
        ("util.cl", "(defn helper [] 42)\n(defn- secret [] 99)"),
    ]);
    let result = cranelisp::pipeline::compile_module_graph(
        &dir.path().join("main.cl"),
        &[],
    );
    assert!(
        result.is_err(),
        "glob import MUST NOT include private names — 'secret' should not be accessible"
    );
}

// spec: 08-modules §8.7.3 — glob export DOES include public names (companion positive)
#[test]
fn neg_glob_export_includes_public() {
    // Companion test: public name IS accessible via glob import.
    let dir = create_test_project(&[
        ("main.cl", "(mod util)\n(import [main.util [*]])\n(defn main [] (helper))"),
        ("util.cl", "(defn helper [] 42)\n(defn- secret [] 99)"),
    ]);
    let result = cranelisp::pipeline::compile_module_graph(
        &dir.path().join("main.cl"),
        &[],
    ).unwrap();
    assert_eq!(result.value, 42);
}

// spec: 08-modules §8.10.2 — circular module dependency MUST error
#[test]
fn neg_circular_module_dependency() {
    // Module A imports from B, module B imports from A — circular dependency.
    let dir = create_test_project(&[
        ("main.cl", "(mod a)\n(import [main.a [a-fn]])\n(defn main [] (a-fn))"),
        ("a.cl", "(import [main.b [b-fn]])\n(defn a-fn [] (b-fn))"),
        ("b.cl", "(import [main.a [a-fn]])\n(defn b-fn [] (a-fn))"),
    ]);
    let result = cranelisp::pipeline::compile_module_graph(
        &dir.path().join("main.cl"),
        &[],
    );
    assert!(
        result.is_err(),
        "circular module dependency MUST produce an error"
    );
}

// spec: 08-modules §8.3.6 — super in root module MUST error
#[test]
fn neg_super_in_root_module_errors() {
    // Using (import [super [...]]) in the root module should error —
    // root has no parent.
    let dir = create_test_project(&[
        ("main.cl", "(import [super [thing]])\n(defn main [] (thing))"),
    ]);
    let result = cranelisp::pipeline::compile_module_graph(
        &dir.path().join("main.cl"),
        &[],
    );
    assert!(
        result.is_err(),
        "import [super ...] in root module MUST error"
    );
}

// spec: 08-modules §8.7.3 — private name not accessible via qualified ref after glob import
#[test]
fn neg_glob_import_private_not_via_qualified() {
    // After glob-importing from util, private names MUST NOT be accessible
    // via qualified ref (main.util/secret) either.
    let dir = create_test_project(&[
        ("main.cl", "(mod util)\n(import [main.util [*]])\n(defn main [] (main.util/secret))"),
        ("util.cl", "(defn helper [] 42)\n(defn- secret [] 99)"),
    ]);
    let result = cranelisp::pipeline::compile_module_graph(
        &dir.path().join("main.cl"),
        &[],
    );
    assert!(
        result.is_err(),
        "private name MUST NOT be accessible via qualified ref"
    );
}

// spec: 08-modules §8.7.3 — private macro not importable
#[test]
fn neg_private_macro_not_importable() {
    // A private defmacro (defmacro- name ...) MUST NOT be importable.
    let dir = create_test_project(&[
        ("main.cl", "(mod util)\n(import [main.util [secret-mac]])\n(defn main [] (secret-mac 1))"),
        ("util.cl", "(defmacro- secret-mac [x] x)\n(defn helper [] 42)"),
    ]);
    let result = cranelisp::pipeline::compile_module_graph(
        &dir.path().join("main.cl"),
        &[],
    );
    assert!(
        result.is_err(),
        "private macro MUST NOT be importable"
    );
}

// =============================================================================
// D5: P2-HIGH Negative Coverage — Type System Invariants (Sprint 16)
// =============================================================================

// spec: 03-types §3.8.2 — occurs check prevents infinite types
#[test]
fn neg_occurs_check_infinite_type() {
    // Attempting to create an infinite type should fail with a type error.
    // Classic example: (defn f [x] (f (f x))) leads to x : a, f : a -> b,
    // then b ~ (a -> b), causing infinite type.
    // More directly: (let [f (fn [x] (x x))] (f f)) — self-application.
    let src = r#"
(defn apply-self [x] (x x))
(defn main [] (apply-self apply-self))
"#;
    let result = cranelisp::pipeline::compile_and_run(src);
    assert!(
        result.is_err(),
        "infinite type (occurs check) MUST produce a type error"
    );
}

// spec: 03-types §3.6.6 — constrained fn MUST NOT be captured in a closure
#[test]
fn neg_constrained_fn_in_closure() {
    // A constrained polymorphic function (e.g., one that uses trait-dispatched +)
    // MUST NOT be used as a first-class value / captured in a closure.
    let src = &format!(
        "{}\n{}",
        num_trait_prelude(),
        r#"
(defn add [x y] (+ x y))
(defn main [] (let [f add] (f 1 2)))
"#
    );
    let result = cranelisp::pipeline::compile_and_run(src);
    // This may either error at typecheck (cannot use constrained fn as value)
    // or at codegen. Either way, it must not succeed silently.
    assert!(
        result.is_err(),
        "constrained fn captured in let binding MUST NOT compile"
    );
}

// spec: 03-types §3.7.4, 07-traits §7.2.3 — primitive types rejected as HKT impl targets
#[test]
fn neg_hkt_impl_primitive_type_rejected() {
    // Implementing a higher-kinded trait on a primitive type should fail.
    // Primitive types (Int, Bool, etc.) are not type constructors.
    let src = r#"
(deftrait (Functor f)
  (fmap [(Fn [a] b) (f a)] (f b)))
(impl Functor Int
  (defn fmap [f x] x))
(defn main [] 1)
"#;
    let result = cranelisp::pipeline::compile_and_run(src);
    assert!(
        result.is_err(),
        "implementing HKT trait on primitive type MUST be rejected"
    );
}

// spec: 07-traits §7.3.1 — impl with missing method MUST error
#[test]
fn neg_impl_missing_method_errors() {
    // An impl block that doesn't implement all required methods should error.
    let src = r#"
(deftrait (Sizeable a)
  (size [a] Int)
  (weight [a] Int))
(deftype Box [:Int val])
(impl Sizeable Box
  (defn size [b] 1))
(defn main [] (size (Box 42)))
"#;
    let result = cranelisp::pipeline::compile_and_run(src);
    assert!(
        result.is_err(),
        "impl block missing required method MUST produce an error"
    );
}

// spec: 03-types §3.8.6 — type mismatch Int vs Bool
#[test]
fn neg_type_mismatch_int_bool() {
    // Passing Bool where Int is expected must error.
    assert_type_error("(defn main [] (add-i64 true 1))", "Int");
}

// spec: 03-types §3.8.3 — function arity mismatch
#[test]
fn neg_type_mismatch_fn_arity() {
    // Calling a function with wrong number of args must error.
    let src = r#"
(defn f [x y] (add-i64 x y))
(defn main [] (f 1 2 3))
"#;
    let result = cranelisp::pipeline::compile_and_run(src);
    assert!(
        result.is_err(),
        "calling function with wrong number of args MUST error"
    );
}

// spec: 04-expressions §4.6.3 — multi-sig bare value is compile error
#[test]
fn neg_multi_sig_bare_value_errors() {
    // Multi-sig function used as a bare value (not called) should error.
    let src = r#"
(defn choose
  ([:Int x] x)
  ([:Int x :Int y] (add-i64 x y)))
(defn main [] (let [f choose] (f 1)))
"#;
    let result = cranelisp::pipeline::compile_and_run(src);
    assert!(
        result.is_err(),
        "multi-sig function used as bare value MUST error"
    );
}

// =============================================================================
// R3 annotation gap tests — HKT traits (spec: 03-types §3.7, 05-definitions §5.3.2, §5.4.4)
//
// Higher-kinded type traits are Ring 3 features. These tests document the
// expected behavior per spec and will be un-ignored when HKT is implemented.
// =============================================================================

// spec: 03-types §3.7 — HKT type variable in trait declaration
#[test]
fn hkt_type_variable_in_trait() {
    // HKT trait declaration: Functor maps over a type constructor.
    let src = r#"
(deftrait (Functor f)
  (fmap [(Fn [a] b) (f a)] (f b)))
(defn main [] 0)
"#;
    let _result = compile_and_run_simple(src);
}

// spec: 05-definitions §5.3.2 — HKT trait declaration syntax
#[test]
fn hkt_trait_declaration() {
    // A trait with a type constructor parameter: (deftrait (Functor f) ...)
    let src = r#"
(deftrait (Functor f)
  (fmap [(Fn [a] b) (f a)] (f b)))
(deftype (Option a) None (Some [:a val]))
(impl Functor Option
  (defn fmap [func opt]
    (match opt
      [None None
       (Some x) (Some (func x))])))
(defn main [] (match (fmap (fn [x] (add-i64 x 1)) (Some 41)) [(Some v) v None 0]))
"#;
    assert_eq!(compile_and_run_simple(src), 42);
}

// spec: 05-definitions §5.4.4 — HKT impl targets bare type constructor
#[test]
fn hkt_impl_bare_constructor() {
    // (impl Functor Option ...) — target is bare Option, not (Option a).
    let src = r#"
(deftrait (Functor f)
  (fmap [(Fn [a] b) (f a)] (f b)))
(deftype (Option a) None (Some [:a val]))
(impl Functor Option
  (defn fmap [func opt]
    (match opt
      [None None
       (Some x) (Some (func x))])))
(defn main [] (match (fmap (fn [x] (add-i64 x 1)) (Some 99)) [(Some v) v None 0]))
"#;
    assert_eq!(compile_and_run_simple(src), 100);
}

// =============================================================================
// R3 annotation gap test — lazy sequences (spec: 12-runtime §12.4.2)
// =============================================================================

// spec: 12-runtime §12.4.2 — lazy sequence thunk-based evaluation
#[test]
fn lazy_seq_take_from_infinite() {
    // Lazy sequences use thunks to defer evaluation. `range-from` produces
    // an infinite sequence; `take` materializes the first N elements.
    // This test will use the multi-sig API once available.
    let src = r#"
(defn main [] 0)
"#;
    // Placeholder: actual test requires Seq type and lazy infrastructure.
    assert_eq!(compile_and_run_simple(src), 0);
}

// =============================================================================
// Constrained auto-curry tests (spec: 04-expressions §4.6.3)
//
// Auto-currying of trait-dispatched operators and constrained polymorphic
// functions. These test the Sprint 21 fix for constrained auto-curry.
// =============================================================================

// spec: 04-expressions §4.6.3 — (+ 5) produces a curried Int closure
#[test]
fn constrained_auto_curry_plus_int() {
    let mut session = repl_session();
    load_traits(&mut session);
    // (+ 5) should produce a closure : (Fn [Int] Int)
    let (_val, ty) = repl_eval_typed(&mut session, "(+ 5)");
    assert!(
        matches!(&ty, Type::Fn(params, ret) if params.len() == 1),
        "expected (Fn [Int] Int) closure, got: {:?}",
        ty
    );
    // Calling the closure should produce 15
    assert_eq!(repl_eval(&mut session, "((+ 5) 10)"), 15);
}

// spec: 04-expressions §4.6.3 — ((+ 5) 10) returns 15
#[test]
fn constrained_auto_curry_plus_apply() {
    let mut session = repl_session();
    load_traits(&mut session);
    assert_eq!(repl_eval(&mut session, "((+ 5) 10)"), 15);
}

// spec: 04-expressions §4.6.3 — (- 5) partial application: (- 5) applied to 10 yields -5
#[test]
fn constrained_auto_curry_minus_int() {
    let mut session = repl_session();
    load_traits(&mut session);
    // (- 5) should produce a closure. When applied to 10: 5 - 10 = -5
    assert_eq!(repl_eval(&mut session, "((- 5) 10)"), -5i64 as i64);
}

// spec: 04-expressions §4.6.3 — constrained polymorphic auto-curry: make-adder
#[test]
fn constrained_auto_curry_make_adder_int() {
    let mut session = repl_session();
    load_traits(&mut session);
    // defn make-adder uses constrained polymorphism: (+ n) auto-curries the trait method
    repl_eval(&mut session, "(defn make-adder [n] (+ n))");
    // (make-adder 10) should monomorphise for Int and return (Fn [Int] Int)
    let (_val, ty) = repl_eval_typed(&mut session, "(make-adder 10)");
    assert!(
        matches!(&ty, Type::Fn(params, ret) if params.len() == 1),
        "expected (Fn [Int] Int) closure from make-adder, got: {:?}",
        ty
    );
    // Applying the result should yield 42
    assert_eq!(repl_eval(&mut session, "((make-adder 10) 32)"), 42);
}

// spec: 04-expressions §4.6.3 — constrained auto-curry monomorphises for Float
#[test]
fn constrained_auto_curry_make_adder_float() {
    let mut session = repl_session();
    load_traits(&mut session);
    repl_eval(&mut session, "(defn make-adder [n] (+ n))");
    // (make-adder 1.5) should monomorphise for Float
    let (_val, ty) = repl_eval_typed(&mut session, "(make-adder 1.5)");
    assert!(
        matches!(&ty, Type::Fn(params, ret) if params.len() == 1),
        "expected (Fn [Float] Float) closure from make-adder with Float, got: {:?}",
        ty
    );
    // ((make-adder 1.5) 2.5) should return 4.0
    // 4.0 as f64 bits reinterpreted as i64
    let result = repl_eval(&mut session, "((make-adder 1.5) 2.5)");
    let float_result = f64::from_bits(result as u64);
    assert!(
        (float_result - 4.0).abs() < 1e-10,
        "expected 4.0, got: {}",
        float_result
    );
}

// spec: 04-expressions §4.6.3 — auto-curry of non-Var callee (lambda) rejected
#[test]
fn auto_curry_lambda_partial_apply() {
    // ((fn [x y] (add-i64 x y)) 1) should be rejected — auto-curry requires a named callee
    let mut session = repl_session();
    let result = session.eval("((fn [x y] (add-i64 x y)) 1)");
    match result {
        Err(e) => {
            let err_msg = format!("{}", e);
            assert!(
                err_msg.contains("auto-curry requires a named function"),
                "expected 'auto-curry requires a named function' error, got: {}",
                err_msg
            );
        }
        Ok(_) => panic!("expected type error for non-Var auto-curry, got Ok"),
    }
}

// =============================================================================
// §7.6 Operators as First-Class Values (spec: 07-traits §7.6)
//
// Trait method names, including operators, are ordinary symbols. They MAY be
// bound to variables and passed as arguments to higher-order functions.
// Currently FAILS — trait methods cannot be used as values.
// =============================================================================

// spec: 07-traits §7.6 — operator bound to variable and called
#[test]
fn trait_method_as_value_operator() {
    // Per §7.6: (let [f +] (f 1 2)) should produce 3.
    // Currently fails with "undefined variable" or similar error because
    // trait methods cannot be used as first-class values.
    let mut session = repl_session_with_test_prelude();
    let result = session.eval("(let [f +] (f 1 2))");
    match result {
        Ok(r) => assert_eq!(r.value, 3, "expected (let [f +] (f 1 2)) = 3"),
        Err(e) => panic!(
            "SPEC VIOLATION §7.6: trait method '+' cannot be used as a value. \
             Expected (let [f +] (f 1 2)) = 3 but got error: {e}"
        ),
    }
}

// spec: 07-traits §7.6 — comparison operator as value
#[test]
fn trait_method_as_value_comparison() {
    // Per §7.6: (let [cmp <] (cmp 3 4)) should produce true.
    let mut session = repl_session_with_test_prelude();
    let result = session.eval("(let [cmp <] (cmp 3 4))");
    match result {
        Ok(r) => assert_eq!(r.value, 1, "expected (let [cmp <] (cmp 3 4)) = true"),
        Err(e) => panic!(
            "SPEC VIOLATION §7.6: trait method '<' cannot be used as a value. \
             Expected (let [cmp <] (cmp 3 4)) = true but got error: {e}"
        ),
    }
}
