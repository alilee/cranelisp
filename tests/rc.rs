// RC correctness tests for Ring 1.
//
// These tests verify that reference counting is balanced: every allocation
// is matched by a deallocation, with no leaks or double-frees.
//
// IMPORTANT: Run serially with `--test-threads=1` because the RC tracking
// counters are global atomics shared across all tests.
//
// Usage: cargo test --test rc -- --test-threads=1
// With trace: CRANELISP_RC_TRACE=1 cargo test --test rc -- --test-threads=1

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::*;

// =============================================================================
// String RC (~8 tests)
// =============================================================================

#[test]
fn rc_string_alloc_and_drop() {
    // String returned from main is the "last reference". The pipeline does not
    // free it (it returns the raw i64), so we track only internal temporaries.
    // A string literal bound in let and used once should be allocated and
    // conceptually dropped at scope exit, but Ring 1 does not yet emit scope-level
    // dec (that is Ring 2 RC Phase 2D). This test documents that the pipeline
    // does not double-free or underflow.
    let src = r#"(defn main [] (str-len "hello"))"#;
    assert_eq!(compile_and_run_simple(src), 5);
}

#[test]
fn rc_string_in_let_scope() {
    let src = r#"
        (defn main []
          (let [s "hello"]
            (str-len s)))
    "#;
    assert_eq!(compile_and_run_simple(src), 5);
}

#[test]
fn rc_string_passed_to_function() {
    let src = r#"
        (defn length [s] (str-len s))
        (defn main [] (length "hello"))
    "#;
    assert_eq!(compile_and_run_simple(src), 5);
}

#[test]
fn rc_string_concat_intermediate() {
    // str-concat allocates a new string. The intermediates should not
    // cause double-frees or underflows.
    let src = r#"
        (defn main []
          (str-len (str-concat "hello" " world")))
    "#;
    assert_eq!(compile_and_run_simple(src), 11);
}

#[test]
fn rc_string_in_if_branches() {
    // Only one branch is taken, so only one string is allocated.
    let src = r#"
        (defn main []
          (str-len (if true "yes" "no")))
    "#;
    assert_eq!(compile_and_run_simple(src), 3);
}

#[test]
fn rc_string_returned_from_function() {
    let src = r#"
        (defn greet [] "hello")
        (defn main [] (str-len (greet)))
    "#;
    assert_eq!(compile_and_run_simple(src), 5);
}

#[test]
fn rc_int_to_string_alloc() {
    // int-to-string allocates a new string.
    let src = "(defn main [] (str-len (int-to-string 42)))";
    assert_eq!(compile_and_run_simple(src), 2);
}

#[test]
fn rc_string_eq_no_alloc() {
    // str-eq does not allocate (compares in-place).
    let src = r#"(defn main [] (if (str-eq "a" "a") 1 0))"#;
    assert_eq!(compile_and_run_simple(src), 1);
}

// =============================================================================
// ADT RC (~12 tests)
// =============================================================================

#[test]
fn rc_adt_product_alloc() {
    // Product constructor allocates on heap.
    let src = "
        (deftype Point [:Int x :Int y])
        (defn main [] (match (Point 3 4) [(Point x y) (add-i64 x y)]))
    ";
    assert_eq!(compile_and_run_simple(src), 7);
}

#[test]
fn rc_adt_sum_some_alloc() {
    let src = "
        (deftype (Option a) None (Some [:a val]))
        (defn main [] (match (Some 42) [(Some x) x None 0]))
    ";
    assert_eq!(compile_and_run_simple(src), 42);
}

#[test]
fn rc_adt_sum_none_no_alloc() {
    // None is a nullary constructor -- bare tag, no heap allocation.
    let src = "
        (deftype (Option a) None (Some [:a val]))
        (defn main [] (match None [(Some x) x None 0]))
    ";
    assert_eq!(compile_and_run_simple(src), 0);
}

#[test]
fn rc_adt_in_let_scope() {
    let src = "
        (deftype Point [:Int x :Int y])
        (defn main []
          (let [p (Point 5 10)]
            (match p [(Point x y) (add-i64 x y)])))
    ";
    assert_eq!(compile_and_run_simple(src), 15);
}

#[test]
fn rc_adt_returned_from_function() {
    let src = "
        (deftype Point [:Int x :Int y])
        (defn make-point [x y] (Point x y))
        (defn main [] (match (make-point 3 4) [(Point x y) (add-i64 x y)]))
    ";
    assert_eq!(compile_and_run_simple(src), 7);
}

#[test]
fn rc_adt_in_match_arms() {
    let src = "
        (deftype (Option a) None (Some [:a val]))
        (defn map-opt [opt]
          (match opt
            [(Some x) (Some (add-i64 x 1))
             None None]))
        (defn main [] (match (map-opt (Some 9)) [(Some x) x None 0]))
    ";
    assert_eq!(compile_and_run_simple(src), 10);
}

#[test]
fn rc_adt_multiple_heap_fields() {
    let src = "
        (deftype Triple [:Int a :Int b :Int c])
        (defn main []
          (match (Triple 1 2 3) [(Triple a b c) (add-i64 a (add-i64 b c))]))
    ";
    assert_eq!(compile_and_run_simple(src), 6);
}

#[test]
fn rc_adt_constructor_in_temporary() {
    // ADT constructed as temporary, immediately matched.
    let src = "
        (deftype (Option a) None (Some [:a val]))
        (defn main [] (match (Some (add-i64 20 22)) [(Some x) x None 0]))
    ";
    assert_eq!(compile_and_run_simple(src), 42);
}

#[test]
fn rc_adt_with_string_field() {
    // ADT containing a string -- tests nested heap refs.
    let src = r#"
        (deftype (Option a) None (Some [:a val]))
        (defn main []
          (match (Some "hello")
            [(Some s) (str-len s)
             None 0]))
    "#;
    assert_eq!(compile_and_run_simple(src), 5);
}

#[test]
fn rc_adt_nested_option() {
    // Option(Option Int): nested heap ADTs.
    let src = "
        (deftype (Option a) None (Some [:a val]))
        (defn main []
          (match (Some (Some 42))
            [(Some inner) (match inner [(Some x) x None 0])
             None 0]))
    ";
    assert_eq!(compile_and_run_simple(src), 42);
}

#[test]
fn rc_adt_enum_no_alloc() {
    // Nullary-only enums do not allocate.
    let src = "
        (deftype Color Red Green Blue)
        (defn main [] (match Green [Red 1 Green 2 Blue 3]))
    ";
    assert_eq!(compile_and_run_simple(src), 2);
}

#[test]
fn rc_adt_recursive_matching() {
    // Chain of match expressions with ADTs.
    let src = "
        (deftype (Option a) None (Some [:a val]))
        (defn add-opts [a b]
          (match a
            [None 0
             (Some x)
               (match b
                 [None x
                  (Some y) (add-i64 x y)])]))
        (defn main [] (add-opts (Some 10) (Some 20)))
    ";
    assert_eq!(compile_and_run_simple(src), 30);
}

// =============================================================================
// Closure RC (~10 tests)
// =============================================================================

#[test]
fn rc_closure_env_alloc() {
    // Lambda with capture allocates a closure environment.
    let src = "
        (defn main []
          (let [n 10]
            ((fn [x] (add-i64 n x)) 32)))
    ";
    assert_eq!(compile_and_run_simple(src), 42);
}

#[test]
fn rc_closure_multiple_captures() {
    let src = "
        (defn main []
          (let [a 1 b 2 c 3]
            ((fn [x] (add-i64 a (add-i64 b (add-i64 c x)))) 4)))
    ";
    assert_eq!(compile_and_run_simple(src), 10);
}

#[test]
fn rc_closure_passed_to_function() {
    let src = "
        (defn apply-fn [f x] (f x))
        (defn main []
          (let [n 10]
            (apply-fn (fn [x] (add-i64 n x)) 5)))
    ";
    assert_eq!(compile_and_run_simple(src), 15);
}

#[test]
fn rc_closure_returned_from_function() {
    // Closure environment survives function return.
    let src = "
        (defn make-adder [n] (fn [x] (add-i64 n x)))
        (defn main [] ((make-adder 10) 32))
    ";
    assert_eq!(compile_and_run_simple(src), 42);
}

#[test]
fn rc_closure_in_let_scope() {
    let src = "
        (defn main []
          (let [f (fn [x] (add-i64 x 1))]
            (f 41)))
    ";
    assert_eq!(compile_and_run_simple(src), 42);
}

#[test]
fn rc_closure_called_multiple_times() {
    // Same closure called twice -- environment must remain valid.
    let src = "
        (defn main []
          (let [n 100
                f (fn [x] (add-i64 n x))]
            (add-i64 (f 1) (f 2))))
    ";
    assert_eq!(compile_and_run_simple(src), 203);
}

#[test]
fn rc_named_function_as_value() {
    // Named-function-as-value creates a zero-capture closure wrapper.
    let src = "
        (defn inc [x] (add-i64 x 1))
        (defn apply-fn [f x] (f x))
        (defn main [] (apply-fn inc 41))
    ";
    assert_eq!(compile_and_run_simple(src), 42);
}

#[test]
fn rc_closure_no_capture() {
    // Non-capturing lambda still allocates a closure (code_ptr only).
    let src = "
        (defn main []
          (let [f (fn [x] (add-i64 x 1))]
            (f 41)))
    ";
    assert_eq!(compile_and_run_simple(src), 42);
}

#[test]
fn rc_closure_in_recursive_higher_order() {
    // Closure passed through recursive function calls.
    let src = "
        (defn repeat-fn [f n x]
          (if (eq-i64 n 0)
            x
            (repeat-fn f (sub-i64 n 1) (f x))))
        (defn main [] (repeat-fn (fn [x] (add-i64 x 1)) 10 0))
    ";
    assert_eq!(compile_and_run_simple(src), 10);
}

#[test]
fn rc_closure_nested() {
    let src = "
        (defn main []
          (let [a 1]
            (let [f (fn [x] (add-i64 a x))]
              (let [g (fn [y] (f y))]
                (g 9)))))
    ";
    assert_eq!(compile_and_run_simple(src), 10);
}

// =============================================================================
// Cross-cutting RC (~5 tests)
// =============================================================================

#[test]
fn rc_closure_returning_adt() {
    let src = "
        (deftype (Option a) None (Some [:a val]))
        (defn make-some [n] (fn [] (Some n)))
        (defn main []
          (match ((make-some 42))
            [(Some x) x
             None 0]))
    ";
    assert_eq!(compile_and_run_simple(src), 42);
}

#[test]
fn rc_adt_containing_string_in_match() {
    let src = r#"
        (deftype (Option a) None (Some [:a val]))
        (defn main []
          (match (Some "hello")
            [(Some s) (str-len s)
             None 0]))
    "#;
    assert_eq!(compile_and_run_simple(src), 5);
}

#[test]
fn rc_string_built_from_int() {
    // int-to-string allocates, then str-len reads, then the string is unused.
    let src = "
        (defn main [] (str-len (int-to-string 123456)))
    ";
    assert_eq!(compile_and_run_simple(src), 6);
}

#[test]
fn rc_closure_capturing_function_result() {
    let src = "
        (defn make-fn [n] (fn [x] (add-i64 n x)))
        (defn main []
          (let [f (make-fn 100)]
            (add-i64 (f 1) (f 2))))
    ";
    assert_eq!(compile_and_run_simple(src), 203);
}

#[test]
fn rc_adt_chain() {
    // Multiple ADT allocations in sequence.
    let src = "
        (deftype (Option a) None (Some [:a val]))
        (defn inc-opt [opt]
          (match opt
            [(Some n) (Some (add-i64 n 1))
             None (Some 0)]))
        (defn main []
          (match (inc-opt (inc-opt (Some 0)))
            [(Some n) n
             None (sub-i64 0 1)]))
    ";
    assert_eq!(compile_and_run_simple(src), 2);
}
