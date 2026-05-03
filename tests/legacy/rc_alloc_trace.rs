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
use serial_test::serial;

// =============================================================================
// String RC (~8 tests)
// =============================================================================

// spec: 12-runtime §12.3 — string RC alloc and drop
#[test]
#[serial]
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

// spec: 12-runtime §12.3 — string RC in let scope
#[test]
#[serial]
fn rc_string_in_let_scope() {
    let src = r#"
        (defn main []
          (let [s "hello"]
            (str-len s)))
    "#;
    assert_eq!(compile_and_run_simple(src), 5);
}

// spec: 12-runtime §12.3 — string RC passed to function
#[test]
#[serial]
fn rc_string_passed_to_function() {
    let src = r#"
        (defn length [s] (str-len s))
        (defn main [] (length "hello"))
    "#;
    assert_eq!(compile_and_run_simple(src), 5);
}

// spec: 12-runtime §12.3 — string RC concat intermediate
#[test]
#[serial]
fn rc_string_concat_intermediate() {
    // str-concat allocates a new string. The intermediates should not
    // cause double-frees or underflows.
    let src = r#"
        (defn main []
          (str-len (str-concat "hello" " world")))
    "#;
    assert_eq!(compile_and_run_simple(src), 11);
}

// spec: 12-runtime §12.3 — string RC in if branches
#[test]
#[serial]
fn rc_string_in_if_branches() {
    // Only one branch is taken, so only one string is allocated.
    let src = r#"
        (defn main []
          (str-len (if true "yes" "no")))
    "#;
    assert_eq!(compile_and_run_simple(src), 3);
}

// spec: 12-runtime §12.3 — string RC returned from function
#[test]
#[serial]
fn rc_string_returned_from_function() {
    let src = r#"
        (defn greet [] "hello")
        (defn main [] (str-len (greet)))
    "#;
    assert_eq!(compile_and_run_simple(src), 5);
}

// spec: 12-runtime §12.3 — int-to-string RC allocation
#[test]
#[serial]
fn rc_int_to_string_alloc() {
    // int-to-string allocates a new string.
    let src = "(defn main [] (str-len (int-to-string 42)))";
    assert_eq!(compile_and_run_simple(src), 2);
}

// spec: 12-runtime §12.3 — string comparison no allocation
#[test]
#[serial]
fn rc_string_eq_no_alloc() {
    // str-eq does not allocate (compares in-place).
    let src = r#"(defn main [] (if (str-eq "a" "a") 1 0))"#;
    assert_eq!(compile_and_run_simple(src), 1);
}

// =============================================================================
// ADT RC (~12 tests)
// =============================================================================

// spec: 12-runtime §12.3 — ADT product heap allocation
#[test]
#[serial]
fn rc_adt_product_alloc() {
    // Product constructor allocates on heap.
    let src = "
        (deftype Point [:Int x :Int y])
        (defn main [] (match (Point 3 4) [(Point x y) (add-i64 x y)]))
    ";
    assert_eq!(compile_and_run_simple(src), 7);
}

// spec: 12-runtime §12.3 — ADT sum Some heap allocation
#[test]
#[serial]
fn rc_adt_sum_some_alloc() {
    let src = "
        (deftype (Option a) None (Some [:a val]))
        (defn main [] (match (Some 42) [(Some x) x None 0]))
    ";
    assert_eq!(compile_and_run_simple(src), 42);
}

// spec: 12-runtime §12.3 — ADT sum None no heap allocation
#[test]
#[serial]
fn rc_adt_sum_none_no_alloc() {
    // None is a nullary constructor -- bare tag, no heap allocation.
    let src = "
        (deftype (Option a) None (Some [:a val]))
        (defn main [] (match None [(Some x) x None 0]))
    ";
    assert_eq!(compile_and_run_simple(src), 0);
}

// spec: 12-runtime §12.3 — ADT RC in let scope
#[test]
#[serial]
fn rc_adt_in_let_scope() {
    let src = "
        (deftype Point [:Int x :Int y])
        (defn main []
          (let [p (Point 5 10)]
            (match p [(Point x y) (add-i64 x y)])))
    ";
    assert_eq!(compile_and_run_simple(src), 15);
}

// spec: 12-runtime §12.3 — ADT RC returned from function
#[test]
#[serial]
fn rc_adt_returned_from_function() {
    let src = "
        (deftype Point [:Int x :Int y])
        (defn make-point [x y] (Point x y))
        (defn main [] (match (make-point 3 4) [(Point x y) (add-i64 x y)]))
    ";
    assert_eq!(compile_and_run_simple(src), 7);
}

// spec: 12-runtime §12.3 — ADT RC in match arms
#[test]
#[serial]
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

// spec: 12-runtime §12.3 — ADT RC multiple heap fields
#[test]
#[serial]
fn rc_adt_multiple_heap_fields() {
    let src = "
        (deftype Triple [:Int a :Int b :Int c])
        (defn main []
          (match (Triple 1 2 3) [(Triple a b c) (add-i64 a (add-i64 b c))]))
    ";
    assert_eq!(compile_and_run_simple(src), 6);
}

// spec: 12-runtime §12.3 — ADT RC constructor as temporary
#[test]
#[serial]
fn rc_adt_constructor_in_temporary() {
    // ADT constructed as temporary, immediately matched.
    let src = "
        (deftype (Option a) None (Some [:a val]))
        (defn main [] (match (Some (add-i64 20 22)) [(Some x) x None 0]))
    ";
    assert_eq!(compile_and_run_simple(src), 42);
}

// spec: 12-runtime §12.3 — ADT RC with nested string field
#[test]
#[serial]
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

// spec: 12-runtime §12.3 — ADT RC nested Option
#[test]
#[serial]
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

// spec: 12-runtime §12.3 — enum ADT no heap allocation
#[test]
#[serial]
fn rc_adt_enum_no_alloc() {
    // Nullary-only enums do not allocate.
    let src = "
        (deftype Color Red Green Blue)
        (defn main [] (match Green [Red 1 Green 2 Blue 3]))
    ";
    assert_eq!(compile_and_run_simple(src), 2);
}

// spec: 12-runtime §12.3 — ADT RC recursive matching
#[test]
#[serial]
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

// spec: 12-runtime §12.3 — closure environment RC allocation
#[test]
#[serial]
fn rc_closure_env_alloc() {
    // Lambda with capture allocates a closure environment.
    let src = "
        (defn main []
          (let [n 10]
            ((fn [x] (add-i64 n x)) 32)))
    ";
    assert_eq!(compile_and_run_simple(src), 42);
}

// spec: 12-runtime §12.3 — closure RC multiple captures
#[test]
#[serial]
fn rc_closure_multiple_captures() {
    let src = "
        (defn main []
          (let [a 1 b 2 c 3]
            ((fn [x] (add-i64 a (add-i64 b (add-i64 c x)))) 4)))
    ";
    assert_eq!(compile_and_run_simple(src), 10);
}

// spec: 12-runtime §12.3 — closure RC passed to function
#[test]
#[serial]
fn rc_closure_passed_to_function() {
    let src = "
        (defn apply-fn [f x] (f x))
        (defn main []
          (let [n 10]
            (apply-fn (fn [x] (add-i64 n x)) 5)))
    ";
    assert_eq!(compile_and_run_simple(src), 15);
}

// spec: 12-runtime §12.3 — closure RC returned from function
#[test]
#[serial]
fn rc_closure_returned_from_function() {
    // Closure environment survives function return.
    let src = "
        (defn make-adder [n] (fn [x] (add-i64 n x)))
        (defn main [] ((make-adder 10) 32))
    ";
    assert_eq!(compile_and_run_simple(src), 42);
}

// spec: 12-runtime §12.3 — closure RC in let scope
#[test]
#[serial]
fn rc_closure_in_let_scope() {
    let src = "
        (defn main []
          (let [f (fn [x] (add-i64 x 1))]
            (f 41)))
    ";
    assert_eq!(compile_and_run_simple(src), 42);
}

// spec: 12-runtime §12.3 — closure RC called multiple times
#[test]
#[serial]
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

// spec: 12-runtime §12.3 — named function as value RC
#[test]
#[serial]
fn rc_named_function_as_value() {
    // Named-function-as-value creates a zero-capture closure wrapper.
    let src = "
        (defn inc [x] (add-i64 x 1))
        (defn apply-fn [f x] (f x))
        (defn main [] (apply-fn inc 41))
    ";
    assert_eq!(compile_and_run_simple(src), 42);
}

// spec: 12-runtime §12.3 — non-capturing closure RC
#[test]
#[serial]
fn rc_closure_no_capture() {
    // Non-capturing lambda still allocates a closure (code_ptr only).
    let src = "
        (defn main []
          (let [f (fn [x] (add-i64 x 1))]
            (f 41)))
    ";
    assert_eq!(compile_and_run_simple(src), 42);
}

// spec: 12-runtime §12.3 — closure RC in recursive HOF
#[test]
#[serial]
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

// spec: 12-runtime §12.3 — nested closure RC
#[test]
#[serial]
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

// spec: 12-runtime §12.3 — closure returning ADT RC
#[test]
#[serial]
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

// spec: 12-runtime §12.3 — ADT containing string in match RC
#[test]
#[serial]
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

// spec: 12-runtime §12.3 — int-to-string allocation RC
#[test]
#[serial]
fn rc_string_built_from_int() {
    // int-to-string allocates, then str-len reads, then the string is unused.
    let src = "
        (defn main [] (str-len (int-to-string 123456)))
    ";
    assert_eq!(compile_and_run_simple(src), 6);
}

// spec: 12-runtime §12.3 — closure capturing function result RC
#[test]
#[serial]
fn rc_closure_capturing_function_result() {
    let src = "
        (defn make-fn [n] (fn [x] (add-i64 n x)))
        (defn main []
          (let [f (make-fn 100)]
            (add-i64 (f 1) (f 2))))
    ";
    assert_eq!(compile_and_run_simple(src), 203);
}

// spec: 12-runtime §12.3 — ADT chain allocation RC
#[test]
#[serial]
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

// =============================================================================
// U1.3 — Nested heap ADT RC (resolves usability finding U1.3)
//
// Functional correctness tests (no crash, correct value) run now.
// Strict RC balance tests are #[ignore] because scope-level dec for heap
// temporaries is deferred to Ring 2 (see sprint notes §"RC Risks").
// =============================================================================

// spec: 12-runtime §12.3 — Option with string field RC
#[test]
#[serial]
fn rc_option_string() {
    // ADT containing a heap-typed field (String). Create and use — no crash.
    let src = r#"
        (deftype (Option a) None (Some [:a val]))
        (defn main []
          (match (Some "hello")
            [(Some s) (str-len s)
             None 0]))
    "#;
    assert_eq!(compile_and_run_simple(src), 5);
}

// spec: 12-runtime §12.3 — Option with string field RC balanced
#[test]
#[serial]
fn rc_option_string_balanced() {
    let src = r#"
        (deftype (Option a) None (Some [:a val]))
        (defn main []
          (match (Some "hello")
            [(Some s) (str-len s)
             None 0]))
    "#;
    assert_rc_balanced(src);
}

// spec: 12-runtime §12.3 — nested Option RC
#[test]
#[serial]
fn rc_nested_option() {
    // Nested ADT: Option(Option(String)). Inner and outer both heap — no crash.
    let src = r#"
        (deftype (Option a) None (Some [:a val]))
        (defn main []
          (match (Some (Some "hello"))
            [(Some inner) (match inner [(Some s) (str-len s) None 0])
             None 0]))
    "#;
    assert_eq!(compile_and_run_simple(src), 5);
}

// spec: 12-runtime §12.3 — nested Option RC balanced
#[test]
#[serial]
fn rc_nested_option_balanced() {
    let src = r#"
        (deftype (Option a) None (Some [:a val]))
        (defn main []
          (match (Some (Some "hello"))
            [(Some inner) (match inner [(Some s) (str-len s) None 0])
             None 0]))
    "#;
    assert_rc_balanced(src);
}

// spec: 12-runtime §12.3 — Option string in let RC
#[test]
#[serial]
fn rc_option_string_in_let() {
    // Access heap field through match in let scope — no crash.
    let src = r#"
        (deftype (Option a) None (Some [:a val]))
        (defn main []
          (let [x (Some "hello")]
            (match x [(Some s) (str-len s) None 0])))
    "#;
    assert_eq!(compile_and_run_simple(src), 5);
}

// spec: 12-runtime §12.3 — Option string in let RC balanced
#[test]
#[serial]
fn rc_option_string_in_let_balanced() {
    let src = r#"
        (deftype (Option a) None (Some [:a val]))
        (defn main []
          (let [x (Some "hello")]
            (match x [(Some s) (str-len s) None 0])))
    "#;
    assert_rc_balanced(src);
}

// =============================================================================
// U1.5 — Closure capturing heap types (resolves usability finding U1.5)
// =============================================================================

// spec: 12-runtime §12.3 — closure captures string RC
#[test]
#[serial]
fn rc_closure_captures_string() {
    // Closure captures a heap-allocated String — no crash.
    let src = r#"
        (defn main []
          (let [s "hello"]
            (let [f (fn [] (str-len s))]
              (f))))
    "#;
    assert_eq!(compile_and_run_simple(src), 5);
}

// spec: 12-runtime §12.3 — closure captures string RC balanced
#[test]
#[serial]
fn rc_closure_captures_string_balanced() {
    let src = r#"
        (defn main []
          (let [s "hello"]
            (let [f (fn [] (str-len s))]
              (f))))
    "#;
    assert_rc_balanced(src);
}

// spec: 12-runtime §12.3 — closure captures ADT RC
#[test]
#[serial]
fn rc_closure_captures_adt() {
    // Closure captures an ADT with a heap field — no crash.
    let src = r#"
        (deftype (Option a) None (Some [:a val]))
        (defn main []
          (let [opt (Some "world")]
            (let [f (fn [] (match opt [(Some s) (str-len s) None 0]))]
              (f))))
    "#;
    assert_eq!(compile_and_run_simple(src), 5);
}

// spec: 12-runtime §12.3 — closure captures ADT RC balanced
#[test]
#[serial]
fn rc_closure_captures_adt_balanced() {
    let src = r#"
        (deftype (Option a) None (Some [:a val]))
        (defn main []
          (let [opt (Some "world")]
            (let [f (fn [] (match opt [(Some s) (str-len s) None 0]))]
              (f))))
    "#;
    assert_rc_balanced(src);
}

// =============================================================================
// F-12 validation — Mixed ADT dec (nullary tag vs heap pointer)
// =============================================================================

// spec: 12-runtime §12.3 — mixed ADT None drop RC
#[test]
#[serial]
fn rc_mixed_adt_none_drop() {
    // None is a bare tag (i64 = 0). Must not be treated as a heap pointer — no crash.
    let src = "
        (deftype (Option a) None (Some [:a val]))
        (defn main []
          (let [x None]
            (match x [(Some n) n None 0])))
    ";
    assert_eq!(compile_and_run_simple(src), 0);
}

// spec: 12-runtime §12.3 — mixed ADT None drop RC balanced
#[test]
#[serial]
fn rc_mixed_adt_none_drop_balanced() {
    let src = "
        (deftype (Option a) None (Some [:a val]))
        (defn main []
          (let [x None]
            (match x [(Some n) n None 0])))
    ";
    assert_rc_balanced(src);
}

// spec: 12-runtime §12.3 — mixed ADT Some drop RC
#[test]
#[serial]
fn rc_mixed_adt_some_drop() {
    // Some("x") allocates on heap. String field must be accessible — no crash.
    let src = r#"
        (deftype (Option a) None (Some [:a val]))
        (defn main []
          (let [x (Some "x")]
            (match x [(Some s) (str-len s) None 0])))
    "#;
    assert_eq!(compile_and_run_simple(src), 1);
}

// spec: 12-runtime §12.3 — mixed ADT Some drop RC balanced
#[test]
#[serial]
fn rc_mixed_adt_some_drop_balanced() {
    let src = r#"
        (deftype (Option a) None (Some [:a val]))
        (defn main []
          (let [x (Some "x")]
            (match x [(Some s) (str-len s) None 0])))
    "#;
    assert_rc_balanced(src);
}

// =============================================================================
// Vec RC (~10 tests)
//
// Vec temporary cleanup: read-only Vec operations (vec-len, vec-get) emit
// vec_drop on temporary (non-variable) Vec arguments after the operation.
// Mutating operations (vec-set, vec-push) transfer ownership to the result.
// =============================================================================

// spec: 12-runtime §12.3 — Vec alloc and drop RC
#[test]
#[serial]
fn rc_vec_alloc_drop() {
    // Create Vec of Ints, let it drop — RC balanced.
    let src = "
        (defn main [] (vec-len [1 2 3]))
    ";
    assert_rc_balanced(src);
}

// spec: 12-runtime §12.3 — empty Vec RC
#[test]
#[serial]
fn rc_vec_empty() {
    // Empty Vec alloc and drop.
    let src = "
        (defn main [] (vec-len []))
    ";
    assert_rc_balanced(src);
}

// spec: 12-runtime §12.3 — Vec of strings RC
#[test]
#[serial]
fn rc_vec_of_strings() {
    // Vec of Strings — element Strings must be freed on Vec drop.
    let src = r#"
        (defn main []
          (vec-len ["a" "b" "c"]))
    "#;
    assert_rc_balanced(src);
}

// spec: 12-runtime §12.3 — Vec get int RC
#[test]
#[serial]
fn rc_vec_get_int() {
    // vec-get on Int Vec — no element RC needed.
    let src = "
        (defn main [] (vec-get [10 20 30] 1))
    ";
    assert_rc_balanced(src);
}

// spec: 12-runtime §12.3 — Vec get string RC
#[test]
#[serial]
fn rc_vec_get_string() {
    // vec-get on String Vec — element RC inc on get, balanced on drop.
    // The extracted string is bound in a let so scope cleanup handles it;
    // string temporary cleanup for extern primitive arguments is a separate issue.
    let src = r#"
        (defn main []
          (let [s (vec-get ["hello" "world"] 0)]
            (str-len s)))
    "#;
    assert_rc_balanced(src);
}

// spec: 12-runtime §12.3.3 — Vec copy-on-write set
#[test]
#[serial]
fn rc_vec_set_copy() {
    // vec-set on shared Vec — copies, original and new both balanced.
    let src = "
        (defn main []
          (let [v [1 2 3]]
            (let [v2 (vec-set v 1 99)]
              (add-i64 (vec-get v 1) (vec-get v2 1)))))
    ";
    assert_rc_balanced(src);
}

// spec: 12-runtime §12.3.3 — Vec copy-on-write push
#[test]
#[serial]
fn rc_vec_push_copy() {
    // vec-push on shared Vec — copies.
    let src = "
        (defn main []
          (let [v [1 2]]
            (let [v2 (vec-push v 3)]
              (add-i64 (vec-len v) (vec-len v2)))))
    ";
    assert_rc_balanced(src);
}

// spec: 12-runtime §12.3 — Vec of ADTs RC
#[test]
#[serial]
fn rc_vec_of_options() {
    // Vec of mixed ADT (Option Int) — Some allocates, None is bare tag.
    let src = "
        (deftype (Option a) None (Some [:a val]))
        (defn main []
          (vec-len [(Some 1) None (Some 3)]))
    ";
    assert_rc_balanced(src);
}

// spec: 12-runtime §12.3 — Vec push to empty RC
#[test]
#[serial]
fn rc_vec_push_to_empty() {
    // Push to empty Vec — no elements to copy.
    let src = "
        (defn main [] (vec-len (vec-push [] 1)))
    ";
    assert_rc_balanced(src);
}

// spec: 12-runtime §12.3 — Vec in let RC
#[test]
#[serial]
fn rc_vec_in_let() {
    // Vec bound in let, used, then dropped at scope exit.
    let src = "
        (defn main []
          (let [v [10 20 30]]
            (vec-get v 2)))
    ";
    assert_rc_balanced(src);
}

// =============================================================================
// U1.3 — Nested heap ADT RC: (List (Option Int)) or similar (Sprint 7 Wave 0)
//
// Tests nested heap types for RC balance: Option wrapping heap types,
// Vec of heap ADTs, and deeper nesting. Exercises the recursive RC
// inc/dec paths through polymorphic ADT fields.
// =============================================================================

// spec: 12-runtime §12.3 — nested Option(Option(String)) RC functional
#[test]
#[serial]
fn rc_u1_3_nested_option_option_string() {
    // Three levels of heap nesting: Option(Option(String)).
    let src = r#"
        (deftype (Option a) None (Some [:a val]))
        (defn main []
          (match (Some (Some "deep"))
            [(Some inner)
               (match inner [(Some s) (str-len s) None 0])
             None 0]))
    "#;
    assert_eq!(compile_and_run_simple(src), 4);
}

// spec: 12-runtime §12.3 — nested Option(Option(String)) RC balanced
#[test]
#[serial]
fn rc_u1_3_nested_option_option_string_balanced() {
    let src = r#"
        (deftype (Option a) None (Some [:a val]))
        (defn main []
          (match (Some (Some "deep"))
            [(Some inner)
               (match inner [(Some s) (str-len s) None 0])
             None 0]))
    "#;
    assert_rc_balanced(src);
}

// spec: 12-runtime §12.3 — Vec of Option(String) RC functional
#[test]
#[serial]
fn rc_u1_3_vec_of_option_string() {
    // Vec containing ADTs that themselves contain heap fields.
    // The Vec and its elements are freed, but the String fields inside
    // (Some "a") / (Some "c") are not dec'd because build_elem_dec_fn
    // doesn't emit inline drop glue for nested heap fields.
    let src = r#"
        (deftype (Option a) None (Some [:a val]))
        (defn main []
          (vec-len [(Some "a") None (Some "c")]))
    "#;
    assert_rc_balanced(src);
}

// spec: 12-runtime §12.3 — nested Option passed through function RC balanced
#[test]
#[serial]
fn rc_u1_3_nested_option_through_function() {
    // Nested heap ADT passed to and returned from a function.
    let src = r#"
        (deftype (Option a) None (Some [:a val]))
        (defn unwrap-inner [opt]
          (match opt
            [(Some inner)
               (match inner [(Some s) (str-len s) None 0])
             None 0]))
        (defn main [] (unwrap-inner (Some (Some "test"))))
    "#;
    assert_rc_balanced(src);
}

// spec: 12-runtime §12.3 — nested Option in if branches RC balanced
#[test]
#[serial]
fn rc_u1_3_nested_option_in_if() {
    // Nested heap ADTs created in conditional branches.
    let src = r#"
        (deftype (Option a) None (Some [:a val]))
        (defn main []
          (let [opt (if true (Some (Some "yes")) (Some None))]
            (match opt
              [(Some inner)
                 (match inner [(Some s) (str-len s) None 0])
               None 0])))
    "#;
    assert_rc_balanced(src);
}

// =============================================================================
// U1.5 — Closure capturing heap types (Sprint 7 Wave 0)
//
// Tests closures that capture String, ADT, or nested heap values.
// Validates that captured heap values maintain correct RC through
// closure creation, invocation, and cleanup.
// =============================================================================

// spec: 12-runtime §12.3 — closure captures string, called twice RC balanced
#[test]
#[serial]
fn rc_u1_5_closure_captures_string_called_twice() {
    // Closure capturing a String called multiple times — the String
    // must remain valid across all invocations.
    let src = r#"
        (defn main []
          (let [s "hello"]
            (let [f (fn [] (str-len s))]
              (add-i64 (f) (f)))))
    "#;
    assert_rc_balanced(src);
}

// spec: 12-runtime §12.3 — closure captures ADT with string field RC balanced
#[test]
#[serial]
fn rc_u1_5_closure_captures_adt_with_string_field() {
    // Closure captures an ADT whose field is a heap type (String).
    // Both the ADT and its String field must survive closure lifetime.
    let src = r#"
        (deftype Wrapper [:String name])
        (defn main []
          (let [w (Wrapper "alice")]
            (let [f (fn [] (match w [(Wrapper n) (str-len n)]))]
              (f))))
    "#;
    assert_rc_balanced(src);
}

// spec: 12-runtime §12.3 — closure captures string returned from function RC balanced
#[test]
#[serial]
fn rc_u1_5_closure_captures_string_returned() {
    // Closure capturing a String is returned from a function —
    // the String must outlive the creating scope.
    let src = r#"
        (defn make-len-fn [s] (fn [] (str-len s)))
        (defn main [] ((make-len-fn "world")))
    "#;
    assert_rc_balanced(src);
}

// spec: 12-runtime §12.3 — closure captures multiple heap values RC balanced
#[test]
#[serial]
fn rc_u1_5_closure_captures_multiple_heap_values() {
    // Closure capturing two Strings — both must be RC-tracked.
    let src = r#"
        (defn main []
          (let [a "hello" b "world"]
            (let [f (fn [] (add-i64 (str-len a) (str-len b)))]
              (f))))
    "#;
    assert_rc_balanced(src);
}

// spec: 12-runtime §12.3 — nested closure captures heap value RC balanced
#[test]
#[serial]
fn rc_u1_5_nested_closure_captures_heap() {
    // Outer closure captures String, inner closure captures outer closure.
    let src = r#"
        (defn main []
          (let [s "hi"]
            (let [f (fn [] (str-len s))]
              (let [g (fn [] (f))]
                (g)))))
    "#;
    assert_rc_balanced(src);
}

// =============================================================================
// U1.3 — Additional nested heap ADT RC coverage (Sprint 8 Wave 3)
//
// These tests go beyond the existing U1.3 tests by exercising deeper nesting
// and additional type combinations: List(String), List(Option(Int)),
// Option(String) through multiple lets, and multiple nested ADTs in sequence.
// =============================================================================

// spec: 12-runtime §12.3 — triple with all String fields RC balanced
#[test]
#[serial]
fn rc_u1_3_triple_all_strings() {
    // Product ADT with three String fields — all must be dec'd on drop.
    let src = r#"
        (deftype Triple [:String a :String b :String c])
        (defn main []
          (match (Triple "x" "y" "z")
            [(Triple a b c) (add-i64 (str-len a) (add-i64 (str-len b) (str-len c)))]))
    "#;
    assert_rc_balanced(src);
}

// spec: 12-runtime §12.3 — Wrapper of Option(String) two-level nesting RC balanced
#[test]
#[serial]
fn rc_u1_3_wrapper_of_option_string() {
    // Product wrapping Option(String) — three levels of heap nesting.
    let src = r#"
        (deftype (Option a) None (Some [:a val]))
        (deftype Wrapper [:(Option String) inner])
        (defn main []
          (match (Wrapper (Some "deep"))
            [(Wrapper opt) (match opt [(Some s) (str-len s) None 0])]))
    "#;
    assert_rc_balanced(src);
}

// spec: 12-runtime §12.3 — multiple Option(String) in let sequence RC balanced
#[test]
#[serial]
fn rc_u1_3_multiple_option_string_in_let() {
    // Two Option(String) values bound in a let — both must be cleaned up.
    let src = r#"
        (deftype (Option a) None (Some [:a val]))
        (defn main []
          (let [a (Some "hello")
                b (Some "world")]
            (add-i64
              (match a [(Some s) (str-len s) None 0])
              (match b [(Some s) (str-len s) None 0]))))
    "#;
    assert_rc_balanced(src);
}

// spec: 12-runtime §12.3 — Pair of two Strings RC balanced
#[test]
#[serial]
fn rc_u1_3_pair_of_strings() {
    // Product type with two heap-typed fields.
    let src = r#"
        (deftype Pair [:String fst :String snd])
        (defn main []
          (match (Pair "hello" "world")
            [(Pair a b) (add-i64 (str-len a) (str-len b))]))
    "#;
    assert_rc_balanced(src);
}

// spec: 12-runtime §12.3 — Option(Option(Int)) three-level nesting RC balanced
#[test]
#[serial]
fn rc_u1_3_option_option_int() {
    // Three-level nesting: Option wrapping Option wrapping Int.
    // Only the outer two Options are heap — Int is not.
    let src = r#"
        (deftype (Option a) None (Some [:a val]))
        (defn main []
          (match (Some (Some 42))
            [(Some inner)
              (match inner [(Some v) v None 0])
             None 0]))
    "#;
    assert_rc_balanced(src);
}

// =============================================================================
// U1.5 — Additional closure-captures-heap coverage (Sprint 8 Wave 3)
//
// These tests cover closures capturing ADTs with heap fields, closures
// capturing multiple heap types, and closures over Option(String).
// =============================================================================

// spec: 12-runtime §12.3 — closure captures Option(String) RC balanced
#[test]
#[serial]
fn rc_u1_5_closure_captures_option_string() {
    // Closure captures an Option containing a String. Both Option and
    // String must survive through the closure invocation.
    let src = r#"
        (deftype (Option a) None (Some [:a val]))
        (defn main []
          (let [opt (Some "captured")]
            (let [f (fn []
                      (match opt [(Some s) (str-len s) None 0]))]
              (f))))
    "#;
    assert_rc_balanced(src);
}

// spec: 12-runtime §12.3 — closure captures string and ADT RC balanced
#[test]
#[serial]
fn rc_u1_5_closure_captures_string_and_adt() {
    // Closure captures both a bare String and an ADT — two different
    // heap types in the same environment.
    let src = r#"
        (deftype (Option a) None (Some [:a val]))
        (defn main []
          (let [s "hello"
                opt (Some 42)]
            (let [f (fn []
                      (add-i64 (str-len s)
                               (match opt [(Some v) v None 0])))]
              (f))))
    "#;
    assert_rc_balanced(src);
}

// spec: 12-runtime §12.3 — closure captures Pair with string fields RC balanced
#[test]
#[serial]
fn rc_u1_5_closure_captures_pair_with_strings() {
    // Closure captures a product ADT with two String fields.
    let src = r#"
        (deftype StrPair [:String fst :String snd])
        (defn main []
          (let [p (StrPair "hello" "world")]
            (let [f (fn []
                      (match p [(StrPair a b) (add-i64 (str-len a) (str-len b))]))]
              (f))))
    "#;
    assert_rc_balanced(src);
}

// ── Lambda unused heap param RC tests (D3 / Sprint 18) ───────────────

// spec: spec/12-runtime.md — consuming convention: callee owns heap params
#[test]
#[serial]
fn rc_lambda_unused_string_param_freed() {
    let src = r#"
        (defn main []
          (let [f (fn [:String _s] 42)] (f "hello")))
    "#;
    assert_rc_balanced(src);
}

// spec: spec/12-runtime.md — consuming convention: callee owns heap params
#[test]
#[serial]
fn rc_lambda_unused_adt_param_freed() {
    let src = r#"
        (deftype (Option a) None (Some [:a val]))
        (defn main []
          (let [f (fn [:(Option Int) _opt] 0)] (f (Some 99))))
    "#;
    assert_rc_balanced(src);
}

// spec: spec/12-runtime.md — consuming convention: callee owns heap params
#[test]
#[serial]
fn rc_lambda_multiple_unused_heap_params_freed() {
    let src = r#"
        (defn main []
          (let [f (fn [:String _a :String _b] 0)] (f "x" "y")))
    "#;
    assert_rc_balanced(src);
}

// spec: spec/12-runtime.md — consuming convention: callee owns heap params
#[test]
#[serial]
fn rc_defn_unused_string_param_freed() {
    let src = r#"
        (defn f [:String _s] 42)
        (defn main [] (f "hello"))
    "#;
    assert_rc_balanced(src);
}
