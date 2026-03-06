// Ring 1 integration tests: strings, ADTs with fields, closures.
//
// Tests the full pipeline from source text to execution result.
// Organized by category per tests/plan/ring1.md.
//
// Ring 1 uses monomorphic named primitives per spec/appendix-a-builtins.md:
//   add-i64, sub-i64, mul-i64, div-i64   (Int arithmetic)
//   eq-i64, lt-i64, gt-i64, le-i64, ge-i64   (Int comparison)
//   str-concat, str-eq, str-len, int-to-string, float-to-string,
//   bool-to-string, parse-int   (String primitives)
//   not   (Boolean)
// Polymorphic operator syntax (+, <, etc.) arrives in Ring 2 via trait dispatch.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::*;
use cranelisp_types::Type;

// =============================================================================
// Strings: literals, primitives, and display (spec: 01-lexical, 03-types)
// =============================================================================

// spec: 04-expressions §4.1.4 — string literal
#[test]
fn string_literal() {
    let (value, ty) = compile_and_run_typed("(defn main [] \"hello\")");
    assert_eq!(ty, Type::String);
    let s = unsafe { cranelisp_runtime::read_string_as_str(value) };
    assert_eq!(s, "hello");
    cranelisp_runtime::heap_dealloc(value);
}

// spec: 04-expressions §4.1.4 — empty string literal
#[test]
fn string_empty_literal() {
    let (value, ty) = compile_and_run_typed("(defn main [] \"\")");
    assert_eq!(ty, Type::String);
    let s = unsafe { cranelisp_runtime::read_string_as_str(value) };
    assert_eq!(s, "");
    cranelisp_runtime::heap_dealloc(value);
}

// spec: 04-expressions §4.3 — string in let scope
#[test]
fn string_in_let() {
    let src = r#"
        (defn main []
          (let [s "world"]
            (str-len s)))
    "#;
    assert_eq!(compile_and_run_simple(src), 5);
}

// spec: 04-expressions §4.6 — string as function argument
#[test]
fn string_as_function_argument() {
    let src = r#"
        (defn length [s] (str-len s))
        (defn main [] (length "hello"))
    "#;
    assert_eq!(compile_and_run_simple(src), 5);
}

// spec: 03-types §3.1 — string return type
#[test]
fn string_as_function_return() {
    let src = r#"
        (defn greet [] "hello")
        (defn main [] (str-len (greet)))
    "#;
    assert_eq!(compile_and_run_simple(src), 5);
}

// spec: appendix-a-builtins §A.3 — str-concat primitive
#[test]
fn string_concat() {
    let src = r#"
        (defn main [] (str-len (str-concat "hello" " world")))
    "#;
    assert_eq!(compile_and_run_simple(src), 11);
}

// spec: appendix-a-builtins §A.3 — str-eq primitive true
#[test]
fn string_eq_true() {
    let src = r#"
        (defn main [] (if (str-eq "abc" "abc") 1 0))
    "#;
    assert_eq!(compile_and_run_simple(src), 1);
}

// spec: appendix-a-builtins §A.3 — str-eq primitive false
#[test]
fn string_eq_false() {
    let src = r#"
        (defn main [] (if (str-eq "abc" "xyz") 1 0))
    "#;
    assert_eq!(compile_and_run_simple(src), 0);
}

// spec: appendix-a-builtins §A.3 — int-to-string primitive
#[test]
fn string_int_to_string() {
    let src = r#"
        (defn main [] (str-len (int-to-string 42)))
    "#;
    assert_eq!(compile_and_run_simple(src), 2);
}

// spec: appendix-a-builtins §A.3 — float-to-string primitive
#[test]
fn string_float_to_string() {
    let src = r#"
        (defn main [] (str-len (float-to-string 3.14)))
    "#;
    // "3.14" has length 4
    let result = compile_and_run_simple(src);
    assert!(result > 0, "float-to-string should produce non-empty string, got len={result}");
}

// spec: appendix-a-builtins §A.3 — bool-to-string primitive
#[test]
fn string_bool_to_string() {
    let src = r#"
        (defn main [] (str-eq (bool-to-string true) "true"))
    "#;
    assert_eq!(compile_and_run_simple(src), 1);
}

// spec: appendix-a-builtins §A.3 — chained str-concat
#[test]
fn string_concat_chained() {
    let src = r#"
        (defn main []
          (str-len (str-concat (str-concat "a" "b") "c")))
    "#;
    assert_eq!(compile_and_run_simple(src), 3);
}

// spec: appendix-a-builtins §A.3 — str-len primitive
#[test]
fn string_len() {
    let src = r#"(defn main [] (str-len "hello"))"#;
    assert_eq!(compile_and_run_simple(src), 5);
}

// spec: appendix-a-builtins §A.3 — str-len empty string
#[test]
fn string_len_empty() {
    let src = r#"(defn main [] (str-len ""))"#;
    assert_eq!(compile_and_run_simple(src), 0);
}

// spec: 04-expressions §4.4 — string in if branches
#[test]
fn string_in_if_branches() {
    let src = r#"
        (defn main []
          (str-len (if true "hello" "hi")))
    "#;
    assert_eq!(compile_and_run_simple(src), 5);
}

// =============================================================================
// REPL Strings
// =============================================================================

// spec: 04-expressions §4.1.4 — string literal in REPL
#[test]
fn repl_string_literal() {
    let mut session = repl_session();
    let (value, ty) = repl_eval_typed(&mut session, "\"hello\"");
    assert_eq!(ty, Type::String);
    let s = unsafe { cranelisp_runtime::read_string_as_str(value) };
    assert_eq!(s, "hello");
}

// spec: appendix-a-builtins §A.3 — str-concat in REPL
#[test]
fn repl_string_concat() {
    let mut session = repl_session();
    let (value, ty) = repl_eval_typed(&mut session, "(str-concat \"hello\" \" world\")");
    assert_eq!(ty, Type::String);
    let s = unsafe { cranelisp_runtime::read_string_as_str(value) };
    assert_eq!(s, "hello world");
}

// spec: appendix-a-builtins §A.3 — str-eq in REPL
#[test]
fn repl_string_eq() {
    let mut session = repl_session();
    assert_eq!(repl_eval(&mut session, "(str-eq \"abc\" \"abc\")"), 1);
    assert_eq!(repl_eval(&mut session, "(str-eq \"abc\" \"xyz\")"), 0);
}

// spec: appendix-a-builtins §A.3 — int-to-string in REPL
#[test]
fn repl_int_to_string() {
    let mut session = repl_session();
    let (value, ty) = repl_eval_typed(&mut session, "(int-to-string 42)");
    assert_eq!(ty, Type::String);
    let s = unsafe { cranelisp_runtime::read_string_as_str(value) };
    assert_eq!(s, "42");
}

// =============================================================================
// ADT Products (spec: 03-types, 06-pattern-matching)
// =============================================================================

// spec: 05-definitions §5.2.1 — product type construct and match
#[test]
fn adt_product_construct_and_match() {
    let src = "
        (deftype Point [:Int x :Int y])
        (defn get-x [p] (match p [(Point x y) x]))
        (defn main [] (get-x (Point 3 4)))
    ";
    assert_eq!(compile_and_run_simple(src), 3);
}

// spec: 05-definitions §5.2.1 — product type field access
#[test]
fn adt_product_get_y() {
    let src = "
        (deftype Point [:Int x :Int y])
        (defn get-y [p] (match p [(Point x y) y]))
        (defn main [] (get-y (Point 3 4)))
    ";
    assert_eq!(compile_and_run_simple(src), 4);
}

// spec: 05-definitions §5.2.1 — product type multiple fields
#[test]
fn adt_product_multi_field() {
    let src = "
        (deftype Triple [:Int a :Int b :Int c])
        (defn sum-triple [t]
          (match t [(Triple a b c) (add-i64 a (add-i64 b c))]))
        (defn main [] (sum-triple (Triple 10 20 30)))
    ";
    assert_eq!(compile_and_run_simple(src), 60);
}

// spec: 05-definitions §5.2.1 — product type in let scope
#[test]
fn adt_product_in_let() {
    let src = "
        (deftype Point [:Int x :Int y])
        (defn main []
          (let [p (Point 5 10)]
            (match p [(Point x y) (add-i64 x y)])))
    ";
    assert_eq!(compile_and_run_simple(src), 15);
}

// spec: 05-definitions §5.2.1 — product type as function argument
#[test]
fn adt_product_as_function_arg() {
    let src = "
        (deftype Point [:Int x :Int y])
        (defn extract-x [p] (match p [(Point x y) x]))
        (defn main [] (extract-x (Point 42 99)))
    ";
    assert_eq!(compile_and_run_simple(src), 42);
}

// spec: 05-definitions §5.2.1 — product type as function return
#[test]
fn adt_product_as_function_return() {
    let src = "
        (deftype Point [:Int x :Int y])
        (defn origin [] (Point 0 0))
        (defn main [] (match (origin) [(Point x y) (add-i64 x y)]))
    ";
    assert_eq!(compile_and_run_simple(src), 0);
}

// spec: 05-definitions §5.2.4 — shortcut syntax inferred type params
#[test]
fn adt_shortcut_syntax() {
    // Shortcut syntax: bare field names get fresh type vars.
    let src = "
        (deftype Pair [first second])
        (defn main []
          (let [p (Pair 10 20)]
            (match p [(Pair a b) (add-i64 a b)])))
    ";
    assert_eq!(compile_and_run_simple(src), 30);
}

// =============================================================================
// ADT Sums (spec: 03-types, 06-pattern-matching)
// =============================================================================

// spec: 05-definitions §5.2.2 — sum type Some constructor
#[test]
fn adt_sum_option_some() {
    let src = "
        (deftype (Option a) None (Some [:a val]))
        (defn unwrap [opt]
          (match opt
            [(Some x) x
             None 0]))
        (defn main [] (unwrap (Some 42)))
    ";
    assert_eq!(compile_and_run_simple(src), 42);
}

// spec: 05-definitions §5.2.2 — sum type None constructor
#[test]
fn adt_sum_option_none() {
    let src = "
        (deftype (Option a) None (Some [:a val]))
        (defn unwrap [opt]
          (match opt
            [(Some x) x
             None 0]))
        (defn main [] (unwrap None))
    ";
    assert_eq!(compile_and_run_simple(src), 0);
}

// spec: 06-pattern-matching §6.2.3 — wildcard pattern in sum
#[test]
fn adt_sum_wildcard_pattern() {
    let src = "
        (deftype (Option a) None (Some [:a val]))
        (defn is-some [opt]
          (match opt
            [(Some x) 1
             _ 0]))
        (defn main [] (add-i64 (is-some (Some 1)) (is-some None)))
    ";
    assert_eq!(compile_and_run_simple(src), 1);
}

// spec: 06-pattern-matching §6.2.4 — variable pattern in sum
#[test]
fn adt_sum_var_pattern() {
    let src = "
        (deftype (Option a) None (Some [:a val]))
        (defn from-opt [opt default]
          (match opt
            [(Some x) x
             other default]))
        (defn main [] (from-opt None 99))
    ";
    assert_eq!(compile_and_run_simple(src), 99);
}

// spec: 06-pattern-matching §6.1 — nested match expressions
#[test]
fn adt_sum_nested_match() {
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

// spec: 03-types §3.3 — polymorphic ADT instantiation
#[test]
fn adt_polymorphic_type() {
    // Polymorphic ADT instantiated at different types.
    let src = "
        (deftype (Option a) None (Some [:a val]))
        (defn int-opt [] (Some 42))
        (defn bool-opt [] (Some true))
        (defn main []
          (match (int-opt)
            [(Some x) x
             None 0]))
    ";
    assert_eq!(compile_and_run_simple(src), 42);
}

// spec: 05-definitions §5.2.2 — sum type with two data constructors
#[test]
fn adt_either_type() {
    let src = "
        (deftype (Either a b) (Left [:a val]) (Right [:b val]))
        (defn get-val [e]
          (match e
            [(Left x) x
             (Right y) y]))
        (defn main [] (get-val (Right 99)))
    ";
    assert_eq!(compile_and_run_simple(src), 99);
}

// spec: 05-definitions §5.2.2 — mixed nullary and data constructors
#[test]
fn adt_enum_mixed_nullary_and_data() {
    let src = "
        (deftype (Result a) Ok (Err [:a val]))
        (defn check [r]
          (match r
            [Ok 1
             (Err x) 0]))
        (defn main [] (add-i64 (check Ok) (check (Err 42))))
    ";
    assert_eq!(compile_and_run_simple(src), 1);
}

// =============================================================================
// REPL ADTs
// =============================================================================

// spec: 05-definitions §5.2.1 — product type in REPL
#[test]
fn repl_adt_product() {
    let mut session = repl_session();
    repl_eval(&mut session, "(deftype Point [:Int x :Int y])");
    let display = repl_eval_display(&mut session, "(Point 3 4)");
    assert_eq!(display, ":Point (Point 3 4)");
}

// spec: 05-definitions §5.2.2 — sum type Some in REPL
#[test]
fn repl_adt_sum_some() {
    let mut session = repl_session();
    repl_eval(&mut session, "(deftype (Option a) None (Some [:a val]))");
    let display = repl_eval_display(&mut session, "(Some 42)");
    assert_eq!(display, ":(Option Int) (Some 42)");
}

// spec: 05-definitions §5.2.2 — sum type None in REPL
#[test]
fn repl_adt_sum_none() {
    let mut session = repl_session();
    repl_eval(&mut session, "(deftype (Option a) None (Some [:a val]))");
    let display = repl_eval_display(&mut session, "None");
    // Type variable name may be source-level `a` or internal `t1` depending on checker.
    assert!(
        display.contains("Option") && display.ends_with("None"),
        "expected :(Option ...) None, got: {display}"
    );
}

// spec: 06-pattern-matching §6.1 — match expression in REPL
#[test]
fn repl_adt_match() {
    let mut session = repl_session();
    repl_eval(&mut session, "(deftype (Option a) None (Some [:a val]))");
    repl_eval(
        &mut session,
        "(defn unwrap [opt] (match opt [(Some x) x None 0]))",
    );
    assert_eq!(repl_eval(&mut session, "(unwrap (Some 99))"), 99);
    assert_eq!(repl_eval(&mut session, "(unwrap None)"), 0);
}

// spec: 06-pattern-matching §6.2.1 — constructor pattern in REPL
#[test]
fn repl_adt_product_match() {
    let mut session = repl_session();
    repl_eval(&mut session, "(deftype Point [:Int x :Int y])");
    repl_eval(
        &mut session,
        "(defn get-x [p] (match p [(Point x y) x]))",
    );
    assert_eq!(repl_eval(&mut session, "(get-x (Point 7 8))"), 7);
}

// =============================================================================
// Closures: lambda with captures (spec: 04-expressions)
// =============================================================================

// spec: 04-expressions §4.5.1 — simple free variable capture
#[test]
fn closure_simple_capture() {
    let src = "
        (defn main []
          (let [n 10]
            ((fn [x] (add-i64 n x)) 32)))
    ";
    assert_eq!(compile_and_run_simple(src), 42);
}

// spec: 04-expressions §4.5.1 — multiple free variable captures
#[test]
fn closure_multiple_captures() {
    let src = "
        (defn main []
          (let [a 1 b 2 c 3]
            ((fn [x] (add-i64 a (add-i64 b (add-i64 c x)))) 4)))
    ";
    assert_eq!(compile_and_run_simple(src), 10);
}

// spec: 04-expressions §4.5.1 — closure returned from function
#[test]
fn closure_returned_from_function() {
    let src = "
        (defn make-adder [n]
          (fn [x] (add-i64 n x)))
        (defn main [] ((make-adder 10) 32))
    ";
    assert_eq!(compile_and_run_simple(src), 42);
}

// spec: 04-expressions §4.5.1 — nested closures
#[test]
fn closure_nested() {
    let src = "
        (defn main []
          (let [a 1]
            (let [f (fn [x] (add-i64 a x))]
              (let [g (fn [y] (f y))]
                (g 9)))))
    ";
    assert_eq!(compile_and_run_simple(src), 10);
}

// spec: 04-expressions §4.6 — closure with higher-order function
#[test]
fn closure_with_higher_order() {
    let src = "
        (defn apply-fn [f x] (f x))
        (defn main []
          (let [n 10]
            (apply-fn (fn [x] (add-i64 n x)) 5)))
    ";
    assert_eq!(compile_and_run_simple(src), 15);
}

// spec: 04-expressions §4.5 — zero-param closure with capture
#[test]
fn closure_zero_param() {
    let src = "
        (defn main []
          (let [x 42]
            ((fn [] x))))
    ";
    assert_eq!(compile_and_run_simple(src), 42);
}

// spec: 04-expressions §4.5 — multi-param closure with capture
#[test]
fn closure_multi_param() {
    let src = "
        (defn main []
          (let [base 100]
            ((fn [a b] (add-i64 base (add-i64 a b))) 1 2)))
    ";
    assert_eq!(compile_and_run_simple(src), 103);
}

// spec: 04-expressions §4.5.1 — closure capturing Bool
#[test]
fn closure_capturing_bool() {
    let src = "
        (defn main []
          (let [flag true]
            ((fn [x] (if flag x 0)) 42)))
    ";
    assert_eq!(compile_and_run_simple(src), 42);
}

// spec: 04-expressions §4.6 — closure applied twice
#[test]
fn closure_apply_twice() {
    let src = "
        (defn apply-twice [f x] (f (f x)))
        (defn main [] (apply-twice (fn [x] (add-i64 x 1)) 0))
    ";
    assert_eq!(compile_and_run_simple(src), 2);
}

// spec: 04-expressions §4.5.1 — function composition via closures
#[test]
fn closure_compose() {
    let src = "
        (defn compose [f g]
          (fn [x] (f (g x))))
        (defn inc [x] (add-i64 x 1))
        (defn double [x] (mul-i64 x 2))
        (defn main [] ((compose inc double) 5))
    ";
    assert_eq!(compile_and_run_simple(src), 11);
}

// spec: 12-runtime §12.2.3 — named function as value
#[test]
fn named_function_as_value_apply() {
    let src = "
        (defn inc [x] (add-i64 x 1))
        (defn apply-fn [f x] (f x))
        (defn main [] (apply-fn inc 41))
    ";
    assert_eq!(compile_and_run_simple(src), 42);
}

// spec: 04-expressions §4.5.1 — closure capturing function argument
#[test]
fn closure_capturing_function_arg() {
    let src = "
        (defn make-fn [n] (fn [x] (add-i64 n x)))
        (defn main []
          (let [f (make-fn 100)]
            (add-i64 (f 1) (f 2))))
    ";
    assert_eq!(compile_and_run_simple(src), 203);
}

// spec: 04-expressions §4.4 — closure in if branch
#[test]
fn closure_in_if_branch() {
    let src = "
        (defn main []
          (let [pick true]
            (let [f (if pick (fn [x] (add-i64 x 1)) (fn [x] (sub-i64 x 1)))]
              (f 10))))
    ";
    assert_eq!(compile_and_run_simple(src), 11);
}

// spec: 04-expressions §4.6 — recursive HOF with closure
#[test]
fn closure_recursive_with_higher_order() {
    let src = "
        (defn repeat-fn [f n x]
          (if (eq-i64 n 0)
            x
            (repeat-fn f (sub-i64 n 1) (f x))))
        (defn main [] (repeat-fn (fn [x] (add-i64 x 1)) 5 0))
    ";
    assert_eq!(compile_and_run_simple(src), 5);
}

// =============================================================================
// REPL Closures
// =============================================================================

// spec: 04-expressions §4.5.1 — simple closure in REPL
#[test]
fn repl_closure_simple() {
    let mut session = repl_session();
    assert_eq!(
        repl_eval(
            &mut session,
            "(let [n 10] ((fn [x] (add-i64 n x)) 32))"
        ),
        42
    );
}

// spec: 04-expressions §4.5.1 — multiple captures in REPL
#[test]
fn repl_closure_multiple_captures() {
    let mut session = repl_session();
    assert_eq!(
        repl_eval(
            &mut session,
            "(let [a 1 b 2] ((fn [x] (add-i64 a (add-i64 b x))) 3))"
        ),
        6
    );
}

// spec: 04-expressions §4.5.1 — closure returned in REPL
#[test]
fn repl_closure_returned() {
    let mut session = repl_session();
    repl_eval(&mut session, "(defn make-adder [n] (fn [x] (add-i64 n x)))");
    assert_eq!(repl_eval(&mut session, "((make-adder 10) 32)"), 42);
}

// spec: repl/spec.md §1.2 — closure display format
#[test]
fn repl_closure_display() {
    let mut session = repl_session();
    repl_eval(&mut session, "(defn make-adder [n] (fn [x] (add-i64 n x)))");
    let display = repl_eval_display(&mut session, "(make-adder 5)");
    assert!(
        display.contains("<closure>"),
        "closure should display as <closure>, got: {display}"
    );
}

// =============================================================================
// ADT + Closure interactions
// =============================================================================

// spec: 04-expressions §4.5.1 — closure returning ADT
#[test]
fn closure_returning_adt() {
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

// spec: 04-expressions §4.5.1 — closure with ADT match
#[test]
fn closure_capturing_int_returning_match_result() {
    let src = "
        (deftype (Option a) None (Some [:a val]))
        (defn map-opt [opt f]
          (match opt
            [(Some x) (Some (f x))
             None None]))
        (defn main []
          (match (map-opt (Some 10) (fn [x] (mul-i64 x 2)))
            [(Some x) x
             None 0]))
    ";
    assert_eq!(compile_and_run_simple(src), 20);
}

// spec: 05-definitions §5.2.2 — ADT containing closure result
#[test]
fn adt_containing_closure_result() {
    let src = "
        (deftype (Option a) None (Some [:a val]))
        (defn main []
          (let [f (fn [x] (add-i64 x 1))]
            (match (Some (f 41))
              [(Some x) x
               None 0])))
    ";
    assert_eq!(compile_and_run_simple(src), 42);
}

// =============================================================================
// String + ADT interactions
// =============================================================================

// spec: 05-definitions §5.2.2 — string field in ADT
#[test]
fn string_in_adt() {
    let src = r#"
        (deftype (Option a) None (Some [:a val]))
        (defn main []
          (match (Some "hello")
            [(Some s) (str-len s)
             None 0]))
    "#;
    assert_eq!(compile_and_run_simple(src), 5);
}

// spec: 06-pattern-matching §6.1 — string conversion in match
#[test]
fn string_from_int_to_string_in_match() {
    let src = r#"
        (deftype (Option a) None (Some [:a val]))
        (defn to-string-opt [opt]
          (match opt
            [(Some n) (int-to-string n)
             None "none"]))
        (defn main [] (str-len (to-string-opt (Some 42))))
    "#;
    assert_eq!(compile_and_run_simple(src), 2);
}

// =============================================================================
// Exhaustiveness (spec: 06-pattern-matching)
// =============================================================================

// spec: 06-pattern-matching §6.5.1 — exhaustive match all constructors
#[test]
fn exhaustive_match_all_constructors() {
    let src = "
        (deftype (Option a) None (Some [:a val]))
        (defn to-int [opt]
          (match opt
            [None 0
             (Some x) x]))
        (defn main [] (to-int (Some 42)))
    ";
    assert_eq!(compile_and_run_simple(src), 42);
}

// spec: 06-pattern-matching §6.5.1 — exhaustive match with wildcard
#[test]
fn exhaustive_match_with_wildcard() {
    let src = "
        (deftype Color Red Green Blue)
        (defn is-red [c]
          (match c
            [Red 1
             _ 0]))
        (defn main [] (is-red Red))
    ";
    assert_eq!(compile_and_run_simple(src), 1);
}

// spec: 06-pattern-matching §6.5.1 — exhaustive match with variable
#[test]
fn exhaustive_match_with_var_pattern() {
    let src = "
        (deftype Color Red Green Blue)
        (defn to-int [c]
          (match c
            [Red 0
             other 1]))
        (defn main [] (to-int Green))
    ";
    assert_eq!(compile_and_run_simple(src), 1);
}

// spec: 06-pattern-matching §6.5.3 — runtime safety net
#[test]
fn non_exhaustive_match_panics() {
    let src = "
        (deftype (Option a) None (Some [:a val]))
        (defn partial [opt]
          (match opt
            [(Some x) x]))
        (defn main [] (partial None))
    ";
    let result = std::panic::catch_unwind(|| compile_and_run_simple(src));
    assert!(result.is_err(), "non-exhaustive match should panic");
}

// spec: 06-pattern-matching §6.5.1 — product type exhaustiveness
#[test]
fn exhaustive_product_type() {
    // Product types have exactly one constructor, so one pattern suffices.
    let src = "
        (deftype Point [:Int x :Int y])
        (defn sum [p]
          (match p [(Point x y) (add-i64 x y)]))
        (defn main [] (sum (Point 3 4)))
    ";
    assert_eq!(compile_and_run_simple(src), 7);
}

// spec: 06-pattern-matching §6.5.1 — three constructor exhaustiveness
#[test]
fn match_three_constructors() {
    let src = "
        (deftype Color Red Green Blue)
        (defn to-int [c]
          (match c
            [Red 1
             Green 2
             Blue 3]))
        (defn main [] (add-i64 (to-int Red) (add-i64 (to-int Green) (to-int Blue))))
    ";
    assert_eq!(compile_and_run_simple(src), 6);
}

// =============================================================================
// Dual-mode parity: compile_both (batch + interactive produce same results)
// =============================================================================

// spec: appendix-a-builtins §A.3 — dual-mode str-len parity
#[test]
fn dual_mode_string_len() {
    compile_both("(defn main [] (str-len \"hello\"))", 5);
}

// spec: appendix-a-builtins §A.3 — dual-mode str-eq parity
#[test]
fn dual_mode_string_eq() {
    compile_both("(defn main [] (if (str-eq \"a\" \"a\") 1 0))", 1);
}

// spec: appendix-a-builtins §A.3 — dual-mode str-concat parity
#[test]
fn dual_mode_string_concat() {
    compile_both("(defn main [] (str-len (str-concat \"ab\" \"cd\")))", 4);
}

// spec: appendix-a-builtins §A.3 — dual-mode int-to-string parity
#[test]
fn dual_mode_int_to_string() {
    compile_both("(defn main [] (str-len (int-to-string 123)))", 3);
}

// spec: 05-definitions §5.2.1 — dual-mode product type parity
#[test]
fn dual_mode_adt_product() {
    let src = "
        (deftype Point [:Int x :Int y])
        (defn main [] (match (Point 3 4) [(Point x y) (add-i64 x y)]))
    ";
    compile_both(src, 7);
}

// spec: 05-definitions §5.2.2 — dual-mode sum Some parity
#[test]
fn dual_mode_adt_sum_some() {
    let src = "
        (deftype (Option a) None (Some [:a val]))
        (defn main [] (match (Some 42) [(Some x) x None 0]))
    ";
    compile_both(src, 42);
}

// spec: 05-definitions §5.2.2 — dual-mode sum None parity
#[test]
fn dual_mode_adt_sum_none() {
    let src = "
        (deftype (Option a) None (Some [:a val]))
        (defn main [] (match None [(Some x) x None 99]))
    ";
    compile_both(src, 99);
}

// spec: 04-expressions §4.5.1 — dual-mode closure capture parity
#[test]
fn dual_mode_closure_capture() {
    compile_both(
        "(defn main [] (let [n 10] ((fn [x] (add-i64 n x)) 32)))",
        42,
    );
}

// spec: 04-expressions §4.5.1 — dual-mode closure return parity
#[test]
fn dual_mode_closure_returned() {
    let src = "
        (defn make-adder [n] (fn [x] (add-i64 n x)))
        (defn main [] ((make-adder 10) 32))
    ";
    compile_both(src, 42);
}

// spec: 04-expressions §4.6 — dual-mode HOF parity
#[test]
fn dual_mode_higher_order() {
    let src = "
        (defn apply-fn [f x] (f x))
        (defn main [] (apply-fn (fn [x] (add-i64 x 10)) 32))
    ";
    compile_both(src, 42);
}

// spec: 12-runtime §12.2.3 — dual-mode named fn value parity
#[test]
fn dual_mode_named_fn_value() {
    let src = "
        (defn inc [x] (add-i64 x 1))
        (defn apply-fn [f x] (f x))
        (defn main [] (apply-fn inc 41))
    ";
    compile_both(src, 42);
}

// spec: 06-pattern-matching §6.2.1 — dual-mode constructor pattern parity
#[test]
fn dual_mode_match_with_field_bindings() {
    let src = "
        (deftype Point [:Int x :Int y])
        (defn get-x [p] (match p [(Point x y) x]))
        (defn main [] (get-x (Point 42 0)))
    ";
    compile_both(src, 42);
}

// spec: 06-pattern-matching §6.2.2 — dual-mode enum match parity
#[test]
fn dual_mode_enum_match() {
    let src = "
        (deftype Color Red Green Blue)
        (defn color-val [c]
          (match c [Red 1 Green 2 Blue 3]))
        (defn main [] (color-val Blue))
    ";
    compile_both(src, 3);
}

// spec: 04-expressions §4.5 — dual-mode lambda immediate parity
#[test]
fn dual_mode_lambda_immediate() {
    compile_both("(defn main [] ((fn [x] (add-i64 x 1)) 5))", 6);
}

// spec: 04-expressions §4.5 — dual-mode lambda in let parity
#[test]
fn dual_mode_lambda_in_let() {
    compile_both(
        "(defn main [] (let [f (fn [x] (mul-i64 x 2))] (f 21)))",
        42,
    );
}

// =============================================================================
// Error paths (spec: various)
// =============================================================================

// spec: 03-types §3.5 — type error String where Int expected
#[test]
fn error_string_where_int_expected() {
    assert_type_error("(defn main [] (add-i64 \"hello\" 1))", "");
}

// spec: 03-types §3.5 — type error Int where String expected
#[test]
fn error_int_where_string_expected() {
    assert_type_error("(defn main [] (str-len 42))", "");
}

// spec: 05-definitions §5.2.7 — constructor wrong arg count
#[test]
fn error_adt_constructor_wrong_arg_count() {
    // Point expects 2 args.
    assert_error(
        "(deftype Point [:Int x :Int y]) (defn main [] (Point 1))",
        "",
    );
}

// spec: 05-definitions §5.2.7 — constructor wrong type
#[test]
fn error_adt_constructor_wrong_type() {
    // Point expects Int, passing Bool.
    assert_type_error(
        "(deftype Point [:Int x :Int y]) (defn main [] (match (Point true 2) [(Point x y) x]))",
        "",
    );
}

// spec: 04-expressions §4.4 — if branch String/Int mismatch
#[test]
fn error_if_branches_type_mismatch_string_int() {
    assert_type_error(
        "(defn main [] (if true \"hello\" 42))",
        "",
    );
}

// spec: 04-expressions §4.6 — closure arity mismatch
#[test]
fn error_closure_arity_mismatch() {
    assert_error(
        "(defn main [] (let [f (fn [x] x)] (f 1 2)))",
        "",
    );
}

// spec: 04-expressions §4.2.1 — undefined constructor reference
#[test]
fn error_undefined_constructor() {
    assert_error(
        "(defn main [] (Foo 1 2))",
        "",
    );
}

// =============================================================================
// Let-polymorphism with closures (spec: 03-types)
// =============================================================================

// spec: 03-types §3.4 — let-polymorphism at multiple types
#[test]
fn let_bound_identity_at_multiple_types() {
    let src = "
        (defn main []
          (let [id (fn [x] x)]
            (add-i64 (id 1) (id 2))))
    ";
    assert_eq!(compile_and_run_simple(src), 3);
}

// spec: 03-types §3.4 — polymorphic higher-order function
#[test]
fn polymorphic_higher_order() {
    let src = "
        (defn apply-fn [f x] (f x))
        (defn main []
          (add-i64 (apply-fn (fn [x] x) 1) (apply-fn (fn [x] x) 2)))
    ";
    assert_eq!(compile_and_run_simple(src), 3);
}

// spec: 03-types §3.4 — let-bound lambda with capture
#[test]
fn let_bound_lambda_with_capture() {
    let src = "
        (defn main []
          (let [base 100
                f (fn [x] (add-i64 base x))]
            (add-i64 (f 1) (f 2))))
    ";
    assert_eq!(compile_and_run_simple(src), 203);
}

// spec: 03-types §3.3 — polymorphic identity on String
#[test]
fn identity_on_string() {
    let src = r#"
        (defn id [x] x)
        (defn main [] (str-len (id "hello")))
    "#;
    assert_eq!(compile_and_run_simple(src), 5);
}

// spec: 03-types §3.3 — polymorphic identity on ADT
#[test]
fn identity_on_adt() {
    let src = "
        (deftype (Option a) None (Some [:a val]))
        (defn id [x] x)
        (defn main [] (match (id (Some 42)) [(Some x) x None 0]))
    ";
    assert_eq!(compile_and_run_simple(src), 42);
}

// spec: 03-types §3.3 — polymorphic HOF on ADT
#[test]
fn higher_order_on_adt() {
    let src = "
        (deftype (Option a) None (Some [:a val]))
        (defn apply-fn [f x] (f x))
        (defn main []
          (match (apply-fn (fn [x] (Some x)) 42)
            [(Some x) x
             None 0]))
    ";
    assert_eq!(compile_and_run_simple(src), 42);
}

// =============================================================================
// parse-int (depends on ADTs: returns Option Int)
// =============================================================================

// spec: appendix-a-builtins §A.3 — parse-int valid input
#[test]
fn parse_int_valid() {
    let src = r#"
        (deftype (Option a) None (Some [:a val]))
        (defn main []
          (match (parse-int "42")
            [(Some n) n
             None 0]))
    "#;
    assert_eq!(compile_and_run_simple(src), 42);
}

// spec: appendix-a-builtins §A.3 — parse-int invalid input
#[test]
fn parse_int_invalid() {
    let src = r#"
        (deftype (Option a) None (Some [:a val]))
        (defn main []
          (match (parse-int "not-a-number")
            [(Some n) n
             None (sub-i64 0 1)]))
    "#;
    assert_eq!(compile_and_run_simple(src), -1);
}

// =============================================================================
// Misc: edge cases and interactions
// =============================================================================

// spec: 12-runtime §12.5 — TCO with higher-order function
#[test]
fn closure_and_tco() {
    // TCO with higher-order function parameter.
    let src = "
        (defn fold [f acc n]
          (if (eq-i64 n 0)
            acc
            (fold f (f acc n) (sub-i64 n 1))))
        (defn main [] (fold (fn [acc n] (add-i64 acc n)) 0 100))
    ";
    assert_eq!(compile_and_run_simple(src), 5050);
}

// spec: 12-runtime §12.5 — TCO with ADT match
#[test]
fn adt_in_tco() {
    // TCO with ADT match in the body.
    let src = "
        (deftype Action Stop Continue)
        (defn loop-fn [n]
          (match (if (eq-i64 n 0) Stop Continue)
            [Stop n
             Continue (loop-fn (sub-i64 n 1))]))
        (defn main [] (loop-fn 100000))
    ";
    assert_eq!(compile_and_run_simple(src), 0);
}

// spec: 03-types §3.1 — string in recursive function
#[test]
fn string_in_recursive_function() {
    let src = r#"
        (defn count-down [n]
          (if (eq-i64 n 0)
            (str-len "done")
            (count-down (sub-i64 n 1))))
        (defn main [] (count-down 10))
    "#;
    assert_eq!(compile_and_run_simple(src), 4);
}

// spec: 05-definitions §5.2 — multiple ADT definitions
#[test]
fn multiple_adt_definitions() {
    let src = "
        (deftype Color Red Green Blue)
        (deftype (Option a) None (Some [:a val]))
        (defn main []
          (match (Some Green)
            [(Some c) (match c [Red 1 Green 2 Blue 3])
             None 0]))
    ";
    assert_eq!(compile_and_run_simple(src), 2);
}

// spec: 04-expressions §4.5.1 — closure over closure
#[test]
fn closure_over_closure() {
    let src = "
        (defn make-counter [start]
          (fn [step] (add-i64 start step)))
        (defn main []
          (let [c (make-counter 100)]
            (add-i64 (c 1) (c 2))))
    ";
    assert_eq!(compile_and_run_simple(src), 203);
}

// spec: 04-expressions §4.5.1 — let-bound ADT and closure
#[test]
fn let_bound_adt_and_closure() {
    let src = "
        (deftype (Option a) None (Some [:a val]))
        (defn main []
          (let [f (fn [x] (Some x))
                result (f 42)]
            (match result
              [(Some n) n
               None 0])))
    ";
    assert_eq!(compile_and_run_simple(src), 42);
}

// =============================================================================
// Vec: literals, primitives (spec: appendix-a-builtins, 04-expressions)
// =============================================================================

// spec: 03-types §3.2.4 — Vec literal of Int
#[test]

fn vec_literal_int() {
    let src = "(defn main [] (vec-len [1 2 3]))";
    assert_eq!(compile_and_run_simple(src), 3);
}

// spec: 03-types §3.2.4 — empty Vec literal
#[test]

fn vec_literal_empty() {
    let src = "(defn main [] (vec-len []))";
    assert_eq!(compile_and_run_simple(src), 0);
}

// spec: 03-types §3.2.4 — Vec literal of String
#[test]

fn vec_literal_strings() {
    let src = r#"(defn main [] (vec-len ["a" "b"]))"#;
    assert_eq!(compile_and_run_simple(src), 2);
}

// spec: appendix-a-builtins §A.3 — vec-get first element
#[test]

fn vec_get_first() {
    let src = "(defn main [] (vec-get [10 20 30] 0))";
    assert_eq!(compile_and_run_simple(src), 10);
}

// spec: appendix-a-builtins §A.3 — vec-get last element
#[test]

fn vec_get_last() {
    let src = "(defn main [] (vec-get [10 20 30] 2))";
    assert_eq!(compile_and_run_simple(src), 30);
}

// spec: appendix-a-builtins §A.3 — vec-get middle element
#[test]

fn vec_get_middle() {
    let src = "(defn main [] (vec-get [10 20 30] 1))";
    assert_eq!(compile_and_run_simple(src), 20);
}

// spec: appendix-a-builtins §A.3 — vec-set element
#[test]

fn vec_set_element() {
    let src = "
        (defn main []
          (vec-get (vec-set [10 20 30] 1 99) 1))
    ";
    assert_eq!(compile_and_run_simple(src), 99);
}

// spec: 12-runtime §12.3.3 — vec-set preserves other elements
#[test]

fn vec_set_preserves_other_elements() {
    let src = "
        (defn main []
          (let [v (vec-set [10 20 30] 1 99)]
            (add-i64 (vec-get v 0) (vec-get v 2))))
    ";
    assert_eq!(compile_and_run_simple(src), 40);
}

// spec: appendix-a-builtins §A.3 — vec-push appends element
#[test]

fn vec_push_appends() {
    let src = "
        (defn main [] (vec-len (vec-push [1 2] 3)))
    ";
    assert_eq!(compile_and_run_simple(src), 3);
}

// spec: appendix-a-builtins §A.3 — vec-push value accessible
#[test]

fn vec_push_value() {
    let src = "
        (defn main [] (vec-get (vec-push [1 2] 3) 2))
    ";
    assert_eq!(compile_and_run_simple(src), 3);
}

// spec: appendix-a-builtins §A.3 — vec-len empty
#[test]

fn vec_len_zero() {
    let src = "(defn main [] (vec-len []))";
    assert_eq!(compile_and_run_simple(src), 0);
}

// spec: appendix-a-builtins §A.3 — vec-len three elements
#[test]

fn vec_len_three() {
    let src = "(defn main [] (vec-len [1 2 3]))";
    assert_eq!(compile_and_run_simple(src), 3);
}

// spec: 04-expressions §4.3 — Vec in let scope
#[test]

fn vec_in_let() {
    let src = "
        (defn main []
          (let [v [1 2 3]]
            (vec-get v 0)))
    ";
    assert_eq!(compile_and_run_simple(src), 1);
}

// spec: 04-expressions §4.6 — Vec as function argument
#[test]

fn vec_in_defn() {
    let src = "
        (defn first [v] (vec-get v 0))
        (defn main [] (first [10 20]))
    ";
    assert_eq!(compile_and_run_simple(src), 10);
}

// spec: 03-types §3.2.4 — Vec of String element access
#[test]

fn vec_of_strings_get() {
    let src = r#"
        (defn main []
          (str-len (vec-get ["hello" "world"] 0)))
    "#;
    assert_eq!(compile_and_run_simple(src), 5);
}

// spec: 03-types §3.2.4 — Vec of String second element
#[test]

fn vec_of_strings_get_second() {
    let src = r#"
        (defn main []
          (str-len (vec-get ["hello" "world"] 1)))
    "#;
    assert_eq!(compile_and_run_simple(src), 5);
}

// spec: 03-types §3.2.4 — Vec of ADTs element access
#[test]

fn vec_of_adts() {
    let src = "
        (deftype (Option a) None (Some [:a val]))
        (defn main []
          (match (vec-get [(Some 1) None (Some 3)] 0)
            [(Some x) x
             None 0]))
    ";
    assert_eq!(compile_and_run_simple(src), 1);
}

// spec: 03-types §3.2.4 — Vec of ADTs None element
#[test]

fn vec_of_adts_none() {
    let src = "
        (deftype (Option a) None (Some [:a val]))
        (defn main []
          (match (vec-get [(Some 1) None (Some 3)] 1)
            [(Some x) x
             None 0]))
    ";
    assert_eq!(compile_and_run_simple(src), 0);
}

// spec: appendix-a-builtins §A.3 — vec-push to empty Vec
#[test]

fn vec_push_to_empty() {
    let src = "
        (defn main []
          (vec-get (vec-push [] 42) 0))
    ";
    assert_eq!(compile_and_run_simple(src), 42);
}

// spec: appendix-a-builtins §A.3 — vec-set first element
#[test]

fn vec_set_first() {
    let src = "
        (defn main []
          (vec-get (vec-set [1 2 3] 0 99) 0))
    ";
    assert_eq!(compile_and_run_simple(src), 99);
}

// spec: appendix-a-builtins §A.3 — vec-set last element
#[test]

fn vec_set_last() {
    let src = "
        (defn main []
          (vec-get (vec-set [1 2 3] 2 99) 2))
    ";
    assert_eq!(compile_and_run_simple(src), 99);
}

// spec: 03-types §3.2.4 — Vec returned from function
#[test]

fn vec_returned_from_function() {
    let src = "
        (defn make-vec [] [10 20 30])
        (defn main [] (vec-get (make-vec) 1))
    ";
    assert_eq!(compile_and_run_simple(src), 20);
}

// spec: 03-types §3.2.4 — Vec passed to function
#[test]

fn vec_passed_to_function() {
    let src = "
        (defn sum-first-two [v]
          (add-i64 (vec-get v 0) (vec-get v 1)))
        (defn main [] (sum-first-two [3 4 5]))
    ";
    assert_eq!(compile_and_run_simple(src), 7);
}

// spec: 04-expressions §4.4 — Vec in if branch
#[test]

fn vec_in_if_branch() {
    let src = "
        (defn main []
          (vec-len (if true [1 2 3] [4 5])))
    ";
    assert_eq!(compile_and_run_simple(src), 3);
}

// spec: appendix-a-builtins §A.3 — chained vec-push
#[test]

fn vec_push_chain() {
    // Push multiple elements via chaining.
    let src = "
        (defn main []
          (vec-len (vec-push (vec-push (vec-push [] 1) 2) 3)))
    ";
    assert_eq!(compile_and_run_simple(src), 3);
}

// =============================================================================
// Dual-mode Vec tests (batch + interactive)
// =============================================================================

// spec: 03-types §3.2.4 — dual-mode Vec literal parity
#[test]

fn dual_mode_vec_literal() {
    compile_both("(defn main [] (vec-len [1 2 3]))", 3);
}

// spec: appendix-a-builtins §A.3 — dual-mode vec-get parity
#[test]

fn dual_mode_vec_get() {
    compile_both("(defn main [] (vec-get [10 20 30] 1))", 20);
}

// spec: appendix-a-builtins §A.3 — dual-mode vec-push parity
#[test]

fn dual_mode_vec_push() {
    compile_both("(defn main [] (vec-len (vec-push [1 2] 3)))", 3);
}

// =============================================================================
// REPL Vec tests
// =============================================================================

// spec: 03-types §3.2.4 — Vec literal in REPL
#[test]

fn repl_vec_literal() {
    let mut session = repl_session();
    assert_eq!(repl_eval(&mut session, "(vec-len [1 2 3])"), 3);
}

// spec: appendix-a-builtins §A.3 — vec-get in REPL
#[test]

fn repl_vec_get() {
    let mut session = repl_session();
    assert_eq!(repl_eval(&mut session, "(vec-get [10 20 30] 0)"), 10);
}

// spec: appendix-a-builtins §A.3 — vec-set in REPL
#[test]

fn repl_vec_set() {
    let mut session = repl_session();
    assert_eq!(
        repl_eval(&mut session, "(vec-get (vec-set [10 20 30] 1 99) 1)"),
        99
    );
}

// spec: appendix-a-builtins §A.3 — vec-push in REPL
#[test]

fn repl_vec_push() {
    let mut session = repl_session();
    assert_eq!(
        repl_eval(&mut session, "(vec-len (vec-push [1 2] 3))"),
        3
    );
}

// spec: repl/spec.md §1.2 — Vec display format in REPL
#[test]
fn repl_vec_display() {
    let mut session = repl_session();
    let display = repl_eval_display(&mut session, "[1 2 3]");
    assert!(
        display.contains("[1, 2, 3]") || display.contains("[1 2 3]"),
        "Vec should display elements, got: {display}"
    );
}
