// Integration tests for the standard library prelude.
//
// This is the ONE allowed exception to the stdlib separation rule:
// these tests load the real stdlib prelude and validate that it works.
// All other tests in tests/ are free-standing (no stdlib dependency).
//
// Tests use a shared session (LazyLock<SendableSession>) to avoid
// expensive re-initialization of the prelude for each test.

mod helpers;

use std::path::Path;
use std::sync::{LazyLock, Mutex};

use cranelisp::repl::{format_result_value, ReplSession};
use cranelisp_types::Type;

// ReplSession contains JIT function pointers (in MacroEnv) which are not
// auto-Send/Sync. Since test threads only access the session through a Mutex,
// this is safe.
struct SendableSession(Mutex<ReplSession>);

// SAFETY: ReplSession is accessed only through Mutex, which provides
// synchronization. The non-Send/Sync fields (JIT function pointers in
// MacroEnv) are only used during eval(), which holds the mutex lock.
unsafe impl Send for SendableSession {}
unsafe impl Sync for SendableSession {}

/// Shared prelude-loaded session for all stdlib tests.
static SESSION: LazyLock<SendableSession> = LazyLock::new(|| {
    let project_root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let stdlib_dir = project_root.join("stdlib");
    let session =
        ReplSession::new_with_prelude(project_root, &[stdlib_dir])
            .expect("prelude should load without errors");
    SendableSession(Mutex::new(session))
});

/// Evaluate an expression in the shared session and return (value, type).
fn eval(src: &str) -> (i64, Type) {
    let mut session = SESSION.0.lock().unwrap_or_else(|poisoned| {
        // Recover from a poisoned mutex (a prior test panicked).
        poisoned.into_inner()
    });
    let result = session
        .eval(src)
        .unwrap_or_else(|e| panic!("eval failed on '{src}': {e}"));
    (result.value, result.ty)
}

/// Evaluate an expression and return its formatted display string.
#[allow(dead_code)]
fn eval_display(src: &str) -> String {
    let mut session = SESSION.0.lock().unwrap_or_else(|poisoned| {
        poisoned.into_inner()
    });
    let result = session
        .eval(src)
        .unwrap_or_else(|e| panic!("eval_display failed on '{src}': {e}"));
    if let Some(display) = result.definition_display {
        display
    } else {
        format_result_value(
            result.value,
            &result.ty,
            session.type_defs(),
            session.type_modules(),
        )
    }
}

// =============================================================================
// a. Prelude loads without errors
// =============================================================================

// spec: spec/09-macros.md §9.5 — prelude loads successfully
#[test]
fn prelude_loads_without_errors() {
    // Accessing the shared session triggers prelude loading.
    // If new_with_prelude returned Err, LazyLock initialization would panic.
    let _session = SESSION.0.lock().unwrap_or_else(|p| p.into_inner());
    // If we get here, prelude loaded successfully.
}

// =============================================================================
// b. Arithmetic operators
// =============================================================================

// spec: spec/07-traits.md §7.1 — Num trait: Int addition
#[test]
fn arithmetic_add_int() {
    let (val, ty) = eval("(+ 1 2)");
    assert_eq!(val, 3);
    assert_eq!(ty, Type::Int);
}

// spec: spec/07-traits.md §7.1 — Num trait: Int subtraction
#[test]
fn arithmetic_sub_int() {
    let (val, ty) = eval("(- 5 3)");
    assert_eq!(val, 2);
    assert_eq!(ty, Type::Int);
}

// spec: spec/07-traits.md §7.1 — Num trait: Int multiplication
#[test]
fn arithmetic_mul_int() {
    let (val, ty) = eval("(* 2 3)");
    assert_eq!(val, 6);
    assert_eq!(ty, Type::Int);
}

// spec: spec/07-traits.md §7.1 — Num trait: Int division
#[test]
fn arithmetic_div_int() {
    let (val, ty) = eval("(/ 10 2)");
    assert_eq!(val, 5);
    assert_eq!(ty, Type::Int);
}

// =============================================================================
// c. Float arithmetic
// =============================================================================

// spec: spec/07-traits.md §7.1 — Num trait: Float addition
#[test]
fn arithmetic_add_float() {
    let (val, ty) = eval("(+ 1.0 2.0)");
    let float_val = f64::from_bits(val as u64);
    assert!((float_val - 3.0).abs() < f64::EPSILON);
    assert_eq!(ty, Type::Float);
}

// =============================================================================
// d. Comparison operators
// =============================================================================

// spec: spec/07-traits.md §7.1 — Eq trait: Int equality
#[test]
fn comparison_eq_int() {
    let (val, ty) = eval("(= 1 1)");
    assert_eq!(val, 1); // true = 1
    assert_eq!(ty, Type::Bool);
}

// spec: spec/07-traits.md §7.1 — Ord trait: Int less-than
#[test]
fn comparison_lt_int() {
    let (val, ty) = eval("(< 1 2)");
    assert_eq!(val, 1); // true = 1
    assert_eq!(ty, Type::Bool);
}

// spec: spec/07-traits.md §7.1 — Ord trait: Int greater-than
#[test]
fn comparison_gt_int() {
    let (val, ty) = eval("(> 2 1)");
    assert_eq!(val, 1); // true = 1
    assert_eq!(ty, Type::Bool);
}

// =============================================================================
// e. Boolean equality
// =============================================================================

// spec: spec/07-traits.md §7.1 — Eq trait: Bool equality
#[test]
fn comparison_eq_bool() {
    let (val, ty) = eval("(= true true)");
    assert_eq!(val, 1); // true = 1
    assert_eq!(ty, Type::Bool);
}

// =============================================================================
// f. String equality
// =============================================================================

// spec: spec/07-traits.md §7.1 — Eq trait: String equality
#[test]
fn comparison_eq_string() {
    let (val, ty) = eval(r#"(= "hi" "hi")"#);
    assert_eq!(val, 1); // true = 1
    assert_eq!(ty, Type::Bool);
}

// =============================================================================
// g. Display trait: show
// =============================================================================

// spec: spec/07-traits.md §7.1 — Display trait: show Int
#[test]
fn display_show_int() {
    let (val, ty) = eval("(show 42)");
    // show returns a String (heap-allocated), so val is a pointer.
    assert_eq!(ty, Type::String);
    // Read the string from the heap to verify its contents.
    let s = unsafe { cranelisp_runtime::read_string_as_str(val) };
    assert_eq!(s, "42");
}

// =============================================================================
// h. Option type
// =============================================================================

// spec: spec/06-adt.md §6.1 — Option type constructors
#[test]
fn option_some_constructs() {
    let (_val, ty) = eval("(Some 1)");
    assert_eq!(
        ty,
        Type::ADT(cranelisp_types::TypeName::from("Option"), vec![Type::Int])
    );
}

// spec: spec/06-adt.md §6.1 — Option None constructor
#[test]
fn option_none_exists() {
    let (val, ty) = eval("None");
    // None is a nullary constructor, represented as bare tag value 0.
    assert_eq!(val, 0);
    match &ty {
        Type::ADT(name, _) => assert_eq!(name.as_ref(), "Option"),
        other => panic!("expected ADT Option, got: {other:?}"),
    }
}

// =============================================================================
// i. Macros: do, when
// =============================================================================

// spec: spec/10-io.md §10.4 — do macro sequences IO actions via bind
#[test]
fn macro_do_returns_last() {
    // do now expands to bind chains (IO semantics).
    // (do (Pure 1) (Pure 2) (Pure 3)) sequences IO actions, returns last.
    let (val, ty) = eval("(do (Pure 1) (Pure 2) (Pure 3))");
    assert!(ty.is_io(), "do should return IO type, got: {:?}", ty);
    let inner = cranelisp_runtime::run_io_trampoline(val);
    assert_eq!(inner, 3);
}

// spec: spec/09-macros.md §9.5 — when macro with true condition
#[test]
fn macro_when_true() {
    // when expands to (if test body None), so body must return Option.
    let (_val, ty) = eval("(when true (Some 42))");
    assert_eq!(
        ty,
        Type::ADT(cranelisp_types::TypeName::from("Option"), vec![Type::Int])
    );
}

// =============================================================================
// j. cond macro
// =============================================================================

// spec: spec/09-macros.md §9.5 — cond macro multi-way conditional
#[test]
fn macro_cond_fallthrough() {
    let (val, ty) = eval("(cond (= 1 2) 0 1)");
    assert_eq!(val, 1);
    assert_eq!(ty, Type::Int);
}

// =============================================================================
// k. Result type (from fn.result module)
// =============================================================================

// spec: spec/06-adt.md §6.1 — Result Ok constructor
#[test]
fn result_ok_constructs() {
    let (_val, ty) = eval("(Ok 42)");
    match &ty {
        Type::ADT(name, _) => assert_eq!(name.as_ref(), "Result"),
        other => panic!("expected ADT Result, got: {other:?}"),
    }
}

// spec: spec/06-adt.md §6.1 — Result Err constructor
#[test]
fn result_err_constructs() {
    let (_val, ty) = eval(r#"(Err "oops")"#);
    match &ty {
        Type::ADT(name, _) => assert_eq!(name.as_ref(), "Result"),
        other => panic!("expected ADT Result, got: {other:?}"),
    }
}

// =============================================================================
// l. Inequality operator
// =============================================================================

// spec: spec/07-traits.md §7.1 — Eq trait: != operator
#[test]
fn comparison_neq_int() {
    let (val, ty) = eval("(!= 1 2)");
    assert_eq!(val, 1); // true
    assert_eq!(ty, Type::Bool);
}

// spec: spec/07-traits.md §7.1 — Eq trait: != false case
#[test]
fn comparison_neq_int_false() {
    let (val, ty) = eval("(!= 1 1)");
    assert_eq!(val, 0); // false
    assert_eq!(ty, Type::Bool);
}

// =============================================================================
// m. Ord operator coverage
// =============================================================================

// spec: spec/07-traits.md §7.1 — Ord trait: <= operator
#[test]
fn comparison_le_int() {
    let (val, ty) = eval("(<= 1 1)");
    assert_eq!(val, 1); // true
    assert_eq!(ty, Type::Bool);
}

// spec: spec/07-traits.md §7.1 — Ord trait: >= operator
#[test]
fn comparison_ge_int() {
    let (val, ty) = eval("(>= 2 1)");
    assert_eq!(val, 1); // true
    assert_eq!(ty, Type::Bool);
}

// spec: spec/07-traits.md §7.1 — Ord trait: Float less-than
#[test]
fn comparison_lt_float() {
    let (val, ty) = eval("(< 1.0 2.0)");
    assert_eq!(val, 1); // true
    assert_eq!(ty, Type::Bool);
}

// =============================================================================
// n. Display trait coverage
// =============================================================================

// spec: spec/07-traits.md §7.1 — Display trait: show Bool
#[test]
fn display_show_bool() {
    let (val, ty) = eval("(show true)");
    assert_eq!(ty, Type::String);
    let s = unsafe { cranelisp_runtime::read_string_as_str(val) };
    assert_eq!(s, "true");
}

// spec: spec/07-traits.md §7.1 — Display trait: show String
#[test]
fn display_show_string() {
    let (val, ty) = eval(r#"(show "hello")"#);
    assert_eq!(ty, Type::String);
    let s = unsafe { cranelisp_runtime::read_string_as_str(val) };
    assert_eq!(s, "hello");
}

// =============================================================================
// o. Multi-module loading (domain modules loaded correctly)
// =============================================================================

// spec: spec/08-modules.md §8.2 — prelude loads domain submodules
#[test]
fn domain_modules_traits_available() {
    // Verify that traits from separate domain modules are accessible
    // via prelude re-export (transitive import chain).
    let (val, ty) = eval("(+ (- 10 3) (* 2 3))");
    assert_eq!(val, 13);
    assert_eq!(ty, Type::Int);
}

// =============================================================================
// p. Prelude macros: cond
// =============================================================================

// spec: spec/09-macros.md §9.5 — cond first branch match
#[test]
fn macro_cond_first_match() {
    let (val, ty) = eval("(cond (= 1 1) 10 20)");
    assert_eq!(val, 10);
    assert_eq!(ty, Type::Int);
}

// spec: spec/09-macros.md §9.5 — cond second branch match
#[test]
fn macro_cond_second_match() {
    let (val, ty) = eval("(cond (= 1 2) 10 (= 2 2) 20 30)");
    assert_eq!(val, 20);
    assert_eq!(ty, Type::Int);
}

// spec: spec/09-macros.md §9.5 — cond default (all conditions false)
#[test]
fn macro_cond_default() {
    let (val, ty) = eval("(cond (= 1 2) 10 (= 3 4) 20 99)");
    assert_eq!(val, 99);
    assert_eq!(ty, Type::Int);
}

// spec: spec/09-macros.md §9.5 — cond with comparison expression
#[test]
fn macro_cond_with_comparison() {
    let (val, ty) = eval("(cond (> 5 10) 1 (< 5 10) 2 3)");
    assert_eq!(val, 2);
    assert_eq!(ty, Type::Int);
}

// =============================================================================
// q. Prelude macros: case
// =============================================================================

// spec: spec/09-macros.md §9.5 — case first match
#[test]
fn macro_case_first_match() {
    let (val, ty) = eval("(case 1 1 10 2 20 99)");
    assert_eq!(val, 10);
    assert_eq!(ty, Type::Int);
}

// spec: spec/09-macros.md §9.5 — case second match
#[test]
fn macro_case_second_match() {
    let (val, ty) = eval("(case 2 1 10 2 20 99)");
    assert_eq!(val, 20);
    assert_eq!(ty, Type::Int);
}

// spec: spec/09-macros.md §9.5 — case default fallthrough
#[test]
fn macro_case_default() {
    let (val, ty) = eval("(case 3 1 10 2 20 99)");
    assert_eq!(val, 99);
    assert_eq!(ty, Type::Int);
}

// =============================================================================
// r. Prelude macros: do (IO semantics)
// =============================================================================

// spec: spec/10-io.md §10.4 — do single expression passes through
#[test]
fn macro_do_single() {
    // Single-expression do returns the expression as-is (no bind).
    let (val, ty) = eval("(do 42)");
    assert_eq!(val, 42);
    assert_eq!(ty, Type::Int);
}

// spec: spec/10-io.md §10.4 — do multi-expression sequences IO actions
#[test]
fn macro_do_multi() {
    // do with multiple expressions expands to nested bind calls.
    let (val, ty) = eval("(do (Pure 1) (Pure 2) (Pure 3) (Pure 42))");
    assert!(ty.is_io(), "do should return IO type, got: {:?}", ty);
    let inner = cranelisp_runtime::run_io_trampoline(val);
    assert_eq!(inner, 42);
}

// =============================================================================
// s. Prelude macros: when
// =============================================================================

// spec: spec/09-macros.md §9.5 — when true returns body wrapped in Some
#[test]
fn macro_when_true_some() {
    let (_val, ty) = eval("(when true (Some 42))");
    assert_eq!(
        ty,
        Type::ADT(cranelisp_types::TypeName::from("Option"), vec![Type::Int])
    );
}

// spec: spec/09-macros.md §9.5 — when false returns None
#[test]
fn macro_when_false_none() {
    let (val, ty) = eval("(when false (Some 42))");
    assert_eq!(val, 0); // None is tag 0
    match &ty {
        Type::ADT(name, _) => assert_eq!(name.as_ref(), "Option"),
        other => panic!("expected Option, got: {other:?}"),
    }
}

// =============================================================================
// t. Prelude macros: vec
// =============================================================================

// spec: spec/09-macros.md §9.5 — vec macro creates vector
#[test]
fn macro_vec_elements() {
    let (val, ty) = eval("(vec-len (vec 10 20 30))");
    assert_eq!(val, 3);
    assert_eq!(ty, Type::Int);
}

// spec: spec/09-macros.md §9.5 — vec macro empty vector
#[test]
fn macro_vec_empty() {
    let (val, ty) = eval("(vec-len (vec))");
    assert_eq!(val, 0);
    assert_eq!(ty, Type::Int);
}

// spec: spec/09-macros.md §9.5 — vec macro access element
#[test]
fn macro_vec_access() {
    let (val, ty) = eval("(vec-get (vec 10 20 30) 1)");
    assert_eq!(val, 20);
    assert_eq!(ty, Type::Int);
}

// =============================================================================
// u. Prelude macros: str
// =============================================================================

// spec: spec/09-macros.md §9.5 — str macro empty
#[test]
fn macro_str_empty() {
    let (val, ty) = eval("(str)");
    assert_eq!(ty, Type::String);
    let s = unsafe { cranelisp_runtime::read_string_as_str(val) };
    assert_eq!(s, "");
}

// spec: spec/09-macros.md §9.5 — str macro single argument
#[test]
fn macro_str_single() {
    let (val, ty) = eval(r#"(str "hello")"#);
    assert_eq!(ty, Type::String);
    let s = unsafe { cranelisp_runtime::read_string_as_str(val) };
    assert_eq!(s, "hello");
}

// spec: spec/09-macros.md §9.5 — str macro concatenation
#[test]
fn macro_str_multi() {
    let (val, ty) = eval(r#"(str "hello" " " "world")"#);
    assert_eq!(ty, Type::String);
    let s = unsafe { cranelisp_runtime::read_string_as_str(val) };
    assert_eq!(s, "hello world");
}

// =============================================================================
// v. Prelude macros: const
// =============================================================================

// spec: spec/09-macros.md §9.5 — const defines bare-symbol macro
// const and def expand to defmacro/begin. In batch mode, bare symbol expansion
// handles zero-arg macros transparently. At the REPL, bare macro names are
// intercepted for introspection (spec §11.4), so we test const/def in batch.
#[test]
fn macro_const_int_batch() {
    let dir = tempfile::tempdir().unwrap();
    let entry = dir.path().join("main.cl");
    std::fs::write(
        &entry,
        "(const MY-CONST 42)\n(defn main [] MY-CONST)",
    )
    .unwrap();
    let stdlib_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("stdlib");
    let (value, _ty) = helpers::batch_run_file(&entry, &[stdlib_dir]).unwrap();
    assert_eq!(value, 42);
}

// spec: spec/09-macros.md §9.5 — const with string value
#[test]
fn macro_const_string_batch() {
    let dir = tempfile::tempdir().unwrap();
    let entry = dir.path().join("main.cl");
    std::fs::write(
        &entry,
        "(const GREETING \"hi\")\n(defn main [] (str-eq GREETING \"hi\"))",
    )
    .unwrap();
    let stdlib_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("stdlib");
    let (value, _ty) = helpers::batch_run_file(&entry, &[stdlib_dir]).unwrap();
    assert_eq!(value, 1); // true
}

// =============================================================================
// w. Prelude macros: def
// =============================================================================

// spec: spec/09-macros.md §9.5 — def creates named value (batch)
#[test]
fn macro_def_basic_batch() {
    let dir = tempfile::tempdir().unwrap();
    let entry = dir.path().join("main.cl");
    std::fs::write(
        &entry,
        "(def MY-VAL 42)\n(defn main [] MY-VAL)",
    )
    .unwrap();
    let stdlib_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("stdlib");
    let (value, _ty) = helpers::batch_run_file(&entry, &[stdlib_dir]).unwrap();
    assert_eq!(value, 42);
}

// spec: spec/09-macros.md §9.5 — def with expression (batch)
#[test]
fn macro_def_expression_batch() {
    let dir = tempfile::tempdir().unwrap();
    let entry = dir.path().join("main.cl");
    // Use add-i64 primitive to avoid prelude import ordering issues.
    std::fs::write(
        &entry,
        "(def MY-SUM (add-i64 1 2))\n(defn main [] MY-SUM)",
    )
    .unwrap();
    let stdlib_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("stdlib");
    let (value, _ty) = helpers::batch_run_file(&entry, &[stdlib_dir]).unwrap();
    assert_eq!(value, 3);
}

// =============================================================================
// x. Prelude macros: -> (thread-first)
// =============================================================================

// spec: spec/09-macros.md §9.5 — thread-first single form
#[test]
fn macro_thread_first_single() {
    // (-> 5 (+ 3)) should expand to (+ 5 3) = 8
    let (val, ty) = eval("(-> 5 (+ 3))");
    assert_eq!(val, 8);
    assert_eq!(ty, Type::Int);
}

// spec: spec/09-macros.md §9.5 — thread-first bare symbol
#[test]
fn macro_thread_first_bare() {
    // (-> 5 show) should expand to (show 5) => "5"
    let (val, ty) = eval("(-> 5 show)");
    assert_eq!(ty, Type::String);
    let s = unsafe { cranelisp_runtime::read_string_as_str(val) };
    assert_eq!(s, "5");
}

// spec: spec/09-macros.md §9.5 — thread-first multi-form
#[test]
fn macro_thread_first_multi() {
    // (-> 1 (+ 2) (* 3)) should expand to (* (+ 1 2) 3) = 9
    let (val, ty) = eval("(-> 1 (+ 2) (* 3))");
    assert_eq!(val, 9);
    assert_eq!(ty, Type::Int);
}

// =============================================================================
// y. Prelude macros: ->> (thread-last)
// =============================================================================

// spec: spec/09-macros.md §9.5 — thread-last single form
#[test]
fn macro_thread_last_single() {
    // (->> 5 (+ 3)) should expand to (+ 3 5) = 8
    let (val, ty) = eval("(->> 5 (+ 3))");
    assert_eq!(val, 8);
    assert_eq!(ty, Type::Int);
}

// spec: spec/09-macros.md §9.5 — thread-last bare symbol
#[test]
fn macro_thread_last_bare() {
    // (->> 5 show) should expand to (show 5) => "5"
    let (val, ty) = eval("(->> 5 show)");
    assert_eq!(ty, Type::String);
    let s = unsafe { cranelisp_runtime::read_string_as_str(val) };
    assert_eq!(s, "5");
}

// spec: spec/09-macros.md §9.5 — thread-last multi-form
#[test]
fn macro_thread_last_multi() {
    // (->> 1 (+ 2) (* 3)) should expand to (* 3 (+ 2 1)) = 9
    let (val, ty) = eval("(->> 1 (+ 2) (* 3))");
    assert_eq!(val, 9);
    assert_eq!(ty, Type::Int);
}
