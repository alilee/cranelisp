// Integration tests for the standard library prelude.
//
// This is the ONE allowed exception to the stdlib separation rule:
// these tests load the real stdlib prelude and validate that it works.
// All other tests in tests/ are free-standing (no stdlib dependency).
//
// Tests use a shared session (LazyLock<SendableSession>) to avoid
// expensive re-initialization of the prelude for each test.

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

// spec: spec/09-macros.md §9.5 — do macro sequences expressions
#[test]
fn macro_do_returns_last() {
    let (val, ty) = eval("(do 1 2 3)");
    assert_eq!(val, 3);
    assert_eq!(ty, Type::Int);
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
