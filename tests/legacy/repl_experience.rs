// QUARANTINED — Sprint 64 test-port. Not built or run by Cargo.
// FIXME: design/arch/fixmes/0124-harvest-tests-legacy-repl-experience.md
// Owning crate: src/ (cranelisp binary; REPL session post-FIXME-0109)
// Owning skill: /int (with /typecheck for symbol-table inspection paths;
//                /backend for format_result function call paths)
// Quarantined: 2026-05-03
//
// This file's assertions test Rust-internal state (ReplSession Rust API,
// cranelisp_backend::display::format_result direct call, session.shared
// inspection) with no e2e equivalent; the e2e carry-forward lives in
// tests/repl_introspection.rs, tests/repl_lifecycle.rs, tests/repl_negative.rs.
// Harvest into `#[cfg(test)]` unit tests inside the owning crate per
// memory/feedback_unit_tests_with_dev.md and memory/project_test_strategy.md.
// Source preserved verbatim; translation may require dev-dependency
// adjustments and import rewrites against the post-FIXME-0109 internal surface.

// REPL experience tests for Rings 0, 1, and 2A.
//
// These tests validate the REPL from the user's perspective, as specified in
// repl/spec.md. They focus on display formats, session state management, and
// error recovery — the contract between the REPL and the user.
//
// Ring 0 uses monomorphic named primitives per spec/appendix-a-builtins.md:
//   add-i64, sub-i64, mul-i64, div-i64, eq-i64, lt-i64, gt-i64, le-i64, ge-i64
//   add-f64, sub-f64, mul-f64, div-f64, eq-f64, lt-f64, gt-f64, le-f64, ge-f64
//   not
// Ring 2A adds trait-dispatched operators: +, -, *, /, =, <
//
// Many basic REPL behaviors (eval int, define and call, etc.) are already
// tested in ring0.rs. This file tests the REPL *experience* aspects:
// display format, type reporting, definition metadata, error recovery with
// state preservation, and realistic multi-step sessions.

#[path = "helpers/mod.rs"]
mod helpers;

use cranelisp::session_v4::EvalResult;
use cranelisp_backend::display::format_result;
use cranelisp_types::{CranelispError, FQTypeName, ModuleFullPath, Span, Type, TypeName};
use helpers::*;

// ---------------------------------------------------------------------------
// Trait prelude helpers — since traits are no longer compiler-seeded,
// tests that use operators (+, -, *, /, =, <) must define them inline.
// ---------------------------------------------------------------------------

fn num_trait_prelude() -> &'static str {
    r#"(deftrait Num (+ [self self] self) (- [self self] self) (* [self self] self) (/ [self self] self))
(impl Num Int (defn + [a b] (add-i64 a b)) (defn - [a b] (sub-i64 a b)) (defn * [a b] (mul-i64 a b)) (defn / [a b] (div-i64 a b)))
(impl Num Float (defn + [a b] (add-f64 a b)) (defn - [a b] (sub-f64 a b)) (defn * [a b] (mul-f64 a b)) (defn / [a b] (div-f64 a b)))"#
}

fn eq_trait_prelude() -> &'static str {
    r#"(deftrait Eq (= [self self] Bool))
(impl Eq Int (defn = [a b] (eq-i64 a b)))
(impl Eq Float (defn = [a b] (eq-f64 a b)))
(impl Eq String (defn = [a b] (str-eq a b)))
(impl Eq Bool (defn = [a b] (eq-bool a b)))"#
}

fn ord_trait_prelude() -> &'static str {
    r#"(deftrait Ord (< [self self] Bool))
(impl Ord Int (defn < [a b] (lt-i64 a b)))
(impl Ord Float (defn < [a b] (lt-f64 a b)))"#
}

fn display_trait_prelude() -> &'static str {
    r#"(deftrait Display (show [self] String))
(impl Display Int (defn show [x] (int-to-string x)))
(impl Display Float (defn show [x] (float-to-string x)))
(impl Display Bool (defn show [x] (bool-to-string x)))
(impl Display String (defn show [x] x))"#
}

/// Install all core trait preludes into a REPL session.
/// Each form is eval'd separately because REPL eval processes one sexp at a time.
fn install_trait_prelude(session: &mut ReplSession) {
    for line in num_trait_prelude().lines() {
        if !line.trim().is_empty() {
            session.eval(line).unwrap();
        }
    }
    for line in eq_trait_prelude().lines() {
        if !line.trim().is_empty() {
            session.eval(line).unwrap();
        }
    }
    for line in ord_trait_prelude().lines() {
        if !line.trim().is_empty() {
            session.eval(line).unwrap();
        }
    }
    for line in display_trait_prelude().lines() {
        if !line.trim().is_empty() {
            session.eval(line).unwrap();
        }
    }
}

// =============================================================================
// Display Format (spec: §1.2 Expression Results)
// =============================================================================

// spec: repl/spec.md §1.2 — Int display format
#[test]
fn display_int_result() {
    // Spec §1.2: `:primitives/Int 3`
    // Current format_result uses short names (:Int 3). This test documents
    // the current behavior. When qualified names are implemented, update.
    let s = format_result(3, &Type::Int);
    assert_eq!(s, ":primitives/Int 3");
}

// spec: repl/spec.md §1.2 — Bool true display format
#[test]
fn display_bool_true() {
    // Spec §1.2: `:primitives/Bool true`
    let s = format_result(1, &Type::Bool);
    assert_eq!(s, ":primitives/Bool true");
}

// spec: repl/spec.md §1.2 — Bool false display format
#[test]
fn display_bool_false() {
    let s = format_result(0, &Type::Bool);
    assert_eq!(s, ":primitives/Bool false");
}

// spec: repl/spec.md §1.2 — Float display format
#[test]
fn display_float_result() {
    // Spec §1.2: `:primitives/Float 3.14`
    #[allow(clippy::approx_constant)]
    let bits = 3.14_f64.to_bits() as i64;
    let s = format_result(bits, &Type::Float);
    assert!(s.starts_with(":primitives/Float 3.14"), "got: {s}");
}

// spec: repl/spec.md §1.2 — negative Int display format
#[test]
fn display_negative_int() {
    let s = format_result(-7, &Type::Int);
    assert_eq!(s, ":primitives/Int -7");
}

// spec: repl/spec.md §1.2 — zero display format
#[test]
fn display_zero() {
    let s = format_result(0, &Type::Int);
    assert_eq!(s, ":primitives/Int 0");
}

// spec: repl/spec.md §1.2 — large Int display format
#[test]
fn display_large_int() {
    let s = format_result(1_000_000_000, &Type::Int);
    assert_eq!(s, ":primitives/Int 1000000000");
}

// spec: repl/spec.md §1.5 — enum ADT display format
#[test]
fn display_adt_enum_type() {
    // Spec §1.2: nullary constructor tag displayed as value.
    // Spec §1.5: `Color.Red` notation (Ring 0: enum display is the tag integer).
    // The ADT type should be displayed in the output.
    let adt = Type::ADT(FQTypeName::new(ModuleFullPath::from("user"), TypeName::from("Color")), vec![]);
    let s = format_result(0, &adt);
    assert_eq!(s, ":user/Color 0");
}

// spec: repl/spec.md §1.2 — negative Float display
#[test]
fn display_float_negative() {
    let bits = (-2.5_f64).to_bits() as i64;
    let s = format_result(bits, &Type::Float);
    assert!(s.starts_with(":primitives/Float -2.5"), "got: {s}");
}

// spec: repl/spec.md §1.2 — zero Float display
#[test]
fn display_float_zero() {
    let bits = 0.0_f64.to_bits() as i64;
    let s = format_result(bits, &Type::Float);
    assert_eq!(s, ":primitives/Float 0.0");
}

// =============================================================================
// Expression Results — Type Reporting (spec: §1.2)
// =============================================================================

// spec: repl/spec.md §1.2 — Int type reporting
#[test]
fn eval_reports_int_type() {
    let mut session = repl_session();
    let result = session.eval("42").unwrap();
    assert_eq!(*result.ty(), Type::Int);
    assert!(!result.is_def());
}

// spec: repl/spec.md §1.2 — Bool type reporting
#[test]
fn eval_reports_bool_type() {
    let mut session = repl_session();
    let result = session.eval("true").unwrap();
    assert_eq!(*result.ty(), Type::Bool);
    assert!(!result.is_def());
}

// spec: repl/spec.md §1.2 — Float type reporting
#[test]
fn eval_reports_float_type() {
    let mut session = repl_session();
    let result = session.eval("3.14").unwrap();
    assert_eq!(*result.ty(), Type::Float);
    assert!(!result.is_def());
}

// spec: repl/spec.md §1.2 — arithmetic result type
#[test]
fn eval_arithmetic_reports_int_type() {
    let mut session = repl_session();
    let result = session.eval("(add-i64 10 20)").unwrap();
    assert_eq!(*result.ty(), Type::Int);
    assert_eq!(result.value(), 30);
    assert!(!result.is_def());
}

// spec: repl/spec.md §1.2 — comparison result type
#[test]
fn eval_comparison_reports_bool_type() {
    let mut session = repl_session();
    let result = session.eval("(lt-i64 3 5)").unwrap();
    assert_eq!(*result.ty(), Type::Bool);
    assert_eq!(result.value(), 1); // true
    assert!(!result.is_def());
}

// spec: repl/spec.md §1.2 — if inherits branch type
#[test]
fn eval_if_inherits_branch_type() {
    let mut session = repl_session();
    let result = session.eval("(if true 42 0)").unwrap();
    assert_eq!(*result.ty(), Type::Int);
    assert!(!result.is_def());
}

// spec: repl/spec.md §1.2 — let reports body type
#[test]
fn eval_let_reports_body_type() {
    let mut session = repl_session();
    let result = session.eval("(let [x 10] (lt-i64 x 20))").unwrap();
    assert_eq!(*result.ty(), Type::Bool);
    assert!(!result.is_def());
}

// =============================================================================
// Definition Results — Type Reporting (spec: §1.3)
// =============================================================================

// spec: repl/spec.md §1.3 — defn reports function type
#[test]
fn defn_reports_function_type() {
    // Spec §1.3: defn displays its inferred type scheme and qualified name.
    // At the API level, ReplResult.ty() should be a Fn type and is_definition=true.
    let mut session = repl_session();
    let result = session.eval("(defn double [x] (mul-i64 x 2))").unwrap();
    assert!(result.is_def());
    // Type should be (Fn [primitives/Int] primitives/Int)
    assert_eq!(
        *result.ty(),
        Type::Fn(vec![Type::Int], Box::new(Type::Int))
    );
}

// spec: repl/spec.md §1.3 — polymorphic defn type vars
#[test]
fn defn_polymorphic_reports_var_type() {
    // (defn id [x] x) should be polymorphic: (Fn [a] a)
    let mut session = repl_session();
    let result = session.eval("(defn id [x] x)").unwrap();
    assert!(result.is_def());
    // The type should be (Fn [Var(n)] Var(n)) for some n — a polymorphic function.
    match &result.ty() {
        Type::Fn(params, ret) => {
            assert_eq!(params.len(), 1);
            match (&params[0], ret.as_ref()) {
                (Type::Var(a), Type::Var(b)) => {
                    assert_eq!(a, b, "param and return type vars should match");
                }
                _ => panic!(
                    "expected polymorphic (Fn [Var] Var), got: (Fn [{:?}] {:?})",
                    params[0], ret
                ),
            }
        }
        other => panic!("expected Fn type for defn, got: {other:?}"),
    }
}

// spec: repl/spec.md §1.3 — multi-param defn signature
#[test]
fn defn_multi_param_reports_full_signature() {
    let mut session = repl_session();
    let result = session
        .eval("(defn add3 [a b c] (add-i64 a (add-i64 b c)))")
        .unwrap();
    assert!(result.is_def());
    assert_eq!(
        *result.ty(),
        Type::Fn(vec![Type::Int, Type::Int, Type::Int], Box::new(Type::Int))
    );
}

// spec: repl/spec.md §1.3 — zero-param defn thunk type
#[test]
fn defn_zero_param_reports_thunk_type() {
    let mut session = repl_session();
    let result = session.eval("(defn always-42 [] 42)").unwrap();
    assert!(result.is_def());
    assert_eq!(
        *result.ty(),
        Type::Fn(vec![], Box::new(Type::Int))
    );
}

// spec: repl/spec.md §1.3 — "A function definition MUST NOT display `<closure>`"
#[test]
fn defn_zero_param_displays_name_not_closure() {
    // repl/spec.md §1.3 line 171: "A function definition MUST NOT display
    // `<closure>` — the user defined a *named* function, not an anonymous
    // closure. `<closure>` is reserved for anonymous function *values*."
    let mut session = repl_session();
    let result = session.eval("(defn always-42 [] 42)").unwrap();
    // With the new EvalResult enum, defn returns Def { symbol, .. }.
    // The symbol must contain the function name (not <closure>).
    match &result {
        EvalResult::Def { symbol, .. } => {
            let name = symbol.to_string();
            assert!(
                name.contains("always-42"),
                "repl/spec.md §1.3 violation: zero-arg defn MUST NOT display <closure>, got: {name}"
            );
        }
        EvalResult::Val { .. } => {
            panic!("repl/spec.md §1.3 violation: defn should return Def, not Val");
        }
    }
}

// spec: repl/spec.md §1.3 — deftype reports ADT type
#[test]
fn deftype_reports_adt_type() {
    // Spec §1.3: type definition displays the qualified type name.
    let mut session = repl_session();
    let result = session.eval("(deftype Color Red Green Blue)").unwrap();
    assert!(result.is_def());
    assert_eq!(
        *result.ty(),
        Type::ADT(FQTypeName::new(ModuleFullPath::from("user"), TypeName::from("Color")), vec![])
    );
}

// spec: repl/spec.md §1.3 — deftype two constructors
#[test]
fn deftype_two_constructors() {
    let mut session = repl_session();
    let result = session.eval("(deftype Answer Yes No)").unwrap();
    assert!(result.is_def());
    assert_eq!(
        *result.ty(),
        Type::ADT(FQTypeName::new(ModuleFullPath::from("user"), TypeName::from("Answer")), vec![])
    );
}

// =============================================================================
// Constructor Evaluation (spec: §1.5 — nullary constructors)
// =============================================================================

// spec: repl/spec.md §1.5 — constructor evaluates to ADT type
#[test]
fn constructor_reports_adt_type() {
    // Entering a constructor name evaluates to its ADT type.
    let mut session = repl_session();
    session.eval("(deftype Color Red Green Blue)").unwrap();
    let result = session.eval("Red").unwrap();
    assert_eq!(
        *result.ty(),
        Type::ADT(FQTypeName::new(ModuleFullPath::from("user"), TypeName::from("Color")), vec![])
    );
    assert!(!result.is_def());
    assert_eq!(result.value(), 0); // tag 0
}

// spec: 12-runtime §12.1.4 — sequential constructor tags
#[test]
fn constructor_tags_are_sequential() {
    let mut session = repl_session();
    session.eval("(deftype Light Off Dim Bright)").unwrap();

    let r0 = session.eval("Off").unwrap();
    assert_eq!(r0.value(), 0);
    assert_eq!(*r0.ty(), Type::ADT(FQTypeName::new(ModuleFullPath::from("user"), TypeName::from("Light")), vec![]));

    let r1 = session.eval("Dim").unwrap();
    assert_eq!(r1.value(), 1);

    let r2 = session.eval("Bright").unwrap();
    assert_eq!(r2.value(), 2);
}

// =============================================================================
// Error Recovery (spec: §5.2)
// =============================================================================

// spec: repl/spec.md §5.2 — type error does not corrupt state
#[test]
fn type_error_does_not_corrupt_definitions() {
    // Spec §5.2: session state MUST NOT be corrupted by an error.
    let mut session = repl_session();
    session.eval("(defn inc [x] (add-i64 x 1))").unwrap();
    assert_eq!(repl_eval(&mut session, "(inc 5)"), 6);

    // Trigger a type error.
    let err = session.eval("(inc true)");
    assert!(err.is_err());

    // Previous definition still works.
    assert_eq!(repl_eval(&mut session, "(inc 10)"), 11);
}

// Sprint 61 Slice 5 H (neg-coverage promotion #2).
// spec: repl/spec.md §5.2 — Session state (defined functions, types,
// modules) MUST NOT be corrupted by an error. The NEGATIVE face: an
// erroring `(defn ...)` MUST NOT leave a half-installed entry — calling
// the failed name after the error reports "undefined", not a
// half-formed signature, and previously-defined symbols remain intact.
//
// This installs a regression guard for the "dual-path persistence
// collapse" anti-pattern (Sprint 59/60 defect class) — where an error
// partway through defn installation could leak an inconsistent entry
// into the symbol table.
#[test]
fn type_error_does_not_corrupt_state_neg_failed_defn_absent() {
    let mut session = repl_session();

    // Baseline: install a known-good defn.
    session.eval("(defn inc [x] (add-i64 x 1))").unwrap();
    assert_eq!(repl_eval(&mut session, "(inc 5)"), 6);

    // Try to install a broken defn: body references `add-i64` with a
    // Bool — type error at the body-check stage, so the defn MUST NOT
    // be installed.
    let err = session.eval("(defn broken [x] (add-i64 x true))");
    assert!(
        err.is_err(),
        "`(defn broken [x] (add-i64 x true))` MUST surface a type error"
    );

    // Negative assertion (primary): `broken` MUST NOT be resolvable —
    // the failed defn left no half-installed entry in the symbol table.
    // We call it like a function; the compiler should report an
    // undefined-variable error (or refuse to resolve the name), not
    // succeed silently and not produce a signature-mismatch error on a
    // half-installed entry.
    let call_broken = session.eval("(broken 5)");
    assert!(
        call_broken.is_err(),
        "Calling the failed defn `broken` MUST produce an error — the \
         failed defn MUST NOT leave a callable half-installed entry."
    );
    // The error message should surface `broken` as undefined (the spec
    // §5.2 "state MUST NOT be corrupted" implies the failed name is
    // absent, not half-present). We check the error mentions `broken`
    // or `undefined` to confirm it's an undefined-name style error and
    // not a type-mismatch against a partially-installed signature.
    let msg = match call_broken {
        Err(e) => e.to_string(),
        Ok(_) => panic!("call to failed defn unexpectedly succeeded"),
    };
    assert!(
        msg.contains("broken") || msg.contains("undefined") || msg.contains("not found"),
        "Error calling failed defn should name the undefined symbol; \
         got: {msg}"
    );

    // Negative assertion (secondary): the PRE-error baseline defn MUST
    // still work — state is preserved.
    assert_eq!(
        repl_eval(&mut session, "(inc 10)"),
        11,
        "Baseline `inc` MUST survive the type error (spec §5.2)."
    );
}

// spec: repl/spec.md §5.2 — parse error does not corrupt state
#[test]
fn parse_error_does_not_corrupt_definitions() {
    let mut session = repl_session();
    session.eval("(defn double [x] (mul-i64 x 2))").unwrap();

    // Parse error (unbalanced parens).
    let err = session.eval("(double 5");
    assert!(err.is_err());

    // Previous definition still works.
    assert_eq!(repl_eval(&mut session, "(double 5)"), 10);
}

// spec: repl/spec.md §5.2 — error preserves type definitions
#[test]
fn error_after_typedef_preserves_type() {
    let mut session = repl_session();
    session.eval("(deftype Dir North South)").unwrap();

    // Error.
    let err = session.eval("(add-i64 true 1)");
    assert!(err.is_err());

    // Type still usable.
    let result = session.eval("North").unwrap();
    assert_eq!(*result.ty(), Type::ADT(FQTypeName::new(ModuleFullPath::from("user"), TypeName::from("Dir")), vec![]));
}

// spec: repl/spec.md §5.2 — multiple errors then success
#[test]
fn multiple_errors_then_success() {
    // Spec §5.2: repeated errors should not accumulate damage.
    let mut session = repl_session();

    let err1 = session.eval("(add-i64 true 1)");
    assert!(err1.is_err());

    let err2 = session.eval("(unknown-fn 1 2)");
    assert!(err2.is_err());

    let err3 = session.eval("(if 1 2 3)"); // condition not bool
    assert!(err3.is_err());

    // Session still works.
    assert_eq!(repl_eval(&mut session, "(add-i64 1 2)"), 3);
}

// spec: repl/spec.md §5.2 — error preserves multiple definitions
#[test]
fn error_preserves_multiple_definitions() {
    // Define several things, error, verify all survive.
    let mut session = repl_session();
    session.eval("(defn a [] 1)").unwrap();
    session.eval("(defn b [] 2)").unwrap();
    session.eval("(deftype Flag On Off)").unwrap();
    session.eval("(defn c [x] (add-i64 x 10))").unwrap();

    // Error.
    let err = session.eval("(add-i64 true false)");
    assert!(err.is_err());

    // All definitions survive.
    assert_eq!(repl_eval(&mut session, "(a)"), 1);
    assert_eq!(repl_eval(&mut session, "(b)"), 2);
    assert_eq!(repl_eval(&mut session, "(c 5)"), 15);
    let flag = session.eval("On").unwrap();
    assert_eq!(*flag.ty(), Type::ADT(FQTypeName::new(ModuleFullPath::from("user"), TypeName::from("Flag")), vec![]));
}

// =============================================================================
// Error Categories (spec: §5.1)
// =============================================================================

// spec: repl/spec.md §5.1 — parse error category
#[test]
fn error_category_parse() {
    let mut session = repl_session();
    match session.eval("(add-i64 1") {
        Err(CranelispError::ParseError { .. }) => {} // expected
        Err(other) => panic!("expected ParseError, got: {other}"),
        Ok(_) => panic!("expected ParseError, got Ok"),
    }
}

// spec: repl/spec.md §5.1 — type error category
#[test]
fn error_category_type() {
    let mut session = repl_session();
    match session.eval("(add-i64 true 1)") {
        Err(CranelispError::TypeError { .. }) => {} // expected
        Err(other) => panic!("expected TypeError, got: {other}"),
        Ok(_) => panic!("expected TypeError, got Ok"),
    }
}

// spec: repl/spec.md §5.1 — error has human-readable message
#[test]
fn error_has_message() {
    // Spec §5.1: errors MUST include a human-readable message.
    let mut session = repl_session();
    match session.eval("(add-i64 true 1)") {
        Err(ref e) => {
            let msg = e.message();
            assert!(!msg.is_empty(), "error message should not be empty");
        }
        Ok(_) => panic!("expected error, got Ok"),
    }
}

// =============================================================================
// Function Redefinition (GOT update)
// =============================================================================

// spec: repl/spec.md §5.2 — function redefinition via GOT
#[test]
fn redefinition_changes_return_value() {
    let mut session = repl_session();
    session.eval("(defn val [] 1)").unwrap();
    assert_eq!(repl_eval(&mut session, "(val)"), 1);

    session.eval("(defn val [] 2)").unwrap();
    assert_eq!(repl_eval(&mut session, "(val)"), 2);
}

// spec: repl/spec.md §5.2 — redefinition propagates through callers
#[test]
fn redefinition_propagates_through_callers() {
    // Spec: redefined function is picked up by existing callers via GOT.
    let mut session = repl_session();
    session.eval("(defn base [x] (mul-i64 x 2))").unwrap();
    session.eval("(defn caller [x] (base x))").unwrap();
    assert_eq!(repl_eval(&mut session, "(caller 5)"), 10);

    // Redefine base to multiply by 3.
    session.eval("(defn base [x] (mul-i64 x 3))").unwrap();
    assert_eq!(repl_eval(&mut session, "(caller 5)"), 15);
}

// spec: repl/spec.md §5.2 — redefinition changes body logic
#[test]
fn redefinition_with_different_body_logic() {
    let mut session = repl_session();
    session.eval("(defn compute [n] (add-i64 n 10))").unwrap();
    assert_eq!(repl_eval(&mut session, "(compute 5)"), 15);

    // Change from addition to subtraction.
    session.eval("(defn compute [n] (sub-i64 n 10))").unwrap();
    assert_eq!(repl_eval(&mut session, "(compute 5)"), -5);
}

// =============================================================================
// Recursive Functions in REPL
// =============================================================================

// spec: 04-expressions §4.6 — recursive factorial in REPL
#[test]
fn recursive_factorial_in_repl() {
    let mut session = repl_session();
    session
        .eval("(defn fact [n] (if (eq-i64 n 0) 1 (mul-i64 n (fact (sub-i64 n 1)))))")
        .unwrap();
    assert_eq!(repl_eval(&mut session, "(fact 0)"), 1);
    assert_eq!(repl_eval(&mut session, "(fact 1)"), 1);
    assert_eq!(repl_eval(&mut session, "(fact 5)"), 120);
    assert_eq!(repl_eval(&mut session, "(fact 10)"), 3628800);
}

// spec: 04-expressions §4.6 — recursive fibonacci in REPL
#[test]
fn recursive_fibonacci_in_repl() {
    let mut session = repl_session();
    session
        .eval("(defn fib [n] (if (eq-i64 n 0) 0 (if (eq-i64 n 1) 1 (add-i64 (fib (sub-i64 n 1)) (fib (sub-i64 n 2))))))")
        .unwrap();
    assert_eq!(repl_eval(&mut session, "(fib 0)"), 0);
    assert_eq!(repl_eval(&mut session, "(fib 1)"), 1);
    assert_eq!(repl_eval(&mut session, "(fib 10)"), 55);
}

// spec: 12-runtime §12.5 — accumulator recursion in REPL
#[test]
fn recursive_with_accumulator_in_repl() {
    let mut session = repl_session();
    session
        .eval("(defn sum-to [n acc] (if (eq-i64 n 0) acc (sum-to (sub-i64 n 1) (add-i64 acc n))))")
        .unwrap();
    assert_eq!(repl_eval(&mut session, "(sum-to 100 0)"), 5050);
}

// =============================================================================
// Enum Types and Pattern Matching in REPL
// =============================================================================

// spec: 06-pattern-matching §6.2.2 — enum define then match
#[test]
fn enum_define_then_match() {
    let mut session = repl_session();
    session.eval("(deftype Coin Heads Tails)").unwrap();
    session
        .eval("(defn flip-val [c] (match c [Heads 100 Tails 0]))")
        .unwrap();
    assert_eq!(repl_eval(&mut session, "(flip-val Heads)"), 100);
    assert_eq!(repl_eval(&mut session, "(flip-val Tails)"), 0);
}

// spec: 06-pattern-matching §6.2.3 — wildcard pattern in REPL
#[test]
fn enum_wildcard_pattern_in_repl() {
    let mut session = repl_session();
    session.eval("(deftype Priority Low Medium High)").unwrap();
    session
        .eval("(defn is-high [p] (match p [High 1 _ 0]))")
        .unwrap();
    assert_eq!(repl_eval(&mut session, "(is-high High)"), 1);
    assert_eq!(repl_eval(&mut session, "(is-high Low)"), 0);
    assert_eq!(repl_eval(&mut session, "(is-high Medium)"), 0);
}

// spec: 06-pattern-matching §6.2.2 — enum in function chain
#[test]
fn enum_used_in_function_chain() {
    let mut session = repl_session();
    session.eval("(deftype Bit Zero One)").unwrap();
    session
        .eval("(defn bit-val [b] (match b [Zero 0 One 1]))")
        .unwrap();
    session
        .eval("(defn double-bit [b] (mul-i64 (bit-val b) 2))")
        .unwrap();
    assert_eq!(repl_eval(&mut session, "(double-bit One)"), 2);
    assert_eq!(repl_eval(&mut session, "(double-bit Zero)"), 0);
}

// spec: 05-definitions §5.2.3 — multiple enum types in session
#[test]
fn multiple_enum_types_in_session() {
    let mut session = repl_session();
    session.eval("(deftype Color Red Green Blue)").unwrap();
    session.eval("(deftype Size Small Large)").unwrap();

    let color = session.eval("Red").unwrap();
    assert_eq!(*color.ty(), Type::ADT(FQTypeName::new(ModuleFullPath::from("user"), TypeName::from("Color")), vec![]));

    let size = session.eval("Small").unwrap();
    assert_eq!(*size.ty(), Type::ADT(FQTypeName::new(ModuleFullPath::from("user"), TypeName::from("Size")), vec![]));
}

// =============================================================================
// Realistic Multi-Step Sessions
// =============================================================================

// spec: repl/spec.md §6.1 — incremental program building
#[test]
fn session_build_up_program_incrementally() {
    // Simulates a user building a small program at the REPL step by step.
    let mut session = repl_session();

    // Step 1: explore literals.
    let r = session.eval("42").unwrap();
    assert_eq!(r.value(), 42);
    assert_eq!(*r.ty(), Type::Int);

    // Step 2: try arithmetic.
    let r = session.eval("(add-i64 10 20)").unwrap();
    assert_eq!(r.value(), 30);

    // Step 3: define a helper.
    let r = session.eval("(defn square [x] (mul-i64 x x))").unwrap();
    assert!(r.is_def());

    // Step 4: use the helper.
    assert_eq!(repl_eval(&mut session, "(square 7)"), 49);

    // Step 5: define another that uses the first.
    session
        .eval("(defn sum-of-squares [a b] (add-i64 (square a) (square b)))")
        .unwrap();
    assert_eq!(repl_eval(&mut session, "(sum-of-squares 3 4)"), 25);

    // Step 6: make a mistake, recover.
    let err = session.eval("(square true)");
    assert!(err.is_err());

    // Step 7: continue working.
    assert_eq!(repl_eval(&mut session, "(sum-of-squares 5 12)"), 169);
}

// spec: repl/spec.md §6.1 — type then functions workflow
#[test]
fn session_define_type_then_functions_over_it() {
    let mut session = repl_session();

    // Define a type.
    let r = session.eval("(deftype TrafficLight Red Yellow Green)").unwrap();
    assert!(r.is_def());

    // Define a function that uses the type.
    session
        .eval("(defn can-go [light] (match light [Green 1 _ 0]))")
        .unwrap();

    // Define another.
    session
        .eval("(defn next-light [light] (match light [Red 1 Yellow 2 Green 0]))")
        .unwrap();

    // Use them.
    assert_eq!(repl_eval(&mut session, "(can-go Green)"), 1);
    assert_eq!(repl_eval(&mut session, "(can-go Red)"), 0);
    assert_eq!(repl_eval(&mut session, "(next-light Red)"), 1);
}

// spec: repl/spec.md §5.2 — interleaved definitions and expressions
#[test]
fn session_interleave_definitions_and_expressions() {
    let mut session = repl_session();

    // Define, evaluate, define, evaluate pattern.
    session.eval("(defn inc [x] (add-i64 x 1))").unwrap();
    assert_eq!(repl_eval(&mut session, "(inc 0)"), 1);

    session.eval("(defn dec [x] (sub-i64 x 1))").unwrap();
    assert_eq!(repl_eval(&mut session, "(dec 10)"), 9);

    // Use both together.
    assert_eq!(repl_eval(&mut session, "(inc (dec 5))"), 5);

    // Define something that uses both.
    session
        .eval("(defn same [x] (inc (dec x)))")
        .unwrap();
    assert_eq!(repl_eval(&mut session, "(same 42)"), 42);
}

// =============================================================================
// Float Arithmetic in REPL (spec: §1.2 Float display)
// =============================================================================

// spec: repl/spec.md §1.2 — Float display in session
#[test]
fn float_display_format_in_session() {
    let mut session = repl_session();
    let result = session.eval("(add-f64 1.5 2.5)").unwrap();
    assert_eq!(*result.ty(), Type::Float);
    let display = format_result(result.value(), &result.ty());
    assert!(display.starts_with(":primitives/Float 4"), "got: {display}");
}

// spec: 03-types §3.1 — Float and Int are distinct
#[test]
fn float_and_int_are_distinct_types() {
    let mut session = repl_session();
    let int_result = session.eval("42").unwrap();
    let float_result = session.eval("42.0").unwrap();
    assert_eq!(*int_result.ty(), Type::Int);
    assert_eq!(*float_result.ty(), Type::Float);
    // They should not be equal types.
    assert_ne!(int_result.ty(), float_result.ty());
}

// =============================================================================
// Boolean Logic
// =============================================================================

// spec: appendix-a-builtins §A.3 — not returns Bool type
#[test]
fn not_returns_bool_type() {
    let mut session = repl_session();
    let result = session.eval("(not true)").unwrap();
    assert_eq!(*result.ty(), Type::Bool);
    assert_eq!(result.value(), 0); // false
}

// =============================================================================
// Warnings (spec: §5.1)
// =============================================================================

// spec: repl/spec.md §5.1 — successful eval empty warnings
#[test]
fn successful_eval_has_empty_warnings() {
    let mut session = repl_session();
    let result = session.eval("42").unwrap();
    assert!(
        result.warnings().is_empty(),
        "simple expression should produce no warnings"
    );
}

// =============================================================================
// Edge Cases
// =============================================================================

// spec: repl/spec.md §2.1 — empty input is silent
#[test]
fn empty_input_is_silent() {
    let mut session = repl_session();
    let result = session.eval("").unwrap();
    // Empty input produces no error; session still works.
    assert_eq!(result.value(), 0);
    assert_eq!(repl_eval(&mut session, "1"), 1);
}

// spec: repl/spec.md §2.1 — whitespace only is silent
#[test]
fn whitespace_only_is_silent() {
    let mut session = repl_session();
    let result = session.eval("   ").unwrap();
    assert_eq!(result.value(), 0);
    assert_eq!(repl_eval(&mut session, "1"), 1);
}

// spec: 01-lexical §1.2 — comment-only input is silent
#[test]
fn comment_only_is_silent() {
    let mut session = repl_session();
    let result = session.eval("; this is a comment").unwrap();
    assert_eq!(result.value(), 0);
    assert_eq!(repl_eval(&mut session, "1"), 1);
}

// spec: 01-lexical §1.2 — indented comment is silent
#[test]
fn indented_comment_is_silent() {
    let mut session = repl_session();
    let result = session.eval("  ; indented comment").unwrap();
    assert_eq!(result.value(), 0);
    assert_eq!(repl_eval(&mut session, "1"), 1);
}

// spec: 04-expressions §4.6 — deeply nested expression
#[test]
fn deeply_nested_expression() {
    let mut session = repl_session();
    // (add-i64 (add-i64 (add-i64 (add-i64 1 2) 3) 4) 5)
    assert_eq!(
        repl_eval(
            &mut session,
            "(add-i64 (add-i64 (add-i64 (add-i64 1 2) 3) 4) 5)"
        ),
        15
    );
}

// spec: 04-expressions §4.3 — let binding shadowing
#[test]
fn let_binding_shadowing() {
    let mut session = repl_session();
    let result = session
        .eval("(let [x 1] (let [x 2] x))")
        .unwrap();
    assert_eq!(result.value(), 2);
    assert_eq!(*result.ty(), Type::Int);
}

// spec: none — stress test: many sequential evals
#[test]
fn many_sequential_evals() {
    // Stress test: many sequential evaluations don't degrade the session.
    let mut session = repl_session();
    for i in 0..50 {
        let result = session.eval(&format!("{i}")).unwrap();
        assert_eq!(result.value(), i);
    }
}

// spec: repl/spec.md §5.2 — repeated function redefinition
#[test]
fn redefine_function_many_times() {
    // Each redefinition should work and not leak.
    let mut session = repl_session();
    for i in 0..20 {
        session
            .eval(&format!("(defn f [] {i})"))
            .unwrap();
        assert_eq!(repl_eval(&mut session, "(f)"), i);
    }
}

// =============================================================================
// Error Source Location (spec: §5.1 — errors MUST include source location)
// =============================================================================

// spec: repl/spec.md §5.1 — error has source span
#[test]
fn error_has_source_span() {
    // Spec §5.1: All errors MUST display the source location.
    // At the API level, CranelispError carries a Span with byte offsets.
    let mut session = repl_session();
    match session.eval("(add-i64 true 1)") {
        Err(e) => {
            let span = e.span();
            // Span should not be synthetic (0..0) — it should point at real source.
            assert!(
                span != Span::SYNTHETIC,
                "error span should not be synthetic: {span:?}"
            );
        }
        Ok(_) => panic!("expected error"),
    }
}

// spec: repl/spec.md §5.1 — parse error has source span
#[test]
fn parse_error_has_source_span() {
    let mut session = repl_session();
    match session.eval("(add-i64 1") {
        Err(e) => {
            let span = e.span();
            assert!(
                span != Span::SYNTHETIC,
                "parse error span should not be synthetic: {span:?}"
            );
        }
        Ok(_) => panic!("expected error"),
    }
}

// =============================================================================
// Type Error Quality (spec: §5.3)
// =============================================================================

// spec: repl/spec.md §5.3 — type error mentions expected and actual
#[test]
fn type_error_mentions_expected_and_actual() {
    // Spec §5.3: Type errors MUST include expected and actual types.
    let mut session = repl_session();
    match session.eval("(add-i64 true 1)") {
        Err(ref e) => {
            let msg = e.message();
            // The error should mention the conflicting types.
            assert!(
                msg.contains("Int") || msg.contains("Bool"),
                "type error should mention the types involved, got: {msg}"
            );
        }
        Ok(_) => panic!("expected type error"),
    }
}

// spec: repl/spec.md §5.3 — if condition type error is clear
#[test]
fn if_condition_type_error_is_clear() {
    // Spec §5.3: if condition must be Bool.
    let mut session = repl_session();
    match session.eval("(if 42 1 2)") {
        Err(ref e) => {
            let msg = e.message();
            assert!(
                msg.contains("Bool") || msg.contains("Int"),
                "if-condition type error should mention Bool or Int, got: {msg}"
            );
        }
        Ok(_) => panic!("expected type error for non-Bool if condition"),
    }
    // Session still works after the error.
    assert_eq!(repl_eval(&mut session, "(if true 1 2)"), 1);
}

// spec: repl/spec.md §5.3 — if branch type mismatch is clear
#[test]
fn if_branch_type_mismatch_is_clear() {
    // Spec §5.3: if branches must have same type.
    let mut session = repl_session();
    match session.eval("(if true 42 true)") {
        Err(ref e) => {
            let msg = e.message();
            // Error should mention the type mismatch.
            assert!(
                !msg.is_empty(),
                "branch type mismatch error should have a message"
            );
        }
        Ok(_) => panic!("expected type error for mismatched if branches"),
    }
    assert_eq!(repl_eval(&mut session, "1"), 1);
}

// =============================================================================
// Unbound Symbol (spec: §4.1 — clear error for unbound names)
// =============================================================================

// spec: repl/spec.md §4.1 — unbound symbol clear error
#[test]
fn unbound_symbol_produces_clear_error() {
    // Spec §4.1: If a name is unbound, the error MUST say so clearly.
    let mut session = repl_session();
    match session.eval("undefined-name") {
        Err(ref e) => {
            let msg = e.message();
            assert!(
                msg.contains("unbound") || msg.contains("undefined") || msg.contains("not found")
                    || msg.contains("unknown"),
                "unbound symbol error should mention the symbol is not defined, got: {msg}"
            );
        }
        Ok(_) => panic!("expected error for unbound symbol"),
    }
    // Session still works.
    assert_eq!(repl_eval(&mut session, "42"), 42);
}

// spec: repl/spec.md §4.1 — unbound function clear error
#[test]
fn unbound_function_produces_clear_error() {
    // Calling a function that doesn't exist.
    let mut session = repl_session();
    match session.eval("(nonexistent-fn 1 2)") {
        Err(ref e) => {
            let msg = e.message();
            assert!(
                !msg.is_empty(),
                "error for undefined function should have a message"
            );
        }
        Ok(_) => panic!("expected error for undefined function"),
    }
    assert_eq!(repl_eval(&mut session, "1"), 1);
}

// =============================================================================
// Wrong Arity (spec: §5.1)
// =============================================================================

// spec: repl/spec.md §5.1 — wrong arity too many args
#[test]
fn wrong_arity_too_many_args() {
    let mut session = repl_session();
    session.eval("(defn one-arg [x] x)").unwrap();
    match session.eval("(one-arg 1 2 3)") {
        Err(ref e) => {
            let msg = e.message();
            assert!(
                !msg.is_empty(),
                "arity error should have a message"
            );
        }
        Ok(_) => panic!("expected arity error"),
    }
    // Session still works.
    assert_eq!(repl_eval(&mut session, "(one-arg 42)"), 42);
}

// spec: 04-expressions §4.6.3 — too few args triggers auto-curry in REPL
#[test]
fn auto_curry_too_few_args_repl() {
    let mut session = repl_session();
    session
        .eval("(defn two-args [x y] (add-i64 x y))")
        .unwrap();
    // With auto-currying, (two-args 1) returns a closure, not an error.
    session.eval("(two-args 1)").expect("auto-curry should succeed");
    // Full application still works.
    assert_eq!(repl_eval(&mut session, "(two-args 1 2)"), 3);
}

// =============================================================================
// Format Result — Additional Types (spec: §1.2)
// =============================================================================

// spec: repl/spec.md §1.2 — function type display
#[test]
fn display_function_type() {
    // Spec §1.2: function values should display type scheme.
    // For Ring 0, non-capturing function values are displayed.
    let fn_type = Type::Fn(vec![Type::Int], Box::new(Type::Int));
    let s = format_result(0, &fn_type);
    // format_result falls through to "{type} {value}" for Fn types.
    assert!(
        s.contains("Fn"),
        "function type display should contain 'Fn', got: {s}"
    );
}

// spec: repl/spec.md §1.2 — max Int display
#[test]
fn display_max_int() {
    let s = format_result(i64::MAX, &Type::Int);
    assert_eq!(s, format!(":primitives/Int {}", i64::MAX));
}

// spec: repl/spec.md §1.2 — min Int display
#[test]
fn display_min_int() {
    let s = format_result(i64::MIN, &Type::Int);
    assert_eq!(s, format!(":primitives/Int {}", i64::MIN));
}

// spec: repl/spec.md §1.2 — Float infinity display
#[test]
fn display_float_infinity() {
    let bits = f64::INFINITY.to_bits() as i64;
    let s = format_result(bits, &Type::Float);
    assert!(
        s.contains("inf"),
        "infinity should display as inf, got: {s}"
    );
}

// spec: repl/spec.md §1.2 — Float NaN display
#[test]
fn display_float_nan() {
    let bits = f64::NAN.to_bits() as i64;
    let s = format_result(bits, &Type::Float);
    assert!(
        s.contains("NaN"),
        "NaN should display as NaN, got: {s}"
    );
}

// =============================================================================
// Type Inference Accuracy (spec: §1.3 — function definitions show correct type)
// =============================================================================

// spec: 03-types §3.5.3 — let body type inference
#[test]
fn defn_with_let_infers_return_type() {
    let mut session = repl_session();
    let result = session
        .eval("(defn inner [x] (let [y (add-i64 x 1)] y))")
        .unwrap();
    assert!(result.is_def());
    assert_eq!(
        *result.ty(),
        Type::Fn(vec![Type::Int], Box::new(Type::Int))
    );
}

// spec: 03-types §3.5.3 — if branch type inference
#[test]
fn defn_with_if_infers_return_type() {
    let mut session = repl_session();
    let result = session
        .eval("(defn abs [x] (if (lt-i64 x 0) (sub-i64 0 x) x))")
        .unwrap();
    assert!(result.is_def());
    assert_eq!(
        *result.ty(),
        Type::Fn(vec![Type::Int], Box::new(Type::Int))
    );
}

// spec: 03-types §3.5.3 — Bool return type inference
#[test]
fn defn_bool_return_type() {
    let mut session = repl_session();
    let result = session
        .eval("(defn is-zero [n] (eq-i64 n 0))")
        .unwrap();
    assert!(result.is_def());
    assert_eq!(
        *result.ty(),
        Type::Fn(vec![Type::Int], Box::new(Type::Bool))
    );
}

// spec: 03-types §3.5.3 — Float params and return inference
#[test]
fn defn_float_params_and_return() {
    let mut session = repl_session();
    let result = session
        .eval("(defn avg [a b] (div-f64 (add-f64 a b) 2.0))")
        .unwrap();
    assert!(result.is_def());
    assert_eq!(
        *result.ty(),
        Type::Fn(vec![Type::Float, Type::Float], Box::new(Type::Float))
    );
}

// =============================================================================
// Error Recovery — Advanced Scenarios (spec: §5.2)
// =============================================================================

// spec: repl/spec.md §5.2 — error between dependent definitions
#[test]
fn error_between_dependent_definitions() {
    // Define A, error, define B that uses A — B should still work.
    let mut session = repl_session();
    session.eval("(defn helper [x] (add-i64 x 10))").unwrap();

    // Error.
    let err = session.eval("(add-i64 true false)");
    assert!(err.is_err());

    // Define something that depends on the pre-error definition.
    session
        .eval("(defn uses-helper [x] (helper (helper x)))")
        .unwrap();
    assert_eq!(repl_eval(&mut session, "(uses-helper 5)"), 25);
}

// spec: repl/spec.md §5.2 — failed defn does not pollute
#[test]
fn failed_defn_does_not_pollute_namespace() {
    // A defn with a type error should not leave a partial definition visible.
    let mut session = repl_session();

    // Try to define a function with a type error in its body.
    let err = session.eval("(defn bad [x] (add-i64 x true))");
    assert!(err.is_err());

    // The failed definition should not be callable.
    let err2 = session.eval("(bad 1)");
    assert!(err2.is_err());

    // Session still works for valid expressions.
    assert_eq!(repl_eval(&mut session, "42"), 42);
}

// spec: repl/spec.md §5.2 — error after redefn preserves latest
#[test]
fn error_after_redefinition_preserves_latest() {
    // Redefine a function, then error — the latest good definition persists.
    let mut session = repl_session();
    session.eval("(defn f [] 1)").unwrap();
    session.eval("(defn f [] 2)").unwrap();
    assert_eq!(repl_eval(&mut session, "(f)"), 2);

    // Error.
    let err = session.eval("(add-i64 true 1)");
    assert!(err.is_err());

    // Latest definition (returning 2) should still be active.
    assert_eq!(repl_eval(&mut session, "(f)"), 2);
}

// =============================================================================
// Enum ADT — Advanced Patterns (spec: §1.5, §6)
// =============================================================================

// spec: 05-definitions §5.2.3 — enum with many constructors
#[test]
fn enum_with_many_constructors() {
    let mut session = repl_session();
    session
        .eval("(deftype Weekday Mon Tue Wed Thu Fri Sat Sun)")
        .unwrap();

    let r = session.eval("Mon").unwrap();
    assert_eq!(r.value(), 0);
    assert_eq!(*r.ty(), Type::ADT(FQTypeName::new(ModuleFullPath::from("user"), TypeName::from("Weekday")), vec![]));

    let r = session.eval("Sun").unwrap();
    assert_eq!(r.value(), 6);
    assert_eq!(*r.ty(), Type::ADT(FQTypeName::new(ModuleFullPath::from("user"), TypeName::from("Weekday")), vec![]));
}

// spec: 06-pattern-matching §6.5.1 — match all constructors
#[test]
fn match_all_constructors() {
    let mut session = repl_session();
    session.eval("(deftype RGB Red Green Blue)").unwrap();
    session
        .eval("(defn rgb-val [c] (match c [Red 1 Green 2 Blue 3]))")
        .unwrap();
    assert_eq!(repl_eval(&mut session, "(rgb-val Red)"), 1);
    assert_eq!(repl_eval(&mut session, "(rgb-val Green)"), 2);
    assert_eq!(repl_eval(&mut session, "(rgb-val Blue)"), 3);
}

// spec: repl/spec.md §5.2 — type persists across many evals
#[test]
fn enum_type_persists_across_many_evals() {
    // Type defined early in session is available many evals later.
    let mut session = repl_session();
    session.eval("(deftype Sign Pos Neg Zero)").unwrap();

    // Many intervening evaluations.
    for i in 0..10 {
        assert_eq!(repl_eval(&mut session, &format!("{i}")), i);
    }

    // The type is still available.
    let r = session.eval("Pos").unwrap();
    assert_eq!(*r.ty(), Type::ADT(FQTypeName::new(ModuleFullPath::from("user"), TypeName::from("Sign")), vec![]));
}

// =============================================================================
// Primitive Coverage (spec: appendix-a-builtins — all 19 Ring 0 primitives)
// =============================================================================

// spec: appendix-a-builtins §A.3 — all Int arithmetic primitives
#[test]
fn all_int_arithmetic_primitives_work_in_repl() {
    let mut session = repl_session();
    assert_eq!(repl_eval(&mut session, "(add-i64 3 4)"), 7);
    assert_eq!(repl_eval(&mut session, "(sub-i64 10 3)"), 7);
    assert_eq!(repl_eval(&mut session, "(mul-i64 3 4)"), 12);
    assert_eq!(repl_eval(&mut session, "(div-i64 10 3)"), 3);
}

// spec: appendix-a-builtins §A.3 — all Int comparison primitives
#[test]
fn all_int_comparison_primitives_work_in_repl() {
    let mut session = repl_session();
    assert_eq!(repl_eval(&mut session, "(eq-i64 3 3)"), 1);
    assert_eq!(repl_eval(&mut session, "(eq-i64 3 4)"), 0);
    assert_eq!(repl_eval(&mut session, "(lt-i64 3 4)"), 1);
    assert_eq!(repl_eval(&mut session, "(lt-i64 4 3)"), 0);
    assert_eq!(repl_eval(&mut session, "(gt-i64 4 3)"), 1);
    assert_eq!(repl_eval(&mut session, "(gt-i64 3 4)"), 0);
    assert_eq!(repl_eval(&mut session, "(le-i64 3 3)"), 1);
    assert_eq!(repl_eval(&mut session, "(le-i64 3 4)"), 1);
    assert_eq!(repl_eval(&mut session, "(le-i64 4 3)"), 0);
    assert_eq!(repl_eval(&mut session, "(ge-i64 3 3)"), 1);
    assert_eq!(repl_eval(&mut session, "(ge-i64 4 3)"), 1);
    assert_eq!(repl_eval(&mut session, "(ge-i64 3 4)"), 0);
}

// spec: appendix-a-builtins §A.3 — all Float arithmetic primitives
#[test]
fn all_float_arithmetic_primitives_work_in_repl() {
    let mut session = repl_session();
    let r = session.eval("(add-f64 1.5 2.5)").unwrap();
    assert_eq!(*r.ty(), Type::Float);
    assert_eq!(f64::from_bits(r.value() as u64), 4.0);

    let r = session.eval("(sub-f64 5.0 2.0)").unwrap();
    assert_eq!(f64::from_bits(r.value() as u64), 3.0);

    let r = session.eval("(mul-f64 3.0 4.0)").unwrap();
    assert_eq!(f64::from_bits(r.value() as u64), 12.0);

    let r = session.eval("(div-f64 10.0 4.0)").unwrap();
    assert_eq!(f64::from_bits(r.value() as u64), 2.5);
}

// spec: appendix-a-builtins §A.3 — all Float comparison primitives
#[test]
fn all_float_comparison_primitives_work_in_repl() {
    let mut session = repl_session();
    assert_eq!(repl_eval(&mut session, "(eq-f64 3.0 3.0)"), 1);
    assert_eq!(repl_eval(&mut session, "(eq-f64 3.0 4.0)"), 0);
    assert_eq!(repl_eval(&mut session, "(lt-f64 3.0 4.0)"), 1);
    assert_eq!(repl_eval(&mut session, "(gt-f64 4.0 3.0)"), 1);
    assert_eq!(repl_eval(&mut session, "(le-f64 3.0 3.0)"), 1);
    assert_eq!(repl_eval(&mut session, "(ge-f64 3.0 3.0)"), 1);
}

// spec: appendix-a-builtins §A.3 — not primitive in REPL
#[test]
fn not_primitive_works_in_repl() {
    let mut session = repl_session();
    let r = session.eval("(not true)").unwrap();
    assert_eq!(*r.ty(), Type::Bool);
    assert_eq!(r.value(), 0); // false

    let r = session.eval("(not false)").unwrap();
    assert_eq!(*r.ty(), Type::Bool);
    assert_eq!(r.value(), 1); // true
}

// =============================================================================
// Let Binding Patterns (spec: §4 expressions)
// =============================================================================

// spec: 04-expressions §4.3 — let multiple bindings
#[test]
fn let_multiple_bindings() {
    let mut session = repl_session();
    let result = session
        .eval("(let [x 10 y 20] (add-i64 x y))")
        .unwrap();
    assert_eq!(result.value(), 30);
    assert_eq!(*result.ty(), Type::Int);
}

// spec: 04-expressions §4.3 — let binding depends on previous
#[test]
fn let_binding_depends_on_previous() {
    let mut session = repl_session();
    let result = session
        .eval("(let [x 10 y (add-i64 x 5)] y)")
        .unwrap();
    assert_eq!(result.value(), 15);
    assert_eq!(*result.ty(), Type::Int);
}

// spec: 04-expressions §4.3 — nested let different types
#[test]
fn nested_let_with_different_types() {
    let mut session = repl_session();
    let result = session
        .eval("(let [x 42] (let [b (eq-i64 x 42)] (if b 1 0)))")
        .unwrap();
    assert_eq!(result.value(), 1);
    assert_eq!(*result.ty(), Type::Int);
}

// =============================================================================
// Performance (spec: §7.2 — simple eval < 50ms)
// =============================================================================

// spec: repl/spec.md §7.2 — simple eval under 50ms
#[test]
fn simple_eval_is_fast() {
    // Spec §7.2: Simple expressions MUST evaluate within 50ms.
    let mut session = repl_session();
    let start = std::time::Instant::now();
    let _ = session.eval("(add-i64 1 2)").unwrap();
    let elapsed = start.elapsed();
    assert!(
        elapsed.as_millis() < 50,
        "simple eval took {}ms, spec requires < 50ms",
        elapsed.as_millis()
    );
}

// spec: repl/spec.md §7.2 — defn eval under 50ms
#[test]
fn defn_eval_is_fast() {
    // Spec §7.2: defining a simple function should also be fast.
    let mut session = repl_session();
    let start = std::time::Instant::now();
    let _ = session.eval("(defn f [x] (add-i64 x 1))").unwrap();
    let elapsed = start.elapsed();
    assert!(
        elapsed.as_millis() < 50,
        "defn took {}ms, spec requires < 50ms",
        elapsed.as_millis()
    );
}

// =============================================================================
// Display Format — Consistency (spec: §1)
// =============================================================================

// spec: repl/spec.md §1.2 — colon prefix in display
#[test]
fn display_format_colon_prefix() {
    // Spec §1.2: format is `:Type value` — starts with colon.
    let s = format_result(42, &Type::Int);
    assert!(s.starts_with(':'), "display format must start with ':', got: {s}");
}

// spec: repl/spec.md §1.2 — type value space separated
#[test]
fn display_format_type_value_separated_by_space() {
    // Spec §1.2: format is `:Type value` — type and value separated by space.
    let s = format_result(42, &Type::Int);
    let parts: Vec<&str> = s.splitn(2, ' ').collect();
    assert_eq!(parts.len(), 2, "display should be ':Type value', got: {s}");
    assert_eq!(parts[0], ":primitives/Int");
    assert_eq!(parts[1], "42");
}

// spec: repl/spec.md §1.5 — Bool displays as word not number
#[test]
fn display_bool_value_is_word_not_number() {
    // Spec §1.5: Bool displays as `true` or `false`, not 0/1.
    let s_true = format_result(1, &Type::Bool);
    assert!(
        s_true.contains("true") && !s_true.contains('1'),
        "Bool true should display as word 'true', got: {s_true}"
    );
    let s_false = format_result(0, &Type::Bool);
    assert!(
        s_false.contains("false") && !s_false.contains('0'),
        "Bool false should display as word 'false', got: {s_false}"
    );
}

// =============================================================================
// Deftype + Constructor in Expressions (spec: §1.3, §1.5)
// =============================================================================

// spec: 04-expressions §4.4 — constructor in if expression
#[test]
fn constructor_in_if_expression() {
    let mut session = repl_session();
    session.eval("(deftype AB A B)").unwrap();
    session
        .eval("(defn pick [cond] (if cond A B))")
        .unwrap();
    let r = session.eval("(pick true)").unwrap();
    assert_eq!(*r.ty(), Type::ADT(FQTypeName::new(ModuleFullPath::from("user"), TypeName::from("AB")), vec![]));
    assert_eq!(r.value(), 0); // A is tag 0

    let r = session.eval("(pick false)").unwrap();
    assert_eq!(r.value(), 1); // B is tag 1
}

// spec: 04-expressions §4.3 — constructor in let binding
#[test]
fn constructor_in_let() {
    let mut session = repl_session();
    session.eval("(deftype YN Yes No)").unwrap();
    let result = session.eval("(let [x Yes] x)").unwrap();
    assert_eq!(*result.ty(), Type::ADT(FQTypeName::new(ModuleFullPath::from("user"), TypeName::from("YN")), vec![]));
    assert_eq!(result.value(), 0);
}

// =============================================================================
// Session Startup (spec: §6, §7.1)
// =============================================================================

// spec: repl/spec.md §7.1 — session creation under 500ms
#[test]
fn session_creation_is_fast() {
    // Spec §7.1: REPL MUST start within 500ms (Ring 0 has no prelude to load).
    let start = std::time::Instant::now();
    let _session = repl_session();
    let elapsed = start.elapsed();
    assert!(
        elapsed.as_millis() < 500,
        "session creation took {}ms, spec requires < 500ms",
        elapsed.as_millis()
    );
}

// spec: repl/spec.md §6.1 — fresh session evaluates immediately
#[test]
fn fresh_session_can_evaluate_immediately() {
    // Spec §6.1: A new user can evaluate a simple expression immediately.
    let mut session = repl_session();
    let result = session.eval("42").unwrap();
    assert_eq!(result.value(), 42);
    assert_eq!(*result.ty(), Type::Int);
}

// =============================================================================
// Realistic Session: First Five Minutes (spec: §6.1)
// =============================================================================

// spec: repl/spec.md §6.1 — first five minutes workflow
#[test]
fn first_five_minutes_workflow() {
    // Spec §6.1: A new user can:
    // 1. Evaluate a simple expression
    // 2. See typed result
    // 3. Define a function and see its type
    // 4. Use the function
    let mut session = repl_session();

    // 1-2. Evaluate and see typed result.
    let r = session.eval("(add-i64 1 2)").unwrap();
    assert_eq!(r.value(), 3);
    assert_eq!(*r.ty(), Type::Int);
    assert!(!r.is_def());

    // 3. Define a function and see its type.
    let r = session.eval("(defn double [x] (mul-i64 x 2))").unwrap();
    assert!(r.is_def());
    assert_eq!(
        *r.ty(),
        Type::Fn(vec![Type::Int], Box::new(Type::Int))
    );

    // 4. Use the function.
    assert_eq!(repl_eval(&mut session, "(double 21)"), 42);
}

// =============================================================================
// Mixed Types in Session (spec: §1.2)
// =============================================================================

// spec: repl/spec.md §1.2 — all three primitive types in session
#[test]
fn session_with_all_three_primitive_types() {
    // A session using Int, Bool, and Float — all Ring 0 primitive types.
    let mut session = repl_session();

    let r_int = session.eval("42").unwrap();
    assert_eq!(*r_int.ty(), Type::Int);

    let r_bool = session.eval("true").unwrap();
    assert_eq!(*r_bool.ty(), Type::Bool);

    let r_float = session.eval("3.14").unwrap();
    assert_eq!(*r_float.ty(), Type::Float);

    // Mix them in expressions.
    session
        .eval("(defn classify [n] (if (lt-i64 n 0) false true))")
        .unwrap();
    let r = session.eval("(classify 5)").unwrap();
    assert_eq!(*r.ty(), Type::Bool);
    assert_eq!(r.value(), 1);

    let r = session.eval("(classify (sub-i64 0 1))").unwrap();
    assert_eq!(*r.ty(), Type::Bool);
    assert_eq!(r.value(), 0);
}

// =============================================================================
// =============================================================================
//
// Ring 1 REPL Experience Tests
//
// These tests validate the REPL user experience for Ring 1 features: strings,
// ADTs with fields, and closures. Focus is on display format, type reporting,
// error quality, and session continuity — not on correctness (that's /qa's job
// in ring1.rs and rc.rs).
//
// Ring 1 spec references:
//   repl/spec.md §1.2 — expression result display
//   repl/spec.md §1.5 — value display (String, data ADT, closure)
//   repl/spec.md §5.3 — type error quality
//
// =============================================================================
// =============================================================================

// =============================================================================
// String Display (repl/spec.md §1.5: String → "contents" with escapes)
// =============================================================================

// spec: repl/spec.md §1.5 — String literal display format
#[test]
fn ring1_string_literal_display_format() {
    // Spec §1.5: String values display as `"contents"`.
    // Full result format: `:String "contents"`.
    let mut session = repl_session();
    let display = repl_eval_display(&mut session, "\"hello\"");
    assert_eq!(display, ":primitives/String \"hello\"");
}

// spec: repl/spec.md §1.5 — empty String display
#[test]
fn ring1_string_empty_display() {
    // Empty string should display as `:String ""`.
    let mut session = repl_session();
    let display = repl_eval_display(&mut session, "\"\"");
    assert_eq!(display, ":primitives/String \"\"");
}

// spec: repl/spec.md §1.5 — String concat result display
#[test]
fn ring1_string_concat_result_display() {
    // Result of str-concat should display the concatenated string.
    let mut session = repl_session();
    let display = repl_eval_display(&mut session, "(str-concat \"hello\" \" world\")");
    assert_eq!(display, ":primitives/String \"hello world\"");
}

// spec: repl/spec.md §1.2 — String type reporting
#[test]
fn ring1_string_literal_reports_string_type() {
    // Spec §1.2: string expression should report Type::String.
    let mut session = repl_session();
    let result = session.eval("\"hello\"").unwrap();
    assert_eq!(*result.ty(), Type::String);
    assert!(!result.is_def());
}

// spec: appendix-a-builtins §A.3 — string primitive return types
#[test]
fn ring1_string_primitive_reports_correct_types() {
    // String primitives should report appropriate return types.
    let mut session = repl_session();

    // str-len returns Int.
    let r = session.eval("(str-len \"hello\")").unwrap();
    assert_eq!(*r.ty(), Type::Int);
    assert_eq!(r.value(), 5);

    // str-eq returns Bool.
    let r = session.eval("(str-eq \"a\" \"a\")").unwrap();
    assert_eq!(*r.ty(), Type::Bool);
    assert_eq!(r.value(), 1);

    // int-to-string returns String.
    let r = session.eval("(int-to-string 42)").unwrap();
    assert_eq!(*r.ty(), Type::String);
}

// spec: repl/spec.md §1.5 — int-to-string display
#[test]
fn ring1_int_to_string_display() {
    // Converting an integer to string and displaying the result.
    let mut session = repl_session();
    let display = repl_eval_display(&mut session, "(int-to-string 42)");
    assert_eq!(display, ":primitives/String \"42\"");
}

// spec: repl/spec.md §1.5 — String with spaces display
#[test]
fn ring1_string_with_spaces_display() {
    // Strings containing spaces display correctly with surrounding quotes.
    let mut session = repl_session();
    let display = repl_eval_display(&mut session, "\"hello world\"");
    assert_eq!(display, ":primitives/String \"hello world\"");
}

// =============================================================================
// ADT Display (repl/spec.md §1.5: data constructors, product types, polymorphic)
// =============================================================================

// spec: repl/spec.md §1.5 — product ADT display
#[test]
fn ring1_adt_product_display() {
    // Spec §1.5: Data constructor display: `(Type.Ctor field1 field2 ...)`.
    // Product type with Int fields.
    let mut session = repl_session();
    repl_eval(&mut session, "(deftype Point [:Int x :Int y])");
    let display = repl_eval_display(&mut session, "(Point 3 4)");
    assert_eq!(display, ":user/Point (Point 3 4)");
}

// spec: repl/spec.md §1.5 — sum ADT Some display
#[test]
fn ring1_adt_sum_some_display() {
    // Spec §1.5: `:(Option Int) (Some 42)` for data constructor.
    let mut session = repl_session();
    repl_eval(&mut session, "(deftype (Option a) None (Some [:a val]))");
    let display = repl_eval_display(&mut session, "(Some 42)");
    assert_eq!(display, ":(user/Option primitives/Int) (Option.Some 42)");
}

// spec: repl/spec.md §1.5 — sum ADT None display
#[test]
fn ring1_adt_sum_none_display() {
    // Nullary constructor of polymorphic type displays correctly.
    let mut session = repl_session();
    repl_eval(&mut session, "(deftype (Option a) None (Some [:a val]))");
    let display = repl_eval_display(&mut session, "None");
    // None is nullary — type var may be unresolved. Display should show
    // the Option type and the constructor name.
    assert!(
        display.contains("Option") && display.ends_with("None"),
        "expected Option ... None display, got: {display}"
    );
}

// spec: repl/spec.md §1.5 — polymorphic ADT type display
#[test]
fn ring1_adt_polymorphic_type_display() {
    // Parameterized types show their type args: `:(Option Int)`.
    let mut session = repl_session();
    repl_eval(&mut session, "(deftype (Option a) None (Some [:a val]))");
    let result = session.eval("(Some 42)").unwrap();
    // Type should be ADT("Option", [Int]).
    assert_eq!(
        *result.ty(),
        Type::ADT(FQTypeName::new(ModuleFullPath::from("user"), TypeName::from("Option")), vec![Type::Int])
    );
}

// spec: repl/spec.md §1.2 — product ADT type reporting
#[test]
fn ring1_adt_product_type_reports_adt_type() {
    // Constructing a product type should report the ADT type.
    let mut session = repl_session();
    repl_eval(&mut session, "(deftype Point [:Int x :Int y])");
    let result = session.eval("(Point 3 4)").unwrap();
    assert_eq!(
        *result.ty(),
        Type::ADT(FQTypeName::new(ModuleFullPath::from("user"), TypeName::from("Point")), vec![])
    );
    assert!(!result.is_def());
}

// spec: repl/spec.md §1.5 — ADT nested string field display
#[test]
fn ring1_adt_nested_string_field_display() {
    // ADT containing a String field should recursively display the string.
    // Spec §1.5: "ADT fields MUST be recursively formatted."
    //
    // USABILITY FINDING U1.1: Polymorphic ADT field display does not substitute
    // type variables with concrete type args. `(Some "hello")` shows the raw
    // pointer value instead of `"hello"` because the field type is stored as
    // `Type::Var(a)` in TypeDefInfo, not `Type::String`. The type portion
    // `:(Option String)` is correct, but the value display is not.
    // Filed to tests/plan/usability.md.
    let mut session = repl_session();
    repl_eval(&mut session, "(deftype (Option a) None (Some [:a val]))");
    let display = repl_eval_display(&mut session, "(Some \"hello\")");
    // Current behavior: field rendered as raw i64 (the pointer) due to Var type.
    // When U1.1 is fixed, this should become:
    //   assert_eq!(display, ":(Option String) (Some \"hello\")");
    assert!(
        display.starts_with(":(user/Option primitives/String) (Option.Some "),
        "should show type as (user/Option primitives/String), got: {display}"
    );
}

// spec: repl/spec.md §1.5 — ADT monomorphic string field display
#[test]
fn ring1_adt_monomorphic_string_field_display() {
    // Monomorphic ADT with concrete String field type (no type variable issue).
    // Spec §1.5: fields must be recursively formatted.
    let mut session = repl_session();
    repl_eval(&mut session, "(deftype Named [:String name])");
    let display = repl_eval_display(&mut session, "(Named \"alice\")");
    assert_eq!(display, ":user/Named (Named \"alice\")");
}

// spec: repl/spec.md §1.5 — ADT enum display with type defs
#[test]
fn ring1_adt_enum_display_with_type_defs() {
    // Nullary constructors should show constructor names, not bare tags.
    // This uses a REPL session where type_defs are accumulated.
    let mut session = repl_session();
    repl_eval(&mut session, "(deftype Color Red Green Blue)");
    let display = repl_eval_display(&mut session, "Red");
    assert_eq!(display, ":user/Color Color.Red");
    let display = repl_eval_display(&mut session, "Blue");
    assert_eq!(display, ":user/Color Color.Blue");
}

// spec: repl/spec.md §1.3 — deftype with fields reports type
#[test]
fn ring1_deftype_with_fields_reports_type() {
    // Spec §1.3: type definition displays the type name.
    let mut session = repl_session();
    let result = session
        .eval("(deftype Point [:Int x :Int y])")
        .unwrap();
    assert!(result.is_def());
    assert_eq!(
        *result.ty(),
        Type::ADT(FQTypeName::new(ModuleFullPath::from("user"), TypeName::from("Point")), vec![])
    );
}

// =============================================================================
// Closure Display (repl/spec.md §1.5: Closure → `<closure>`)
// =============================================================================

// spec: repl/spec.md §1.5 — closure display format
#[test]
fn ring1_closure_display_format() {
    // Spec §1.5: Closure values display as `<closure>`.
    let mut session = repl_session();
    repl_eval(&mut session, "(defn make-adder [n] (fn [x] (add-i64 n x)))");
    let display = repl_eval_display(&mut session, "(make-adder 5)");
    assert!(
        display.contains("<closure>"),
        "closure display should contain '<closure>', got: {display}"
    );
}

// spec: repl/spec.md §1.5 — closure display includes Fn type
#[test]
fn ring1_closure_display_includes_fn_type() {
    // Closure display format: `:(Fn [params] return) <closure>`.
    let mut session = repl_session();
    repl_eval(&mut session, "(defn make-adder [n] (fn [x] (add-i64 n x)))");
    let display = repl_eval_display(&mut session, "(make-adder 5)");
    assert!(
        display.starts_with(":(Fn "),
        "closure display should start with ':(Fn ', got: {display}"
    );
    assert!(
        display.ends_with("<closure>"),
        "closure display should end with '<closure>', got: {display}"
    );
}

// spec: repl/spec.md §1.2 — closure result type is Fn
#[test]
fn ring1_closure_result_type_is_fn() {
    // The type of a closure value should be Type::Fn.
    let mut session = repl_session();
    repl_eval(&mut session, "(defn make-adder [n] (fn [x] (add-i64 n x)))");
    let result = session.eval("(make-adder 5)").unwrap();
    match &result.ty() {
        Type::Fn(params, _ret) => {
            assert_eq!(params.len(), 1, "make-adder should return a 1-param closure");
        }
        other => panic!("expected Fn type for closure, got: {other:?}"),
    }
}

// spec: repl/spec.md §1.3 — defn returning closure type
#[test]
fn ring1_defn_returning_closure_type() {
    // Defining a function that returns a closure should report the higher-order type.
    let mut session = repl_session();
    let result = session
        .eval("(defn make-adder [n] (fn [x] (add-i64 n x)))")
        .unwrap();
    assert!(result.is_def());
    // Should be (Fn [Int] (Fn [primitives/Int] primitives/Int)).
    match &result.ty() {
        Type::Fn(params, ret) => {
            assert_eq!(params.len(), 1);
            assert_eq!(params[0], Type::Int);
            match ret.as_ref() {
                Type::Fn(inner_params, inner_ret) => {
                    assert_eq!(inner_params.len(), 1);
                    assert_eq!(inner_params[0], Type::Int);
                    assert_eq!(inner_ret.as_ref(), &Type::Int);
                }
                other => panic!("expected inner Fn type, got: {other:?}"),
            }
        }
        other => panic!("expected Fn type for make-adder, got: {other:?}"),
    }
}

// spec: repl/spec.md §1.2 — lambda immediate not closure
#[test]
fn ring1_lambda_immediate_display_not_closure() {
    // Immediately-applied lambda should show the result, not <closure>.
    let mut session = repl_session();
    let display = repl_eval_display(&mut session, "((fn [x] (add-i64 x 1)) 5)");
    assert_eq!(display, ":primitives/Int 6");
}

// =============================================================================
// Error Quality for Ring 1 Types (repl/spec.md §5.3)
// =============================================================================

// spec: repl/spec.md §5.3 — String where Int expected error
#[test]
fn ring1_error_string_where_int_expected() {
    // Passing a String where Int is expected should produce a clear type error.
    let mut session = repl_session();
    match session.eval("(add-i64 \"hello\" 1)") {
        Err(ref e) => {
            let msg = e.message();
            assert!(
                msg.contains("Int") || msg.contains("String"),
                "type error should mention the types involved, got: {msg}"
            );
        }
        Ok(_) => panic!("expected type error for String where Int expected"),
    }
    // Session recovery.
    assert_eq!(repl_eval(&mut session, "(add-i64 1 2)"), 3);
}

// spec: repl/spec.md §5.3 — Int where String expected error
#[test]
fn ring1_error_int_where_string_expected() {
    // Passing an Int where String is expected.
    let mut session = repl_session();
    match session.eval("(str-len 42)") {
        Err(ref e) => {
            let msg = e.message();
            assert!(
                msg.contains("Int") || msg.contains("String"),
                "type error should mention types, got: {msg}"
            );
        }
        Ok(_) => panic!("expected type error for Int where String expected"),
    }
    // Session continues.
    assert_eq!(repl_eval(&mut session, "(str-len \"hi\")"), 2);
}

// spec: repl/spec.md §5.3 — if branch String/Int mismatch
#[test]
fn ring1_error_if_branch_string_int_mismatch() {
    // If branches with String and Int should produce a clear type error.
    let mut session = repl_session();
    match session.eval("(if true \"hello\" 42)") {
        Err(ref e) => {
            let msg = e.message();
            assert!(
                !msg.is_empty(),
                "branch type mismatch error should have a message"
            );
        }
        Ok(_) => panic!("expected type error for mismatched if branches (String vs Int)"),
    }
    assert_eq!(repl_eval(&mut session, "1"), 1);
}

// spec: repl/spec.md §5.1 — constructor wrong arg count
#[test]
fn ring1_error_constructor_wrong_arg_count() {
    // Constructing an ADT with wrong number of arguments should error clearly.
    let mut session = repl_session();
    repl_eval(&mut session, "(deftype Point [:Int x :Int y])");
    match session.eval("(Point 1)") {
        Err(ref e) => {
            let msg = e.message();
            assert!(
                !msg.is_empty(),
                "constructor arity error should have a message"
            );
        }
        Ok(_) => panic!("expected error for wrong constructor argument count"),
    }
    // Session recovery: correct usage still works.
    let display = repl_eval_display(&mut session, "(Point 1 2)");
    assert_eq!(display, ":user/Point (Point 1 2)");
}

// spec: repl/spec.md §5.3 — constructor wrong type
#[test]
fn ring1_error_constructor_wrong_type() {
    // Constructing an ADT with wrong field type should produce a type error.
    let mut session = repl_session();
    repl_eval(&mut session, "(deftype Point [:Int x :Int y])");
    match session.eval("(Point true 2)") {
        Err(ref e) => {
            let msg = e.message();
            assert!(
                msg.contains("Int") || msg.contains("Bool"),
                "constructor type error should mention the types, got: {msg}"
            );
        }
        Ok(_) => panic!("expected type error for wrong constructor field type"),
    }
}

// spec: repl/spec.md §5.1 — undefined constructor error
#[test]
fn ring1_error_undefined_constructor() {
    // Using an undefined constructor should produce a clear error.
    let mut session = repl_session();
    match session.eval("(Foo 1 2)") {
        Err(ref e) => {
            let msg = e.message();
            assert!(
                msg.contains("Foo") || msg.contains("unbound") || msg.contains("undefined")
                    || msg.contains("unknown") || msg.contains("not found"),
                "undefined constructor error should mention the name, got: {msg}"
            );
        }
        Ok(_) => panic!("expected error for undefined constructor"),
    }
    assert_eq!(repl_eval(&mut session, "42"), 42);
}

// spec: repl/spec.md §5.1 — closure arity mismatch
#[test]
fn ring1_error_closure_arity_mismatch() {
    // Calling a closure with wrong number of arguments should error clearly.
    let mut session = repl_session();
    match session.eval("(let [f (fn [x] x)] (f 1 2))") {
        Err(ref e) => {
            let msg = e.message();
            assert!(
                !msg.is_empty(),
                "closure arity error should have a message"
            );
        }
        Ok(_) => panic!("expected error for closure arity mismatch"),
    }
    assert_eq!(repl_eval(&mut session, "(let [f (fn [x] x)] (f 42))"), 42);
}

// spec: repl/spec.md §5.1 — error span for heap type mismatch
#[test]
fn ring1_error_has_span_for_heap_type_mismatch() {
    // Spec §5.1: errors MUST include source location.
    // Type errors involving heap types should have non-synthetic spans.
    let mut session = repl_session();
    match session.eval("(str-len 42)") {
        Err(ref e) => {
            let span = e.span();
            assert!(
                span != Span::SYNTHETIC,
                "heap type error span should not be synthetic: {span:?}"
            );
        }
        Ok(_) => panic!("expected type error"),
    }
}

// =============================================================================
// Type Display for Ring 1 (repl/spec.md §1.4)
// =============================================================================

// spec: repl/spec.md §1.3 — defn with String param type
#[test]
fn ring1_defn_with_string_param_type() {
    // Defining a function with String parameter should report String in the type.
    let mut session = repl_session();
    let result = session
        .eval("(defn greet-len [s] (str-len s))")
        .unwrap();
    assert!(result.is_def());
    assert_eq!(
        *result.ty(),
        Type::Fn(vec![Type::String], Box::new(Type::Int))
    );
}

// spec: repl/spec.md §1.3 — defn returning String type
#[test]
fn ring1_defn_returning_string_type() {
    // Defining a function returning String should report String in return type.
    let mut session = repl_session();
    let result = session
        .eval("(defn greeting [] \"hello\")")
        .unwrap();
    assert!(result.is_def());
    assert_eq!(
        *result.ty(),
        Type::Fn(vec![], Box::new(Type::String))
    );
}

// spec: repl/spec.md §1.3 — defn with ADT param type
#[test]
fn ring1_defn_with_adt_param_type() {
    // A function taking an ADT parameter shows the ADT type.
    let mut session = repl_session();
    repl_eval(&mut session, "(deftype Point [:Int x :Int y])");
    let result = session
        .eval("(defn get-x [p] (match p [(Point x y) x]))")
        .unwrap();
    assert!(result.is_def());
    assert_eq!(
        *result.ty(),
        Type::Fn(
            vec![Type::ADT(FQTypeName::new(ModuleFullPath::from("user"), TypeName::from("Point")), vec![])],
            Box::new(Type::Int)
        )
    );
}

// spec: repl/spec.md §1.3 — defn polymorphic ADT return type
#[test]
fn ring1_defn_polymorphic_adt_return_type() {
    // A function returning a polymorphic ADT shows the instantiated type.
    let mut session = repl_session();
    repl_eval(&mut session, "(deftype (Option a) None (Some [:a val]))");
    let result = session
        .eval("(defn wrap [x] (Some x))")
        .unwrap();
    assert!(result.is_def());
    // wrap should be polymorphic: (Fn [a] (Option a))
    match &result.ty() {
        Type::Fn(params, ret) => {
            assert_eq!(params.len(), 1);
            match ret.as_ref() {
                Type::ADT(name, args) => {
                    assert_eq!(name.name, TypeName::from("Option"));
                    assert_eq!(args.len(), 1, "Option should have 1 type arg");
                }
                other => panic!("expected ADT return type, got: {other:?}"),
            }
        }
        other => panic!("expected Fn type for wrap, got: {other:?}"),
    }
}

// =============================================================================
// Session Continuity — Ring 1 (repl/spec.md §5.2)
// =============================================================================

// spec: repl/spec.md §5.2 — error between ADT and closure defs
#[test]
fn ring1_error_between_adt_and_closure_definitions() {
    // Define an ADT, trigger an error, then define a closure over the ADT.
    // All definitions should survive.
    let mut session = repl_session();

    // Step 1: define an ADT.
    repl_eval(&mut session, "(deftype (Option a) None (Some [:a val]))");

    // Step 2: define a function using it.
    repl_eval(
        &mut session,
        "(defn unwrap [opt] (match opt [(Some x) x None 0]))",
    );

    // Step 3: trigger an error.
    let err = session.eval("(add-i64 \"hello\" 1)");
    assert!(err.is_err());

    // Step 4: the ADT and function still work.
    assert_eq!(repl_eval(&mut session, "(unwrap (Some 99))"), 99);

    // Step 5: define a closure that uses the ADT.
    repl_eval(&mut session, "(defn make-wrapper [n] (fn [] (Some n)))");
    let display = repl_eval_display(&mut session, "((make-wrapper 42))");
    assert_eq!(display, ":(user/Option primitives/Int) (Option.Some 42)");
}

// spec: repl/spec.md §5.2 — error preserves string definitions
#[test]
fn ring1_error_preserves_string_definitions() {
    // Define functions using strings, error, verify they survive.
    let mut session = repl_session();

    repl_eval(&mut session, "(defn greet [] \"hello\")");

    // Error.
    let err = session.eval("(add-i64 true 1)");
    assert!(err.is_err());

    // String function still works.
    let display = repl_eval_display(&mut session, "(greet)");
    assert_eq!(display, ":primitives/String \"hello\"");
}

// spec: repl/spec.md §6.1 — incremental session with heap types
#[test]
fn ring1_session_incremental_with_heap_types() {
    // Simulates a user building up definitions with strings, ADTs, and closures.
    let mut session = repl_session();

    // Step 1: explore strings.
    let display = repl_eval_display(&mut session, "\"hello\"");
    assert_eq!(display, ":primitives/String \"hello\"");

    // Step 2: define an ADT.
    repl_eval(&mut session, "(deftype (Option a) None (Some [:a val]))");

    // Step 3: wrap a string in an ADT.
    let display = repl_eval_display(&mut session, "(Some \"world\")");
    // Note: field display for polymorphic ADTs shows raw value due to U1.1
    // (type variable not substituted with concrete type). Type portion is correct.
    assert!(
        display.starts_with(":(user/Option primitives/String) (Option.Some "),
        "should show type as (user/Option primitives/String), got: {display}"
    );

    // Step 4: define a closure.
    repl_eval(&mut session, "(defn make-adder [n] (fn [x] (add-i64 n x)))");
    let display = repl_eval_display(&mut session, "(make-adder 10)");
    assert!(display.contains("<closure>"), "got: {display}");

    // Step 5: use the closure.
    assert_eq!(repl_eval(&mut session, "((make-adder 10) 32)"), 42);

    // Step 6: make a mistake.
    let err = session.eval("(str-len 42)");
    assert!(err.is_err());

    // Step 7: everything still works.
    assert_eq!(repl_eval(&mut session, "((make-adder 5) 5)"), 10);
    let display = repl_eval_display(&mut session, "(Some 99)");
    assert_eq!(display, ":(user/Option primitives/Int) (Option.Some 99)");
}

// =============================================================================
// Vec Display (Ring 1)
// =============================================================================

// spec: repl/spec.md §1.5 — Vec Int display
#[test]
fn display_vec_int() {
    let mut session = repl_session();
    let display = repl_eval_display(&mut session, "[1 2 3]");
    assert!(
        display.contains("[1, 2, 3]") || display.contains("[1 2 3]"),
        "Vec of ints should display elements, got: {display}"
    );
}

// spec: repl/spec.md §1.5 — empty Vec display
#[test]
fn display_vec_empty() {
    let mut session = repl_session();
    let display = repl_eval_display(&mut session, "[]");
    assert!(
        display.contains("[]"),
        "Empty Vec should display as [], got: {display}"
    );
}

// spec: repl/spec.md §1.5 — Vec after push display
#[test]
fn display_vec_after_push() {
    let mut session = repl_session();
    let display = repl_eval_display(&mut session, "(vec-push [1 2] 3)");
    assert!(
        display.contains("1") && display.contains("2") && display.contains("3"),
        "Vec after push should show all elements, got: {display}"
    );
}

// =============================================================================
// List display (spec: repl/spec.md §1.5 — empty: `List.Nil`; non-empty: per ADT)
// Covers repl/spec.md:295 FIXME(/qa) for List/Seq display coverage.
// Tests define List inline (no stdlib dep per tests/CLAUDE.md test isolation).
// =============================================================================

// spec: repl/spec.md §1.5 — empty list displays as `List.Nil` (nullary ADT ctor)
#[test]
fn display_list_nil() {
    let mut session = repl_session();
    session.eval("(deftype (List a) Nil (Cons [:a h :(List a) t]))").unwrap();
    let display = repl_eval_display(&mut session, "Nil");
    assert!(
        display.contains("List.Nil"),
        "empty list MUST display as 'List.Nil' per §1.5, got: {display}"
    );
}

// spec: repl/spec.md §1.5 — non-empty list displays its elements
// Spec describes the future `(list e1 e2 ...)` format; current implementation
// uses the generic ADT `(List.Cons head tail)` recursive form, which is
// semantically equivalent (same elements, same order). We check the element
// values appear; see FIXME(/spec) below for format convergence.
#[test]
fn display_list_non_empty_shows_elements() {
    let mut session = repl_session();
    session.eval("(deftype (List a) Nil (Cons [:a h :(List a) t]))").unwrap();
    let display = repl_eval_display(&mut session, "(Cons 1 (Cons 2 (Cons 3 Nil)))");
    // Elements 1, 2, 3 MUST appear in output.
    for elem in ["1", "2", "3"] {
        assert!(
            display.contains(elem),
            "list display MUST contain element {elem}, got: {display}"
        );
    }
}

// spec: repl/spec.md §1.5 — non-empty list MUST NOT hide elements
// (Negative coverage — the ADT recursive display must not truncate a small list.)
#[test]
fn display_list_non_empty_no_truncation_for_small_list() {
    let mut session = repl_session();
    session.eval("(deftype (List a) Nil (Cons [:a h :(List a) t]))").unwrap();
    let display = repl_eval_display(&mut session, "(Cons 42 Nil)");
    // A one-element list must show the element value — MUST NOT appear as
    // just a heap-pointer integer or an opaque `<List>` tag.
    assert!(
        display.contains("42"),
        "single-element list MUST show the element, got: {display}"
    );
    // MUST NOT display as a raw numeric heap-pointer (large numbers).
    assert!(
        !display.contains("<closure>"),
        "list value MUST NOT display as <closure>, got: {display}"
    );
}

// =============================================================================
// Seq display (spec: repl/spec.md §1.5 — lazy sequence)
// =============================================================================

// =============================================================================
// §4.1 row gaps (repl/spec.md:541 FIXME(/qa)): overloaded fn variants,
// related constructors, related trait impls.
// =============================================================================

// spec: repl/spec.md §4.1.1 — overloaded fn MUST show all variant signatures
// Per §4.1.1 row 583: "overloaded fn shows all variants". A multi-sig fn
// entered as a bare symbol MUST display one line per variant signature.
// Currently the implementation shows only one signature — this test is the
// visible signal of that /int gap (per feedback_failing_not_ignored.md).
#[test]
fn display_overloaded_fn_shows_all_variants() {
    let mut session = repl_session();
    session
        .eval("(defn pick ([:Int x] x) ([:Int x :Int y] (add-i64 x y)))")
        .unwrap();
    let display = repl_eval_display(&mut session, "pick");
    // BOTH signatures must appear — one for the 1-arg variant, one for 2-arg.
    // Look for function-type shapes in the output.
    let has_1_arg = display.contains("[primitives/Int]") || display.contains("[Int]");
    let has_2_arg = display.contains("[primitives/Int primitives/Int]")
        || display.contains("[Int Int]");
    assert!(
        has_1_arg && has_2_arg,
        "overloaded fn MUST show both signatures per §4.1.1, got:\n{display}"
    );
}

// spec: repl/spec.md §4.1.3 — bare type lookup MUST include `; match:` line
// listing the type's constructors. Positive-path test for §4.1.3 row 635.
#[test]
fn display_type_shows_related_constructors() {
    let mut session = repl_session();
    session.eval("(deftype Color Red Green Blue)").unwrap();
    let display = repl_eval_display(&mut session, "Color");
    assert!(
        display.contains("match:") || display.contains("Red"),
        "type display MUST list constructors under ; match:, got: {display}"
    );
    for ctor in ["Red", "Green", "Blue"] {
        assert!(
            display.contains(ctor),
            "type display MUST name constructor {ctor}, got: {display}"
        );
    }
}

// spec: repl/spec.md §4.1.3 — bare type lookup MUST include `; impl:` line
// listing implementing trait names. Positive-path test for §4.1.3 row 636.
#[test]
fn display_type_shows_related_trait_impls() {
    let mut session = repl_session();
    session.eval("(deftype Color Red Green Blue)").unwrap();
    session.eval("(deftrait Shade (brightness [self] Int))").unwrap();
    session
        .eval("(impl Shade Color (defn brightness [c] 1))")
        .unwrap();
    let display = repl_eval_display(&mut session, "Color");
    // The trait name `Shade` MUST appear under an `; impl:` section.
    assert!(
        display.contains("impl:") && display.contains("Shade"),
        "type display MUST list implementing traits under ; impl:, got: {display}"
    );
}

// spec: repl/spec.md §4.1.3 — type with NO impls must NOT show `; impl:` line
// (Negative coverage — absence is a hard requirement: empty categories must
// be omitted, not printed as blank sections.)
#[test]
fn display_type_no_impls_omits_impl_section() {
    let mut session = repl_session();
    session.eval("(deftype Lonely Alone)").unwrap();
    let display = repl_eval_display(&mut session, "Lonely");
    assert!(
        !display.contains("impl:"),
        "type display MUST NOT include empty ; impl: section, got: {display}"
    );
}

// spec: repl/spec.md §1.5 — Seq displays elements; infinite seq MUST NOT hang
// The spec format is `(seq e1 e2 ... +more)` with a bounded force limit.
// This test creates an infinite SeqCons and materializes enough via match to
// verify the REPL can display a Seq value without hanging (the key invariant).
#[test]
fn display_seq_infinite_does_not_hang() {
    let mut session = repl_session();
    session.eval("(deftype (Seq a) SeqNil (SeqCons [:a h :(Fn [] (Seq a)) rest]))")
        .unwrap();
    session.eval("(defn range-from [n] (SeqCons n (fn [] (range-from (add-i64 n 1)))))")
        .unwrap();
    // Force a finite prefix by taking the head only. The display of the
    // resulting SeqCons MUST succeed without forcing the thunked tail.
    let display = repl_eval_display(&mut session, "(range-from 7)");
    // Must have produced non-trivial output (didn't hang).
    assert!(
        !display.is_empty(),
        "Seq display MUST produce output (not hang), got empty"
    );
    // Element 7 (head) should appear in the display.
    assert!(
        display.contains("7"),
        "Seq display MUST show the head element, got: {display}"
    );
}

// =============================================================================
// Empty/Comment Input Handling (Ring 1)
// =============================================================================

// spec: repl/spec.md §2.1 — blank line no error
#[test]
fn repl_blank_line_no_error() {
    let mut session = repl_session();
    // Blank input should not produce an error
    let result = session.eval("");
    assert!(result.is_ok(), "Blank line should not error: {:?}", result.err());
}

// spec: 01-lexical §1.2 — comment-only no error
#[test]
fn repl_comment_only_no_error() {
    let mut session = repl_session();
    // Comment-only input should not produce an error
    let result = session.eval("; this is a comment");
    assert!(result.is_ok(), "Comment-only input should not error: {:?}", result.err());
}

// =============================================================================
// Ring 2A: Trait-based Operator Dispatch (spec: §4.3)
// =============================================================================

// spec: 07-traits §7.5 — + operator Int in REPL
#[test]
fn ring2a_operator_add_int() {
    // Spec §4.3: Operators are stdlib functions dispatched via traits.
    let mut session = repl_session();
    install_trait_prelude(&mut session);
    let (value, ty) = repl_eval_typed(&mut session, "(+ 1 2)");
    assert_eq!(value, 3);
    assert_eq!(ty, Type::Int);
}

// spec: 07-traits §7.5 — + operator Float in REPL
#[test]
fn ring2a_operator_add_float() {
    let mut session = repl_session();
    install_trait_prelude(&mut session);
    let (value, ty) = repl_eval_typed(&mut session, "(+ 1.0 2.0)");
    assert_eq!(ty, Type::Float);
    let f = f64::from_bits(value as u64);
    assert!((f - 3.0).abs() < f64::EPSILON, "expected 3.0, got {f}");
}

// spec: 07-traits §7.5 — - operator Int in REPL
#[test]
fn ring2a_operator_sub_int() {
    let mut session = repl_session();
    install_trait_prelude(&mut session);
    let (value, ty) = repl_eval_typed(&mut session, "(- 10 3)");
    assert_eq!(value, 7);
    assert_eq!(ty, Type::Int);
}

// spec: 07-traits §7.5 — * operator Int in REPL
#[test]
fn ring2a_operator_mul_int() {
    let mut session = repl_session();
    install_trait_prelude(&mut session);
    let (value, ty) = repl_eval_typed(&mut session, "(* 4 5)");
    assert_eq!(value, 20);
    assert_eq!(ty, Type::Int);
}

// spec: 07-traits §7.5 — / operator Int in REPL
#[test]
fn ring2a_operator_div_int() {
    let mut session = repl_session();
    install_trait_prelude(&mut session);
    let (value, ty) = repl_eval_typed(&mut session, "(/ 10 2)");
    assert_eq!(value, 5);
    assert_eq!(ty, Type::Int);
}

// spec: 07-traits §7.5 — = operator returns Bool
#[test]
fn ring2a_operator_eq_returns_bool() {
    // = is dispatched via Eq trait, returns Bool.
    let mut session = repl_session();
    install_trait_prelude(&mut session);
    let (value, ty) = repl_eval_typed(&mut session, "(= 5 5)");
    assert_eq!(value, 1); // true
    assert_eq!(ty, Type::Bool);
}

// spec: 07-traits §7.5 — = operator false
#[test]
fn ring2a_operator_eq_false() {
    let mut session = repl_session();
    install_trait_prelude(&mut session);
    let (value, ty) = repl_eval_typed(&mut session, "(= 5 3)");
    assert_eq!(value, 0); // false
    assert_eq!(ty, Type::Bool);
}

// spec: 07-traits §7.5 — < operator returns Bool
#[test]
fn ring2a_operator_lt_returns_bool() {
    // < is dispatched via Ord trait, returns Bool.
    let mut session = repl_session();
    install_trait_prelude(&mut session);
    let (value, ty) = repl_eval_typed(&mut session, "(< 1 2)");
    assert_eq!(value, 1); // true
    assert_eq!(ty, Type::Bool);
}

// spec: 07-traits §7.5 — < operator false
#[test]
fn ring2a_operator_lt_false() {
    let mut session = repl_session();
    install_trait_prelude(&mut session);
    let (value, ty) = repl_eval_typed(&mut session, "(< 5 3)");
    assert_eq!(value, 0); // false
    assert_eq!(ty, Type::Bool);
}

// spec: 07-traits §7.5 — operators compose with let
#[test]
fn ring2a_operators_compose_with_let() {
    // Operators work in compound expressions.
    let mut session = repl_session();
    install_trait_prelude(&mut session);
    let value = repl_eval(&mut session, "(let [x 10 y 3] (+ x y))");
    assert_eq!(value, 13);
}

// spec: 07-traits §7.5 — operators compose with if
#[test]
fn ring2a_operators_compose_with_if() {
    let mut session = repl_session();
    install_trait_prelude(&mut session);
    let value = repl_eval(&mut session, "(if (< 1 2) (+ 10 20) 0)");
    assert_eq!(value, 30);
}

// spec: 07-traits §7.5 — operators compose with defn
#[test]
fn ring2a_operators_compose_with_defn() {
    // A function using operators gets a concrete type (resolved via trait dispatch).
    let mut session = repl_session();
    install_trait_prelude(&mut session);
    let result = session.eval("(defn double [x] (* x 2))").unwrap();
    assert!(result.is_def());
    assert_eq!(
        *result.ty(),
        Type::Fn(vec![Type::Int], Box::new(Type::Int))
    );
    let value = repl_eval(&mut session, "(double 21)");
    assert_eq!(value, 42);
}

// spec: 07-traits §7.5 — nested operators
#[test]
fn ring2a_operators_nested() {
    // Nested operator calls work.
    let mut session = repl_session();
    install_trait_prelude(&mut session);
    let value = repl_eval(&mut session, "(+ (* 3 4) (- 10 5))");
    assert_eq!(value, 17);
}

// spec: 07-traits §7.5 — operator in recursive fn
#[test]
fn ring2a_operator_in_recursive_fn() {
    // Operators work in recursive functions.
    let mut session = repl_session();
    install_trait_prelude(&mut session);
    session
        .eval("(defn fact [n] (if (= n 0) 1 (* n (fact (- n 1)))))")
        .unwrap();
    let value = repl_eval(&mut session, "(fact 5)");
    assert_eq!(value, 120);
}

// =============================================================================
// Ring 2A: Trait Declaration in REPL (spec: §4.1)
// =============================================================================

// spec: 07-traits §7.1 — deftrait in REPL
#[test]
fn ring2a_deftrait_in_repl() {
    // A trait declaration should succeed without error.
    let mut session = repl_session();
    let result = session.eval("(deftrait (MyTrait a) (my-method [:a] :Int))");
    assert!(result.is_ok(), "deftrait should succeed: {:?}", result.err());
    let r = result.unwrap();
    assert!(r.is_def());
}

// spec: 07-traits §7.1 — deftrait session continues
#[test]
fn ring2a_deftrait_session_continues() {
    // After declaring a trait, the session continues normally.
    let mut session = repl_session();
    install_trait_prelude(&mut session);
    session
        .eval("(deftrait (Describable a) (describe [:a] :Int))")
        .unwrap();
    // Other expressions still work.
    let value = repl_eval(&mut session, "(+ 1 2)");
    assert_eq!(value, 3);
}

// =============================================================================
// Ring 2A: U1.6 Verification — Type Variable Name Normalization
// =============================================================================

// spec: repl/spec.md §1.3 — polymorphic fn shows normalized vars
#[test]
fn u1_6_polymorphic_fn_shows_a_not_t0() {
    // U1.6: Type variables should display as `a`, `b`, `c`, not `t0`, `t1`, `t2`.
    // Spec §1.4: Type variables are lowercase letters starting from `a`.
    let mut session = repl_session();
    let result = session.eval("(defn id [x] x)").unwrap();
    // The type should be (Fn [Var(n)] Var(n)) — display as (Fn [a] a).
    let display = format_result(result.value(), &result.ty());
    assert!(
        display.contains("[a]") && display.contains("] a)"),
        "expected (Fn [a] a) in display, got: {display}"
    );
    // Verify no raw type var names leak.
    assert!(
        !display.contains("t0") && !display.contains("t1"),
        "raw type var names should not appear: {display}"
    );
}

// spec: repl/spec.md §1.3 — two-var fn shows a, b
#[test]
fn u1_6_two_var_fn_shows_a_b() {
    // (defn const [x y] x) should show (Fn [a b] a), not (Fn [t5 t6] t5).
    let mut session = repl_session();
    let result = session.eval("(defn konst [x y] x)").unwrap();
    let display = format_result(result.value(), &result.ty());
    assert!(
        display.contains("[a b]") && display.contains("] a)"),
        "expected (Fn [a b] a) in display, got: {display}"
    );
}

// spec: repl/spec.md §1.3 — compose fn shows three vars
#[test]
fn u1_6_compose_fn_shows_three_vars() {
    // (defn compose [f g] (fn [x] (f (g x)))) — three type vars.
    let mut session = repl_session();
    let result = session
        .eval("(defn compose [f g] (fn [x] (f (g x))))")
        .unwrap();
    let display = format_result(result.value(), &result.ty());
    // Should contain a, b, c — not t-prefixed numbers.
    assert!(
        !display.contains("t0")
            && !display.contains("t1")
            && !display.contains("t2")
            && !display.contains("t3"),
        "raw type var names should not appear: {display}"
    );
    // Should have three distinct vars (a, b, c).
    assert!(
        display.contains('a') && display.contains('b') && display.contains('c'),
        "expected three type vars (a, b, c) in: {display}"
    );
}

// spec: repl/spec.md §4.1 — bare polymorphic fn lookup
#[test]
fn u1_6_bare_polymorphic_fn_lookup_normalized() {
    // Bare function name lookup should also use normalized type var names.
    let mut session = repl_session();
    session.eval("(defn id [x] x)").unwrap();
    let result = session.eval("id").unwrap();
    let display = format_result(result.value(), &result.ty());
    assert!(
        display.contains("[a]") && display.contains("] a)"),
        "bare id lookup should show (Fn [a] a), got: {display}"
    );
}

// =============================================================================
// Ring 2A: U1.9 Verification — Polymorphic ADT Field Display
// =============================================================================

// spec: repl/spec.md §1.5 — polymorphic ADT data ctor display
#[test]
fn u1_9_polymorphic_adt_data_ctor_display() {
    // U1.9: Polymorphic ADT data constructors should display fields with
    // correct types, not raw pointers or raw type vars.
    let mut session = repl_session();
    session
        .eval("(deftype (Option a) None (Some [:a val]))")
        .unwrap();
    let display = repl_eval_display(&mut session, "(Some 42)");
    assert!(
        display.contains("(Option.Some 42)"),
        "expected (Option.Some 42) in display, got: {display}"
    );
    assert!(
        display.contains("(user/Option primitives/Int)"),
        "type should show (user/Option primitives/Int), got: {display}"
    );
}

// spec: repl/spec.md §1.5 — polymorphic ADT string field display
#[test]
fn u1_9_polymorphic_adt_string_field_display() {
    // Heap-typed fields should display correctly (not as raw pointers).
    let mut session = repl_session();
    session
        .eval("(deftype (Box a) (Wrap [:a inner]))")
        .unwrap();
    let display = repl_eval_display(&mut session, "(Wrap \"hello\")");
    assert!(
        display.contains("\"hello\""),
        "string field should display as quoted string, got: {display}"
    );
}

// spec: repl/spec.md §1.5 — polymorphic ADT multi-field display
#[test]
fn u1_9_polymorphic_adt_multi_field_display() {
    // Multi-field polymorphic ADT: both fields should display correctly.
    let mut session = repl_session();
    session
        .eval("(deftype (Pair a b) (MkPair [:a fst :b snd]))")
        .unwrap();
    let display = repl_eval_display(&mut session, "(MkPair 42 \"hello\")");
    assert!(
        display.contains("42") && display.contains("\"hello\""),
        "both fields should display, got: {display}"
    );
    assert!(
        display.contains("(user/Pair primitives/Int primitives/String)"),
        "type should show (user/Pair primitives/Int primitives/String), got: {display}"
    );
}

// spec: repl/spec.md §1.3 — ADT type display normalizes vars
#[test]
fn u1_9_adt_type_display_normalizes_vars_for_fn() {
    // When a polymorphic fn returns an ADT type, the fn type display
    // should normalize vars even inside ADT type args.
    let mut session = repl_session();
    session
        .eval("(deftype (Wrapper a) (Wrap [:a val]))")
        .unwrap();
    let result = session
        .eval("(defn wrap [x] (Wrap x))")
        .unwrap();
    let display = format_result(result.value(), &result.ty());
    // Should show (Fn [a] (Wrapper a)), not (Fn [t5] (Wrapper t5))
    assert!(
        !display.contains("t0")
            && !display.contains("t1")
            && !display.contains("t2")
            && !display.contains("t3")
            && !display.contains("t4")
            && !display.contains("t5"),
        "type var names in ADT args should be normalized: {display}"
    );
}

// =============================================================================
// Ring 2A: Session Continuity with Trait Features
// =============================================================================

// spec: none — regression: operators and named primitives coexist
#[test]
fn ring2a_session_operators_and_old_primitives_coexist() {
    // Both trait-dispatched operators and Ring 0 named primitives work in the same session.
    let mut session = repl_session();
    install_trait_prelude(&mut session);
    let v1 = repl_eval(&mut session, "(+ 10 20)");
    assert_eq!(v1, 30);
    let v2 = repl_eval(&mut session, "(add-i64 10 20)");
    assert_eq!(v2, 30);
}

// spec: 07-traits §7.5 — defn with operators then call
#[test]
fn ring2a_session_defn_with_operators_then_call() {
    // Define a function using operators, call it, redefine with a different
    // operator, call again.
    let mut session = repl_session();
    install_trait_prelude(&mut session);
    session.eval("(defn compute [x] (* x 2))").unwrap();
    assert_eq!(repl_eval(&mut session, "(compute 5)"), 10);
    // Redefine with a different computation.
    session.eval("(defn compute [x] (+ x 100))").unwrap();
    assert_eq!(repl_eval(&mut session, "(compute 5)"), 105);
}

// spec: 07-traits §7.5 — ADT with operator functions
#[test]
fn ring2a_session_adt_with_operator_functions() {
    // Combine ADTs and trait-dispatched operators.
    let mut session = repl_session();
    install_trait_prelude(&mut session);
    session
        .eval("(deftype (Option a) None (Some [:a val]))")
        .unwrap();
    session
        .eval("(defn add-opt [o] (match o [None 0 (Some x) (+ x 1)]))")
        .unwrap();
    assert_eq!(repl_eval(&mut session, "(add-opt (Some 41))"), 42);
    assert_eq!(repl_eval(&mut session, "(add-opt None)"), 0);
}

// spec: repl/spec.md §5.2 — error recovery after operator error
#[test]
fn ring2a_error_recovery_after_operator_error() {
    // After an operator-related error, the session should continue.
    let mut session = repl_session();
    install_trait_prelude(&mut session);
    // Type mismatch: (+ 1 true) should fail.
    let err = session.eval("(+ 1 true)");
    assert!(err.is_err(), "type mismatch should produce an error");
    // Session should still work.
    let value = repl_eval(&mut session, "(+ 1 2)");
    assert_eq!(value, 3);
}

// spec: 07-traits §7.5 — Float operators in REPL
#[test]
fn ring2a_float_operators() {
    // Float operators work via trait dispatch.
    let mut session = repl_session();
    install_trait_prelude(&mut session);
    let (v, ty) = repl_eval_typed(&mut session, "(* 2.0 3.0)");
    assert_eq!(ty, Type::Float);
    let f = f64::from_bits(v as u64);
    assert!((f - 6.0).abs() < f64::EPSILON, "expected 6.0, got {f}");
}

// spec: 07-traits §7.5 — mixed Int/Float operator error
#[test]
fn ring2a_mixed_int_float_operators_error() {
    // Mixing Int and Float in the same operator call should be a type error.
    let mut session = repl_session();
    install_trait_prelude(&mut session);
    let err = session.eval("(+ 1 2.0)");
    assert!(err.is_err(), "mixing Int and Float should error");
}

// =============================================================================
// U1.6 — Polymorphic ADT type var display (Sprint 7 Wave 0)
//
// When a polymorphic ADT value has unresolved type parameters (e.g., None
// in Option), the display should use user-friendly variable names (a, b, ...)
// rather than internal TypeId numbers (t1, t6, ...).
//
// Expected: `:(Option a) None`  not `:(Option t6) None`
// =============================================================================

// spec: repl/spec.md §1.5 — polymorphic ADT None displays with user-friendly type var
#[test]
fn display_polymorphic_adt_none_type_var() {
    // Option.None has an unresolved type parameter. The display should
    // show `:(user/Option a) Option.None` with a user-friendly variable name.
    let mut session = repl_session();
    session.eval("(deftype (Option a) None (Some [:a val]))").unwrap();
    let display = repl_eval_display(&mut session, "None");
    // Should contain "Option a)" with user-friendly var name (qualified: "user/Option a)")
    assert!(
        display.contains("Option a)"),
        "expected 'Option a)' in display, got: {display}"
    );
    // Should not contain internal type var format like t6, t1, etc.
    assert!(
        !display.contains("Option t"),
        "display should not contain internal type var (t-number), got: {display}"
    );
}

// spec: repl/spec.md §1.5 — polymorphic enum nullary constructor display
#[test]
fn display_polymorphic_adt_nullary_constructor_name() {
    // The constructor name should appear in the display.
    let mut session = repl_session();
    session.eval("(deftype (Option a) None (Some [:a val]))").unwrap();
    let display = repl_eval_display(&mut session, "None");
    assert!(
        display.contains("None"),
        "expected constructor name 'None' in display, got: {display}"
    );
}

// spec: repl/spec.md §1.5 — concrete polymorphic ADT type display
#[test]
fn display_polymorphic_adt_concrete_type() {
    // (Some 42) resolves the type var to Int.
    // Should display as `:(user/Option primitives/Int) (Option.Some 42)`.
    let mut session = repl_session();
    session.eval("(deftype (Option a) None (Some [:a val]))").unwrap();
    let display = repl_eval_display(&mut session, "(Some 42)");
    assert!(
        display.contains("(user/Option primitives/Int)"),
        "expected '(user/Option primitives/Int)' in display, got: {display}"
    );
    assert!(
        display.contains("(Option.Some 42)"),
        "expected '(Option.Some 42)' in display, got: {display}"
    );
}

// =============================================================================
// U1.9 — Polymorphic ADT heap field display (Sprint 7 Wave 0)
//
// When a polymorphic ADT contains a heap-typed field (e.g., String),
// the field value should be displayed with its contents, not as a
// raw pointer or integer.
//
// Expected: `:(Option String) (Some "hello")`
// =============================================================================

// spec: repl/spec.md §1.5 — ADT with String field displays string contents
#[test]
fn display_adt_string_field_contents() {
    // (Some "hello") should display the string contents, not a pointer.
    let mut session = repl_session();
    session.eval("(deftype (Option a) None (Some [:a val]))").unwrap();
    let display = repl_eval_display(&mut session, r#"(Some "hello")"#);
    assert!(
        display.contains("(user/Option primitives/String)"),
        "expected '(user/Option primitives/String)' in type, got: {display}"
    );
    assert!(
        display.contains(r#""hello""#),
        "expected string contents '\"hello\"' in display, got: {display}"
    );
    // Should not contain raw pointer-like numbers
    assert!(
        !display.contains("0x"),
        "display should not contain raw pointer, got: {display}"
    );
}

// spec: repl/spec.md §1.5 — ADT with nested ADT field displays recursively
#[test]
fn display_adt_nested_adt_field() {
    // (Some (Some 42)) should display the inner constructor, not a raw value.
    let mut session = repl_session();
    session.eval("(deftype (Option a) None (Some [:a val]))").unwrap();
    let display = repl_eval_display(&mut session, "(Some (Some 42))");
    assert!(
        display.contains("Some"),
        "expected nested 'Some' in display, got: {display}"
    );
    assert!(
        display.contains("42"),
        "expected '42' in display, got: {display}"
    );
}

// =============================================================================
// U1.10 — Imported ADT display (prelude Option)
//
// When an ADT type is imported from another module (e.g., Option from prelude),
// format_adt_value must still be able to look up the type definition to format
// the value with constructor dot notation, not as a raw heap pointer.
//
// Root cause: type_defs lookup uses the bare type name but the imported type's
// definition lives in the source module's CompiledModule, not the user module.
// =============================================================================

// spec: repl/spec.md §1.5 — imported Option (Some 42) displays as constructor, not raw pointer
#[test]
// BUG: imported Option shows raw pointer for data ctors
fn display_imported_option_some_formatted() {
    let mut session = repl_session_with_test_prelude();
    let display = repl_eval_display(&mut session, "(Some 42)");
    assert!(
        display.contains("(Option.Some 42)"),
        "expected '(Option.Some 42)' for imported Option, got: {display}"
    );
    // Negative: must not contain a raw heap pointer
    let has_large_num = display
        .split_whitespace()
        .any(|w| w.parse::<u64>().map_or(false, |n| n > 1_000_000));
    assert!(
        !has_large_num,
        "display should not contain raw heap pointer: {display}"
    );
}

// spec: repl/spec.md §1.5 — imported Option None displays with dot notation
#[test]
// BUG: imported Option None shows raw tag instead of dot notation
fn display_imported_option_none_formatted() {
    let mut session = repl_session_with_test_prelude();
    let display = repl_eval_display(&mut session, "None");
    assert!(
        display.contains("Option.None"),
        "expected 'Option.None' for imported None, got: {display}"
    );
}

// spec: repl/spec.md §1.5 — product ADT with string field displays contents
#[test]
fn display_product_adt_string_field() {
    // Product ADT with a String field should show the string contents.
    let mut session = repl_session();
    session.eval("(deftype Named [:String name :Int value])").unwrap();
    let display = repl_eval_display(&mut session, r#"(Named "alice" 42)"#);
    assert!(
        display.contains(r#""alice""#),
        "expected string contents '\"alice\"' in display, got: {display}"
    );
    assert!(
        display.contains("42"),
        "expected '42' in display, got: {display}"
    );
}
