// ===== FIXME 0135 harvest (backend part): the sparkability-analysis
// assertions from the quarantined `tests/legacy/lenient.rs`. The
// spark-*execution* parts of that file (value-correctness via
// `repl_eval`, the `CRANELISP_NO_LENIENT` process-global env-var, IO
// scheduling) need the int worker/session and remain in 0135's
// 0109-adjacent remainder. These tests exercise the pure
// `find_sparkable_bindings` analysis pass directly — no session, no
// runtime, no env-var — per `memory/project_test_strategy.md`. =====

use super::{find_sparkable_args, find_sparkable_bindings};
use cranelisp_types::{ConcreteType, MonoExpr, Span, Symbol};
use std::collections::HashSet;

fn sym(s: &str) -> Symbol {
    Symbol::from(s)
}

fn span() -> Span {
    Span::new(0, 0)
}

fn var(name: Symbol) -> MonoExpr {
    MonoExpr::Var { name, span: span(), resolved_call: None, ty: ConcreteType::Int }
}

/// A function-call binding `(f arg)` against a named callee.
fn call(callee: &str) -> MonoExpr {
    MonoExpr::Apply {
        callee: Box::new(var(sym(callee))),
        args: vec![],
        span: span(),
        resolved_call: None,
        ty: ConcreteType::Int,
    }
}

/// A function-call binding that references `dep_var` as an argument, so
/// it depends on any earlier binding named `dep_var`.
fn call_with_arg(callee: &str, dep_var: &str) -> MonoExpr {
    MonoExpr::Apply {
        callee: Box::new(var(sym(callee))),
        args: vec![var(sym(dep_var))],
        span: span(),
        resolved_call: None,
        ty: ConcreteType::Int,
    }
}

/// An integer literal expression — never sparkable (not an `Apply`).
fn literal(value: i64) -> MonoExpr {
    MonoExpr::IntLit { value, span: span(), ty: ConcreteType::Int }
}

// spec: design/backend/lenient-eval.md §2 — two independent calls are sparkable
//
// Two data-independent non-trivial function calls clear the
// min-2-sparkable threshold and are both returned.
#[test]
fn two_independent_calls_are_sparkable() {
    let bindings = vec![(sym("a"), call("compute")), (sym("b"), call("derive"))];
    let ctors = HashSet::new();
    assert_eq!(find_sparkable_bindings(&bindings, &ctors), vec![0, 1]);
}

// spec: design/backend/lenient-eval.md §2 — below the min-2 threshold yields nothing
//
// A single sparkable binding (the other is a cheap builtin) is below the
// threshold; the analysis returns an empty set (sequential codegen).
#[test]
fn single_sparkable_below_threshold_returns_empty() {
    let bindings = vec![(sym("a"), call("compute")), (sym("b"), call("+"))];
    let ctors = HashSet::new();
    assert!(find_sparkable_bindings(&bindings, &ctors).is_empty());
}

// spec: design/backend/lenient-eval.md §2 — dependent bindings are not sparkable
//
// The second binding references the first (`b` uses `a`), so it depends on
// an earlier binding and is excluded — leaving fewer than 2, so empty.
#[test]
fn dependent_binding_is_not_sparkable() {
    let bindings = vec![
        (sym("a"), call("compute")),
        (sym("b"), call_with_arg("derive", "a")),
    ];
    let ctors = HashSet::new();
    assert!(
        find_sparkable_bindings(&bindings, &ctors).is_empty(),
        "a dependent binding must drop the set below the spark threshold"
    );
}

// spec: design/backend/lenient-eval.md §2 — cheap builtins are not worth sparking
//
// Negative guard: arithmetic/comparison builtins (`+`, `<`, ...) are
// single-instruction and excluded even when there are two of them.
#[test]
fn cheap_builtins_are_not_sparkable() {
    let bindings = vec![(sym("a"), call("+")), (sym("b"), call("<"))];
    let ctors = HashSet::new();
    assert!(
        find_sparkable_bindings(&bindings, &ctors).is_empty(),
        "cheap builtins must not be sparked"
    );
}

// spec: design/backend/lenient-eval.md §2 — ADT constructors are not worth sparking
//
// Negative guard: calls whose callee is a known constructor name are
// excluded (alloc+tag, not real work). With both bindings being
// constructors, nothing is sparkable.
#[test]
fn constructors_are_not_sparkable() {
    let mut ctors = HashSet::new();
    ctors.insert(sym("Some"));
    ctors.insert(sym("Cons"));
    let bindings = vec![(sym("a"), call("Some")), (sym("b"), call("Cons"))];
    assert!(
        find_sparkable_bindings(&bindings, &ctors).is_empty(),
        "constructor calls must not be sparked"
    );
}

// spec: design/backend/lenient-eval.md §2 — literals and var-refs are not sparkable
//
// Negative guard: non-Apply expressions (literals, bare variable
// references) are never sparkable regardless of count.
#[test]
fn literals_and_var_refs_are_not_sparkable() {
    let bindings = vec![
        (sym("a"), MonoExpr::IntLit { value: 1, span: span(), ty: ConcreteType::Int }),
        (sym("b"), var(sym("x"))),
    ];
    let ctors = HashSet::new();
    assert!(find_sparkable_bindings(&bindings, &ctors).is_empty());
}

// spec: design/backend/lenient-eval.md §2 — independence is positional, not global
//
// A later binding that does NOT reference an earlier one stays sparkable;
// mixing a sparkable independent pair around a dependent middle binding
// returns exactly the independent indices.
#[test]
fn mixed_independent_and_dependent_returns_only_independent() {
    let bindings = vec![
        (sym("a"), call("compute")),
        (sym("b"), call_with_arg("derive", "a")), // depends on a → excluded
        (sym("c"), call("evaluate")),             // independent → sparkable
    ];
    let ctors = HashSet::new();
    // a (idx 0) and c (idx 2) are independent + non-trivial → both sparked.
    assert_eq!(find_sparkable_bindings(&bindings, &ctors), vec![0, 2]);
}

// ===== `find_sparkable_args` — the apply-argument sibling (Sprint 92,
// lenient-eval.md §2.5.2). Apply args bind nothing into sibling scope, so all
// args are mutually independent by construction: there is NO depends_on_earlier
// analogue (that `let`-path test class is correctly absent here). Independence
// collapses to the cost heuristic + the ≥2 gate, both shared with the `let`
// path (Principle 7). =====

// spec: design/backend/lenient-eval.md §2.5.2 — two independent expensive args
//
// Two data-independent non-trivial calls clear the ≥2 gate → both sparked.
#[test]
fn sparkable_args_two_expensive_independent() {
    let args = vec![call("compute"), call("derive")];
    let ctors = HashSet::new();
    assert_eq!(find_sparkable_args(&args, &ctors), vec![0, 1]);
}

// spec: design/backend/lenient-eval.md §2.5.2 — the FIXME 0424(i) canonical case
//
// `(Pair (fib a) (fib b))`: the outer constructor `Pair` is the callee
// (irrelevant to arg sparkability) — the two `(fib …)` ARGS are what spark.
#[test]
fn sparkable_args_constructor_pair_case() {
    let args = vec![call("fib"), call("fib")];
    let ctors = HashSet::new();
    assert_eq!(find_sparkable_args(&args, &ctors), vec![0, 1]);
}

// spec: design/backend/lenient-eval.md §2.5.2 — var-ref arg excluded; ≥2 still holds
//
// A bare variable reference is not an `Apply` → excluded; the two flanking
// calls still clear the ≥2 gate, so exactly [0, 2] spark.
#[test]
fn sparkable_args_three_mixed_var_skipped() {
    let args = vec![call("fib"), var(sym("x")), call("derive")];
    let ctors = HashSet::new();
    assert_eq!(find_sparkable_args(&args, &ctors), vec![0, 2]);
}

// spec: design/backend/lenient-eval.md §2.1 — below the ≥2 gate yields nothing
//
// Only ONE candidate (`compute`); the `+` arg is a cheap builtin. Below the
// gate → empty (the single-expensive arg never pays spark overhead).
#[test]
fn sparkable_args_single_expensive_below_gate() {
    let args = vec![call("compute"), call("+")];
    let ctors = HashSet::new();
    assert!(find_sparkable_args(&args, &ctors).is_empty());
}

// spec: design/backend/lenient-eval.md §2.2 — cheap builtins are not worth sparking
//
// `CHEAP_BUILTINS` are the operator SYMBOLS (`+`, `<`, …), not the `*-i64`
// primitive names. Both args are cheap-builtin calls → nothing sparks.
#[test]
fn sparkable_args_all_cheap_empty() {
    let args = vec![call("+"), call("<")];
    let ctors = HashSet::new();
    assert!(find_sparkable_args(&args, &ctors).is_empty());
}

// spec: design/backend/lenient-eval.md §2.2 — constructor-callee args excluded
//
// Args whose callee is a known constructor are alloc+tag, not real work →
// excluded exactly as in the `let` path. Both constructor calls → empty.
#[test]
fn sparkable_args_constructor_arg_excluded() {
    let mut ctors = HashSet::new();
    ctors.insert(sym("Some"));
    ctors.insert(sym("Cons"));
    let args = vec![call("Some"), call("Cons")];
    assert!(find_sparkable_args(&args, &ctors).is_empty());
}

// spec: design/backend/lenient-eval.md §2.2 — literal + var-ref args excluded
//
// A var ref and an int literal are not `Apply`s → excluded, leaving only ONE
// real candidate (`compute`) → below the ≥2 gate → empty.
#[test]
fn sparkable_args_literal_var_excluded() {
    let args = vec![var(sym("x")), literal(1), call("compute")];
    let ctors = HashSet::new();
    assert!(find_sparkable_args(&args, &ctors).is_empty());
}
