// ===== FIXME 0135 harvest (backend part): the sparkability-analysis
// assertions from the quarantined `tests/legacy/lenient.rs`. The
// spark-*execution* parts of that file (value-correctness via
// `repl_eval`, the `CRANELISP_NO_LENIENT` process-global env-var, IO
// scheduling) need the int worker/session and remain in 0135's
// 0109-adjacent remainder. These tests exercise the pure
// `find_sparkable_bindings` analysis pass directly — no session, no
// runtime, no env-var — per `memory/project_test_strategy.md`. =====

use super::{
    find_sparkable_args, find_sparkable_args_with, find_sparkable_bindings,
    find_sparkable_bindings_with, spark_density,
};
use cranelisp_types::{ConcreteType, FQTypeName, MonoExpr, Span, Symbol};
use std::collections::HashSet;

fn sym(s: &str) -> Symbol {
    Symbol::from(s)
}

/// The callee name of an `Apply` candidate (for the synthetic admission
/// predicate below). Non-`Apply` / computed callee → `None`.
fn callee_name(e: &MonoExpr) -> Option<&str> {
    match e {
        MonoExpr::Apply { callee, .. } => match callee.as_ref() {
            MonoExpr::Var { name, .. } => Some(name.as_ref()),
            _ => None,
        },
        _ => None,
    }
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
        confined: None,
        escapes: None,
        provenance: None,
        unique_static: None,
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
        confined: None,
        escapes: None,
        provenance: None,
        unique_static: None,
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

// spec: design/arch/dotted-ctor-canonical-keys.md §10.4 (BU-2, I-1 exclusion) —
// under canonical keying the ctor-exclusion set holds bare terminal names
// (`bare_member_name` of the storage key `Maybe.Some`), and the callee is
// compared through the SAME grammar, so a sum-ctor call written bare (`Some`),
// dotted (`Maybe.Some`), OR module-qualified (`m/Some`) is EXCLUDED from the
// sparkable set — a real function call alongside it is not enough to admit it.
// Without the two-sided normalisation the dotted/FQ ctor calls would leak in.
#[test]
fn canonically_keyed_sum_ctor_calls_are_excluded_from_sparkable_set() {
    // The exclusion set is what `collect_module_constructors` now produces:
    // `bare_member_name("Maybe.Some") == "Some"`.
    let ctors: HashSet<Symbol> =
        [sym(cranelisp_types::bare_member_name("Maybe.Some"))].into_iter().collect();
    assert!(ctors.contains(&sym("Some")), "the exclusion set holds the bare terminal name");

    // Two ctor calls (bare + dotted) alongside — both must be excluded (the
    // set is non-empty only if a ctor leaked in). A real `compute` call keeps
    // the min-2 gate reachable so a leak would show as a non-empty result.
    let bindings = vec![
        (sym("a"), call("Some")),        // bare sum-ctor call
        (sym("b"), call("Maybe.Some")),  // dotted canonical sum-ctor call
        (sym("c"), call("mmod/Some")),   // module-qualified sum-ctor call
    ];
    assert!(
        find_sparkable_bindings(&bindings, &ctors).is_empty(),
        "every sum-ctor call form (bare / dotted / FQ) is excluded via bare_member_name"
    );

    // Control: a genuine two-call set with NO ctor names IS sparkable — proving
    // the exclusion above is the ctor filter, not an unrelated gate.
    let real = vec![(sym("a"), call("compute")), (sym("b"), call("derive"))];
    assert_eq!(find_sparkable_bindings(&real, &ctors), vec![0, 1]);
}

// spec: design/backend/lenient-eval.md §2.6 — dependent-on-sparked is admitted
//
// FIXME 0424 limit #2: the second binding references the first (`b` uses `a`),
// and `a` is itself sparked (an independent non-trivial call), so `b` is
// admitted as a *dependent* spark — its dependency `a` is available as an IVar
// to force on demand. Both indices spark. (Pre-S94 this returned empty; the
// relaxed admission rule is what the par-reduce/divide-and-conquer substrate
// needs.)
#[test]
fn dependent_binding_on_sparked_is_admitted() {
    let bindings = vec![
        (sym("a"), call("compute")),
        (sym("b"), call_with_arg("derive", "a")),
    ];
    let ctors = HashSet::new();
    assert_eq!(
        find_sparkable_bindings(&bindings, &ctors),
        vec![0, 1],
        "a dependent binding whose dependency is sparked must itself be sparkable"
    );
}

// spec: design/backend/lenient-eval.md §2.6 — dependent-on-NON-sparked excluded
//
// Negative face of the carve-out: `a` is a cheap builtin (`+`) → NOT sparked, so
// it is bound only as an ordinary `Value` in Phase 2 that a concurrent thunk
// cannot see. The dependent `b` (which references `a`) is therefore EXCLUDED even
// though it is itself worth sparking. The two independent expensive calls `c`/`d`
// keep the set above the ≥2 gate, isolating that `b` (index 1) is dropped
// specifically because its dependency is non-sparked — not by the threshold.
#[test]
fn dependent_binding_on_non_sparked_is_excluded() {
    let bindings = vec![
        (sym("a"), call("+")),                      // cheap → not sparked
        (sym("b"), call_with_arg("derive", "a")),   // dep on non-sparked → excluded
        (sym("c"), call("compute")),                // independent → sparked
        (sym("d"), call("evaluate")),               // independent → sparked
    ];
    let ctors = HashSet::new();
    assert_eq!(
        find_sparkable_bindings(&bindings, &ctors),
        vec![2, 3],
        "a dependent binding whose dependency is NOT sparked must be excluded"
    );
}

// spec: design/backend/lenient-eval.md §2.6 — the cost heuristic still gates
//
// A dependent binding that is itself a cheap builtin is excluded by the cost
// heuristic regardless of its dependency being sparked: `b` = `(+ a)` references
// the sparked `a` but is not worth sparking, so only `a` remains → below the ≥2
// gate → empty. Confirms §2.2 is unchanged by the limit-#2 relaxation.
#[test]
fn dependent_but_cheap_binding_is_excluded() {
    let bindings = vec![
        (sym("a"), call("compute")),
        (sym("b"), call_with_arg("+", "a")), // cheap callee → not worth sparking
    ];
    let ctors = HashSet::new();
    assert!(
        find_sparkable_bindings(&bindings, &ctors).is_empty(),
        "a cheap dependent binding must not be sparked even when its dep is sparked"
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

// spec: design/backend/lenient-eval.md §2.6 — a dependent chain over sparked deps
//
// FIXME 0424 limit #2: `a` is independent (sparked); `b` depends on the sparked
// `a` (admitted as a dependent spark); `c` is independent (sparked). All three
// are sparkable — the chain pipelines `b`'s independent sub-work against `a`'s
// computation while `b`'s thunk forces `a` on demand. (Pre-S94 the dependent `b`
// was excluded and this returned `[0, 2]`.)
#[test]
fn dependent_chain_over_sparked_deps_all_admitted() {
    let bindings = vec![
        (sym("a"), call("compute")),
        (sym("b"), call_with_arg("derive", "a")), // dep on sparked a → admitted
        (sym("c"), call("evaluate")),             // independent → sparked
    ];
    let ctors = HashSet::new();
    assert_eq!(find_sparkable_bindings(&bindings, &ctors), vec![0, 1, 2]);
}

// ===== `_with` cores (S104 Wave 1, lenient-eval.md §2.8.2/§2.8.6) — the
// admission-predicate-parametric seam M-static plugs into. These pin that the
// `let`-path independence carve-out (§2.6) and the ≥2 gate compose with an
// ARBITRARY `worth` predicate (here a synthetic M-static-style filter that
// admits only recursive callees `rec*` and declines flat accessors), verifying
// the composition Principle 7 keeps single-source across both admission
// filters. The classifier itself is exercised on the real `FnCompiler` in
// `utilization.rs` tests. =====

// spec: design/backend/lenient-eval.md §2.8.2 — through the seam, recursive
// candidates admitted / flat accessor declined / ≥2 gate passes.
#[test]
fn find_sparkable_args_with_admits_recursive_declines_flat() {
    let args = vec![call("rec-a"), call("cell-at"), call("rec-b")];
    let admit = |e: &MonoExpr| callee_name(e).is_some_and(|n| n.starts_with("rec"));
    assert_eq!(find_sparkable_args_with(&args, admit), vec![0, 2]);
}

// spec: design/backend/lenient-eval.md §2.8.2 — a lone admitted candidate is
// below the ≥2 gate → no sparks, identical composition for any predicate.
#[test]
fn find_sparkable_args_with_below_gate_is_empty() {
    let args = vec![call("rec-a"), call("cell-at")];
    let admit = |e: &MonoExpr| callee_name(e).is_some_and(|n| n.starts_with("rec"));
    assert!(find_sparkable_args_with(&args, admit).is_empty());
}

// spec: design/backend/lenient-eval.md §2.6 + §2.8.2 — the dependency-on-sparked
// carve-out composes with an arbitrary admission predicate: a dependent binding
// whose earlier dep was DECLINED by the predicate (a flat accessor here) is
// itself declined, even though its own callee is admitted.
#[test]
fn find_sparkable_bindings_with_dependent_on_declined_dep_is_declined() {
    let bindings = vec![
        (sym("a"), call("cell-at")),               // declined by predicate
        (sym("b"), call_with_arg("rec-b", "a")),   // admitted callee, dep on declined `a`
        (sym("c"), call("rec-c")),                 // independent, admitted
    ];
    let admit = |e: &MonoExpr| callee_name(e).is_some_and(|n| n.starts_with("rec"));
    // `a` declined (flat); `b` depends on non-sparked `a` → declined; only `c`
    // survives → below the ≥2 gate → empty.
    assert!(find_sparkable_bindings_with(&bindings, admit).is_empty());
}

// spec: design/backend/lenient-eval.md §2.6 + §2.8.2 — the dependency-on-sparked
// carve-out admits a dependent binding when its dep WAS admitted by the predicate.
#[test]
fn find_sparkable_bindings_with_dependent_on_sparked_dep_is_admitted() {
    let bindings = vec![
        (sym("a"), call("rec-a")),                 // admitted
        (sym("b"), call_with_arg("rec-b", "a")),   // admitted, dep on sparked `a`
    ];
    let admit = |e: &MonoExpr| callee_name(e).is_some_and(|n| n.starts_with("rec"));
    assert_eq!(find_sparkable_bindings_with(&bindings, admit), vec![0, 1]);
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

// ===== B4 static allocation/RC-density admission axis (lenient-eval.md §2.7;
// ownership-codegen.md §13.4/§13.5 unit matrix). Seam × class grain per
// `memory/feedback_dev_strategy_derived_unit_scenarios.md`: the matrix is
// {facts present / absent} × {alloc-dense / compute-dense / mixed / NoEscape}
// × {threshold boundary}, exercised through BOTH shared call sites
// (`find_sparkable_bindings` = the `let` path, `find_sparkable_args` = the
// apply path) so the single-source property (Principle 7 — one `is_worth_
// sparking`, two callers) is verified from each.
//
// All end-to-end `find_sparkable_*` cells assume the DEFAULT threshold
// (`SPARK_DENSITY_MAX_DEFAULT = 0` since S104 Wave 0 — B4 off by default;
// `CRANELISP_SPARK_DENSITY_MAX` unset in the test process): the axis is inert,
// so every compute-worthy candidate is admitted regardless of density score.
// The `spark_density` cells assert the raw `Option<usize>` and are threshold-
// independent (the score machinery is preserved for the opt-in / Phase-H path). =====

/// A heap-returning (ADT-typed) call `(callee)` carrying the given ownership
/// site facts — the shape of a real spark candidate whose result is an ADT
/// (F4's `(solve-range …)` returns a `SolveResult`). Heap result ⇒ a scored
/// density site (unlike the `Int`-returning `call` helper above — F1/F2's
/// `(reduce-tree …)` accumulator, which is never a scored site).
fn heap_call(callee: &str, escapes: Option<bool>, confined: Option<bool>) -> MonoExpr {
    MonoExpr::Apply {
        callee: Box::new(var(sym(callee))),
        args: vec![],
        span: span(),
        resolved_call: None,
        ty: ConcreteType::ADT(FQTypeName { module: "user".into(), name: "SolveResult".into() }, vec![]),
        confined,
        escapes,
        provenance: None,
        unique_static: None,
    }
}

/// An `Int`-returning call carrying facts — a compute-bound candidate that pass5
/// annotated (engaged) but which allocates nothing at its own site (F1's
/// `(reduce-tree …)`). Scores 0 → always admitted (the §9 compute-win).
fn scalar_call_with_facts(callee: &str, escapes: Option<bool>, confined: Option<bool>) -> MonoExpr {
    MonoExpr::Apply {
        callee: Box::new(var(sym(callee))),
        args: vec![],
        span: span(),
        resolved_call: None,
        ty: ConcreteType::Int,
        confined,
        escapes,
        provenance: None,
        unique_static: None,
    }
}

// --- `spark_density` raw-score matrix (threshold-independent) ---

// spec: design/backend/lenient-eval.md §2.7 — facts-absent ⇒ axis inert (None)
//
// A heap-returning candidate with NO `Some` fact (escapes/confined both None)
// is the CRANELISP_NO_OWNERSHIP / pre-increment-I / facts-absent state: the
// engage gate reports `None`, so the axis never scores it and admission is
// byte-identical to pre-B4. This is the structural byte-identity discipline.
#[test]
fn density_facts_absent_is_inert() {
    // Even a heap ADT result, if pass5 did not annotate it, is inert.
    assert_eq!(spark_density(&heap_call("solve", None, None)), None);
    // The Int-returning fixtures used by every pre-B4 test are likewise inert.
    assert_eq!(spark_density(&call("compute")), None);
}

// spec: design/backend/lenient-eval.md §2.7 — alloc-dense (escaping, non-confined)
//
// The F4 `(solve-range …)` signature: a heap ADT result that escapes
// (`escapes = Some(true)`) and is NOT confined (`confined = None` ⇒ conservative
// atomic, cross-strand). +1 heap-pressure, +1 surviving-RC ⇒ score 2 (dense).
#[test]
fn density_alloc_dense_scores_two() {
    assert_eq!(spark_density(&heap_call("solve-range", Some(true), None)), Some(2));
}

// spec: design/backend/lenient-eval.md §2.7 — compute-dense heap-blind (score 0)
//
// An engaged scalar-returning candidate (`Int` result, pass5-annotated) is NOT
// a scored density site — the density axis does not touch the compute win. It
// is engaged (a `Some` fact) yet scores 0 ⇒ always admitted.
#[test]
fn density_compute_dense_scores_zero() {
    assert_eq!(spark_density(&scalar_call_with_facts("reduce-tree", Some(true), None)), Some(0));
}

// spec: design/backend/lenient-eval.md §2.7 — confined heap ⇒ boundary score 1
//
// A heap result that escapes but whose RC ops are CONFINED (`confined =
// Some(true)` ⇒ non-atomic, no cross-core bounce): +1 heap-pressure, +0
// surviving-RC ⇒ score 1 (== the default threshold ⇒ admitted, not declined).
#[test]
fn density_confined_heap_scores_one() {
    assert_eq!(spark_density(&heap_call("mk", Some(true), Some(true))), Some(1));
}

// spec: design/backend/lenient-eval.md §2.7 — NoEscape ⇒ score 0 (stack/immortal RC)
//
// `escapes = Some(false)` (a B3.4 stack-slot site) contributes 0 to BOTH axes:
// stack/region-served with an immortal-RC header, no allocator contention and
// no surviving RC traffic (§4.2). Engaged (a `Some` fact) but score 0.
#[test]
fn density_noescape_scores_zero() {
    assert_eq!(spark_density(&heap_call("mk-box", Some(false), None)), Some(0));
    // Even a non-confined NoEscape site stays 0 — the NoEscape short-circuit
    // precedes the RC axis.
    assert_eq!(spark_density(&heap_call("mk-box", Some(false), Some(false))), Some(0));
}

// spec: design/backend/lenient-eval.md §2.7 — mixed: nested alloc sites sum
//
// A candidate whose top heap Apply (score 2) also carries a nested escaping
// ConstrADT arg (score 2) sums across the subtree: the density walk recurses
// every child, so an allocation deep in the candidate is counted. 2 + 2 = 4.
#[test]
fn density_mixed_nested_sites_sum() {
    let nested_ctor = MonoExpr::ConstrADT {
        type_name: FQTypeName { module: "user".into(), name: "Cell".into() },
        tag: 0,
        fields: vec![],
        span: span(),
        ty: ConcreteType::ADT(FQTypeName { module: "user".into(), name: "Cell".into() }, vec![]),
        escapes: Some(true),
        confined: None,
        unique_static: None,
    };
    let candidate = MonoExpr::Apply {
        callee: Box::new(var(sym("process"))),
        args: vec![nested_ctor],
        span: span(),
        resolved_call: None,
        ty: ConcreteType::ADT(FQTypeName { module: "user".into(), name: "SolveResult".into() }, vec![]),
        escapes: Some(true),
        confined: None,
        provenance: None,
        unique_static: None,
    };
    assert_eq!(spark_density(&candidate), Some(4));
}

// spec: design/backend/lenient-eval.md §2.7 — borrow-elided Apply skips the RC axis
//
// A projection `Apply` with a `provenance` root (borrow-elided — its RC op is
// elided entirely, §3.3): +1 heap-pressure, but the surviving-RC axis is
// skipped ⇒ score 1, not 2.
#[test]
fn density_borrow_elided_skips_rc_axis() {
    let mut proj = heap_call("vec-get", Some(true), None);
    if let MonoExpr::Apply { provenance, .. } = &mut proj {
        *provenance = Some(sym("root"));
    }
    assert_eq!(spark_density(&proj), Some(1));
}

// --- End-to-end admission through BOTH call sites (default threshold = 0) ---
//
// S104 Wave 0 flipped `SPARK_DENSITY_MAX_DEFAULT` `1 → 0` (`lenient-eval.md`
// §2.8.5, B4 off by default). At the new default the density axis is INERT
// (`max == 0` ⇒ `density_declines` returns false for every candidate), so a
// score-2 alloc-dense pair that the old default declined is now ADMITTED. The
// score itself is unchanged and still asserted, threshold-independent, by
// `density_alloc_dense_scores_two`; only the default *use* of that score moved.

// spec: design/backend/lenient-eval.md §2.8.5 — LET path: B4 off by default ⇒ admitted
//
// Two alloc-dense (score-2) heap bindings clear the compute axis + ≥2 gate; with
// B4 default-off the density axis does not decline them, so both are admitted.
// (The decline mechanism is preserved — re-enabled by CRANELISP_SPARK_DENSITY_MAX=N.)
#[test]
fn density_let_alloc_dense_pair_admitted_axis_off_by_default() {
    let bindings = vec![
        (sym("a"), heap_call("solve-range", Some(true), None)),
        (sym("b"), heap_call("solve-range", Some(true), None)),
    ];
    let ctors = HashSet::new();
    assert_eq!(
        find_sparkable_bindings(&bindings, &ctors),
        vec![0, 1],
        "with B4 default-off (SPARK_DENSITY_MAX_DEFAULT = 0) the axis is inert ⇒ admitted"
    );
}

// spec: design/backend/lenient-eval.md §2.8.5 — APPLY path: B4 off by default ⇒ admitted
//
// The single-source density axis is inert at the apply-argument site too.
#[test]
fn density_args_alloc_dense_pair_admitted_axis_off_by_default() {
    let args = vec![
        heap_call("solve-range", Some(true), None),
        heap_call("solve-range", Some(true), None),
    ];
    let ctors = HashSet::new();
    assert_eq!(
        find_sparkable_args(&args, &ctors),
        vec![0, 1],
        "with B4 default-off the shared density axis admits the alloc-dense pair"
    );
}

// spec: design/backend/lenient-eval.md §2.7 — compute-dense pair ADMITTED (both sites)
//
// Two engaged scalar-returning (score-0) candidates are NOT touched by the
// density axis — the compute win is preserved (§9). Both the `let` and apply
// sites admit them.
#[test]
fn density_compute_dense_pair_admitted_both_sites() {
    let a = scalar_call_with_facts("reduce-tree", Some(true), None);
    let b = scalar_call_with_facts("reduce-tree", Some(true), None);
    let ctors = HashSet::new();
    assert_eq!(
        find_sparkable_bindings(&[(sym("x"), a.clone()), (sym("y"), b.clone())], &ctors),
        vec![0, 1],
        "compute-bound (score 0) let bindings stay admitted"
    );
    assert_eq!(
        find_sparkable_args(&[a, b], &ctors),
        vec![0, 1],
        "compute-bound (score 0) apply args stay admitted"
    );
}

// spec: design/backend/lenient-eval.md §2.7 — confined-heap pair ADMITTED (boundary)
//
// Score-1 candidates sit exactly AT the threshold (1 > 1 is false) ⇒ admitted.
// This is the boundary companion to the score-2 decline: a confined heap spark
// is cheap enough to keep.
#[test]
fn density_confined_heap_pair_admitted_at_boundary() {
    let args = vec![
        heap_call("mk", Some(true), Some(true)),
        heap_call("mk", Some(true), Some(true)),
    ];
    let ctors = HashSet::new();
    assert_eq!(
        find_sparkable_args(&args, &ctors),
        vec![0, 1],
        "score == threshold (1) is admitted, not declined"
    );
}

// spec: design/backend/lenient-eval.md §2.7 — facts-absent admits exactly as pre-B4
//
// Negative / byte-identity face: heap-returning candidates with NO facts (the
// CRANELISP_NO_OWNERSHIP / facts-absent state) are admitted exactly as the
// pre-B4 pipeline would — the axis is inert, so the admission set equals the
// compute-axis-only result for the full shape.
#[test]
fn density_facts_absent_admits_like_pre_b4() {
    // Two heap calls, no facts ⇒ inert ⇒ admitted purely on the compute axis.
    let args = vec![heap_call("solve", None, None), heap_call("solve", None, None)];
    let ctors = HashSet::new();
    assert_eq!(
        find_sparkable_args(&args, &ctors),
        vec![0, 1],
        "facts-absent heap candidates admit exactly as pre-B4 (axis inert)"
    );
}
