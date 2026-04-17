//! Bind chain independence analysis: transforms `bind!`-expanded nested
//! bind/lambda forms into `Expr::ParBind` nodes for automatic IO scheduling.
//!
//! This pass runs after macro expansion and AST building, before typechecking.
//! It requires a scheduling class registry populated during platform DLL loading.
//!
//! Algorithm (per design/int/bind-chain-analysis.md):
//! 1. Detect the `bind` chain pattern: `Apply(Var("bind"), [io_expr, Lambda([name], body)])`.
//! 2. Collect the flat list of `(name, io_expr)` steps plus the final body.
//! 3. Classify each step's scheduling class via the registry.
//! 4. Group data-independent, non-Sequential steps into `ParBind` nodes.
//! 5. Rebuild the nested expression from the grouped segments.

use std::collections::HashSet;

use cranelisp_platform::SchedulingClass;
use cranelisp_types::{Defn, Expr, MatchArm, Span, Symbol, TypeExpr, free_vars_expr};

use crate::platform_registry::PlatformRegistry;

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Transform bind chains in a function body into `ParBind` nodes where safe.
///
/// Takes ownership of the body via `std::mem::replace` with a dummy expression,
/// transforms it, and puts the result back. The dummy is never observed.
pub fn auto_schedule_defn(defn: &mut Defn, registry: &PlatformRegistry) {
    // Single-sig only (multi-sig functions are not auto-scheduled)
    assert!(!defn.is_multi_sig(), "auto_schedule_defn called on multi-sig defn");
    let body = std::mem::replace(
        &mut defn.variants[0].body,
        Expr::BoolLit { value: false, span: defn.span, inferred_type: None },
    );
    defn.variants[0].body = transform_expr(body, registry);
}

/// Transform bind chains in a standalone expression (REPL eval path).
pub fn auto_schedule_expr(expr: &mut Expr, registry: &PlatformRegistry) {
    let owned = std::mem::replace(
        expr,
        Expr::BoolLit { value: false, span: Span::SYNTHETIC, inferred_type: None },
    );
    *expr = transform_expr(owned, registry);
}

/// Transform bind chains in an owned expression (for DefnVariant bodies).
pub fn auto_schedule_expr_owned(expr: Expr, registry: &PlatformRegistry) -> Expr {
    transform_expr(expr, registry)
}

// ---------------------------------------------------------------------------
// Expression transformation
// ---------------------------------------------------------------------------

/// Recursively transform an expression, optimizing bind chains into ParBind.
fn transform_expr(expr: Expr, registry: &PlatformRegistry) -> Expr {
    if is_bind_chain_start(&expr) {
        let (chain, final_body) = collect_bind_chain(expr);
        rebuild_chain(chain, final_body, registry)
    } else {
        recurse_children(expr, registry)
    }
}

/// True if `expr` is `Apply(Var("bind"/"*/bind"), [io_expr, Lambda([name], body)])`.
fn is_bind_chain_start(expr: &Expr) -> bool {
    matches!(expr, Expr::Apply { callee, args, .. }
        if is_bind_var(callee)
        && args.len() == 2
        && matches!(&args[1], Expr::Lambda { params, .. } if params.len() == 1))
}

/// True if `expr` is a reference to the `bind` primitive.
fn is_bind_var(expr: &Expr) -> bool {
    match expr {
        Expr::Var { name, .. } => name.as_ref() == "bind" || name.ends_with("/bind"),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Chain collection
// ---------------------------------------------------------------------------

/// A single step in a bind chain: (bound_name, io_expr, annotation, span).
type BindStep = (Symbol, Expr, Option<TypeExpr>, Span);

/// Collect a complete bind chain into a flat vec of steps plus the final body.
///
/// The chain must be non-empty (caller checks via `is_bind_chain_start`).
/// The `annotation` field preserves the Lambda parameter's optional type
/// annotation for round-tripping.
fn collect_bind_chain(expr: Expr) -> (Vec<BindStep>, Expr) {
    let Expr::Apply { mut args, span, .. } = expr else {
        unreachable!("invariant: collect_bind_chain called on non-bind expr")
    };

    // args[1] is the Lambda; extract it first to avoid borrow conflicts.
    let lambda = args.remove(1);
    let io_expr = args.remove(0);

    let Expr::Lambda {
        mut params,
        mut param_annotations,
        body,
        ..
    } = lambda
    else {
        unreachable!("invariant: bind lambda is not a Lambda")
    };

    let name = params.remove(0);
    let annotation = param_annotations.pop().flatten();
    let inner = *body;
    let binding_span = span;

    if is_bind_chain_start(&inner) {
        let (mut rest, final_body) = collect_bind_chain(inner);
        rest.insert(0, (name, io_expr, annotation, binding_span));
        (rest, final_body)
    } else {
        (vec![(name, io_expr, annotation, binding_span)], inner)
    }
}

// ---------------------------------------------------------------------------
// Scheduling classification
// ---------------------------------------------------------------------------

/// Return the `SchedulingClass` of the platform function called by `io_expr`.
///
/// Falls back to `Sequential` for anything other than a direct platform call.
/// Only direct calls to platform functions are eligible — wrapper functions
/// that call platform functions are conservatively treated as sequential.
fn classify_expr(expr: &Expr, registry: &PlatformRegistry) -> SchedulingClass {
    if let Expr::Apply { callee, .. } = expr
        && let Expr::Var { name, .. } = callee.as_ref()
    {
        // Direct lookup via PlatformRegistry (bare name match across entries).
        if let Some(sc) = registry.scheduling_class(name)
            && sc != SchedulingClass::Sequential
        {
            return sc;
        }
        // Qualified name fallback: "platform.stdio/print" → "print".
        if let Some(pos) = name.rfind('/') {
            let bare = Symbol::from(&name[pos + 1..]);
            if let Some(sc) = registry.scheduling_class(&bare) {
                return sc;
            }
        }
    }
    SchedulingClass::Sequential
}

/// True if none of the names in `bound_names` appear free in `expr`.
fn is_independent(expr: &Expr, bound_names: &HashSet<Symbol>) -> bool {
    if bound_names.is_empty() {
        return true;
    }
    let globals = HashSet::new();
    free_vars_expr(expr, &globals).is_disjoint(bound_names)
}

// ---------------------------------------------------------------------------
// Chain rebuilding
// ---------------------------------------------------------------------------

/// A segment in the rebuilt chain.
enum Segment {
    /// A single sequential bind step.
    Sequential(Symbol, Expr, Option<TypeExpr>, Span),
    /// A group of data-independent non-Sequential steps to run in parallel.
    Parallel(Vec<(Symbol, Expr, Span)>),
}

/// Flush the current parallel group into `segments`, updating `bound_so_far`.
///
/// - If the group has >= 2 entries: emit a `Parallel` segment.
/// - If the group has exactly 1 entry: demote to `Sequential`.
/// - If empty: no-op.
fn flush_par_group(
    segments: &mut Vec<Segment>,
    bound_so_far: &mut HashSet<Symbol>,
    group: Vec<BindStep>,
) {
    if group.is_empty() {
        return;
    }
    for (name, _, _, _) in &group {
        bound_so_far.insert(name.clone());
    }
    if group.len() >= 2 {
        let par_bindings: Vec<(Symbol, Expr, Span)> =
            group.into_iter().map(|(n, e, _, s)| (n, e, s)).collect();
        segments.push(Segment::Parallel(par_bindings));
    } else {
        let (name, io_expr, annotation, span) = group.into_iter().next()
            .expect("invariant: group is non-empty");
        segments.push(Segment::Sequential(name, io_expr, annotation, span));
    }
}

/// Group a flat bind chain and rebuild it into an optimised nested expression.
fn rebuild_chain(
    chain: Vec<BindStep>,
    final_body: Expr,
    registry: &PlatformRegistry,
) -> Expr {
    let mut segments: Vec<Segment> = Vec::new();
    let mut current_par: Vec<BindStep> = Vec::new();
    let mut bound_so_far: HashSet<Symbol> = HashSet::new();

    for (name, io_expr, annotation, span) in chain {
        let sc = classify_expr(&io_expr, registry);

        // Names already committed + names in the current parallel group.
        let mut all_bound = bound_so_far.clone();
        for (n, _, _, _) in &current_par {
            all_bound.insert(n.clone());
        }

        if sc != SchedulingClass::Sequential && is_independent(&io_expr, &all_bound) {
            current_par.push((name, io_expr, annotation, span));
        } else {
            // This entry can't join the parallel group — flush first.
            flush_par_group(
                &mut segments,
                &mut bound_so_far,
                std::mem::take(&mut current_par),
            );
            bound_so_far.insert(name.clone());
            segments.push(Segment::Sequential(name, io_expr, annotation, span));
        }
    }
    // Flush any remaining parallel group.
    flush_par_group(
        &mut segments,
        &mut bound_so_far,
        std::mem::take(&mut current_par),
    );

    // Rebuild from right to left: innermost expression is the transformed final_body.
    let mut result = transform_expr(final_body, registry);
    for segment in segments.into_iter().rev() {
        result = match segment {
            Segment::Sequential(name, io_expr, annotation, span) => {
                let io_expr = transform_expr(io_expr, registry);
                make_bind(name, io_expr, annotation, result, span)
            }
            Segment::Parallel(bindings_with_span) => {
                let span = bindings_with_span[0].2;
                let bindings: Vec<(Symbol, Expr)> = bindings_with_span
                    .into_iter()
                    .map(|(name, io_expr, _span)| (name, transform_expr(io_expr, registry)))
                    .collect();
                Expr::ParBind {
                    bindings,
                    body: Box::new(result),
                    span,
                    inferred_type: None,
                }
            }
        };
    }
    result
}

/// Reconstruct a sequential `(bind io_expr (fn [name] body))` expression.
fn make_bind(
    name: Symbol,
    io_expr: Expr,
    annotation: Option<TypeExpr>,
    body: Expr,
    span: Span,
) -> Expr {
    Expr::Apply {
        callee: Box::new(Expr::Var {
            name: Symbol::from("bind"),
            span,
            inferred_type: None,
        }),
        args: vec![
            io_expr,
            Expr::Lambda {
                params: vec![name],
                param_annotations: vec![annotation],
                body: Box::new(body),
                span,
                inferred_type: None,
            },
        ],
        span,
        resolved_call: None,
        inferred_type: None,
    }
}

// ---------------------------------------------------------------------------
// Child recursion
// ---------------------------------------------------------------------------

/// Recurse into sub-expressions without touching this node's structure.
///
/// Called for any expression that is not itself a bind chain start.
fn recurse_children(expr: Expr, registry: &PlatformRegistry) -> Expr {
    match expr {
        Expr::Let { bindings, body, span, inferred_type } => Expr::Let {
            bindings: bindings
                .into_iter()
                .map(|(n, v)| (n, transform_expr(v, registry)))
                .collect(),
            body: Box::new(transform_expr(*body, registry)),
            span,
            inferred_type,
        },
        Expr::If { cond, then_branch, else_branch, span, inferred_type } => Expr::If {
            cond: Box::new(transform_expr(*cond, registry)),
            then_branch: Box::new(transform_expr(*then_branch, registry)),
            else_branch: Box::new(transform_expr(*else_branch, registry)),
            span,
            inferred_type,
        },
        Expr::Lambda { params, param_annotations, body, span, inferred_type } => Expr::Lambda {
            params,
            param_annotations,
            body: Box::new(transform_expr(*body, registry)),
            span,
            inferred_type,
        },
        Expr::Apply { callee, args, span, resolved_call, inferred_type } => Expr::Apply {
            callee: Box::new(transform_expr(*callee, registry)),
            args: args.into_iter().map(|a| transform_expr(a, registry)).collect(),
            span,
            resolved_call,
            inferred_type,
        },
        Expr::Match { scrutinee, arms, span, compiler_generated, inferred_type } => Expr::Match {
            scrutinee: Box::new(transform_expr(*scrutinee, registry)),
            arms: arms
                .into_iter()
                .map(|arm| MatchArm {
                    pattern: arm.pattern,
                    body: transform_expr(arm.body, registry),
                    span: arm.span,
                })
                .collect(),
            span,
            compiler_generated,
            inferred_type,
        },
        Expr::VecLit { elements, span, inferred_type } => Expr::VecLit {
            elements: elements.into_iter().map(|e| transform_expr(e, registry)).collect(),
            span,
            inferred_type,
        },
        Expr::Annotate { annotation, expr, span, inferred_type } => Expr::Annotate {
            annotation,
            expr: Box::new(transform_expr(*expr, registry)),
            span,
            inferred_type,
        },
        Expr::ParBind { bindings, body, span, inferred_type } => Expr::ParBind {
            bindings: bindings
                .into_iter()
                .map(|(n, v)| (n, transform_expr(v, registry)))
                .collect(),
            body: Box::new(transform_expr(*body, registry)),
            span,
            inferred_type,
        },
        Expr::Trace { modules, body, span, inferred_type } => Expr::Trace {
            modules,
            body: Box::new(transform_expr(*body, registry)),
            span,
            inferred_type,
        },
        // Leaf nodes.
        leaf @ (Expr::IntLit { .. }
        | Expr::FloatLit { .. }
        | Expr::BoolLit { .. }
        | Expr::StringLit { .. }
        | Expr::Var { .. }) => leaf,
    }
}

// ---------------------------------------------------------------------------
// Scheduling registry lookup
// ---------------------------------------------------------------------------

/// Look up the scheduling class for a platform function name.
///
/// Tries direct lookup first, then strips module qualifiers as a fallback
/// (e.g., "platform.stdio/print" -> "print").
pub fn scheduling_of(registry: &PlatformRegistry, name: &str) -> SchedulingClass {
    let sym = Symbol::from(name);
    if let Some(sc) = registry.scheduling_class(&sym)
        && sc != SchedulingClass::Sequential
    {
        return sc;
    }
    // Qualified name fallback.
    if let Some(pos) = name.rfind('/') {
        let bare = Symbol::from(&name[pos + 1..]);
        if let Some(sc) = registry.scheduling_class(&bare) {
            return sc;
        }
    }
    SchedulingClass::Sequential
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::Span;

    fn make_var(name: &str) -> Expr {
        Expr::Var { name: Symbol::from(name), span: Span::SYNTHETIC, inferred_type: None }
    }

    fn make_int(value: i64) -> Expr {
        Expr::IntLit { value, span: Span::SYNTHETIC, inferred_type: None }
    }

    fn make_apply(callee: &str, args: Vec<Expr>) -> Expr {
        Expr::Apply {
            callee: Box::new(make_var(callee)),
            args,
            span: Span::SYNTHETIC,
            resolved_call: None,
            inferred_type: None,
        }
    }

    fn make_bind_expr(io_expr: Expr, name: &str, body: Expr) -> Expr {
        Expr::Apply {
            callee: Box::new(make_var("bind")),
            args: vec![
                io_expr,
                Expr::Lambda {
                    params: vec![Symbol::from(name)],
                    param_annotations: vec![None],
                    body: Box::new(body),
                    span: Span::SYNTHETIC,
                    inferred_type: None,
                },
            ],
            span: Span::SYNTHETIC,
            resolved_call: None,
            inferred_type: None,
        }
    }

    fn commutative_registry() -> PlatformRegistry {
        use cranelisp_types::{FQSymbol, ModuleFullPath};
        PlatformRegistry::with_test_entries(vec![
            (FQSymbol { module: ModuleFullPath::from("platform.test"), symbol: Symbol::from("get-time") }, SchedulingClass::Commutative),
            (FQSymbol { module: ModuleFullPath::from("platform.test"), symbol: Symbol::from("http-get") }, SchedulingClass::Commutative),
            (FQSymbol { module: ModuleFullPath::from("platform.test"), symbol: Symbol::from("print") }, SchedulingClass::Sequential),
        ])
    }

    // spec: 10-io §10.12.1 — pattern recognition
    #[test]
    fn test_is_bind_chain_start() {
        let expr = make_bind_expr(make_apply("get-time", vec![]), "t", make_int(0));
        assert!(is_bind_chain_start(&expr));
    }

    #[test]
    fn test_non_bind_not_chain_start() {
        let expr = make_apply("foo", vec![make_int(1)]);
        assert!(!is_bind_chain_start(&expr));
    }

    // spec: 10-io §10.12.1 — chain collection
    #[test]
    fn test_collect_two_step_chain() {
        // (bind (get-time) (fn [t1] (bind (get-time) (fn [t2] body))))
        let inner = make_bind_expr(
            make_apply("get-time", vec![]),
            "t2",
            make_int(42),
        );
        let expr = make_bind_expr(
            make_apply("get-time", vec![]),
            "t1",
            inner,
        );
        let (chain, body) = collect_bind_chain(expr);
        assert_eq!(chain.len(), 2);
        assert_eq!(chain[0].0.as_ref(), "t1");
        assert_eq!(chain[1].0.as_ref(), "t2");
        assert!(matches!(body, Expr::IntLit { value: 42, .. }));
    }

    // spec: 10-io §10.12.1 — scheduling classification
    #[test]
    fn test_classify_commutative() {
        let registry = commutative_registry();
        let expr = make_apply("get-time", vec![]);
        assert_eq!(classify_expr(&expr, &registry), SchedulingClass::Commutative);
    }

    #[test]
    fn test_classify_sequential_default() {
        let registry = commutative_registry();
        let expr = make_apply("unknown-fn", vec![]);
        assert_eq!(classify_expr(&expr, &registry), SchedulingClass::Sequential);
    }

    #[test]
    fn test_classify_qualified_name_fallback() {
        let registry = commutative_registry();
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("platform.time/get-time"),
                span: Span::SYNTHETIC,
                inferred_type: None,
            }),
            args: vec![],
            span: Span::SYNTHETIC,
            resolved_call: None,
            inferred_type: None,
        };
        assert_eq!(classify_expr(&expr, &registry), SchedulingClass::Commutative);
    }

    // spec: 10-io §10.12.1 — independence check
    #[test]
    fn test_independent_expressions() {
        let expr = make_apply("get-time", vec![]);
        let bound: HashSet<Symbol> = [Symbol::from("x")].into();
        assert!(is_independent(&expr, &bound));
    }

    #[test]
    fn test_dependent_expression() {
        let expr = make_apply("http-get", vec![make_var("x")]);
        let bound: HashSet<Symbol> = [Symbol::from("x")].into();
        assert!(!is_independent(&expr, &bound));
    }

    // spec: 10-io §10.12.1 — two commutative independent steps become ParBind
    #[test]
    fn test_two_commutative_independent_become_par_bind() {
        let registry = commutative_registry();
        // (bind (get-time) (fn [t1] (bind (http-get "url") (fn [t2] body))))
        let inner = make_bind_expr(
            make_apply("http-get", vec![make_var("url")]),
            "t2",
            make_int(99),
        );
        let expr = make_bind_expr(
            make_apply("get-time", vec![]),
            "t1",
            inner,
        );
        let result = transform_expr(expr, &registry);
        // Should produce a ParBind with 2 bindings.
        match &result {
            Expr::ParBind { bindings, .. } => {
                assert_eq!(bindings.len(), 2);
                assert_eq!(bindings[0].0.as_ref(), "t1");
                assert_eq!(bindings[1].0.as_ref(), "t2");
            }
            other => panic!("expected ParBind, got {:?}", other),
        }
    }

    // spec: 10-io §10.12.1 — sequential stays sequential
    #[test]
    fn test_sequential_stays_sequential() {
        let registry = commutative_registry();
        // (bind (print "hi") (fn [_] (bind (print "bye") (fn [_] 0))))
        let inner = make_bind_expr(
            make_apply("print", vec![make_var("s2")]),
            "_b",
            make_int(0),
        );
        let expr = make_bind_expr(
            make_apply("print", vec![make_var("s1")]),
            "_a",
            inner,
        );
        let result = transform_expr(expr, &registry);
        // Should remain as nested Apply (no ParBind).
        assert!(!matches!(result, Expr::ParBind { .. }));
    }

    // spec: 10-io §10.12.1 — dependent commutative stays sequential
    #[test]
    fn test_dependent_commutative_stays_sequential() {
        let registry = commutative_registry();
        // (bind (get-time) (fn [t1] (bind (http-get t1) (fn [t2] body))))
        // t1 appears free in the second io_expr → dependent → no parallelism.
        let inner = make_bind_expr(
            make_apply("http-get", vec![make_var("t1")]),
            "t2",
            make_int(0),
        );
        let expr = make_bind_expr(
            make_apply("get-time", vec![]),
            "t1",
            inner,
        );
        let result = transform_expr(expr, &registry);
        assert!(!matches!(result, Expr::ParBind { .. }));
    }

    // spec: 10-io §10.12.1 — single-element group demotion
    #[test]
    fn test_single_element_demoted() {
        let registry = commutative_registry();
        // Single bind step — should not produce ParBind.
        let expr = make_bind_expr(
            make_apply("get-time", vec![]),
            "t1",
            make_int(0),
        );
        let result = transform_expr(expr, &registry);
        assert!(!matches!(result, Expr::ParBind { .. }));
    }

    // spec: 10-io §10.12 — empty registry skips analysis
    #[test]
    fn test_empty_registry_no_transform() {
        let registry = PlatformRegistry::new();
        let inner = make_bind_expr(
            make_apply("get-time", vec![]),
            "t2",
            make_int(0),
        );
        let expr = make_bind_expr(
            make_apply("get-time", vec![]),
            "t1",
            inner,
        );
        let result = transform_expr(expr, &registry);
        // With empty registry, all calls are Sequential → no ParBind.
        assert!(!matches!(result, Expr::ParBind { .. }));
    }

    // spec: 10-io §10.12.1 — scheduling_of lookup
    #[test]
    fn test_scheduling_of_bare_name() {
        let registry = commutative_registry();
        assert_eq!(scheduling_of(&registry, "get-time"), SchedulingClass::Commutative);
        assert_eq!(scheduling_of(&registry, "print"), SchedulingClass::Sequential);
        assert_eq!(scheduling_of(&registry, "unknown"), SchedulingClass::Sequential);
    }

    #[test]
    fn test_scheduling_of_qualified_name() {
        let registry = commutative_registry();
        assert_eq!(
            scheduling_of(&registry, "platform.time/get-time"),
            SchedulingClass::Commutative,
        );
    }
}
