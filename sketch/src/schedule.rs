//! Auto-scheduling pass: transforms `bind!` chains into `ParBind` nodes for
//! data-independent, non-Sequential IO expressions.
//!
//! This pass runs after macro expansion and AST building, before typechecking.
//! It only requires `tc.platform_scheduling` (populated during platform loading).
//!
//! **Algorithm**
//! 1. Detect the `bind` chain pattern:
//!    `Apply(Var("bind"), [io_expr, Lambda([name], body)])` chains.
//! 2. Collect the flat list of `(name, io_expr)` steps plus the final body.
//! 3. Group data-independent, non-Sequential steps into `ParBind` nodes.
//! 4. Rebuild the nested expression from the grouped segments.
//!
//! A step is eligible for parallel grouping if:
//! - Its IO expression has `SchedulingClass != Sequential` (it's a Commutative or
//!   ResourceSerial platform function call), AND
//! - None of the names bound by earlier steps appear free in the IO expression
//!   (data independence).

use std::collections::HashSet;

use crate::ast::{Defn, Expr, MatchArm};
use crate::captures::free_vars;
use crate::error::Span;
use crate::platform::SchedulingClass;
use crate::typechecker::TypeChecker;

// ── Public entry point ────────────────────────────────────────────────────────

/// Transform bind chains in a function body into `ParBind` nodes where safe.
pub fn auto_schedule_defn(defn: &mut Defn, tc: &TypeChecker) {
    let body = std::mem::replace(&mut defn.body, Expr::BoolLit { value: false, span: defn.span });
    defn.body = transform_expr(body, tc);
}

// ── Expression transformation ─────────────────────────────────────────────────

/// Recursively transform an expression, optimizing bind chains into ParBind.
fn transform_expr(expr: Expr, tc: &TypeChecker) -> Expr {
    // If this is the start of a bind chain, collect and optimise the whole chain.
    if is_bind_chain_start(&expr) {
        let (chain, final_body) = collect_bind_chain(expr);
        rebuild_chain(chain, final_body, tc)
    } else {
        recurse_children(expr, tc)
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
        Expr::Var { name, .. } => name == "bind" || name.ends_with("/bind"),
        _ => false,
    }
}

/// Collect a complete bind chain into a flat vec of `(name, io_expr, annotation, span)`
/// plus the final non-bind body.  The chain must be non-empty (caller must check).
///
/// The `annotation` field preserves the Lambda parameter's optional type annotation.
fn collect_bind_chain(
    expr: Expr,
) -> (Vec<(String, Expr, Option<crate::ast::TypeExpr>, Span)>, Expr) {
    // This is guarded by is_bind_chain_start, so the destructuring below is safe.
    let Expr::Apply { mut args, span, .. } = expr else {
        unreachable!("collect_bind_chain called on non-bind expr")
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
        unreachable!("bind lambda is not a Lambda")
    };

    let name = params.remove(0);
    let annotation = param_annotations.pop().flatten(); // may be None
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

// ── Scheduling classification ─────────────────────────────────────────────────

/// Return the `SchedulingClass` of the platform function called by `io_expr`.
/// Falls back to `Sequential` for anything other than a direct platform call.
fn classify_expr(expr: &Expr, tc: &TypeChecker) -> SchedulingClass {
    if let Expr::Apply { callee, .. } = expr {
        if let Expr::Var { name, .. } = callee.as_ref() {
            // Direct lookup (bare name after import, e.g. "print").
            let sc = tc.scheduling_of(name);
            if sc != SchedulingClass::Sequential {
                return sc;
            }
            // Qualified name fallback: "platform.stdio/print" → "print".
            if let Some(pos) = name.rfind('/') {
                return tc.scheduling_of(&name[pos + 1..]);
            }
        }
    }
    SchedulingClass::Sequential
}

/// True if none of the names in `bound_names` appear free in `expr`.
fn is_independent(expr: &Expr, bound_names: &HashSet<String>) -> bool {
    if bound_names.is_empty() {
        return true;
    }
    let globals = HashSet::new();
    free_vars(expr, &globals).is_disjoint(bound_names)
}

// ── Chain rebuilding ──────────────────────────────────────────────────────────

/// A segment in the rebuilt chain.
enum Segment {
    /// A single sequential bind step.
    Sequential(String, Expr, Option<crate::ast::TypeExpr>, Span),
    /// A group of data-independent non-Sequential steps to run in parallel.
    Parallel(Vec<(String, Expr, Span)>),
}

/// Flush the current parallel group into `segments`, updating `bound_so_far`.
///
/// - If the group has ≥2 entries: emit a `Parallel` segment.
/// - If the group has exactly 1 entry: demote it to `Sequential`.
/// - If empty: no-op.
fn flush_par_group(
    segments: &mut Vec<Segment>,
    bound_so_far: &mut HashSet<String>,
    group: Vec<(String, Expr, Option<crate::ast::TypeExpr>, Span)>,
) {
    if group.is_empty() {
        return;
    }
    for (name, _, _, _) in &group {
        bound_so_far.insert(name.clone());
    }
    if group.len() >= 2 {
        let par_bindings: Vec<(String, Expr, Span)> =
            group.into_iter().map(|(n, e, _, s)| (n, e, s)).collect();
        segments.push(Segment::Parallel(par_bindings));
    } else {
        let (name, io_expr, annotation, span) = group.into_iter().next().unwrap();
        segments.push(Segment::Sequential(name, io_expr, annotation, span));
    }
}

/// Group a flat bind chain and rebuild it into an optimised nested expression.
fn rebuild_chain(
    chain: Vec<(String, Expr, Option<crate::ast::TypeExpr>, Span)>,
    final_body: Expr,
    tc: &TypeChecker,
) -> Expr {
    let mut segments: Vec<Segment> = Vec::new();
    let mut current_par: Vec<(String, Expr, Option<crate::ast::TypeExpr>, Span)> = Vec::new();
    let mut bound_so_far: HashSet<String> = HashSet::new();

    for (name, io_expr, annotation, span) in chain {
        let sc = classify_expr(&io_expr, tc);

        // Names already committed + names in the current parallel group.
        let mut all_bound = bound_so_far.clone();
        for (n, _, _, _) in &current_par {
            all_bound.insert(n.clone());
        }

        if sc != SchedulingClass::Sequential && is_independent(&io_expr, &all_bound) {
            current_par.push((name, io_expr, annotation, span));
        } else {
            // This entry can't join the parallel group — flush it first.
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
    let mut result = transform_expr(final_body, tc);
    for segment in segments.into_iter().rev() {
        result = match segment {
            Segment::Sequential(name, io_expr, annotation, span) => {
                let io_expr = transform_expr(io_expr, tc);
                make_bind(name, io_expr, annotation, result, span)
            }
            Segment::Parallel(bindings_with_span) => {
                let span = bindings_with_span[0].2;
                let bindings: Vec<(String, Expr)> = bindings_with_span
                    .into_iter()
                    .map(|(name, io_expr, _span)| (name, transform_expr(io_expr, tc)))
                    .collect();
                Expr::ParBind {
                    bindings,
                    body: Box::new(result),
                    span,
                }
            }
        };
    }
    result
}

/// Reconstruct a sequential `(bind io_expr (fn [name] body))` expression.
fn make_bind(
    name: String,
    io_expr: Expr,
    annotation: Option<crate::ast::TypeExpr>,
    body: Expr,
    span: Span,
) -> Expr {
    Expr::Apply {
        callee: Box::new(Expr::Var {
            name: "bind".to_string(),
            span,
        }),
        args: vec![
            io_expr,
            Expr::Lambda {
                params: vec![name],
                param_annotations: vec![annotation],
                body: Box::new(body),
                span,
            },
        ],
        span,
    }
}

// ── Child recursion ───────────────────────────────────────────────────────────

/// Recurse into sub-expressions without touching this node's structure.
///
/// Called for any expression that is not itself a bind chain start.
fn recurse_children(expr: Expr, tc: &TypeChecker) -> Expr {
    match expr {
        Expr::Let { bindings, body, span } => Expr::Let {
            bindings: bindings
                .into_iter()
                .map(|(n, v)| (n, transform_expr(v, tc)))
                .collect(),
            body: Box::new(transform_expr(*body, tc)),
            span,
        },
        Expr::If {
            cond,
            then_branch,
            else_branch,
            span,
        } => Expr::If {
            cond: Box::new(transform_expr(*cond, tc)),
            then_branch: Box::new(transform_expr(*then_branch, tc)),
            else_branch: Box::new(transform_expr(*else_branch, tc)),
            span,
        },
        Expr::Lambda {
            params,
            param_annotations,
            body,
            span,
        } => Expr::Lambda {
            params,
            param_annotations,
            body: Box::new(transform_expr(*body, tc)),
            span,
        },
        Expr::Apply { callee, args, span } => Expr::Apply {
            callee: Box::new(transform_expr(*callee, tc)),
            args: args.into_iter().map(|a| transform_expr(a, tc)).collect(),
            span,
        },
        Expr::Match {
            scrutinee,
            arms,
            span,
            compiler_generated,
        } => Expr::Match {
            scrutinee: Box::new(transform_expr(*scrutinee, tc)),
            arms: arms
                .into_iter()
                .map(|arm| MatchArm {
                    pattern: arm.pattern,
                    body: transform_expr(arm.body, tc),
                    span: arm.span,
                })
                .collect(),
            span,
            compiler_generated,
        },
        Expr::VecLit { elements, span } => Expr::VecLit {
            elements: elements.into_iter().map(|e| transform_expr(e, tc)).collect(),
            span,
        },
        Expr::Annotate {
            annotation,
            expr,
            span,
        } => Expr::Annotate {
            annotation,
            expr: Box::new(transform_expr(*expr, tc)),
            span,
        },
        Expr::ParLet { bindings, body, span } => Expr::ParLet {
            bindings: bindings
                .into_iter()
                .map(|(n, v)| (n, transform_expr(v, tc)))
                .collect(),
            body: Box::new(transform_expr(*body, tc)),
            span,
        },
        Expr::ParBind { bindings, body, span } => Expr::ParBind {
            bindings: bindings
                .into_iter()
                .map(|(n, v)| (n, transform_expr(v, tc)))
                .collect(),
            body: Box::new(transform_expr(*body, tc)),
            span,
        },
        Expr::Trace {
            modules,
            body,
            span,
        } => Expr::Trace {
            modules,
            body: Box::new(transform_expr(*body, tc)),
            span,
        },
        // Leaf nodes and RunTests (complex runtime; don't attempt to transform inside).
        leaf @ (Expr::IntLit { .. }
        | Expr::FloatLit { .. }
        | Expr::BoolLit { .. }
        | Expr::StringLit { .. }
        | Expr::Var { .. }
        | Expr::RunTests { .. }) => leaf,
    }
}
