// Free-variable analysis over the post-monomorphisation AST (`MonoExpr`).
//
// Pure traversal — no `FnCompiler`, no codegen. Consumed by `lambda.rs`,
// `par_bind.rs`, and `sparkability.rs`. Isolating it makes those three
// consumers' dependency explicit (P1).

use std::collections::HashSet;

use cranelisp_types::{MonoExpr, Symbol};

/// Find free variables in an expression (variables not bound by local let/lambda/match).
pub(crate) fn find_free_vars(expr: &MonoExpr, bound: &[Symbol]) -> Vec<Symbol> {
    let mut free = Vec::new();
    let mut seen = HashSet::new();
    let bound_set: HashSet<_> = bound.iter().cloned().collect();
    collect_free_vars(expr, &bound_set, &mut free, &mut seen);
    free
}

/// Recursive helper for free variable collection.
fn collect_free_vars(
    expr: &MonoExpr,
    bound: &HashSet<Symbol>,
    free: &mut Vec<Symbol>,
    seen: &mut HashSet<Symbol>,
) {
    match expr {
        MonoExpr::Var { name, .. } => {
            if !bound.contains(name) && !seen.contains(name) {
                seen.insert(name.clone());
                free.push(name.clone());
            }
        }
        MonoExpr::Let { bindings, body, .. } => {
            let mut extended = bound.clone();
            for (name, val_expr) in bindings {
                collect_free_vars(val_expr, &extended, free, seen);
                extended.insert(name.clone());
            }
            collect_free_vars(body, &extended, free, seen);
        }
        MonoExpr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_free_vars(cond, bound, free, seen);
            collect_free_vars(then_branch, bound, free, seen);
            collect_free_vars(else_branch, bound, free, seen);
        }
        MonoExpr::Lambda { params, body, .. } => {
            let mut extended = bound.clone();
            for p in params {
                extended.insert(p.clone());
            }
            collect_free_vars(body, &extended, free, seen);
        }
        MonoExpr::Apply { callee, args, .. } => {
            collect_free_vars(callee, bound, free, seen);
            for arg in args {
                collect_free_vars(arg, bound, free, seen);
            }
        }
        MonoExpr::Match {
            scrutinee, arms, ..
        } => {
            collect_free_vars(scrutinee, bound, free, seen);
            for arm in arms {
                let mut arm_bound = bound.clone();
                match &arm.pattern {
                    cranelisp_types::Pattern::Var { name, .. } => {
                        arm_bound.insert(name.clone());
                    }
                    cranelisp_types::Pattern::Constructor { bindings, .. } => {
                        for b in bindings {
                            arm_bound.insert(b.clone());
                        }
                    }
                    cranelisp_types::Pattern::Wildcard { .. } => {}
                }
                collect_free_vars(&arm.body, &arm_bound, free, seen);
            }
        }
        MonoExpr::VecLit { elements, .. } => {
            for e in elements {
                collect_free_vars(e, bound, free, seen);
            }
        }
        MonoExpr::Trace { body, .. } => {
            collect_free_vars(body, bound, free, seen);
        }
        MonoExpr::ParBind { bindings, body, .. } => {
            // Same as Let: each binding may reference earlier ones
            let mut extended = bound.clone();
            for (name, val_expr) in bindings {
                collect_free_vars(val_expr, &extended, free, seen);
                extended.insert(name.clone());
            }
            collect_free_vars(body, &extended, free, seen);
        }
        MonoExpr::LaunchContinue {
            launched,
            continuation,
            ..
        } => {
            // The launched effect binds no name (its result is discarded), so the
            // free-var set is simply the union over both sub-trees — like a
            // sequential `Bind(launched, λ_. continuation)`.
            collect_free_vars(launched, bound, free, seen);
            collect_free_vars(continuation, bound, free, seen);
        }
        MonoExpr::ConstrADT { fields, .. } => {
            for f in fields {
                collect_free_vars(f, bound, free, seen);
            }
        }
        MonoExpr::StringLit { .. }
        | MonoExpr::IntLit { .. }
        | MonoExpr::FloatLit { .. }
        | MonoExpr::BoolLit { .. } => {}
    }
}
