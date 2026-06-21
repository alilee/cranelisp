// Sparkability analysis for lenient evaluation.
//
// This is the lenient-eval *decision* pass (`design/backend/lenient-eval.md
// §2`), distinct from the lenient *emission* in `let_if.rs`. It decides which
// `let` bindings are independent + non-trivial enough to be worth sparking as
// parallel IVar tasks.

use std::collections::HashSet;

use cranelisp_types::{MonoExpr, Symbol};

use super::free_vars::find_free_vars;

/// Whether lenient evaluation is disabled via CRANELISP_NO_LENIENT=1.
pub(crate) static LENIENT_DISABLED: std::sync::LazyLock<bool> =
    std::sync::LazyLock::new(|| {
        std::env::var("CRANELISP_NO_LENIENT").is_ok_and(|v| v == "1")
    });

/// Known-cheap builtins that are not worth sparking.
/// Single-instruction or near-single-instruction at the hardware level.
const CHEAP_BUILTINS: &[&str] = &[
    "+", "-", "*", "/", "=", "<", ">", "<=", ">=", "not", "and", "or",
];

/// Find indices of sparkable bindings in a `let` block.
///
/// A binding is sparkable if:
/// 1. Its free variables do not reference any earlier binding in the same block.
/// 2. It is a non-trivial function call (not a cheap builtin, literal,
///    constructor, or var ref).
///
/// `constructors` is the set of known ADT constructor names.
///
/// Returns an empty vec if fewer than 2 sparkable bindings are found.
pub(crate) fn find_sparkable_bindings(
    bindings: &[(Symbol, MonoExpr)],
    constructors: &HashSet<Symbol>,
) -> Vec<usize> {
    let mut bound_names: HashSet<Symbol> = HashSet::new();
    let mut sparkable: Vec<usize> = Vec::new();

    // Free-variable traversal over `MonoExpr` (the in-crate `find_free_vars`,
    // mirroring `cranelisp_types::free_vars_expr` over the post-mono AST).
    for (i, (name, val_expr)) in bindings.iter().enumerate() {
        let fv = find_free_vars(val_expr, &[]);
        // Filter to only those free vars that are bound by earlier bindings
        // in this let block (not globals or outer scope).
        let depends_on_earlier = fv.iter().any(|v| bound_names.contains(v));

        if !depends_on_earlier && is_worth_sparking(val_expr, constructors) {
            sparkable.push(i);
        }

        bound_names.insert(name.clone());
    }

    if sparkable.len() < 2 {
        Vec::new()
    } else {
        sparkable
    }
}

/// Check if an expression is worth sparking (non-trivial function call).
///
/// Excludes: cheap builtins (+, -, etc.), data constructors (Some, Cons),
/// literals, variable references.
fn is_worth_sparking(expr: &MonoExpr, constructors: &HashSet<Symbol>) -> bool {
    match expr {
        MonoExpr::Apply { callee, .. } => {
            if let MonoExpr::Var { name, .. } = callee.as_ref() {
                // Cheap builtins and constructors are not worth sparking.
                !CHEAP_BUILTINS.contains(&name.as_ref())
                    && !constructors.contains(name)
            } else {
                // Non-variable callee (computed function) — conservatively spark.
                true
            }
        }
        // Non-Apply expressions are not worth sparking.
        _ => false,
    }
}
