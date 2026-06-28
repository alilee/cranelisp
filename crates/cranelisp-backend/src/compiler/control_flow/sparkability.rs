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
/// 1. It is a non-trivial function call (not a cheap builtin, literal,
///    constructor, or var ref) — the cost heuristic (§2.2).
/// 2. **Dependency-on-sparked carve-out (§2.6, FIXME 0424 limit #2).** Every
///    earlier-bound free var it references is *itself* already in the sparkable
///    set. An *independent* binding (no earlier-bound free var) trivially
///    satisfies this. A *dependent* binding is admitted iff all of its
///    earlier-bound dependencies are themselves sparked — they are then
///    available as IVars to force on demand inside its thunk (`let_if.rs`
///    `compile_dependent_thunk`, lenient-eval.md §4.5). A dependent binding that
///    touches a *non-sparked* earlier binding (a cheap one, or a literal/var
///    binding bound only as an ordinary `Value` in Phase 2) is NOT sparkable —
///    a concurrently-running thunk cannot see that `Value`.
///
/// Because `let` bindings are sequential, dependencies only point backward (no
/// cycles), so source order is already a valid topological order and a single
/// left-to-right pass suffices.
///
/// `constructors` is the set of known ADT constructor names.
///
/// Returns an empty vec if fewer than 2 sparkable bindings are found.
pub(crate) fn find_sparkable_bindings(
    bindings: &[(Symbol, MonoExpr)],
    constructors: &HashSet<Symbol>,
) -> Vec<usize> {
    let mut bound_names: HashSet<Symbol> = HashSet::new();
    // Names of earlier bindings that were themselves admitted as sparks — the
    // dependency-on-sparked carve-out tests membership here.
    let mut sparked_names: HashSet<Symbol> = HashSet::new();
    let mut sparkable: Vec<usize> = Vec::new();

    // Free-variable traversal over `MonoExpr` (the in-crate `find_free_vars`,
    // mirroring `cranelisp_types::free_vars_expr` over the post-mono AST).
    for (i, (name, val_expr)) in bindings.iter().enumerate() {
        let fv = find_free_vars(val_expr, &[]);
        // Admit iff worth sparking AND every earlier-bound dependency it
        // references is itself already sparked (so it is available as an IVar to
        // force on demand). Independent bindings (no earlier-bound free var)
        // satisfy the `all` vacuously.
        let deps_all_sparked = fv
            .iter()
            .filter(|v| bound_names.contains(*v))
            .all(|v| sparked_names.contains(v));

        if is_worth_sparking(val_expr, constructors) && deps_all_sparked {
            sparkable.push(i);
            sparked_names.insert(name.clone());
        }

        bound_names.insert(name.clone());
    }

    if sparkable.len() < 2 {
        Vec::new()
    } else {
        sparkable
    }
}

/// Find indices of sparkable arguments in a function application `(f a₁ … aₙ)`.
///
/// Sibling of [`find_sparkable_bindings`] for the apply-argument call site
/// (`design/backend/lenient-eval.md` §2.5). Per Principle 7 it shares the gate
/// helpers verbatim — [`is_worth_sparking`], `CHEAP_BUILTINS`, the constructor
/// set, and the ≥2-candidate gate — differing only in its independence rule:
///
/// Apply arguments bind nothing into sibling scope (`a₂` cannot reference a name
/// bound by evaluating `a₁`), so **all arguments are mutually independent by
/// construction** as pure expressions (§2.5.2). There is therefore no
/// `depends_on_earlier` free-var check — the `let` path's sequential-prefix rule
/// has no apply analogue. Independence collapses to "is this argument
/// individually worth sparking" (the cost heuristic) plus the ≥2 gate.
///
/// `constructors` is the set of known ADT constructor names (their args are
/// excluded exactly as in the `let` path — a constructor callee is alloc+tag,
/// not real work).
///
/// Returns an empty vec if fewer than 2 sparkable arguments are found — a single
/// expensive argument never pays IVar/thread-pool overhead for no concurrency.
pub(crate) fn find_sparkable_args(
    args: &[MonoExpr],
    constructors: &HashSet<Symbol>,
) -> Vec<usize> {
    let sparkable: Vec<usize> = args
        .iter()
        .enumerate()
        .filter(|(_, arg)| is_worth_sparking(arg, constructors))
        .map(|(i, _)| i)
        .collect();

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
///
/// Shared (single-source, Principle 7) by both lenient decision sites:
/// [`find_sparkable_bindings`] (the `let` path) and [`find_sparkable_args`]
/// (the apply-argument path).
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
