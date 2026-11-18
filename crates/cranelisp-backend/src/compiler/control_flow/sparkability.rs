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
    std::sync::LazyLock::new(|| std::env::var("CRANELISP_NO_LENIENT").is_ok_and(|v| v == "1"));

/// Which admission filter governs *which* spark candidates are admitted
/// (`design/backend/lenient-eval.md` §2.8.2 / §2.8.6). Selected once per process
/// by `CRANELISP_SPARK_ADMIT`:
///
/// - `mstatic` (**default**, S104 Wave 1) — the M-static QUALITY axis: a
///   candidate `Apply` is admitted iff its resolved callee is in a **recursive
///   SCC** of the static call graph (incl. direct self-recursion) **and** the
///   apply is **not** in tail position — the *probably-large* (non-tail
///   recursion) signal that declines the fine flat-accessor firehose (0534)
///   structurally while keeping the coarse divide-and-conquer sparks. Wired at
///   both spark sites via `FnCompiler::mstatic_admits_candidate` over the
///   single-sourced classifier (`control_flow::utilization`).
/// - `syntactic` — the pre-S104 §2.2 filter ([`is_worth_sparking`]: a non-cheap,
///   non-constructor `Apply`). Kept selectable so `/qa`'s Stage-0 matrix can run
///   the old admission as its comparison row against `mstatic`.
///
/// The independence rule (`let`-path §2.6 carve-out / apply-path §2.5.2) and the
/// ≥2-candidate gate are unchanged and single-source across both filters — only
/// the per-candidate "worth admitting" predicate swaps (Principle 7).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum SparkAdmit {
    Mstatic,
    Syntactic,
}

/// The active spark-admission filter. `CRANELISP_SPARK_ADMIT=syntactic` selects
/// the pre-S104 syntactic filter; any other value (including unset and
/// `mstatic`) selects M-static, the S104 Wave-1 default. Read once per process.
pub(crate) static SPARK_ADMIT: std::sync::LazyLock<SparkAdmit> =
    std::sync::LazyLock::new(
        || match std::env::var("CRANELISP_SPARK_ADMIT").ok().as_deref() {
            Some("syntactic") => SparkAdmit::Syntactic,
            _ => SparkAdmit::Mstatic,
        },
    );

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
    // The syntactic §2.2 admission filter (`CRANELISP_SPARK_ADMIT=syntactic`).
    find_sparkable_bindings_with(bindings, |e| is_worth_sparking(e, constructors))
}

/// Admission-predicate-parametric core of [`find_sparkable_bindings`]
/// (`design/backend/lenient-eval.md` §2.8.2). The `worth` predicate is the sole
/// per-candidate admission test; the **independence carve-out** (§2.6 —
/// dependency-on-sparked) and the **≥2-candidate gate** stay here, single-source
/// (Principle 7), so both the syntactic filter and the M-static recursion signal
/// compose with them identically:
///
/// - Syntactic filter — `worth = |e| is_worth_sparking(e, constructors)`
///   ([`find_sparkable_bindings`]).
/// - M-static filter — `worth = |e| self.mstatic_admits_candidate(e, &recursive)`
///   (the recursive-SCC ∧ non-tail signal; wired at `compile_let`'s §4.1 seam).
///
/// A binding at index `i` is admitted iff `worth(rhs)` holds AND every
/// earlier-bound free var it references is *itself* already in the admitted set
/// (available as an IVar to force on demand). Because `let` bindings are
/// sequential, dependencies only point backward, so a single left-to-right pass
/// suffices. Returns an empty vec if fewer than 2 candidates survive.
pub(crate) fn find_sparkable_bindings_with(
    bindings: &[(Symbol, MonoExpr)],
    worth: impl Fn(&MonoExpr) -> bool,
) -> Vec<usize> {
    // Positions of earlier bindings that were themselves admitted as sparks —
    // the dependency-on-sparked carve-out tests membership here. POSITIONS, not
    // names (`design/backend/binding-scope.md` §"Binding environment"): a non-sparked rebinding of
    // a sparked name displaces it by construction, so the carve-out answers
    // about the binder the dependency actually denotes.
    let mut sparked: HashSet<usize> = HashSet::new();
    let mut sparkable: Vec<usize> = Vec::new();

    // Free-variable traversal over `MonoExpr` (the in-crate `find_free_vars`,
    // mirroring `cranelisp_types::free_vars_expr` over the post-mono AST).
    for (i, (_, val_expr)) in bindings.iter().enumerate() {
        let fv = find_free_vars(val_expr, &[]);
        // Admit iff worth sparking AND every earlier-bound dependency it
        // references is itself already sparked (so it is available as an IVar to
        // force on demand). Independent bindings (no earlier-bound free var)
        // satisfy the `all` vacuously.
        let deps_all_sparked = fv
            .iter()
            .filter_map(|v| binder_before(bindings, i, v))
            .all(|j| sparked.contains(&j));

        if worth(val_expr) && deps_all_sparked {
            sparkable.push(i);
            sparked.insert(i);
        }
    }

    if sparkable.len() < 2 {
        Vec::new()
    } else {
        sparkable
    }
}

/// Which binder does `name` denote immediately before position `i` in this
/// binding vector?
///
/// THE shared resolver for per-binding-vector lenient state
/// (`design/backend/binding-scope.md` §"Binding environment"). `let` bindings are sequential, so
/// the answer is the LATEST binder at a position `< i` bearing the name; `None`
/// means the name is free in the vector (an enclosing binding, a capture or a
/// global). Reading the per-vector state through this one function is what makes
/// a rebinding displace an earlier binder's spark record structurally: in
/// `(let [a (ping n) a 5 c (ping a)] c)` the `a` that `c` denotes is position 1,
/// which was never sparked, so `c` is not independent of it and reads 5.
pub(crate) fn binder_before(
    bindings: &[(Symbol, MonoExpr)],
    i: usize,
    name: &Symbol,
) -> Option<usize> {
    bindings[..i.min(bindings.len())]
        .iter()
        .rposition(|(bound, _)| bound == name)
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
pub(crate) fn find_sparkable_args(args: &[MonoExpr], constructors: &HashSet<Symbol>) -> Vec<usize> {
    // The syntactic §2.2 admission filter (`CRANELISP_SPARK_ADMIT=syntactic`).
    find_sparkable_args_with(args, |e| is_worth_sparking(e, constructors))
}

/// Admission-predicate-parametric core of [`find_sparkable_args`]
/// (`design/backend/lenient-eval.md` §2.8.2). Apply arguments are mutually
/// independent by construction (§2.5.2 — nothing binds into a sibling's scope),
/// so admission collapses to the per-candidate `worth` predicate plus the ≥2
/// gate — no independence carve-out. The `worth` predicate is single-source
/// (Principle 7): the syntactic wrapper passes [`is_worth_sparking`]; the
/// M-static seam at `compile_apply` §4.4 passes the recursive-SCC ∧ non-tail
/// signal (`FnCompiler::mstatic_admits_candidate`). Returns an empty vec if
/// fewer than 2 candidates survive.
pub(crate) fn find_sparkable_args_with(
    args: &[MonoExpr],
    worth: impl Fn(&MonoExpr) -> bool,
) -> Vec<usize> {
    let sparkable: Vec<usize> = args
        .iter()
        .enumerate()
        .filter(|(_, arg)| worth(arg))
        .map(|(i, _)| i)
        .collect();

    if sparkable.len() < 2 {
        Vec::new()
    } else {
        sparkable
    }
}

/// Check if an expression is worth sparking (§2.2), shared by both lenient
/// decision sites, [`find_sparkable_bindings`] (the `let` path) and
/// [`find_sparkable_args`] (the apply-argument path): the candidate must be a
/// non-trivial function call — an `Apply` whose callee is neither a cheap
/// builtin (`+`, `-`, …) nor a data constructor (`Some`, `Cons`). Literals,
/// var refs and non-`Apply` nodes are excluded.
fn is_worth_sparking(expr: &MonoExpr, constructors: &HashSet<Symbol>) -> bool {
    match expr {
        MonoExpr::Apply { callee, .. } => {
            if let MonoExpr::Var { name, .. } = callee.as_ref() {
                // Cheap builtins and constructors are not worth sparking. The
                // ctor-exclusion set holds bare terminal names (§10.4); compare
                // the callee through the SAME `bare_member_name` grammar so a
                // dotted / FQ / bare sum-ctor call all match.
                !CHEAP_BUILTINS.contains(&name.as_ref())
                    && !constructors.contains(&Symbol::from(cranelisp_types::bare_member_name(
                        name.as_ref(),
                    )))
            } else {
                // Non-variable callee (computed function) — conservatively spark.
                true
            }
        }
        // Non-Apply expressions are not worth sparking.
        _ => false,
    }
}
