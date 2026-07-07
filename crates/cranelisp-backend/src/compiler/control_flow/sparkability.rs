// Sparkability analysis for lenient evaluation.
//
// This is the lenient-eval *decision* pass (`design/backend/lenient-eval.md
// §2`), distinct from the lenient *emission* in `let_if.rs`. It decides which
// `let` bindings are independent + non-trivial enough to be worth sparking as
// parallel IVar tasks.

use std::collections::HashSet;

use cranelisp_types::{ConcreteType, MonoExpr, Symbol};

use super::free_vars::find_free_vars;
use crate::compiler::fn_compiler::{node_confined, node_escapes};

/// Whether lenient evaluation is disabled via CRANELISP_NO_LENIENT=1.
pub(crate) static LENIENT_DISABLED: std::sync::LazyLock<bool> =
    std::sync::LazyLock::new(|| {
        std::env::var("CRANELISP_NO_LENIENT").is_ok_and(|v| v == "1")
    });

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
    std::sync::LazyLock::new(|| match std::env::var("CRANELISP_SPARK_ADMIT")
        .ok()
        .as_deref()
    {
        Some("syntactic") => SparkAdmit::Syntactic,
        _ => SparkAdmit::Mstatic,
    });

/// Whether capture-by-borrow across structured fork-join is enabled via
/// `CRANELISP_CAPTURE_BORROW=1` (Sprint 99 Wave 1b, FIXME 0461 / `ring2-rc.md`
/// §5.5.2 + `lenient-eval.md` §4.4.1).
///
/// **OFF by default** — this cure is under A/B ablation measurement/review
/// before it becomes default-on (a close-time decision after `/review`). When
/// unset the flag is never raised at any emission site, so the capture-store
/// inc + drop-glue dec path is **byte-identical** to the pre-S99 behaviour.
/// When set, a *structurally-joined* spark thunk's heap captures become
/// borrows (rc-invisible): the capture-store inc and its symmetric drop-glue
/// dec are both elided, because the joined parent frame outlives every spark
/// and its own scope-cleanup dec is the single dec accounting for the cell.
/// The detached `LaunchContinue` path never raises the flag (§5.5.2.1 exclusion).
pub(crate) static CAPTURE_BORROW_ENABLED: std::sync::LazyLock<bool> =
    std::sync::LazyLock::new(|| {
        std::env::var("CRANELISP_CAPTURE_BORROW").is_ok_and(|v| v == "1")
    });

/// Known-cheap builtins that are not worth sparking.
/// Single-instruction or near-single-instruction at the hardware level.
const CHEAP_BUILTINS: &[&str] = &[
    "+", "-", "*", "/", "=", "<", ">", "<=", ">=", "not", "and", "or",
];

/// B4 static allocation/RC-density admission axis default threshold
/// (`design/backend/lenient-eval.md` §2.7; ladder entry B4 in
/// `design/backend/ownership-codegen.md` §13.2/§13.4).
///
/// A spark candidate whose density score **exceeds** this bound is DECLINED —
/// it compiles on the sequential arm exactly as a cheap candidate. Declining is
/// always sound (§8 observational equivalence; the decline direction restores
/// the never-slower-than-serial floor rather than risking it).
///
/// **Chosen by measurement at this change-set** (S102 increment I, settled
/// load). With the [`spark_density`] scoring (below), a scalar-returning
/// compute-bound spark (F1/`fib`'s `(reduce-tree …)` / `(fib …)` — result
/// `Int`) scores `0` and is admitted; a *confined* heap-returning spark scores
/// `1` and is admitted; an **escaping, cross-strand (non-confined) heap-
/// returning** spark (F4's `(solve-range …)` speculative search over the shared
/// grid — result a `SolveResult` ADT) scores `2` and is DECLINED at this bound.
/// `2` therefore moves the F4-hard parallel wall toward serial (its purpose)
/// while leaving every compute-bound / lightly-allocating shape admitted (the
/// §9 near-linear-speedup acceptance unchanged, I-G4 non-regression held). See
/// the as-built note in `ownership-codegen.md` §13.4.
///
/// **S104 Wave 0 default-flip `1 → 0` (B4 off by default)** — `lenient-eval.md`
/// §2.8.5, `effect-concurrency.md` §3.1.1. B4 is *net-harmful* at full cores on
/// the recursion/search class (it declines the coarse D&C sparks while the fine
/// score-0 accessors stay admitted — the incoherent decline-coarse-while-
/// admitting-nested-fine state; 0534). With M-static owning *selection* and
/// M-dynamic owning *quantity* (Waves 1–2), B4 has no role for that class. The
/// §2.7 design + the scoring machinery are **preserved** (they still serve the
/// alloc/RC-dense compute class and may return Phase-H-composed); only the
/// default polarity changes. `CRANELISP_SPARK_DENSITY_MAX=N` still opts back in
/// (the Stage-0 B4-on diagnostic row). `0` = axis inert (never declines).
const SPARK_DENSITY_MAX_DEFAULT: usize = 0;

/// The active density threshold. `CRANELISP_SPARK_DENSITY_MAX=N` overrides
/// [`SPARK_DENSITY_MAX_DEFAULT`]; **`0` disables the axis entirely** (no
/// candidate is ever declined by density — the pre-B4 admission set verbatim).
/// A non-parsing value falls back to the default. Read once per process.
pub(crate) static SPARK_DENSITY_MAX: std::sync::LazyLock<usize> =
    std::sync::LazyLock::new(|| {
        std::env::var("CRANELISP_SPARK_DENSITY_MAX")
            .ok()
            .and_then(|v| v.parse::<usize>().ok())
            .unwrap_or(SPARK_DENSITY_MAX_DEFAULT)
    });

/// `CRANELISP_SPARK_DENSITY_TRACE=1` — silent-by-default diagnostic that prints
/// one line per spark candidate reaching the density axis (`[SPARK_DENSITY] …`)
/// with its engaged/score/decision. Codegen-time only; no emitted IR, so it is
/// byte-identical whether set or not (it is the measurement instrument that set
/// [`SPARK_DENSITY_MAX_DEFAULT`], kept as a durable diagnostic).
static SPARK_DENSITY_TRACE: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| {
    std::env::var("CRANELISP_SPARK_DENSITY_TRACE").is_ok_and(|v| v == "1")
});

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

        if worth(val_expr) && deps_all_sparked {
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

/// Check if an expression is worth sparking.
///
/// Two axes, both single-source (Principle 7) — shared verbatim by both lenient
/// decision sites, [`find_sparkable_bindings`] (the `let` path) and
/// [`find_sparkable_args`] (the apply-argument path):
///
/// 1. **Compute axis (§2.2, unchanged):** the candidate must be a non-trivial
///    function call — an `Apply` whose callee is neither a cheap builtin
///    (`+`, `-`, …) nor a data constructor (`Some`, `Cons`). Literals, var
///    refs, and non-`Apply` nodes are excluded.
/// 2. **Density axis (B4, §2.7):** even a compute-worthy candidate is DECLINED
///    when its allocation/RC-density score exceeds the threshold — it then
///    compiles on the sequential arm exactly as a cheap candidate. See
///    [`density_declines`].
fn is_worth_sparking(expr: &MonoExpr, constructors: &HashSet<Symbol>) -> bool {
    let compute_worthy = match expr {
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
    };

    compute_worthy && !density_declines(expr)
}

/// The B4 density decline verdict (`design/backend/lenient-eval.md` §2.7).
///
/// Returns `true` when the candidate's allocation/RC-density score **exceeds**
/// the threshold — i.e. it should be declined and compiled sequentially.
///
/// **Two inert conditions restore the pre-B4 admission set verbatim:**
/// - `CRANELISP_SPARK_DENSITY_MAX=0` disables the axis (never declines).
/// - The candidate carries **no** `Some` ownership site fact ⇒ pass5 did not
///   annotate it (`CRANELISP_NO_OWNERSHIP`, a pre-increment-I build, or any
///   facts-absent unit). [`spark_density`] returns `None`, the axis is inert,
///   and admission is byte-for-byte today's. This is the §2.2 byte-identity
///   discipline realized **structurally**: with zero `Some` facts anywhere the
///   axis provably cannot change any admission decision — the polarity the
///   toggle needs (a facts-absent build must NOT naively score, else every
///   heap site would count dense and sparking would vanish, the wrong failure
///   mode). See the L-B1 golden differential expectation for B4 (§13.2).
fn density_declines(expr: &MonoExpr) -> bool {
    let max = *SPARK_DENSITY_MAX;
    if max == 0 {
        return false; // axis disabled via CRANELISP_SPARK_DENSITY_MAX=0
    }
    let verdict = spark_density(expr);
    if *SPARK_DENSITY_TRACE {
        eprintln!(
            "[SPARK_DENSITY] engaged={} score={:?} max={} decision={}",
            verdict.is_some(),
            verdict,
            max,
            if verdict.is_some_and(|s| s > max) { "decline" } else { "admit" },
        );
    }
    // Inert (None) ⇒ admit as today. Engaged ⇒ decline iff over the threshold.
    verdict.is_some_and(|score| score > max)
}

/// Is a codegen result type heap-represented (String / closure / ADT — Vec is
/// an ADT) rather than an unboxed scalar (Int / Bool / Float)? A scalar-
/// returning call (`fib`, the F1/F2 `reduce-tree` accumulator) allocates
/// nothing at its own site and produces no RC-managed cell, so it is not a
/// scored density site. Exact on [`ConcreteType`] — no symbol-table lookup
/// needed (the authoritative `FnCompiler::is_heap_type` resolves ADT layout for
/// codegen; the density heuristic only needs the coarse scalar-vs-heap split,
/// and any misclassification only shifts a *scheduling* choice, never
/// correctness — declining is always sound, §8).
fn result_is_heap(ty: &ConcreteType) -> bool {
    matches!(
        ty,
        ConcreteType::String | ConcreteType::Fn(..) | ConcreteType::ADT(..)
    )
}

/// Whether a node is one of the five allocation/capture-producing variants that
/// carry ownership site facts (`design/arch/ownership-inference.md` §3.2 — the
/// same set `node_escapes` / `node_confined` read).
fn is_fact_bearing(node: &MonoExpr) -> bool {
    matches!(
        node,
        MonoExpr::StringLit { .. }
            | MonoExpr::Lambda { .. }
            | MonoExpr::Apply { .. }
            | MonoExpr::VecLit { .. }
            | MonoExpr::ConstrADT { .. }
    )
}

/// The B4 density score over a spark-candidate subtree
/// (`design/backend/lenient-eval.md` §2.7). Consumes **only** the per-site
/// `escapes` / `confined` facts pass5 already annotated (zero new analysis,
/// Principle 7 — reusing the `node_escapes` / `node_confined` single-source
/// readers B3.3/B3.4 use).
///
/// Returns:
/// - `None` — **axis inert**: the subtree carries no `Some` ownership fact, so
///   pass5 did not run over it. Admission is byte-identical to today (the
///   engage gate; see [`density_declines`]).
/// - `Some(score)` — pass5 ran; `score` is the density proxy for the S99 (b)
///   term (the concurrent atomic-RC + allocator traffic this branch generates):
///     - **+1** (heap-allocation / heap-pressure axis) per heap-producing
///       fact-bearing site NOT covered by a `NoEscape` fact
///       (`escapes != Some(false)` — it will contend on the shared allocator;
///       fact-absent counts dense);
///     - **+1** (surviving-RC axis) per such site whose RC op survives — the
///       cell is neither `Confined` (`confined == Some(true)` ⇒ non-atomic, no
///       cross-core bounce) nor borrow-elided (an `Apply` projection with a
///       `provenance` root, whose op is elided entirely). Fact-absent counts
///       dense.
///   A `NoEscape` site (`escapes == Some(false)`) contributes **0** to both
///   axes: it is stack/region-served with an immortal-RC header, so neither its
///   allocation nor its RC ops are real contention (§4.2). A scalar-returning
///   site (not [`result_is_heap`]) is not scored at all.
pub(crate) fn spark_density(expr: &MonoExpr) -> Option<usize> {
    let mut engaged = false;
    let mut score = 0usize;
    accumulate_density(expr, &mut engaged, &mut score);
    engaged.then_some(score)
}

/// Post-order walk feeding [`spark_density`]. `engaged` becomes true on the
/// first `Some` escapes/confined fact anywhere in the subtree (⇒ pass5 ran);
/// `score` accumulates the per-site density per the rules in `spark_density`.
fn accumulate_density(node: &MonoExpr, engaged: &mut bool, score: &mut usize) {
    // Engage signal — any Some site fact means pass5 annotated this subtree.
    let esc = node_escapes(node);
    let conf = node_confined(node);
    if esc.is_some() || conf.is_some() {
        *engaged = true;
    }

    // Score only genuine heap allocation / RC sites (fact-bearing + heap
    // result). A scalar-returning `Apply` (fib / reduce-tree) allocates nothing
    // at its own site and is skipped — this is what keeps compute-bound sparks
    // admitted (§9). The four non-`Apply` alloc variants are always heap.
    if is_fact_bearing(node) && result_is_heap(node.ty()) {
        match esc {
            // NoEscape: stack/region-served + immortal-RC header ⇒ no allocator
            // contention and no surviving RC traffic (§4.2). Contributes 0.
            Some(false) => {}
            _ => {
                *score += 1; // heap-pressure axis
                let borrow_elided =
                    matches!(node, MonoExpr::Apply { provenance: Some(_), .. });
                if conf != Some(true) && !borrow_elided {
                    *score += 1; // surviving-RC axis
                }
            }
        }
    }

    // Recurse into every child (the same subtree shape the sparkability walk and
    // `node_*` readers cover). Non-fact-bearing structural nodes still recurse so
    // a nested allocation deep in the candidate is scored.
    for child in mono_children(node) {
        accumulate_density(child, engaged, score);
    }
}

/// Immediate `MonoExpr` children, for the density walk. Total match so a new
/// variant is a compile error here (mirrors the `node_escapes` discipline).
fn mono_children(node: &MonoExpr) -> Vec<&MonoExpr> {
    match node {
        MonoExpr::IntLit { .. }
        | MonoExpr::FloatLit { .. }
        | MonoExpr::BoolLit { .. }
        | MonoExpr::StringLit { .. }
        | MonoExpr::Var { .. } => Vec::new(),
        MonoExpr::Let { bindings, body, .. } | MonoExpr::ParBind { bindings, body, .. } => {
            let mut v: Vec<&MonoExpr> = bindings.iter().map(|(_, e)| e).collect();
            v.push(body);
            v
        }
        MonoExpr::If { cond, then_branch, else_branch, .. } => {
            vec![cond, then_branch, else_branch]
        }
        MonoExpr::Lambda { body, .. } => vec![body],
        MonoExpr::Apply { callee, args, .. } => {
            let mut v = vec![callee.as_ref()];
            v.extend(args.iter());
            v
        }
        MonoExpr::Match { scrutinee, arms, .. } => {
            let mut v = vec![scrutinee.as_ref()];
            v.extend(arms.iter().map(|a| &a.body));
            v
        }
        MonoExpr::VecLit { elements, .. } => elements.iter().collect(),
        MonoExpr::Trace { body, .. } => vec![body],
        MonoExpr::LaunchContinue { launched, continuation, .. } => {
            vec![launched, continuation]
        }
        MonoExpr::ConstrADT { fields, .. } => fields.iter().collect(),
    }
}
