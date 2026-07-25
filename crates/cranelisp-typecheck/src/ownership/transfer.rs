//! CS-2 — the transfer function
//! (`design/typecheck/ownership-inference.md` §3.3, §4.2, §13.2 CS-2).
//!
//! One pre-order [`MonoExpr`] body walk producing a [`ModeSummary`], the
//! per-site facts ([`SiteFacts`]), and the harvested dependency set
//! ([`DepSet`]). **Pure** — it holds no symbol table; every callee fact arrives
//! through the [`TransferEnv`] abstraction (real pass: a chain-follow wrapper;
//! unit tests: a `HashMap`-backed fixture). This is the §11 testability pin.
//!
//! # What one walk computes (§3.3)
//!
//! - **Per-param mode** (`param_modes`) — init `Copy` (scalars) / `Borrowed`,
//!   widened to `Owned` at owned-handoff / Decision-24 / store / return /
//!   escaping-capture / suspension edges. This is the ABI-bearing half.
//! - **Per-param flow** (`param_flow`, advisory) — `Consumed` / `IntoResult` /
//!   the conservative `Retained` default. Over-approximating toward `Retained`
//!   is always sound (spine §6.1); this pass computes the precise `Consumed` /
//!   `IntoResult` only for the clear cases and defaults the rest to `Retained`.
//! - **Result mode** (`result`) — from the tail position(s), with the
//!   §13.6(c) multi-path join.
//! - **Escape + provenance site facts** — escape edges per §2.2 rules 1–5
//!   (incl. R6 suspension), borrowed-projection roots per §4.2.
//! - **Value-use marks** — callable names referenced in non-callee position (§8.3).
//!
//! `spark_ops` is initialised all-`false` (optimistic-clear) here and widened
//! by the confinement stratum (CS-3); `result_unique` is hardwired `false`
//! (increment-I pin, §10). Monotone soundness: every join only widens.

use std::collections::{HashMap, HashSet};

use cranelisp_types::{
    ConcreteType, FQSymbol, Mode, ModeSummary, MonoExpr, MonoMatchArm, ParamFlow, Pattern,
    ResultMode, Span, Symbol,
};

use super::classify::{CallClass, CopyClassifier, TerminalKind, classify_call};

/// The harvested dependency set (§13.3): every in-cluster callee whose summary
/// an `Apply` classification consulted, at the grain consulted. Drives fixpoint
/// re-entry (self-describing — immune to any persisted-feed gap).
pub(crate) type DepSet = HashSet<FQSymbol>;

/// Advisory site facts computed by the transfer walk, keyed by node span
/// (`design/arch/ownership-inference.md` §3.2). The confinement stratum (CS-3)
/// fills `confined`; CS-4 writes all of these onto the stored `codegen_view`.
#[derive(Debug, Default, Clone)]
pub(crate) struct SiteFacts {
    /// span → `escapes` verdict for allocation / capture / store sites.
    pub escapes: HashMap<Span, bool>,
    /// span → `confined` verdict (filled by confinement, CS-3).
    pub confined: HashMap<Span, bool>,
    /// span → borrowed-projection root binding (Apply accessor / `vec-get` /
    /// match-arm sites; §4.4). Symbol-keyed with the §13.6(d) shadow rule.
    pub provenance: HashMap<Span, Symbol>,
    /// span → `unique_static` verdict for a fresh-producing node proven a
    /// unique single-use root (§14.2, CS-II-2, increment II). Only ever
    /// `Some(true)` entries are inserted; absent ⇒ `None` ⇒ conservative
    /// (no reuse). Filled by the uniqueness stratum (CS-3, [`super::uniqueness`]).
    pub unique: HashMap<Span, bool>,
}

/// The result of one body transfer walk.
#[derive(Debug, Clone)]
pub(crate) struct TransferResult {
    pub summary: ModeSummary,
    pub facts: SiteFacts,
    pub deps: DepSet,
    /// Callable names referenced in value position in this body (§8.3).
    pub value_uses: HashSet<Symbol>,
}

/// The callee-fact abstraction the transfer walk consults — the only coupling
/// to the symbol table, kept behind a trait so the walk stays pure and
/// unit-testable (§11).
pub(crate) trait TransferEnv {
    /// The terminal callable kind a callee `Var` name chain-resolves to — for
    /// the classifier's `resolved_call == None` row. A local `let`/param
    /// binding or an unresolved name yields `None` (⇒ Decision-24).
    fn terminal_kind(&self, name: &Symbol) -> Option<TerminalKind>;
    /// The callee summary + its FQ identity for a summarised call. `None` reads
    /// as ⊤ (the Decision-24 conservative point). The `FQSymbol` is recorded in
    /// the `DepSet` (in-cluster callees only re-enter; leaves/imports are
    /// boundary conditions).
    fn summary_of(&self, name: &Symbol) -> Option<(FQSymbol, ModeSummary)>;
}

/// The context a sub-expression is evaluated in — determines how a param use
/// classifies (widen + flow) and whether an allocation escapes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum UseCtx {
    /// The callee position of an `Apply` — a callable name here is a call, not
    /// a value-use.
    CalleePos,
    /// A neutral read position (cond, scrutinee, non-tail let value) — no escape.
    Neutral,
    /// An argument to a summarised callee at param position with this mode+flow.
    Arg { mode: Mode, flow: ParamFlow },
    /// An argument to a Decision-24 site — Owned + Retained (rule 5).
    Decision24Arg,
    /// A field stored into an aggregate; a stored param inherits this flow
    /// (`IntoResult` when the aggregate is directly returned, `Retained` when
    /// the aggregate escapes by retention, `Consumed` when it stays local).
    Field { flow: ParamFlow },
    /// The tail / return position of the body.
    Return,
    /// Captured by an escaping closure, or crossing a suspension edge (R6).
    EscapingCapture,
}

impl UseCtx {
    /// Does a value produced in this context escape its frame?
    fn escapes(self) -> bool {
        match self {
            UseCtx::Return | UseCtx::EscapingCapture | UseCtx::Decision24Arg => true,
            UseCtx::Arg { mode, flow } => {
                mode == Mode::Owned && matches!(flow, ParamFlow::Retained | ParamFlow::IntoResult)
            }
            UseCtx::Field { flow } => matches!(flow, ParamFlow::Retained | ParamFlow::IntoResult),
            UseCtx::CalleePos | UseCtx::Neutral => false,
        }
    }

    /// The flow a param stored into an aggregate constructed in this context
    /// inherits.
    fn field_flow(self) -> ParamFlow {
        match self {
            UseCtx::Return => ParamFlow::IntoResult,
            UseCtx::Arg {
                mode: Mode::Owned,
                flow,
            } => flow,
            UseCtx::Decision24Arg | UseCtx::EscapingCapture => ParamFlow::Retained,
            UseCtx::Field { flow } => flow,
            UseCtx::Arg { .. } | UseCtx::CalleePos | UseCtx::Neutral => ParamFlow::Consumed,
        }
    }
}

/// The provenance/freshness of an expression's value — the §16.1 monotone
/// provenance lattice (S113 W5, `safety-invariants.md` §3a). Ordered by CLAIM
/// STRENGTH: `Fresh` and `Unconditional` are the STRONG claims (each licenses a
/// safety-op elision); `Conditional` is the conservative ⊤-ward point.
///
/// The §16.3 P20 reshape makes "publish a hard claim from a conditional origin"
/// STRUCTURALLY unrepresentable (B-2's class becomes a non-compile, not a review
/// finding): the hard-claim producer arms (`origin_to_result_mode`'s
/// `AliasOf`/`ProjectionOf`) pattern-match ONLY `Unconditional`, and every
/// constructor that handles a conditional input (rows 3/4/5/6) builds ONLY
/// `Conditional`. Internal-only — the persisted `ResultMode` already carries the
/// conditional point (`MayAliasOf`, schema 20), so NO types edit / NO schema bump
/// (§16.3 verdict).
#[derive(Debug, Clone)]
enum Origin {
    /// A fresh allocation / `Fresh`-result call / literal — no param reaches it.
    Fresh,
    /// UNCONDITIONAL: this value IS param `root`'s reference on EVERY path (a
    /// param used directly, or a `let x = p` alias when `projection == false`) —
    /// or a borrowed view of it on every path (`projection == true`, the clean
    /// accessor). The strong claim that licenses a hard `AliasOf`/`ProjectionOf`
    /// publish (row 9). Constructable ONLY from a provably-unconditional source.
    Unconditional { root: Symbol, projection: bool },
    /// CONDITIONAL (the ⊤-ward conservative point, today's `MayParam`): the value
    /// MAY reach param `rep` on some control-flow path and be fresh/other on
    /// another — the not-`Fresh` join of divergent paths (FIXME 0520), a COW
    /// may-alias, an element-store fold, or a projection of a conditional
    /// container. `rep` is a representative param-rooted binding (lowest reaching
    /// index on a join). A hard claim is UNREPRESENTABLE from here — it can only
    /// publish `MayAliasOf` (§16.3), keeping every protect/dec the fresh arm needs.
    ///
    /// **`cow` — the may-alias LINK set (§17.2, S115 MS-P7 chained family).** The
    /// `Apply` spans at which a `MayAliasOf`-declared call MINTED a may-alias
    /// reference on this value's provenance chain. The obligation "every
    /// may-alias link whose accounting includes a consumer-emitted release needs
    /// its protect" belongs to the VALUE (P25 — narrowing carries its check), not
    /// to a consumer's syntactic view of its argument, so the value carries its
    /// own allocation history: row 8 unions each new link, rows 2/4 carry and
    /// join it, and the single projection-out consumer (row 6) discharges the
    /// WHOLE chain by forcing the escape fact at every carried span. This is what
    /// makes a chain of length ≥2 — nested `Apply`, or `let`-mediated `Var` —
    /// reachable from one arm instead of one arm per chain shape (§17.3).
    ///
    /// Walk-internal ONLY: it never crosses the summary boundary (the persisted
    /// `ResultMode` is unchanged — §17.6, no `cranelisp-types` edit, no
    /// `CACHE_SCHEMA_VERSION` bump).
    Conditional {
        rep: Symbol,
        projection: bool,
        cow: Vec<Span>,
    },
}

impl Origin {
    /// Construct an unconditional alias (`projection == false`) or borrowed view
    /// (`projection == true`) — the ex-`Root`/`Projection` variants.
    fn unconditional(root: Symbol, projection: bool) -> Origin {
        Origin::Unconditional { root, projection }
    }
    /// Construct a conditional (may-reach) origin — the ex-`MayParam` variant —
    /// carrying `cow`, the §17.2 may-alias link set.
    fn conditional(rep: Symbol, projection: bool, cow: Vec<Span>) -> Origin {
        Origin::Conditional {
            rep,
            projection,
            cow,
        }
    }
    fn root(&self) -> Option<&Symbol> {
        match self {
            Origin::Unconditional { root, .. } => Some(root),
            Origin::Conditional { rep, .. } => Some(rep),
            Origin::Fresh => None,
        }
    }
    /// The §17.2 may-alias link set this value carries (empty for every origin
    /// that is not a `Conditional`).
    fn cow_spans(&self) -> &[Span] {
        match self {
            Origin::Conditional { cow, .. } => cow,
            Origin::Fresh | Origin::Unconditional { .. } => &[],
        }
    }
}

/// UNION two may-alias link sets (§17.2 rows 4/8), order-stable and deduped —
/// the set only ever grows along a chain, so the composition is monotone.
fn union_cow(a: &[Span], b: &[Span]) -> Vec<Span> {
    let mut out: Vec<Span> = a.to_vec();
    for s in b {
        if !out.contains(s) {
            out.push(*s);
        }
    }
    out
}

#[derive(Debug, Clone)]
struct BindState {
    origin: Origin,
    /// `Some(idx)` iff this binding is a formal parameter.
    param_idx: Option<usize>,
}

/// A saved lexical-scope frame (§13.6(i), F4 cure). For every name a binding
/// scope (`Let`, `ParBind`, each `Match` arm) introduces, records the value
/// `bindings` held for that name **before** the insertion (`None` if the name
/// was unbound). On scope EXIT the frame is replayed in reverse so `bindings`
/// faithfully models lexical scope: a name shadowed by an inner branch-sibling
/// binding is restored to its outer/param `BindState` before a sibling scope is
/// walked, closing the ABI-half narrowing (`param_modes` Owned→Borrowed) that
/// the flat, never-restored map caused. Params are the base frame, never
/// restored away.
type ScopeFrame = Vec<(Symbol, Option<BindState>)>;

struct Walker<'e, E: TransferEnv> {
    env: &'e E,
    bindings: HashMap<Symbol, BindState>,
    /// Per-param accumulated mode (index-aligned with the formal list).
    param_modes: Vec<Mode>,
    param_flow: Vec<ParamFlow>,
    /// `true` for params seeded `Copy` — never widened.
    param_copy: Vec<bool>,
    facts: SiteFacts,
    deps: DepSet,
    value_uses: HashSet<Symbol>,
    /// Fresh-aggregate bindings discovered to escape (used in a return / store /
    /// retained-arg context) during the enclosing `Let` body walk, with the
    /// escaping context. Drained per-`Let` after its body: the RHS is re-walked
    /// in `ctx` so folded-in params widen (`Consumed`→`IntoResult`/`Retained`)
    /// and the aggregate's escape fact flips (§13.6, blocker 1). Monotone —
    /// every re-walk only widens.
    escaped: Vec<(Symbol, UseCtx)>,
}

impl<'e, E: TransferEnv> Walker<'e, E> {
    /// Resolve a binding name to the formal-parameter it ultimately roots in
    /// (following `Root` aliases), or `None` if it roots in no param.
    fn param_root(&self, name: &Symbol) -> Option<usize> {
        let mut cur = name.clone();
        let mut guard = 0;
        loop {
            guard += 1;
            if guard > 64 {
                return None;
            }
            let bs = self.bindings.get(&cur)?;
            if let Some(idx) = bs.param_idx {
                return Some(idx);
            }
            match &bs.origin {
                // An unconditional ALIAS (`projection:false`) IS its root — follow
                // the chain. An unconditional PROJECTION is a borrowed view, NOT an
                // alias, so it is NOT followed here (a projection rooted in a param
                // is reached by `classify_capture_escape`'s recursion instead).
                Origin::Unconditional {
                    root,
                    projection: false,
                } => cur = root.clone(),
                // A conditional binding roots (on its param-reaching path) in `rep`;
                // follow it (either projection kind) so a store of such a binding
                // widens the param (over-approximating toward Owned — always sound).
                Origin::Conditional { rep, .. } => cur = rep.clone(),
                _ => return None,
            }
        }
    }

    /// Map the body's final value origin to a [`ResultMode`] (§3.3). The
    /// multi-path join (§13.6(c) as corrected by FIXME 0520) is already applied
    /// via [`Walker::join_origin`] at `If`/`Match`: a partial param-return has
    /// become a [`Origin::MayParam`] (not `Fresh`), and only a provably-no-param
    /// path yields `Fresh`.
    fn origin_to_result_mode(&self, origin: &Origin) -> ResultMode {
        match origin {
            // Row 9 — the HARD-claim arms match ONLY `Unconditional` (§16.3 P20):
            // an alias publishes `AliasOf(i)`, a borrowed view `ProjectionOf(i)`
            // — both UNCONDITIONAL, so a consumer's elision is sound. A `root` (for
            // a projection) or the alias chain (`param_root`) that reaches no param
            // is an owned local returned by value ⇒ `Fresh`.
            Origin::Unconditional { root, projection } => match self.param_root(root) {
                Some(i) if *projection => ResultMode::ProjectionOf(i),
                Some(i) => ResultMode::AliasOf(i),
                None => ResultMode::Fresh,
            },
            // A CONDITIONAL claim can never publish a hard `AliasOf`/`ProjectionOf`
            // (a `Fresh` path exists) — both projection arms publish `MayAliasOf`
            // (S111 §15.3, spine §3.7(a1); §16.3): the consumer keeps its
            // protect/dec on the fresh arm. Retain-side imprecision (the
            // may-projection loses its provenance fact) is acceptable; the flagship
            // bare-accessor stays an `Unconditional` projection (row 6), so no
            // S99-target read-path shrinks.
            Origin::Conditional { rep, .. } => match self.param_root(rep) {
                Some(idx) => ResultMode::MayAliasOf(idx),
                None => ResultMode::Fresh,
            },
            Origin::Fresh => ResultMode::Fresh,
        }
    }

    /// The param a value origin can carry to the result, if any: `(param index,
    /// is-projection, representative param-rooted symbol)`, or `None` when the
    /// origin roots in no param (fresh, or an owned local returned by value —
    /// both `Fresh` at the result). The single reach classifier both
    /// [`Walker::join_origin`] strata and the result-mode read share.
    fn reach(&self, o: &Origin) -> Option<(usize, bool, Symbol)> {
        match o {
            Origin::Fresh => None,
            Origin::Unconditional { root, projection } => self
                .param_root(root)
                .map(|i| (i, *projection, root.clone())),
            Origin::Conditional {
                rep, projection, ..
            } => self.param_root(rep).map(|i| (i, *projection, rep.clone())),
        }
    }

    /// Join two value origins from divergent control-flow paths — the result may
    /// be `a` OR `b` (FIXME 0520, correcting §13.6(c)). The join is `Fresh`
    /// **only** when NEITHER path can carry a param to the result; any path that
    /// may alias/project a param makes the join a not-`Fresh` [`Origin::MayParam`].
    ///
    /// Collapsing a param-reaching disagreement to `Fresh` (the old rule) is the
    /// ABI-half soundness narrowing 0520 cures: `Fresh` means "not aliased to any
    /// param", which a borrow-elision consumer trusts to drop a needed RC op and
    /// free the returned param. Widening toward not-`Fresh` (may-alias) is always
    /// sound; `Fresh` is reserved for provably-no-param-reaches-result.
    ///
    /// When both paths reach the SAME param with the SAME kind, the definite
    /// origin is preserved (a full-`if`/same-param-`match` stays the precise
    /// `AliasOf(i)`/`ProjectionOf(i)`). Otherwise (a param vs fresh, two distinct
    /// params, or mixed alias/projection kinds) the conservative may-alias:
    /// representative = the reaching param of LOWEST index (deterministic);
    /// `projection` only when EVERY reaching path is a projection (a mixed
    /// alias/projection join is the stronger `AliasOf`, keeping protect).
    /// **Row 4 (§17.2, as CORRECTED by FIXME 0772) — the may-alias link sets
    /// UNION across the join, and the joined VARIANT is the ⊤-ward of the two
    /// operands, both INDEPENDENTLY OF OPERAND ORDER (P24).** An `If`/`Match`-
    /// produced container carries the links of BOTH arms, so the terminal
    /// projection-out (row 6) discharges whichever arm ran. Widening and
    /// monotone (the set only grows, and `Unconditional ⊑ Conditional`), and it
    /// is the composition — not a new consumer arm — that covers the face-3
    /// container shape (§17.4).
    ///
    /// The as-built pre-0772 arm read the joined variant off `a` alone
    /// (`match a { Conditional => …, other => other }`), which BOTH discarded
    /// the union it had just computed AND published a hard `AliasOf` claim from
    /// a may-alias operand — whenever `a` happened to be the `Unconditional`
    /// one. `MonoExpr::If` joins in source order, so the answer depended on
    /// which arm the COW producer was written in: the P24 acid test. Order
    /// symmetry is pinned by the `join_lattice_*` property cells in
    /// `transfer/tests.rs` (seam-level, no program involved).
    fn join_origin(&self, a: Origin, b: Origin) -> Origin {
        let cow = union_cow(a.cow_spans(), b.cow_spans());
        // `Conditional` is the ⊤-ward point of the variant lattice: a join with a
        // may-alias operand is a may-alias, whichever side contributed it.
        let conditional =
            matches!(a, Origin::Conditional { .. }) || matches!(b, Origin::Conditional { .. });
        match (self.reach(&a), self.reach(&b)) {
            (None, None) => Origin::Fresh,
            (Some((ia, pa, sa)), Some((ib, pb, _sb))) if ia == ib && pa == pb => {
                // Same param, same kind ⇒ both paths definitely reach it that
                // way, so the definite origin is preserved (a full-`if` /
                // same-param-`match` stays the precise `AliasOf(i)` /
                // `ProjectionOf(i)`) — but ONLY when NEITHER operand was itself a
                // may-alias. `rep`/`root` is a REPRESENTATIVE: `sa` and `sb` both
                // root in param `ia`, so either serves; `sa` keeps the
                // both-`Unconditional` path byte-identical to pre-0772.
                if conditional {
                    Origin::conditional(sa, pa, cow)
                } else {
                    Origin::unconditional(sa, pa)
                }
            }
            (Some((ia, pa, sa)), Some((ib, pb, sb))) => {
                let (idx_sym, _) = if ia <= ib { (sa, ia) } else { (sb, ib) };
                Origin::conditional(idx_sym, pa && pb, cow)
            }
            (Some((_, p, s)), None) | (None, Some((_, p, s))) => Origin::conditional(s, p, cow),
        }
    }

    /// Widen a param's mode/flow from a use in `ctx`. No-op for `Copy` params.
    fn classify_param_use(&mut self, idx: usize, ctx: UseCtx) {
        if self.param_copy[idx] {
            return;
        }
        match ctx {
            UseCtx::Arg {
                mode: Mode::Borrowed,
                ..
            }
            | UseCtx::Arg {
                mode: Mode::Copy, ..
            }
            | UseCtx::CalleePos
            | UseCtx::Neutral => { /* non-widening read / borrowed handoff */ }
            UseCtx::Arg {
                mode: Mode::Owned,
                flow,
            } => {
                self.param_modes[idx] = Mode::Owned;
                self.join_flow(idx, flow);
            }
            UseCtx::Decision24Arg | UseCtx::EscapingCapture => {
                self.param_modes[idx] = Mode::Owned;
                self.join_flow(idx, ParamFlow::Retained);
            }
            UseCtx::Field { flow } => {
                self.param_modes[idx] = Mode::Owned;
                self.join_flow(idx, flow);
            }
            UseCtx::Return => {
                self.param_modes[idx] = Mode::Owned;
                self.join_flow(idx, ParamFlow::IntoResult);
            }
        }
    }

    /// Join a param's flow toward the conservative point
    /// (`Consumed ⊑ IntoResult ⊑ Retained`).
    fn join_flow(&mut self, idx: usize, incoming: ParamFlow) {
        let rank = |f: ParamFlow| match f {
            ParamFlow::Consumed => 0,
            ParamFlow::IntoResult => 1,
            ParamFlow::Retained => 2,
        };
        if rank(incoming) > rank(self.param_flow[idx]) {
            self.param_flow[idx] = incoming;
        }
    }

    /// Walk an expression in `ctx`, returning its value's [`Origin`].
    fn walk(&mut self, expr: &MonoExpr, ctx: UseCtx) -> Origin {
        match expr {
            MonoExpr::IntLit { .. }
            | MonoExpr::FloatLit { .. }
            | MonoExpr::BoolLit { .. }
            | MonoExpr::StringLit { .. } => {
                if let MonoExpr::StringLit { span, .. } = expr {
                    self.facts.escapes.insert(*span, ctx.escapes());
                }
                Origin::Fresh
            }

            MonoExpr::Var { name, .. } => self.walk_var(name, ctx),

            MonoExpr::Let { bindings, body, .. } => {
                // §13.6(i) (F4): a scope frame saves each shadowed prior so the
                // bindings map is restored on scope exit (below) — lexical-scope
                // discipline, not a flat leak.
                let mut frame: ScopeFrame = Vec::with_capacity(bindings.len());
                for (n, rhs) in bindings {
                    // The RHS value's escape is not yet known (forward info);
                    // walk it Neutral and record its origin so uses of `n`
                    // propagate provenance. A param folded into a let-bound
                    // *Fresh* aggregate that later escapes is re-propagated by
                    // the post-body drain below (blocker 1); a `Root`/`Projection`
                    // binding's escape is re-classified through its origin at the
                    // escaping use of `n` (`param_root` reaches the param).
                    let origin = self.walk(rhs, UseCtx::Neutral);
                    // §13.6(d) let-shadow provenance guard (blocker 3, F2 helper).
                    self.drop_shadowed_provenance(n);
                    // Save the shadowed prior BEFORE inserting (scope discipline).
                    let prior = self.bindings.insert(
                        n.clone(),
                        BindState {
                            origin,
                            param_idx: None,
                        },
                    );
                    frame.push((n.clone(), prior));
                }
                let body_origin = self.walk(body, ctx);
                // Blocker 1 (F1): re-propagate binding-mediated escapes to
                // fixpoint. Runs BEFORE the frame restore, so RHS re-walks resolve
                // in this let's defining scope (enclosing + this-let's bindings).
                self.drain_escaped(bindings, &frame);
                // Restore the shadowed priors in reverse (scope exit, §13.6(i)).
                self.restore_frame(frame);
                body_origin
            }

            MonoExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                self.walk(cond, UseCtx::Neutral);
                // Both branches are in the enclosing context (tail-preserving).
                let a = self.walk(then_branch, ctx);
                let b = self.walk(else_branch, ctx);
                // Origin join (FIXME 0520): a param-reaching path survives as a
                // may-alias; only both-Fresh collapses to `Fresh`.
                self.join_origin(a, b)
            }

            MonoExpr::Match {
                scrutinee, arms, ..
            } => {
                let scrut_origin = self.walk(scrutinee, UseCtx::Neutral);
                let mut acc: Option<Origin> = None;
                // ESCAPE half of §16 row 3 (0641 B-2) — the scrutinee is walked
                // `Neutral` above (its allocation-site escape fact = false). But a
                // WHOLE-VALUE `Pattern::Var` arm binds the scrutinee ITSELF; if that
                // binding flows to the arm result and thence outward, the
                // scrutinee's allocation escapes. Present-but-wrong (`escapes=
                // Some(false)`) defeats the backend's P25 absent-default: for
                // `(match (vec-set v 1 99) [r r])` the COW `Apply` reads
                // non-escaping, the ruled gate declines the inc, and the match decs
                // the scrutinee while `r` returns it → UAF. Detect the binding's
                // escape (it was pushed to the worklist during the arm-body walk in
                // an escaping ctx) and re-walk the scrutinee in that ctx to record
                // the true escape (+ widen folded params — idempotent, monotone).
                let mut scrut_escapes = false;
                for arm in arms {
                    let whole_var = match &arm.pattern {
                        Pattern::Var { name, .. } => Some(name.clone()),
                        _ => None,
                    };
                    let escaped_mark = self.escaped.len();
                    // §13.6(i) (F4): each arm gets its OWN scope frame — a pattern
                    // binding is restored before the sibling arm (and the post-match
                    // uses) are walked, so an arm binding that shadows a param/outer
                    // binding cannot leak past its arm.
                    let frame = self.bind_pattern(&arm.pattern, &scrut_origin, arm);
                    let o = self.walk(&arm.body, ctx);
                    if let Some(vn) = &whole_var {
                        // Only the arm-LOCAL new worklist entries (a match-arm
                        // binding is not a `Let` binding — nothing drains it, so
                        // remove its entries here; the scrutinee re-walk below
                        // records the escape). Enclosing entries (< mark) untouched.
                        let arm_local: Vec<_> = self.escaped.split_off(escaped_mark);
                        if arm_local.iter().any(|(n, _)| n == vn) {
                            scrut_escapes = true;
                        }
                        self.escaped
                            .extend(arm_local.into_iter().filter(|(n, _)| n != vn));
                    }
                    self.restore_frame(frame);
                    acc = Some(match acc.take() {
                        None => o,
                        Some(prev) => self.join_origin(prev, o),
                    });
                }
                if scrut_escapes {
                    // `scrut_escapes` implies the arm body walked in an escaping
                    // `ctx` (the worklist push condition). Re-walk the scrutinee
                    // there — the loop/recur cells (arm result consumed in-frame,
                    // `ctx` non-escaping) never reach here, so they do not regress.
                    self.walk(scrutinee, ctx);
                }
                acc.unwrap_or(Origin::Fresh)
            }

            MonoExpr::Apply { .. } => self.walk_apply(expr, ctx),

            MonoExpr::VecLit { elements, span, .. }
            | MonoExpr::ConstrADT {
                fields: elements,
                span,
                ..
            } => {
                self.facts.escapes.insert(*span, ctx.escapes());
                let flow = ctx.field_flow();
                // Row 5 (§16.2, 0641 B-1 + I-2 CORRECTION) — the container Origin is
                // the JOIN of its element Origins, NOT unconditional `Fresh`. The
                // as-built anti-monotone rule returned `Fresh` unconditionally,
                // laundering an element's param reach: `(vec-get [v] 0)` → `Fresh`
                // (freed COW read), `[(vec-set v 0 9)]` → a fresh container whose
                // escaping element is a COW alias. Folding `join_origin` over the
                // elements makes an element reaching param i widen the container to
                // `Conditional{rep:i}` — a projection-OUT (row 6) then inherits the
                // alias reach. Losing per-element detail is fine (widen); losing the
                // reach is the unsound direction.
                let mut acc = Origin::Fresh;
                for el in elements {
                    let el_origin = self.walk(el, UseCtx::Field { flow });
                    acc = self.join_origin(acc, el_origin);
                }
                acc
            }

            MonoExpr::Lambda {
                params, body, span, ..
            } => {
                // The closure value is an allocation; if it escapes, its captured
                // free vars escape (rule 3 / R6). The closure's OWN span carries
                // the value-escape verdict; the body-return escape (below) is about
                // the LAMBDA's frame, a distinct axis (FIXME 0524).
                let escapes = ctx.escapes();
                self.facts.escapes.insert(*span, escapes);
                if escapes {
                    // Capture IS an escape edge — INDEPENDENT of how the captured
                    // value is used inside the closure body (FIXME 0523). The
                    // body walk below only escapes a capture in a directly-escaping
                    // sub-position; a capture used as a Borrowed arg (or any
                    // non-escaping sub-position) resets the context at the `Apply`
                    // and lost its escape (the hard UAF at B3.4). Drive
                    // capture-escape from the free-var set so every captured
                    // enclosing binding escapes, regardless of use-position.
                    let mut caps = HashSet::new();
                    free_vars(body, params, &mut caps);
                    for c in &caps {
                        self.classify_capture_escape(c);
                    }
                    // The lambda VALUE escapes, so its body allocations already
                    // escape via the `EscapingCapture` context (escapes()==true);
                    // that context also records nested escaping-allocation site
                    // facts, value-uses (§8.3) and nested-closure capture sets.
                    // Monotone with the free-var pass above (both only widen).
                    self.walk(body, UseCtx::EscapingCapture);
                } else {
                    // FIXME 0524 — the lambda/HOF-returned-constructor escape gap.
                    // The lambda VALUE does NOT escape the enclosing frame (it is a
                    // Borrowed arg to a HOF, or bound-and-discarded), but a lambda
                    // body is its OWN frame: any allocation reaching the lambda's
                    // tail/return position escapes the LAMBDA frame — the lambda
                    // WILL be called (that is why it is a value) and its result
                    // outlives its frame, exactly as a named `defn`'s returned
                    // allocation does. The cluster-centric pre-cure walked this
                    // body in the ENCLOSING frame's `Neutral` context, so the
                    // returned `(Some y)` never received the escape edge its
                    // named-`defn` sibling gets from the result-mode/`Return` walk
                    // (`escapes = Some(false)` ⇒ B3.4 stack-allocs it ⇒ dangles
                    // once the lambda/HOF frame pops). Walk the body in `Return` so
                    // its tail allocations escape.
                    //
                    // ISOLATED escaped worklist: lambda-LOCAL fresh bindings still
                    // drain within the body (their own `Let`/`ParBind` scopes run
                    // during this walk), but a capture of an ENCLOSING fresh local
                    // must NOT bubble to the enclosing drain — capture-escape is
                    // gated on the lambda VALUE escaping (the branch above), so a
                    // non-escaping lambda's captures stay in-frame (the §13.6(j)
                    // precision pin that keeps B3.4's stack-alloc win alive). After
                    // the body walk the only escaped entries left are those
                    // enclosing captures; discard them by restoring `outer`.
                    let outer = std::mem::take(&mut self.escaped);
                    // Row 5 interaction (§16.2): with a fresh aggregate now carrying
                    // a `Conditional` origin, a capture of an ENCLOSING param used in
                    // this non-escaping lambda's `Return`-walked tail would widen the
                    // enclosing param's flow/mode via `param_root` — but the lambda
                    // does NOT escape, so its captures do not escape and the
                    // enclosing param must not widen from them (the pre-row-5
                    // behaviour, where captures were `Fresh` and `param_root` missed;
                    // the §13.6(j) B3.4 precision pin). Snapshot + restore the
                    // enclosing param flow/mode around the isolated body walk, exactly
                    // as `escaped` is isolated — the lambda's own tail allocations
                    // still get their escape site facts (the fix's point).
                    let saved_flow = self.param_flow.clone();
                    let saved_modes = self.param_modes.clone();
                    self.walk(body, UseCtx::Return);
                    self.escaped = outer;
                    self.param_flow = saved_flow;
                    self.param_modes = saved_modes;
                }
                Origin::Fresh
            }

            MonoExpr::Trace { body, .. } => self.walk(body, ctx),

            MonoExpr::ParBind { bindings, body, .. } => {
                // A joined spark: bindings' RHS run on a spark strand but join
                // within the frame's extent (non-escape, §4.3). Confinement
                // (CS-3) handles the strand axis; here they are Neutral reads.
                // §13.6(i) (F4): the same scope-frame discipline as `Let`.
                let mut frame: ScopeFrame = Vec::with_capacity(bindings.len());
                for (n, rhs) in bindings {
                    let origin = self.walk(rhs, UseCtx::Neutral);
                    self.drop_shadowed_provenance(n);
                    let prior = self.bindings.insert(
                        n.clone(),
                        BindState {
                            origin,
                            param_idx: None,
                        },
                    );
                    frame.push((n.clone(), prior));
                }
                let body_origin = self.walk(body, ctx);
                // Blocker 1 (F1): a joined-spark binding that flows out (returned /
                // stored) escapes exactly like a `let` binding — drain to fixpoint.
                // The non-escape property of §4.3 is a STRAND fact (confinement),
                // not a frame-escape fact.
                self.drain_escaped(bindings, &frame);
                self.restore_frame(frame);
                body_origin
            }

            MonoExpr::LaunchContinue {
                launched,
                continuation,
                ..
            } => {
                // `launched` is a suspension escape edge (R6): every free var it
                // captures escapes — independent of use-position, the same gap as
                // closure capture (FIXME 0523). The continuation proceeds in the
                // enclosing context.
                let mut caps = HashSet::new();
                free_vars(launched, &[], &mut caps);
                for c in &caps {
                    self.classify_capture_escape(c);
                }
                self.walk(launched, UseCtx::EscapingCapture);
                self.walk(continuation, ctx)
            }
        }
    }

    fn walk_var(&mut self, name: &Symbol, ctx: UseCtx) -> Origin {
        if let Some(bs) = self.bindings.get(name).cloned() {
            // A bound name. Classify the use against the param it roots in.
            if let Some(idx) = self.param_root(name) {
                self.classify_param_use(idx, ctx);
            }
            // Blocker 1: a freshly-CONSTRUCTED binding used in an escaping context
            // re-propagates to its defining RHS — recorded here, drained at the
            // enclosing `Let`. `Fresh` (no param) AND `Conditional` (a fresh
            // aggregate/COW carrying a param — row 5 now gives such a container a
            // `Conditional` origin, not `Fresh`) both need the re-walk to flip the
            // allocation's escape site fact; the folded param's FLOW is already
            // widened via `param_root` above (idempotent with the re-walk). An
            // UNCONDITIONAL binding is a direct param alias/view, not a fresh
            // allocation — it is fully handled by `param_root`, no re-walk owed.
            if matches!(bs.origin, Origin::Fresh | Origin::Conditional { .. }) && ctx.escapes() {
                self.escaped.push((name.clone(), ctx));
            }
            bs.origin
        } else {
            // A free name = a callable / global reference. In non-callee
            // position this is a value-use (§8.3).
            if !matches!(ctx, UseCtx::CalleePos) {
                self.value_uses.insert(name.clone());
            }
            Origin::Fresh
        }
    }

    fn walk_apply(&mut self, expr: &MonoExpr, ctx: UseCtx) -> Origin {
        let MonoExpr::Apply {
            callee,
            args,
            resolved_call,
            span,
            ..
        } = expr
        else {
            unreachable!()
        };
        let class = classify_call(resolved_call.as_deref(), callee, |n| {
            self.env.terminal_kind(n)
        });
        // The callee position (never a value-use).
        self.walk(callee, UseCtx::CalleePos);

        match class {
            CallClass::Summarised(name) => {
                let summary = self.env.summary_of(&name);
                if let Some((fq, _)) = &summary {
                    self.deps.insert(fq.clone());
                }
                let summary = summary.map(|(_, s)| s);
                // Walk args at their param modes/flows (⊤ = Owned/Retained).
                let mut arg_origins = Vec::with_capacity(args.len());
                for (j, arg) in args.iter().enumerate() {
                    let (mode, flow) = match &summary {
                        Some(s) => (s.param_mode(j), s.param_flow(j)),
                        None => (Mode::Owned, ParamFlow::Retained),
                    };
                    let o = self.walk(arg, UseCtx::Arg { mode, flow });
                    arg_origins.push(o);
                }
                // Result origin from the callee's result mode. A may-alias arg
                // (FIXME 0520) is carried through as a may-alias — an `AliasOf`/
                // `ProjectionOf` result of a param-reaching arg never collapses
                // to `Fresh`, so a partial param-return composes soundly through
                // an `Apply` body (the borrow-elision consumer's binary read).
                let result = summary
                    .as_ref()
                    .map(|s| s.result)
                    .unwrap_or(ResultMode::Fresh);
                let origin = match result {
                    ResultMode::ProjectionOf(k) => {
                        // Row 6 (§16.2) — a projection-out roots at the container's
                        // Origin: an UNCONDITIONAL container yields an unconditional
                        // projection (+ the provenance fact); a CONDITIONAL container
                        // yields a conditional projection (never strengthens — no
                        // provenance fact, the backend materializes at Decision-24).
                        // With row 5 (container carries its element-join) this
                        // inherits the aliased element's reach.
                        match arg_origins.get(k).cloned().unwrap_or(Origin::Fresh) {
                            Origin::Unconditional { root, .. } => {
                                self.facts.provenance.insert(*span, root.clone());
                                Origin::unconditional(root, true)
                            }
                            Origin::Conditional { rep, cow, .. } => {
                                // MS-P7 (§3.6) — PROJECTING OUT of a may-alias
                                // CONTAINER: `(vec-get (vec-set v 0 9) 0)`, where the
                                // container `(vec-set v 0 9)` is a COW result that may
                                // BE param `v` in the rc==1 in-place arm. The inline
                                // vec-get lowering RELEASES its container arg-temp
                                // (`vec_codegen::emit_vec_drop_if_temporary`) after
                                // the read, while the aliased param's own scope-dec
                                // ALSO fires → both decs hit the SAME box in the
                                // in-place arm → double-free (`--link` abort; --run
                                // tolerates it). The §3.7 fix's protect/publish did
                                // not cover this projection-out ARG-TEMP. Force the
                                // CONTAINER'S escape fact TRUE so the backend's
                                // escape-gated COW retain (`cow_source_ownership` →
                                // `retain_reused`) incs the in-place result — the
                                // container drop is then balanced (ONE net dec).
                                //
                                // Scoped to the PROJECTION consumer (this arm), NOT
                                // the container's own Arg-context escape: a COW
                                // may-alias TRANSFERRED to a recur / user-fn (l_c3
                                // `(churn (vec-set v i 0) …)`) has the IDENTICAL
                                // `Arg{Borrowed}` ctx + `Conditional` origin but is
                                // NOT projected-out (no `emit_vec_drop_if_temporary`),
                                // so its escape fact stays `Some(false)` and the
                                // in-place reuse is preserved. Only a Fresh container
                                // (no param reach) skips this (the `Fresh` arm).
                                //
                                // §17.2 ROW 6 (S115 MS-P7 chained family) — the
                                // W7 reach `if let MonoExpr::Apply = &args[k]` is
                                // DELETED. That syntactic reach found the
                                // allocation to protect only when the consumer's
                                // immediate argument HAPPENED to be a direct
                                // `Apply`, so a chain of length ≥2 (a nested
                                // `Apply`, or a `let`-mediated `Var`) hid its
                                // INNER links and they double-dec'd. The
                                // container's own `Origin` already carries EVERY
                                // may-alias allocation on the chain (rows 8/2/4),
                                // so the force covers all of them from this ONE
                                // pre-existing arm — no per-shape arm is added
                                // (§17.3, the family-grain ruling). Monotone: the
                                // force only ADDS incs.
                                for cow_span in &cow {
                                    self.facts.escapes.insert(*cow_span, true);
                                }
                                Origin::conditional(rep, true, cow)
                            }
                            Origin::Fresh => Origin::Fresh,
                        }
                    }
                    // The result IS arg k — carry its origin through verbatim.
                    ResultMode::AliasOf(k) => arg_origins.get(k).cloned().unwrap_or(Origin::Fresh),
                    // COW result (S111 §15.4, spine §3.7(a1)): the result is
                    // EITHER fresh OR arg k's reference, decided at runtime. Join
                    // `Fresh` with the arg's origin — a param-reaching arg yields
                    // `MayParam` (never collapses to `Fresh`, the 0520 rule keeps
                    // protect); a fresh/non-param arg yields `Fresh`. Reuses the
                    // exact 0520 may-alias composition, no new join logic.
                    ResultMode::MayAliasOf(k) => {
                        let arg = arg_origins.get(k).cloned().unwrap_or(Origin::Fresh);
                        // §17.2 ROW 8 — this call MINTS a fresh may-alias LINK at
                        // its own span, so the produced `Conditional` unions THIS
                        // `Apply`'s span with the links the container argument
                        // already carried. That union is what composes a chain:
                        // `(vec-set (vec-set v 0 1) 1 2)` carries `[inner, outer]`
                        // by the time the terminal projection consumes it. The
                        // `rep`/reach axis is unchanged (§16 already correct); the
                        // link set is the added carrier, and it only grows.
                        //
                        // A container with NO param reach joins to `Fresh` — no
                        // aliased param can be double-dec'd, so no link is
                        // recorded (the fresh container's own dec is balanced).
                        match self.join_origin(Origin::Fresh, arg) {
                            Origin::Conditional {
                                rep,
                                projection,
                                cow,
                            } => Origin::conditional(rep, projection, union_cow(&cow, &[*span])),
                            other => other,
                        }
                    }
                    ResultMode::Fresh => Origin::Fresh,
                };
                // The Apply node is itself an allocation/result site.
                self.facts.escapes.insert(*span, ctx.escapes());
                origin
            }
            CallClass::Decision24 => {
                for arg in args {
                    self.walk(arg, UseCtx::Decision24Arg);
                }
                self.facts.escapes.insert(*span, ctx.escapes());
                Origin::Fresh
            }
        }
    }

    /// Mark a value captured by an escaping closure / suspension as escaping
    /// (FIXME 0523, R6). Capture is an escape edge regardless of use-position:
    ///
    /// - roots in a **param** ⇒ widen it `Owned`/`Retained` (the escape rides the
    ///   ABI, so a caller passing a fresh value at that position sees the escape —
    ///   the inter-procedural half);
    /// - a **Fresh** local (a fresh aggregate / `Fresh`-result) ⇒ push to the
    ///   escaped worklist so the enclosing scope's drain re-walks its RHS in the
    ///   escaping context (flips the allocation's escape site fact);
    /// - a **borrowed view / alias of another local** ⇒ materialize at its root
    ///   (§4.2 rule 5): follow to the owning local and escape that.
    ///
    /// A free name that is not a binding (a callable / global) is not a
    /// capture-escape — its value-use is recorded by the body walk (§8.3).
    fn classify_capture_escape(&mut self, name: &Symbol) {
        let bs = self.bindings.get(name).cloned();
        // Widen any param this name roots in (a direct param, an alias chain, or
        // the param-reaching path of a conditional). The escape rides the ABI, so
        // a caller passing a fresh value at that position sees the escape (the
        // inter-procedural half). This runs for ALL param-reaching origins — but a
        // fresh AGGREGATE carrying a param (a `Conditional` binding) ALSO needs its
        // allocation to escape (below), so it does NOT early-return.
        if let Some(idx) = self.param_root(name) {
            self.classify_param_use(idx, UseCtx::EscapingCapture);
        }
        let Some(bs) = bs else { return };
        match bs.origin {
            // Row 7 (§16.2, 0641 I-1 CORRECTION) — a FRESH ALLOCATION captured by an
            // escaping closure escapes: `Fresh` (no param) OR `Conditional` (a fresh
            // aggregate/COW carrying a param — row 5 now gives it a `Conditional`
            // origin, not `Fresh`) both push to the worklist so the enclosing scope
            // re-walks the RHS in the escaping context (flips the alloc site fact,
            // folds params IntoResult). Pre-cure, a captured let-bound param alias /
            // aggregate laundered (the freed-heap read I-1) because it was treated
            // as a fresh local with no reach; now its param is widened above AND its
            // allocation escapes here.
            Origin::Fresh | Origin::Conditional { .. } => {
                self.escaped.push((name.clone(), UseCtx::EscapingCapture))
            }
            // An UNCONDITIONAL alias/projection of another LOCAL (not itself the
            // param — that case is a direct param, `root == name`, and was widened
            // above): follow to the owning binding and escape it. `param_root` does
            // not chase an unconditional projection, so a projection rooted in a
            // param is reached here and resolves on the recursion.
            Origin::Unconditional { root: s, .. } if s != *name => self.classify_capture_escape(&s),
            Origin::Unconditional { .. } => {}
        }
    }

    /// §13.6(d) shadow provenance guard — the ONE home shared by the `Let` and
    /// `Match` binding seams (F2: single-sourced, no mirror). When `name` shadows
    /// an already-bound binding, any pre-existing projection provenance rooted in
    /// `name` becomes ambiguous under the symbol-keyed backend (two live bindings
    /// answer to one `Symbol`), so drop those facts — `None` ⇒ Decision-24
    /// materialize. No-op when `name` is not yet bound (no shadow).
    fn drop_shadowed_provenance(&mut self, name: &Symbol) {
        if self.bindings.contains_key(name) {
            self.facts.provenance.retain(|_, root| root != name);
        }
    }

    /// Restore a lexical-scope frame on scope exit (§13.6(i), F4 cure): replay
    /// the saved `(name, prior)` entries in **reverse** insertion order —
    /// `Some(old)` reinserts the shadowed prior, `None` removes the binding.
    /// This is what makes `bindings` faithfully model lexical scope, so an inner
    /// branch-sibling binding never leaks past its scope.
    fn restore_frame(&mut self, frame: ScopeFrame) {
        for (name, prior) in frame.into_iter().rev() {
            match prior {
                Some(old) => {
                    self.bindings.insert(name, old);
                }
                None => {
                    self.bindings.remove(&name);
                }
            }
        }
    }

    /// Drain this lexical scope's binding-mediated escapes to **fixpoint**
    /// (§13.6(g), F1 cure). A `Fresh` binding used escaping in the body was
    /// recorded by [`Self::walk_var`]; re-walking its RHS in the escaping context
    /// widens the folded-in params and flips the aggregate's escape fact. A
    /// re-walk can newly escape an EARLIER binding of the same flat `let`
    /// fold-chain (`[a (Some x), b (Some a)]`, `b` returned ⇒ `a` escapes ⇒ `x`
    /// escapes), so we loop over `self.escaped` for THIS scope's names until it
    /// settles. Outer-scope entries bubble up (partitioned into `rest`).
    ///
    /// **Defining-scope re-walk (§13.6(i), F4).** Each RHS is re-walked with the
    /// binding-being-drained temporarily restored to its shadowed (`prior`)
    /// value from `frame`, so a self-alias RHS (`(let [a a] …)` — the
    /// `case`/`cond` macro shape) and a forward-reference-shaped fold chain
    /// resolve their free vars in the RHS's *defining* scope (the binding itself
    /// is not yet in scope while its own RHS evaluates), which is the correct
    /// sequential-let reading. Restored to the inner binding after each re-walk
    /// so sibling bindings stay visible.
    ///
    /// **Defensive termination bound (each `(name, ctx)` re-walked at most
    /// once).** Since escaped entries are `Symbol`-keyed, a self-aliasing binding
    /// whose defining-scope re-walk resolves `var("a")` to a still-`Fresh`,
    /// still-`"a"`-named outer binding re-pushes `("a", ctx)`; the `(name, ctx)`
    /// dedup caps this at |bindings| × |UseCtx| re-walks. Scope discipline makes
    /// the re-walk resolve correctly; the dedup is the belt-and-braces bound that
    /// guarantees termination (§13.6(g) — role downgraded from the F1 cure's
    /// termination mechanism to a defensive cap). Re-walking one RHS in one
    /// context is idempotent (monotone joins), so no flow is under-widened.
    fn drain_escaped(&mut self, bindings: &[(Symbol, MonoExpr)], frame: &ScopeFrame) {
        let mut done: HashSet<(Symbol, UseCtx)> = HashSet::new();
        loop {
            let escaped = std::mem::take(&mut self.escaped);
            // This scope's entries vs outer-scope entries (which bubble up).
            let (mine, rest): (Vec<_>, Vec<_>) = escaped
                .into_iter()
                .partition(|(name, _)| bindings.iter().any(|(n, _)| n == name));
            self.escaped = rest;
            let todo: Vec<_> = mine
                .into_iter()
                .filter(|pair| !done.contains(pair))
                .collect();
            if todo.is_empty() {
                break;
            }
            for (name, esc_ctx) in todo {
                if done.insert((name.clone(), esc_ctx))
                    && let Some((_, rhs)) = bindings.iter().find(|(n, _)| n == &name)
                {
                    // Re-walk in the RHS's defining scope: temporarily restore the
                    // binding to its shadowed prior (the binding is not in scope
                    // while its own RHS evaluates — sequential-let semantics).
                    let prior = frame
                        .iter()
                        .find(|(n, _)| n == &name)
                        .and_then(|(_, p)| p.clone());
                    let inner = match prior {
                        Some(p) => self.bindings.insert(name.clone(), p),
                        None => self.bindings.remove(&name),
                    };
                    self.walk(rhs, esc_ctx);
                    // Restore the inner binding for subsequent sibling re-walks.
                    match inner {
                        Some(iv) => {
                            self.bindings.insert(name.clone(), iv);
                        }
                        None => {
                            self.bindings.remove(&name);
                        }
                    }
                }
            }
        }
    }

    /// Bind a match-arm pattern's field bindings as borrowed projections rooted
    /// in the scrutinee's root (§4.2 rule 1), recording the arm provenance fact
    /// with the §13.6(d) shadow guard. Returns the arm's [`ScopeFrame`] — the
    /// caller restores it after the arm body so a pattern binding does not leak
    /// past its arm (§13.6(i), F4).
    fn bind_pattern(
        &mut self,
        pattern: &Pattern,
        scrut_origin: &Origin,
        arm: &MonoMatchArm,
    ) -> ScopeFrame {
        let scrut_root = scrut_origin.root().cloned();
        let mut names = Vec::new();
        collect_pattern_bindings(pattern, &mut names);
        // §13.6(d) shadow guard (arm-own): if any bound name would shadow the
        // scrutinee root, emit no provenance for the arm (conservative).
        let shadow = scrut_root
            .as_ref()
            .map(|r| names.iter().any(|n| n == r))
            .unwrap_or(false);
        // Row 3 (§16.2) — the arm provenance fact is emitted ONLY for an
        // UNCONDITIONAL scrutinee (a hard projection root the backend may trust). A
        // CONDITIONAL (COW) scrutinee gets NO arm provenance fact — Decision-24
        // materializes at the site, the safe direction.
        if !shadow
            && matches!(scrut_origin, Origin::Unconditional { .. })
            && let Some(r) = &scrut_root
        {
            self.facts.provenance.insert(arm.span, r.clone());
        }
        // Row 3 (§16.2, 0641 B-2 CORRECTION): a binding's Origin roots at the
        // SCRUTINEE'S Origin — a whole-value `Pattern::Var` binds it VERBATIM (a
        // `Conditional` scrutinee yields a `Conditional` binding, never an
        // unconditional `Projection`/`Root`); a destructuring `Pattern::Constructor`
        // field binds a PROJECTION of the scrutinee, unconditional ONLY if the
        // scrutinee is itself unconditional, else `Conditional{projection:true}`.
        // The as-built published a hard `Projection(scrut_root)` for every name even
        // under a COW `Conditional` scrutinee (`(match (vec-set v 1 99) [r r])` →
        // hard `Projection(v)`) — a narrowing with no justification.
        let is_whole_var = matches!(pattern, Pattern::Var { .. });
        let mut frame: ScopeFrame = Vec::with_capacity(names.len());
        for n in names {
            // §13.6(d) shadow guard (pre-existing): a pattern binding also shadows
            // any OTHER live binding of that name — drop pre-existing provenance
            // rooted in it (F2 mirror cure, single-sourced with the Let seam).
            self.drop_shadowed_provenance(&n);
            let origin = if shadow {
                Origin::Fresh
            } else if is_whole_var {
                scrut_origin.clone()
            } else {
                match scrut_origin {
                    Origin::Unconditional { root, .. } => Origin::unconditional(root.clone(), true),
                    // Row 3 (§17.2 rider) — a destructured field of a
                    // CONDITIONAL scrutinee carries the scrutinee's may-alias
                    // link set, so a match-mediated chain composes exactly as a
                    // `let`-mediated one does.
                    Origin::Conditional { rep, cow, .. } => {
                        Origin::conditional(rep.clone(), true, cow.clone())
                    }
                    Origin::Fresh => Origin::Fresh,
                }
            };
            let prior = self.bindings.insert(
                n.clone(),
                BindState {
                    origin,
                    param_idx: None,
                },
            );
            frame.push((n, prior));
        }
        frame
    }
}

/// The free variables of `expr` — names used that are bound neither by `params`
/// (a lambda's own formals; empty for a `LaunchContinue.launched` expr) nor by
/// any binder inside `expr` (the R6 capture set; FIXME 0523).
///
/// Proper lexical scoping (binders save + restore) so the set never
/// UNDER-reports a real capture — under-reporting is the unsound direction (a
/// missed escape). Over-reporting is sound: a spuriously-included locally-bound
/// name is absent from the caller's `bindings`, so [`Walker::classify_capture_escape`]
/// no-ops on it.
fn free_vars(expr: &MonoExpr, params: &[Symbol], out: &mut HashSet<Symbol>) {
    let mut bound: HashSet<Symbol> = params.iter().cloned().collect();
    collect_free(expr, &mut bound, out);
}

/// Push `names` that are newly bound into `bound`, returning the ones actually
/// added (a name already bound — a shadow — is NOT re-added, so it is not
/// removed on scope exit and stays bound as its outer occurrence).
fn enter_scope(
    names: impl IntoIterator<Item = Symbol>,
    bound: &mut HashSet<Symbol>,
) -> Vec<Symbol> {
    let mut added = Vec::new();
    for n in names {
        if bound.insert(n.clone()) {
            added.push(n);
        }
    }
    added
}

fn collect_free(expr: &MonoExpr, bound: &mut HashSet<Symbol>, out: &mut HashSet<Symbol>) {
    match expr {
        MonoExpr::Var { name, .. } => {
            if !bound.contains(name) {
                out.insert(name.clone());
            }
        }
        MonoExpr::IntLit { .. }
        | MonoExpr::FloatLit { .. }
        | MonoExpr::BoolLit { .. }
        | MonoExpr::StringLit { .. } => {}
        // A `let`/`par` is sequential: each RHS sees the prior bindings, so bind
        // after walking each RHS; restore all on scope exit.
        MonoExpr::Let { bindings, body, .. } | MonoExpr::ParBind { bindings, body, .. } => {
            let mut added = Vec::new();
            for (n, rhs) in bindings {
                collect_free(rhs, bound, out);
                added.extend(enter_scope([n.clone()], bound));
            }
            collect_free(body, bound, out);
            for n in added {
                bound.remove(&n);
            }
        }
        MonoExpr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_free(cond, bound, out);
            collect_free(then_branch, bound, out);
            collect_free(else_branch, bound, out);
        }
        MonoExpr::Match {
            scrutinee, arms, ..
        } => {
            collect_free(scrutinee, bound, out);
            for arm in arms {
                let mut names = Vec::new();
                collect_pattern_bindings(&arm.pattern, &mut names);
                let added = enter_scope(names, bound);
                collect_free(&arm.body, bound, out);
                for n in added {
                    bound.remove(&n);
                }
            }
        }
        MonoExpr::Apply { callee, args, .. } => {
            collect_free(callee, bound, out);
            for a in args {
                collect_free(a, bound, out);
            }
        }
        MonoExpr::Lambda { params, body, .. } => {
            let added = enter_scope(params.iter().cloned(), bound);
            collect_free(body, bound, out);
            for n in added {
                bound.remove(&n);
            }
        }
        MonoExpr::Trace { body, .. } => collect_free(body, bound, out),
        MonoExpr::VecLit { elements, .. } => {
            for e in elements {
                collect_free(e, bound, out);
            }
        }
        MonoExpr::ConstrADT { fields, .. } => {
            for f in fields {
                collect_free(f, bound, out);
            }
        }
        MonoExpr::LaunchContinue {
            launched,
            continuation,
            ..
        } => {
            collect_free(launched, bound, out);
            collect_free(continuation, bound, out);
        }
    }
}

pub(super) fn collect_pattern_bindings(pattern: &Pattern, out: &mut Vec<Symbol>) {
    match pattern {
        Pattern::Var { name, .. } => out.push(name.clone()),
        // Ring-0/1 constructor patterns bind a flat list of field names.
        Pattern::Constructor { bindings, .. } => out.extend(bindings.iter().cloned()),
        Pattern::Wildcard { .. } => {}
    }
}

/// The transfer function (§13.2 CS-2 signature). `params` is the formal
/// parameter list with concrete types; `body` is the callable's `MonoExpr`;
/// `env` supplies callee facts; `copy` classifies scalar params.
pub(crate) fn transfer<E: TransferEnv>(
    params: &[(Symbol, ConcreteType)],
    body: &MonoExpr,
    env: &E,
    copy: &CopyClassifier<'_>,
) -> TransferResult {
    let n = params.len();
    let mut param_modes = Vec::with_capacity(n);
    let mut param_copy = Vec::with_capacity(n);
    let mut bindings = HashMap::new();
    for (i, (name, ty)) in params.iter().enumerate() {
        let is_copy = copy.is_copy(ty);
        param_copy.push(is_copy);
        param_modes.push(if is_copy { Mode::Copy } else { Mode::Borrowed });
        bindings.insert(
            name.clone(),
            BindState {
                origin: Origin::unconditional(name.clone(), false),
                param_idx: Some(i),
            },
        );
    }
    let mut w = Walker {
        env,
        bindings,
        param_modes,
        param_flow: vec![ParamFlow::Consumed; n],
        param_copy,
        facts: SiteFacts::default(),
        deps: DepSet::new(),
        value_uses: HashSet::new(),
        escaped: Vec::new(),
    };
    let body_origin = w.walk(body, UseCtx::Return);
    let result = w.origin_to_result_mode(&body_origin);

    let summary = ModeSummary {
        param_modes: w.param_modes,
        result,
        param_flow: w.param_flow,
        spark_ops: vec![false; n], // optimistic-clear; widened by confinement (CS-3)
        result_unique: false,      // increment-I pin (§10)
    };
    TransferResult {
        summary,
        facts: w.facts,
        deps: w.deps,
        value_uses: w.value_uses,
    }
}

#[cfg(test)]
mod tests;
