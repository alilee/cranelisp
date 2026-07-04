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

use super::classify::{classify_call, CallClass, CopyClassifier, TerminalKind};

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
#[derive(Debug, Clone, Copy)]
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
            UseCtx::Arg { mode: Mode::Owned, flow } => flow,
            UseCtx::Decision24Arg | UseCtx::EscapingCapture => ParamFlow::Retained,
            UseCtx::Field { flow } => flow,
            UseCtx::Arg { .. } | UseCtx::CalleePos | UseCtx::Neutral => ParamFlow::Consumed,
        }
    }
}

/// The provenance/freshness of an expression's value.
#[derive(Debug, Clone)]
enum Origin {
    /// A fresh allocation / `Fresh`-result call / literal.
    Fresh,
    /// This value IS the named binding's root (a param used directly, or an
    /// alias `let x = p`).
    Root(Symbol),
    /// A borrowed view rooted in the named binding.
    Projection(Symbol),
}

impl Origin {
    fn root(&self) -> Option<&Symbol> {
        match self {
            Origin::Root(s) | Origin::Projection(s) => Some(s),
            Origin::Fresh => None,
        }
    }
}

#[derive(Debug, Clone)]
struct BindState {
    origin: Origin,
    /// `Some(idx)` iff this binding is a formal parameter.
    param_idx: Option<usize>,
}

struct Walker<'e, E: TransferEnv> {
    env: &'e E,
    copy: &'e CopyClassifier,
    bindings: HashMap<Symbol, BindState>,
    /// Per-param accumulated mode (index-aligned with the formal list).
    param_modes: Vec<Mode>,
    param_flow: Vec<ParamFlow>,
    /// `true` for params seeded `Copy` — never widened.
    param_copy: Vec<bool>,
    facts: SiteFacts,
    deps: DepSet,
    value_uses: HashSet<Symbol>,
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
                Origin::Root(s) => cur = s.clone(),
                _ => return None,
            }
        }
    }

    /// Map the body's final value origin to a [`ResultMode`] (§3.3). The
    /// §13.6(c) multi-path join is already applied via [`join_origin`] at
    /// `If`/`Match` — a disagreement has collapsed to `Fresh` before here.
    fn origin_to_result_mode(&self, origin: &Origin) -> ResultMode {
        match origin {
            Origin::Root(s) => match self.param_root(s) {
                Some(idx) => ResultMode::AliasOf(idx),
                None => ResultMode::Fresh,
            },
            Origin::Projection(s) => match self.param_root(s) {
                Some(idx) => ResultMode::ProjectionOf(idx),
                None => ResultMode::Fresh,
            },
            Origin::Fresh => ResultMode::Fresh,
        }
    }

    /// Widen a param's mode/flow from a use in `ctx`. No-op for `Copy` params.
    fn classify_param_use(&mut self, idx: usize, ctx: UseCtx) {
        if self.param_copy[idx] {
            return;
        }
        match ctx {
            UseCtx::Arg { mode: Mode::Borrowed, .. }
            | UseCtx::Arg { mode: Mode::Copy, .. }
            | UseCtx::CalleePos
            | UseCtx::Neutral => { /* non-widening read / borrowed handoff */ }
            UseCtx::Arg { mode: Mode::Owned, flow } => {
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
                for (n, rhs) in bindings {
                    // The RHS value's escape is not yet known (forward info);
                    // walk it Neutral and record its origin so uses of `n`
                    // propagate provenance. A param stored into a let-bound
                    // aggregate that later escapes is handled conservatively
                    // (the aggregate walk widens to Retained when its own ctx
                    // escapes; a Neutral RHS keeps params un-widened — sound
                    // because a later escaping *use of `n`* re-classifies the
                    // param root through `n`'s Root/Projection origin).
                    let origin = self.walk(rhs, UseCtx::Neutral);
                    self.bindings.insert(n.clone(), BindState { origin, param_idx: None });
                }
                self.walk(body, ctx)
            }

            MonoExpr::If { cond, then_branch, else_branch, .. } => {
                self.walk(cond, UseCtx::Neutral);
                // Both branches are in the enclosing context (tail-preserving).
                let a = self.walk(then_branch, ctx);
                let b = self.walk(else_branch, ctx);
                // Origin join: identical roots survive; otherwise Fresh.
                join_origin(a, b)
            }

            MonoExpr::Match { scrutinee, arms, .. } => {
                let scrut_origin = self.walk(scrutinee, UseCtx::Neutral);
                let scrut_root = scrut_origin.root().cloned();
                let mut acc: Option<Origin> = None;
                for arm in arms {
                    self.bind_pattern(&arm.pattern, scrut_root.as_ref(), arm);
                    let o = self.walk(&arm.body, ctx);
                    acc = Some(match acc.take() {
                        None => o,
                        Some(prev) => join_origin(prev, o),
                    });
                }
                acc.unwrap_or(Origin::Fresh)
            }

            MonoExpr::Apply { .. } => self.walk_apply(expr, ctx),

            MonoExpr::VecLit { elements, span, .. } | MonoExpr::ConstrADT { fields: elements, span, .. } => {
                self.facts.escapes.insert(*span, ctx.escapes());
                let flow = ctx.field_flow();
                for el in elements {
                    self.walk(el, UseCtx::Field { flow });
                }
                Origin::Fresh
            }

            MonoExpr::Lambda { body, span, .. } => {
                // The closure value is an allocation; if it escapes, its
                // free-var captures escape (rule 3). Increment-I conservative:
                // walk the body with EscapingCapture when the closure escapes,
                // else Neutral.
                let escapes = ctx.escapes();
                self.facts.escapes.insert(*span, escapes);
                let inner = if escapes { UseCtx::EscapingCapture } else { UseCtx::Neutral };
                self.walk(body, inner);
                Origin::Fresh
            }

            MonoExpr::Trace { body, .. } => self.walk(body, ctx),

            MonoExpr::ParBind { bindings, body, .. } => {
                // A joined spark: bindings' RHS run on a spark strand but join
                // within the frame's extent (non-escape, §4.3). Confinement
                // (CS-3) handles the strand axis; here they are Neutral reads.
                for (n, rhs) in bindings {
                    let origin = self.walk(rhs, UseCtx::Neutral);
                    self.bindings.insert(n.clone(), BindState { origin, param_idx: None });
                }
                self.walk(body, ctx)
            }

            MonoExpr::LaunchContinue { launched, continuation, .. } => {
                // `launched` is a suspension escape edge (R6): anything it uses
                // escapes. The continuation proceeds in the enclosing context.
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
        let MonoExpr::Apply { callee, args, resolved_call, span, .. } = expr else {
            unreachable!()
        };
        let class = classify_call(resolved_call.as_deref(), callee, |n| self.env.terminal_kind(n));
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
                // Result origin from the callee's result mode.
                let result = summary.as_ref().map(|s| s.result).unwrap_or(ResultMode::Fresh);
                let origin = match result {
                    ResultMode::ProjectionOf(k) => match arg_origins.get(k).and_then(|o| o.root()) {
                        Some(root) => {
                            self.facts.provenance.insert(*span, root.clone());
                            Origin::Projection(root.clone())
                        }
                        None => Origin::Fresh,
                    },
                    ResultMode::AliasOf(k) => match arg_origins.get(k).and_then(|o| o.root()) {
                        Some(root) => Origin::Root(root.clone()),
                        None => Origin::Fresh,
                    },
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

    /// Bind a match-arm pattern's field bindings as borrowed projections rooted
    /// in the scrutinee's root (§4.2 rule 1), recording the arm provenance fact
    /// with the §13.6(d) shadow guard.
    fn bind_pattern(&mut self, pattern: &Pattern, scrut_root: Option<&Symbol>, arm: &MonoMatchArm) {
        let mut names = Vec::new();
        collect_pattern_bindings(pattern, &mut names);
        // §13.6(d) shadow guard: if any bound name would shadow a live
        // provenance root, emit no provenance for the arm (conservative).
        let shadow = scrut_root.map(|r| names.iter().any(|n| n == r)).unwrap_or(false);
        let root = if shadow { None } else { scrut_root.cloned() };
        if let Some(r) = &root {
            self.facts.provenance.insert(arm.span, r.clone());
        }
        for n in names {
            let origin = match &root {
                Some(r) => Origin::Projection(r.clone()),
                None => Origin::Fresh,
            };
            self.bindings.insert(n, BindState { origin, param_idx: None });
        }
    }
}

/// Join two value origins: identical roots survive; any disagreement (mixed
/// roots, mixed kinds, any `Fresh`) collapses to `Fresh` (the conservative
/// point — §13.6(c) applied at the value level).
fn join_origin(a: Origin, b: Origin) -> Origin {
    match (&a, &b) {
        (Origin::Root(x), Origin::Root(y)) if x == y => a,
        (Origin::Projection(x), Origin::Projection(y)) if x == y => a,
        _ => Origin::Fresh,
    }
}

fn collect_pattern_bindings(pattern: &Pattern, out: &mut Vec<Symbol>) {
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
    copy: &CopyClassifier,
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
            BindState { origin: Origin::Root(name.clone()), param_idx: Some(i) },
        );
    }
    let mut w = Walker {
        env,
        copy,
        bindings,
        param_modes,
        param_flow: vec![ParamFlow::Consumed; n],
        param_copy,
        facts: SiteFacts::default(),
        deps: DepSet::new(),
        value_uses: HashSet::new(),
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
    TransferResult { summary, facts: w.facts, deps: w.deps, value_uses: w.value_uses }
}

#[cfg(test)]
mod tests;
