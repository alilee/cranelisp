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
                    let prior = self.bindings.insert(n.clone(), BindState { origin, param_idx: None });
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
                    // §13.6(i) (F4): each arm gets its OWN scope frame — a pattern
                    // binding is restored before the sibling arm (and the post-match
                    // uses) are walked, so an arm binding that shadows a param/outer
                    // binding cannot leak past its arm.
                    let frame = self.bind_pattern(&arm.pattern, scrut_root.as_ref(), arm);
                    let o = self.walk(&arm.body, ctx);
                    self.restore_frame(frame);
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
                // §13.6(i) (F4): the same scope-frame discipline as `Let`.
                let mut frame: ScopeFrame = Vec::with_capacity(bindings.len());
                for (n, rhs) in bindings {
                    let origin = self.walk(rhs, UseCtx::Neutral);
                    self.drop_shadowed_provenance(n);
                    let prior = self.bindings.insert(n.clone(), BindState { origin, param_idx: None });
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
            // Blocker 1: a Fresh (freshly-constructed) binding used in an
            // escaping context re-propagates to its defining RHS — recorded here
            // and drained at the enclosing `Let`. `Root`/`Projection` bindings
            // are already handled through `param_root` above.
            if matches!(bs.origin, Origin::Fresh) && ctx.escapes() {
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
            let todo: Vec<_> = mine.into_iter().filter(|pair| !done.contains(pair)).collect();
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
        scrut_root: Option<&Symbol>,
        arm: &MonoMatchArm,
    ) -> ScopeFrame {
        let mut names = Vec::new();
        collect_pattern_bindings(pattern, &mut names);
        // §13.6(d) shadow guard (arm-own): if any bound name would shadow the
        // scrutinee root, emit no provenance for the arm (conservative).
        let shadow = scrut_root.map(|r| names.iter().any(|n| n == r)).unwrap_or(false);
        let root = if shadow { None } else { scrut_root.cloned() };
        if let Some(r) = &root {
            self.facts.provenance.insert(arm.span, r.clone());
        }
        let mut frame: ScopeFrame = Vec::with_capacity(names.len());
        for n in names {
            // §13.6(d) shadow guard (pre-existing): a pattern binding also shadows
            // any OTHER live binding of that name — drop pre-existing provenance
            // rooted in it (F2 mirror cure, single-sourced with the Let seam).
            self.drop_shadowed_provenance(&n);
            let origin = match &root {
                Some(r) => Origin::Projection(r.clone()),
                None => Origin::Fresh,
            };
            let prior = self.bindings.insert(n.clone(), BindState { origin, param_idx: None });
            frame.push((n, prior));
        }
        frame
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
    TransferResult { summary, facts: w.facts, deps: w.deps, value_uses: w.value_uses }
}

#[cfg(test)]
mod tests;
