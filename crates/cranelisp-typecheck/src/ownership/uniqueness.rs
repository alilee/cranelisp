//! CS-3 — the uniqueness stratum: `result_unique` chaining + `unique_static`
//! site facts (`design/typecheck/ownership-inference.md` §7, §14.2; spine §10
//! item 5). Increment II, write path.
//!
//! This is the **third fixpoint stratum**, stratified AFTER the modes and
//! confinement strata converge (§3.2 — nothing in modes/confinement reads
//! uniqueness, so the stratification is exact). It computes, per callable:
//!
//! - **`result_unique: bool`** — the chaining discriminator (§14.2 clause 3):
//!   `true` iff the callable's returned value is provably a fresh unique root
//!   (rc == 1), computed intraprocedurally from the body's return shape + the
//!   callees' `result_unique` bits (the chaining). A must-property; the fixpoint
//!   is a **greatest fixpoint** (init-optimistic-`true`, narrow to `false`), with
//!   `false` the conservative point (degrades to the backend's dynamic rc==1
//!   check). The driver ([`super::fixpoint`]) owns the worklist iteration; this
//!   module is the pure per-body transfer.
//! - **`unique_static: Option<bool>`** site facts — `Some(true)` on a
//!   fresh-producing node whose value is a proven unique single-use root (§14.2
//!   clauses 1–3). Advisory: the backend elides its dynamic rc==1 check where
//!   the proof holds and runs the check everywhere else (§14.3). `None`
//!   everywhere is sound.
//!
//! # Soundness (monotone; §14.2)
//!
//! Every fact's absent/`false`/`None` reading is exactly the pre-write-path
//! behaviour (the dynamic check / no reuse). The analysis only ever moves a
//! value *toward* `false`/`None` when it cannot prove uniqueness. In particular:
//!
//! - a call result is admitted as a unique root **only** when the callee's own
//!   `result_unique` proves it (never the weaker `result == Fresh`, which a
//!   callee that stashes its returned value would satisfy while the value is
//!   *not* rc == 1 — the caller cannot see the callee-side stash, so it must
//!   trust the callee's proof, not its provenance);
//! - a value with more than one **consuming** use (a projection/borrowed read is
//!   NOT a consuming use, §7.2 clause 2) is not admitted;
//! - the use count is a sound **over-approximation** (flat, scope-insensitive:
//!   over-counting only ever demotes a value toward the dynamic check).

use std::collections::{HashMap, HashSet};

use cranelisp_types::{ConcreteType, Mode, ModeSummary, MonoExpr, Span, Symbol};

use super::classify::{classify_call, CallClass, TerminalKind};
use super::transfer::collect_pattern_bindings;

/// The uniqueness stratum's per-callable output.
#[derive(Debug, Clone, Default)]
pub(crate) struct UniquenessResult {
    /// The callable's `result_unique` bit (§14.2 clause 3).
    pub result_unique: bool,
    /// span → `unique_static` verdict for proven fresh unique single-use roots.
    /// Only `Some(true)` entries are recorded (absent ⇒ `None` ⇒ conservative).
    pub unique_sites: HashMap<Span, bool>,
}

/// The callee-fact abstraction the uniqueness analysis consults — kept behind a
/// trait so the analysis stays pure and unit-testable (§11). The driver's
/// implementation reads the WORKING `result_unique` map (in-cluster, mid-
/// fixpoint) and the CONVERGED modes summaries; unit tests supply stubs.
pub(crate) trait UniqEnv {
    /// The terminal callable kind a callee `Var` chain-resolves to — for the
    /// `classify_call` `resolved_call == None` row. `None` ⇒ Decision-24.
    fn terminal_kind(&self, name: &Symbol) -> Option<TerminalKind>;
    /// The callee's CONVERGED modes summary — read for its `param_modes` (to
    /// classify an arg use as consuming vs a borrowed/projection read).
    /// `None` ⇒ the ⊤ (Decision-24) conservative point (every arg consuming).
    fn summary_of(&self, name: &Symbol) -> Option<ModeSummary>;
    /// The callee's `result_unique` bit — the chaining read. In-cluster callees
    /// read the WORKING (mid-fixpoint) map; imports/leaves read their persisted
    /// summary. Absent ⇒ `false` (the conservative point — a call whose callee
    /// does not prove uniqueness yields no unique root).
    fn result_unique_of(&self, name: &Symbol) -> bool;
    /// Is `ty` layout-eligible for in-place reuse (a heap object with an
    /// overwritable slot)? Copy-flattened / scalar values have no reusable heap
    /// slot (§14.2 clause 3). Absent-eligibility ⇒ conservative `false`.
    fn layout_eligible(&self, ty: &ConcreteType) -> bool;
}

/// The consuming-ness of the position a value flows into.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Pos {
    /// The value here is consumed (owned handoff / Decision-24 arg / aggregate
    /// field / return / capture) — a `Var` use here is a consuming use.
    Consume,
    /// The value here is only read (borrowed arg / scrutinee / condition) — a
    /// `Var` use here is NOT a consuming use (§7.2 clause 2).
    Borrow,
}

/// Analyse one callable body for uniqueness (§14.2). Pure over [`UniqEnv`].
///
/// Two passes: (1) count consuming uses per binding + record which let/parbind
/// bindings have a directly-fresh RHS; (2) compute `result_unique` (from the
/// body's return shape) and the `unique_static` site facts.
pub(crate) fn analyze_uniqueness<E: UniqEnv>(
    params: &[(Symbol, ConcreteType)],
    body: &MonoExpr,
    env: &E,
) -> UniquenessResult {
    let mut w = UniqWalker {
        env,
        tracked: params.iter().map(|(n, _)| n.clone()).collect(),
        fresh_bindings: HashSet::new(),
        consuming_uses: HashMap::new(),
        unique_sites: HashMap::new(),
    };
    // Pass 1 — count consuming uses + record fresh bindings. The body is the
    // return position (Consume).
    w.count(body, Pos::Consume);
    // Pass 2a — the result_unique bit from the body's return shape.
    let result_unique = w.is_fresh_unique_value(body);
    // Pass 2b — the unique_static site facts (Consume = return position).
    w.emit(body, Pos::Consume, None);
    UniquenessResult { result_unique, unique_sites: w.unique_sites }
}

struct UniqWalker<'e, E: UniqEnv> {
    env: &'e E,
    /// All binding names in scope (params + let/parbind/match bindings) — flat,
    /// scope-insensitive (a sound over-approximation: merging a shadowed name
    /// only over-counts uses, demoting toward the dynamic check).
    tracked: HashSet<Symbol>,
    /// The subset of `tracked` that are let/parbind bindings with a directly-
    /// fresh RHS (an allocation or a chained-unique call). Params and projection
    /// bindings are never fresh.
    fresh_bindings: HashSet<Symbol>,
    /// Consuming-use count per tracked binding (flat).
    consuming_uses: HashMap<Symbol, usize>,
    /// The accumulated `Some(true)` site facts.
    unique_sites: HashMap<Span, bool>,
}

impl<E: UniqEnv> UniqWalker<'_, E> {
    // ---- Pass 1: consuming-use counting + fresh-binding discovery ----

    fn count(&mut self, expr: &MonoExpr, pos: Pos) {
        match expr {
            MonoExpr::Var { name, .. } => {
                if pos == Pos::Consume && self.tracked.contains(name) {
                    *self.consuming_uses.entry(name.clone()).or_insert(0) += 1;
                }
            }
            MonoExpr::IntLit { .. }
            | MonoExpr::FloatLit { .. }
            | MonoExpr::BoolLit { .. }
            | MonoExpr::StringLit { .. } => {}
            MonoExpr::Apply { callee, args, resolved_call, .. } => {
                self.count(callee, Pos::Borrow);
                let summary = match classify_call(
                    resolved_call.as_deref(),
                    callee,
                    |n| self.env.terminal_kind(n),
                ) {
                    CallClass::Summarised(name) => Some((true, self.env.summary_of(&name))),
                    CallClass::Decision24 => None,
                };
                for (j, arg) in args.iter().enumerate() {
                    let p = arg_pos(&summary, j);
                    self.count(arg, p);
                }
            }
            MonoExpr::VecLit { elements, .. } => {
                for e in elements {
                    self.count(e, Pos::Consume);
                }
            }
            MonoExpr::ConstrADT { fields, .. } => {
                for f in fields {
                    self.count(f, Pos::Consume);
                }
            }
            MonoExpr::Lambda { body, .. } => {
                // A captured enclosing binding used inside the closure is
                // conservatively a consume (the closure holds it).
                self.count(body, Pos::Consume);
            }
            MonoExpr::Let { bindings, body, .. } | MonoExpr::ParBind { bindings, body, .. } => {
                for (n, rhs) in bindings {
                    if self.is_direct_fresh(rhs) {
                        self.fresh_bindings.insert(n.clone());
                    }
                    self.tracked.insert(n.clone());
                    // The RHS produces the bound value; walk it in a consuming
                    // position (a bare-`Var` alias is conservatively a consume).
                    self.count(rhs, Pos::Consume);
                }
                self.count(body, pos);
            }
            MonoExpr::If { cond, then_branch, else_branch, .. } => {
                self.count(cond, Pos::Borrow);
                self.count(then_branch, pos);
                self.count(else_branch, pos);
            }
            MonoExpr::Match { scrutinee, arms, .. } => {
                self.count(scrutinee, Pos::Borrow);
                for arm in arms {
                    let mut names = Vec::new();
                    collect_pattern_bindings(&arm.pattern, &mut names);
                    for n in names {
                        self.tracked.insert(n);
                    }
                    self.count(&arm.body, pos);
                }
            }
            MonoExpr::Trace { body, .. } => self.count(body, pos),
            MonoExpr::LaunchContinue { launched, continuation, .. } => {
                self.count(launched, Pos::Consume);
                self.count(continuation, pos);
            }
        }
    }

    // ---- clause-1 provenance predicates ----

    /// The DIRECT clause-1 provenance test for a node: is the value this node
    /// produces a fresh unique root, judged from the node alone (not chasing a
    /// bound `Var`)? A fresh allocation, or a static call whose callee's
    /// `result_unique` proves its result rc == 1 (the sound chaining read —
    /// never `result == Fresh`; §14.2 clause 1).
    fn is_direct_fresh(&self, expr: &MonoExpr) -> bool {
        match expr {
            MonoExpr::VecLit { .. }
            | MonoExpr::ConstrADT { .. }
            | MonoExpr::StringLit { .. }
            | MonoExpr::Lambda { .. } => true,
            MonoExpr::IntLit { .. } | MonoExpr::FloatLit { .. } | MonoExpr::BoolLit { .. } => true,
            MonoExpr::Apply { callee, resolved_call, .. } => {
                match classify_call(resolved_call.as_deref(), callee, |n| self.env.terminal_kind(n))
                {
                    CallClass::Summarised(name) => self.env.result_unique_of(&name),
                    CallClass::Decision24 => false,
                }
            }
            _ => false,
        }
    }

    /// The SOUND recursive "this value is a proven unique fresh root" predicate
    /// (used for `result_unique` and for a returned bound `Var`). Extends
    /// [`Self::is_direct_fresh`] with control-flow transparency and the
    /// bound-`Var` single-use rule.
    fn is_fresh_unique_value(&self, expr: &MonoExpr) -> bool {
        match expr {
            MonoExpr::If { then_branch, else_branch, .. } => {
                self.is_fresh_unique_value(then_branch) && self.is_fresh_unique_value(else_branch)
            }
            MonoExpr::Match { arms, .. } => {
                !arms.is_empty() && arms.iter().all(|a| self.is_fresh_unique_value(&a.body))
            }
            MonoExpr::Let { body, .. } | MonoExpr::ParBind { body, .. } => {
                self.is_fresh_unique_value(body)
            }
            MonoExpr::Trace { body, .. } => self.is_fresh_unique_value(body),
            // A bound name is a unique fresh root iff its binding is directly
            // fresh AND it is consumed at most once (single consuming use —
            // §7.2 clause 2; a projection/borrow read did not count).
            MonoExpr::Var { name, .. } => {
                self.fresh_bindings.contains(name)
                    && self.consuming_uses.get(name).copied().unwrap_or(0) <= 1
            }
            other => self.is_direct_fresh(other),
        }
    }

    // ---- Pass 2b: unique_static site-fact emission ----

    /// Emit `unique_static = Some(true)` on fresh-producing nodes whose value is
    /// a proven unique single-use root (§14.2 clauses 1–3). `bound_to` is the
    /// let/parbind binding whose value flows through this position (so the
    /// single-use test reads that binding's consuming-use count); `None` for an
    /// inline value (single-use by construction, gated on `pos == Consume`).
    fn emit(&mut self, expr: &MonoExpr, pos: Pos, bound_to: Option<&Symbol>) {
        // A directly-fresh node in a consuming context, layout-eligible, with a
        // single consuming use ⇒ the write-path proof.
        if self.is_direct_fresh(expr) && self.env.layout_eligible(expr.ty()) {
            let single_consume = match bound_to {
                Some(n) => self.consuming_uses.get(n).copied().unwrap_or(0) <= 1,
                None => pos == Pos::Consume,
            };
            if single_consume {
                self.unique_sites.insert(expr.span(), true);
            }
        }

        // Recurse. Control-flow nodes pass `bound_to` through transparently (the
        // branch value IS the bound value on that path); everything else clears
        // it (a child is not the binding's top-level value).
        match expr {
            MonoExpr::Apply { callee, args, resolved_call, .. } => {
                self.emit(callee, Pos::Borrow, None);
                let summary = match classify_call(
                    resolved_call.as_deref(),
                    callee,
                    |n| self.env.terminal_kind(n),
                ) {
                    CallClass::Summarised(name) => Some((true, self.env.summary_of(&name))),
                    CallClass::Decision24 => None,
                };
                for (j, arg) in args.iter().enumerate() {
                    self.emit(arg, arg_pos(&summary, j), None);
                }
            }
            MonoExpr::VecLit { elements, .. } => {
                for e in elements {
                    self.emit(e, Pos::Consume, None);
                }
            }
            MonoExpr::ConstrADT { fields, .. } => {
                for f in fields {
                    self.emit(f, Pos::Consume, None);
                }
            }
            MonoExpr::Lambda { body, .. } => self.emit(body, Pos::Consume, None),
            MonoExpr::Let { bindings, body, .. } | MonoExpr::ParBind { bindings, body, .. } => {
                for (n, rhs) in bindings {
                    self.emit(rhs, Pos::Consume, Some(n));
                }
                self.emit(body, pos, bound_to);
            }
            MonoExpr::If { cond, then_branch, else_branch, .. } => {
                self.emit(cond, Pos::Borrow, None);
                self.emit(then_branch, pos, bound_to);
                self.emit(else_branch, pos, bound_to);
            }
            MonoExpr::Match { scrutinee, arms, .. } => {
                self.emit(scrutinee, Pos::Borrow, None);
                for arm in arms {
                    self.emit(&arm.body, pos, bound_to);
                }
            }
            MonoExpr::Trace { body, .. } => self.emit(body, pos, bound_to),
            MonoExpr::LaunchContinue { launched, continuation, .. } => {
                self.emit(launched, Pos::Consume, None);
                self.emit(continuation, pos, bound_to);
            }
            MonoExpr::Var { .. }
            | MonoExpr::IntLit { .. }
            | MonoExpr::FloatLit { .. }
            | MonoExpr::BoolLit { .. }
            | MonoExpr::StringLit { .. } => {}
        }
    }
}

/// The consuming-ness of arg `j` of a call: a `Borrowed`/`Copy` param position
/// of a summarised callee is a borrowed/projection read (NOT consuming); every
/// other position (owned, absent-summary ⊤, or a Decision-24 site) consumes.
fn arg_pos(summary: &Option<(bool, Option<ModeSummary>)>, j: usize) -> Pos {
    match summary {
        // Summarised call: read the callee's param mode (absent ⇒ ⊤ = Owned).
        Some((true, Some(s))) => match s.param_mode(j) {
            Mode::Borrowed | Mode::Copy => Pos::Borrow,
            Mode::Owned => Pos::Consume,
        },
        Some((true, None)) => Pos::Consume, // summarised but ⊤ summary ⇒ Owned
        // Decision-24 site (`None`) or any other shape ⇒ consuming (rule 5).
        _ => Pos::Consume,
    }
}

#[cfg(test)]
mod tests;
