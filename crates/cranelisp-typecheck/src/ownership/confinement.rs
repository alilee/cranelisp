//! CS-3 — confinement: strand-context classification + the per-cell join
//! (`design/typecheck/ownership-inference.md` §5, §13.2 CS-3, §13.7
//! `confinement.rs`).
//!
//! Runs as the **second stratum** after modes/escape/flow converge (§3.2
//! stratification — confinement never feeds back into modes). It computes, per
//! callable:
//!
//! - **`spark_ops[i]`** — the interprocedural confinement bit that rides the
//!   summary: may the callee (transitively) run an RC op on param `i` off the
//!   calling strand? Set when a consuming op on (anything rooted in) param `i`
//!   sits in a joined-spark / deferred context, or when `i` is passed to a
//!   callee whose corresponding `spark_op` is set (§5.3).
//! - **`confined` site facts** — per allocation, `Some(true)` when every
//!   surviving op stays parent-strand, `Some(false)` (Crossing) otherwise.
//!   `Transferred` is **never emitted** — it collapses to `Crossing` at
//!   emission for increment I (§5.4).
//!
//! The lenient-spark placement is codegen-internal (typecheck cannot see it),
//! so the analysis **over-approximates**: every lenient-eligible position (a
//! `let`/`ParBind` binding RHS, an apply argument) is treated as potentially
//! off-strand (§5.2). Monotone-sound: a subtree with no surviving op on a cell
//! is harmless whether sparked or not.

use std::collections::HashMap;

use cranelisp_types::{Mode, MonoExpr, Span, Symbol};

use super::classify::{CallClass, classify_call};
use super::transfer::{TransferEnv, collect_pattern_bindings};

/// A saved confinement scope frame (§13.6(i), F4 — the sibling walker gets the
/// same lexical-scope discipline for precision + anti-recurrence). For every
/// name a binding scope introduces, records the `param_idx` entry it shadows
/// (`Some(idx)` when the name collides with a param, `None` otherwise). On scope
/// exit the entry is restored, so an inner binding that shadows a param does not
/// spuriously match the param (`spark_ops[i]` false-set toward `Crossing`). The
/// over-approximation is sound either way (spine §5.2); this only tightens it.
type ConfineFrame = Vec<(Symbol, Option<usize>)>;

/// The confinement stratum's output for one callable.
#[derive(Debug, Clone)]
pub(crate) struct ConfineResult {
    /// Per-param `spark_ops` bit (index-aligned with the formal list).
    pub spark_ops: Vec<bool>,
    /// Per allocation-site `confined` verdict (`true` = Confined / non-atomic).
    pub confined: HashMap<Span, bool>,
}

/// The strand a sub-expression can execute on (§5.2).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Strand {
    /// Ordinary body code outside any fork construct.
    Parent,
    /// Inside a `ParBind` binding or a lenient-eligible position — potentially
    /// off-strand (the over-approximation).
    PotentialFork,
    /// Inside `LaunchContinue.launched` / a deferred continuation — suspension.
    Deferred,
}

impl Strand {
    fn off_parent(self) -> bool {
        !matches!(self, Strand::Parent)
    }
}

struct Confiner<'e, E: TransferEnv> {
    env: &'e E,
    /// param name → index, for the params in scope.
    param_idx: HashMap<Symbol, usize>,
    /// param index → converged mode (Copy params carry no RC ops).
    param_mode: Vec<Mode>,
    spark_ops: Vec<bool>,
    confined: HashMap<Span, bool>,
}

impl<'e, E: TransferEnv> Confiner<'e, E> {
    /// Restore a confinement scope frame on scope exit (§13.6(i)): reinsert each
    /// shadowed `param_idx` entry (`Some(idx)`) or drop the temporary shadow
    /// (`None`, a no-op — the name was not a param). Reverse order so nested
    /// shadows of one name unwind correctly.
    fn restore_frame(&mut self, frame: ConfineFrame) {
        for (name, prior) in frame.into_iter().rev() {
            match prior {
                Some(idx) => {
                    self.param_idx.insert(name, idx);
                }
                None => {
                    self.param_idx.remove(&name);
                }
            }
        }
    }

    fn walk(&mut self, expr: &MonoExpr, strand: Strand) {
        match expr {
            MonoExpr::StringLit { span, .. }
            | MonoExpr::VecLit { span, .. }
            | MonoExpr::ConstrADT { span, .. }
            | MonoExpr::Lambda { span, .. } => {
                // An allocation site: Confined iff produced parent-strand.
                self.confined.insert(*span, !strand.off_parent());
                if let MonoExpr::VecLit { elements, .. } = expr {
                    for el in elements {
                        self.walk(el, strand);
                    }
                }
                if let MonoExpr::ConstrADT { fields, .. } = expr {
                    for f in fields {
                        self.walk(f, strand);
                    }
                }
                if let MonoExpr::Lambda { body, .. } = expr {
                    self.walk(body, strand);
                }
            }
            MonoExpr::IntLit { .. } | MonoExpr::FloatLit { .. } | MonoExpr::BoolLit { .. } => {}
            MonoExpr::Var { .. } => {}
            MonoExpr::Let { bindings, body, .. } => {
                // §13.6(i) (F4): shadow the colliding param names for the body +
                // subsequent RHSs, restore on scope exit.
                let mut frame: ConfineFrame = Vec::with_capacity(bindings.len());
                for (n, rhs) in bindings {
                    // A let-binding RHS is a lenient-eligible position.
                    self.walk(rhs, join_strand(strand, Strand::PotentialFork));
                    frame.push((n.clone(), self.param_idx.remove(n)));
                }
                self.walk(body, strand);
                self.restore_frame(frame);
            }
            MonoExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                self.walk(cond, strand);
                self.walk(then_branch, strand);
                self.walk(else_branch, strand);
            }
            MonoExpr::Match {
                scrutinee, arms, ..
            } => {
                self.walk(scrutinee, strand);
                for arm in arms {
                    // §13.6(i) (F4): each arm shadows its pattern bindings, restored
                    // before the sibling arm — no arm-binding leak.
                    let mut names = Vec::new();
                    collect_pattern_bindings(&arm.pattern, &mut names);
                    let frame: ConfineFrame = names
                        .iter()
                        .map(|n| (n.clone(), self.param_idx.remove(n)))
                        .collect();
                    self.walk(&arm.body, strand);
                    self.restore_frame(frame);
                }
            }
            MonoExpr::Apply {
                callee,
                args,
                resolved_call,
                span,
                ..
            } => {
                self.confined.insert(*span, !strand.off_parent());
                let class = classify_call(resolved_call.as_deref(), callee, |n| {
                    self.env.terminal_kind(n)
                });
                self.walk(callee, strand);
                // The consuming op on a param arg runs on the CALL's enclosing
                // strand; only sub-allocations *within* an arg expression are
                // lenient-sparkable (the §5.2 over-approximation applies to
                // computation, not to the handoff of a bare param Var).
                let arg_strand = join_strand(strand, Strand::PotentialFork);
                match class {
                    CallClass::Summarised(name) => {
                        let summary = self.env.summary_of(&name).map(|(_, s)| s);
                        for (j, arg) in args.iter().enumerate() {
                            if let MonoExpr::Var { name: an, .. } = arg
                                && let Some(&i) = self.param_idx.get(an)
                                && self.param_mode[i] != Mode::Copy
                            {
                                let callee_owns = summary
                                    .as_ref()
                                    .map(|s| s.param_mode(j) == Mode::Owned)
                                    .unwrap_or(true); // ⊤ = Owned
                                let callee_sparks =
                                    summary.as_ref().map(|s| s.spark_op(j)).unwrap_or(true);
                                // A consuming op off-strand (the call runs in a
                                // spark/deferred context), OR a callee that
                                // itself sparks over this position (any strand).
                                if (strand.off_parent() && callee_owns) || callee_sparks {
                                    self.spark_ops[i] = true;
                                }
                            }
                            self.walk(arg, arg_strand);
                        }
                    }
                    CallClass::Decision24 => {
                        for arg in args {
                            if let MonoExpr::Var { name: an, .. } = arg
                                && let Some(&i) = self.param_idx.get(an)
                                && self.param_mode[i] != Mode::Copy
                                && strand.off_parent()
                            {
                                // Decision-24 consumes (Owned) off-strand.
                                self.spark_ops[i] = true;
                            }
                            self.walk(arg, arg_strand);
                        }
                    }
                }
            }
            MonoExpr::Trace { body, .. } => self.walk(body, strand),
            MonoExpr::ParBind { bindings, body, .. } => {
                // §13.6(i) (F4): same scope discipline as `Let`.
                let mut frame: ConfineFrame = Vec::with_capacity(bindings.len());
                for (n, rhs) in bindings {
                    // A ParBind binding runs on a joined spark strand.
                    self.walk(rhs, Strand::PotentialFork);
                    frame.push((n.clone(), self.param_idx.remove(n)));
                }
                self.walk(body, strand);
                self.restore_frame(frame);
            }
            MonoExpr::LaunchContinue {
                launched,
                continuation,
                ..
            } => {
                self.walk(launched, Strand::Deferred);
                self.walk(continuation, strand);
            }
        }
    }
}

/// Join two strand contexts toward the more off-parent point
/// (`Parent ⊑ PotentialFork ⊑ Deferred`).
fn join_strand(a: Strand, b: Strand) -> Strand {
    let rank = |s: Strand| match s {
        Strand::Parent => 0,
        Strand::PotentialFork => 1,
        Strand::Deferred => 2,
    };
    if rank(b) > rank(a) { b } else { a }
}

/// Compute the confinement stratum for one callable body (§5).
pub(crate) fn confine<E: TransferEnv>(
    params: &[(Symbol, Mode)],
    body: &MonoExpr,
    env: &E,
) -> ConfineResult {
    let mut param_idx = HashMap::new();
    let mut param_mode = Vec::with_capacity(params.len());
    for (i, (name, mode)) in params.iter().enumerate() {
        param_idx.insert(name.clone(), i);
        param_mode.push(*mode);
    }
    let mut c = Confiner {
        env,
        param_idx,
        param_mode,
        spark_ops: vec![false; params.len()],
        confined: HashMap::new(),
    };
    c.walk(body, Strand::Parent);
    ConfineResult {
        spark_ops: c.spark_ops,
        confined: c.confined,
    }
}

#[cfg(test)]
mod tests;
