//! CS-3 — the per-cluster fixpoint driver + the `pass5_ownership` entry
//! (`design/typecheck/ownership-inference.md` §3.2, §13.2 CS-3, §13.5 toggle).
//!
//! The driver runs inside `finalize_check_result_inner` after mono + the callee
//! write-back. It:
//!
//! 1. **Gates on the toggle** — `CRANELISP_NO_OWNERSHIP` set ⇒ return at entry,
//!    emit nothing (§13.5; the differential-oracle anchor).
//! 2. **Collects the universe** — the cluster's codegen-bound callables (every
//!    `Def` with a `codegen_view`, incl. mono instances registered by
//!    `register_mono_entry`).
//! 3. **Runs the worklist fixpoint** (modes / escape / flow) — optimistic init,
//!    monotone widening, re-entry driven by the harvested `DepSet` (§13.3, the
//!    §13.6(e) ruling — not the persisted `call_graph_edges`, which seed order
//!    only).
//! 4. **Runs the confinement stratum** over the converged summaries (§5,
//!    stratified — never feeds back into modes, §3.2).
//! 5. **Publishes** via [`super::publish`] (staging-aware, cluster-atomic).
//!
//! # The memo (§6)
//!
//! The in-pass `summaries` map **is** the memo for one compile: each callable
//! converges once and repeated `Apply` reads are map hits. The cross-invocation
//! session memo the design sketches (a `DashMap` on the checker env, keyed
//! `(template home, mangled name)`) needs a session-owned borrowed field
//! threaded from `int` — out of scope for this typecheck-narrow change-set;
//! filed as a follow-up (determinism makes its absence a re-compute cost, never
//! a wrong result — §6).

use std::collections::{HashMap, HashSet, VecDeque};

use cranelisp_types::{
    ConcreteType, DefKind, FQSymbol, Mode, ModeSummary, ModuleEntry, ModuleFullPath, MonoExpr,
    PrimitiveBody, Symbol, Type, UserFnState,
};

use crate::checker::{CheckState, TypeCheckEnv};

use super::classify::{CopyClassifier, TerminalKind};
use super::confinement::confine;
use super::transfer::{transfer, SiteFacts, TransferEnv};

/// One codegen-bound callable in the cluster universe.
struct Callable {
    key: Symbol,
    params: Vec<(Symbol, ConcreteType)>,
    body: MonoExpr,
}

/// The pass output for one cluster — consumed by [`super::publish`].
pub(crate) struct ClusterOwnership {
    /// Converged summary per callable key.
    pub summaries: HashMap<Symbol, ModeSummary>,
    /// Site facts per callable key (escape + provenance + confined) — consumed
    /// by the CS-4 site-fact annotation walk + H5 trace.
    pub facts: HashMap<Symbol, SiteFacts>,
    /// Callable names referenced in value position anywhere in the cluster (§8.3).
    pub value_used: HashSet<Symbol>,
}

/// The real callee-fact environment: working in-cluster summaries first, then
/// chain-follow through the symbol table for imports / declared leaves.
struct ClusterEnv<'e, 'a, C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore> {
    env: &'e TypeCheckEnv<'a, C, L>,
    current_module: ModuleFullPath,
    working: &'e HashMap<Symbol, ModeSummary>,
}

impl<C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore> TransferEnv
    for ClusterEnv<'_, '_, C, L>
{
    fn terminal_kind(&self, name: &Symbol) -> Option<TerminalKind> {
        if self.working.contains_key(name) {
            return Some(TerminalKind::UserFnConcrete);
        }
        let (entry, _home) =
            self.env.resolve_terminal_entry_and_home(&self.current_module, name.as_ref())?;
        kind_of_entry(&entry)
    }

    fn summary_of(&self, name: &Symbol) -> Option<(FQSymbol, ModeSummary)> {
        if let Some(s) = self.working.get(name) {
            return Some((
                FQSymbol { module: self.current_module.clone(), symbol: name.clone() },
                s.clone(),
            ));
        }
        let (entry, home) =
            self.env.resolve_terminal_entry_and_home(&self.current_module, name.as_ref())?;
        entry
            .mode_summary()
            .map(|s| (FQSymbol { module: home, symbol: name.clone() }, s.clone()))
    }
}

/// Classify a chain-follow terminal entry into a [`TerminalKind`] (§2.1).
fn kind_of_entry<C: cranelisp_types::CodeStore>(entry: &ModuleEntry<C>) -> Option<TerminalKind> {
    match entry {
        ModuleEntry::Def { kind, .. } => match kind.as_ref() {
            DefKind::UserFn { fn_state: UserFnState::Concrete { .. } } => {
                Some(TerminalKind::UserFnConcrete)
            }
            DefKind::Primitive { body: PrimitiveBody::Inline | PrimitiveBody::Extern { .. }, .. } => {
                Some(TerminalKind::DeclaredLeaf)
            }
            DefKind::Constructor { .. } | DefKind::PlatformEffect { .. } => {
                Some(TerminalKind::PinnedBoundary)
            }
            _ => None,
        },
        _ => None,
    }
}

/// The `pass5_ownership` driver (§13.2 CS-3). Reads the cluster's converged
/// callable set, runs the two strata, and publishes. Toggle-gated at entry
/// (§13.5): when analysis is off, emits nothing.
pub(crate) fn run_pass5<C, L>(env: &TypeCheckEnv<C, L>, state: &CheckState)
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    if cranelisp_types::ownership_analysis_off() {
        return; // toggle-off: no summaries, no facts, no marks (§13.5)
    }

    let current_module = state.current_module.clone();
    let universe = collect_universe(env, state);
    if universe.is_empty() {
        return;
    }

    let cluster = compute_cluster(env, &current_module, &universe);
    super::publish::publish(env, state, &cluster);
}

/// Collect the cluster's codegen-bound callables (a `Def` with a
/// `codegen_view`), cloning the body + deriving param types from the scheme.
fn collect_universe<C, L>(env: &TypeCheckEnv<C, L>, state: &CheckState) -> Vec<Callable>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    let read = env.current_symbol_table(state);
    let view = read.view();
    let mut out = Vec::new();
    for (key, entry) in view.iter() {
        let Some(cv) = entry.codegen_view() else { continue };
        let scheme_ty = match entry {
            ModuleEntry::Def { scheme, .. } => Some(scheme.ty.clone()),
            _ => None,
        };
        let params = param_types(&cv.params, scheme_ty.as_ref());
        out.push(Callable { key: key.clone(), params, body: cv.body.clone() });
    }
    out
}

/// Derive `(name, ConcreteType)` per formal from the callable scheme's `Fn`
/// param list. Any non-`Fn` scheme, arity mismatch, or non-concrete param type
/// falls back to a non-scalar placeholder (`String`) — never mis-classified as
/// `Copy` (sound: a non-`Copy` param seeds `Borrowed`).
fn param_types(names: &[Symbol], scheme_ty: Option<&Type>) -> Vec<(Symbol, ConcreteType)> {
    let concretes: Vec<ConcreteType> = match scheme_ty {
        Some(Type::Fn(ps, _)) if ps.len() == names.len() => ps
            .iter()
            .map(|t| ConcreteType::from_type(t).unwrap_or(ConcreteType::String))
            .collect(),
        _ => vec![ConcreteType::String; names.len()],
    };
    names.iter().cloned().zip(concretes).collect()
}

/// The worklist fixpoint (modes/escape/flow) + the confinement stratum.
fn compute_cluster<C, L>(
    env: &TypeCheckEnv<C, L>,
    current_module: &ModuleFullPath,
    universe: &[Callable],
) -> ClusterOwnership
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    let copy = CopyClassifier::new();

    // Optimistic init: every param Borrowed/Copy, Fresh, Consumed, spark clear.
    let mut summaries: HashMap<Symbol, ModeSummary> = HashMap::new();
    for c in universe {
        summaries.insert(c.key.clone(), optimistic(&c.params, &copy));
    }

    let mut facts: HashMap<Symbol, SiteFacts> = HashMap::new();
    let mut deps: HashMap<Symbol, HashSet<FQSymbol>> = HashMap::new();
    let mut value_used: HashSet<Symbol> = HashSet::new();

    // Worklist — BFS, dedup via an in-queue set. Termination bound: the summary
    // lattice height is O(params) per callable, so O(universe × (maxp+4)) visits
    // suffice; the cap is a defensive guard (result-mode is not a clean lattice).
    let max_params = universe.iter().map(|c| c.params.len()).max().unwrap_or(0);
    let cap = universe.len().saturating_mul(max_params + 4) + 32;
    let mut queue: VecDeque<Symbol> = universe.iter().map(|c| c.key.clone()).collect();
    let mut queued: HashSet<Symbol> = queue.iter().cloned().collect();
    let by_key: HashMap<&Symbol, &Callable> = universe.iter().map(|c| (&c.key, c)).collect();

    let mut visits = 0usize;
    while let Some(key) = queue.pop_front() {
        queued.remove(&key);
        visits += 1;
        if visits > cap {
            break;
        }
        let Some(c) = by_key.get(&key) else { continue };

        let cluster_env =
            ClusterEnv { env, current_module: current_module.clone(), working: &summaries };
        let r = transfer(&c.params, &c.body, &cluster_env, &copy);

        deps.insert(key.clone(), r.deps.clone());
        facts.insert(key.clone(), r.facts);
        value_used.extend(r.value_uses);

        let changed = summaries.get(&key) != Some(&r.summary);
        summaries.insert(key.clone(), r.summary);
        if changed {
            // Re-enter intra-cluster callers: any callable whose harvested
            // DepSet named this key (§13.3 self-describing re-entry).
            let this_fq = FQSymbol { module: current_module.clone(), symbol: key.clone() };
            for (other, dset) in &deps {
                if other != &key && dset.contains(&this_fq) && queued.insert(other.clone()) {
                    queue.push_back(other.clone());
                }
            }
        }
    }

    // Confinement stratum (§5) over the converged summaries.
    for c in universe {
        let param_modes: Vec<(Symbol, Mode)> = c
            .params
            .iter()
            .enumerate()
            .map(|(i, (n, _))| {
                (n.clone(), summaries.get(&c.key).map(|s| s.param_mode(i)).unwrap_or(Mode::Owned))
            })
            .collect();
        let cluster_env =
            ClusterEnv { env, current_module: current_module.clone(), working: &summaries };
        let cr = confine(&param_modes, &c.body, &cluster_env);
        if let Some(s) = summaries.get_mut(&c.key) {
            s.spark_ops = cr.spark_ops;
        }
        if let Some(f) = facts.get_mut(&c.key) {
            f.confined = cr.confined;
        }
    }

    ClusterOwnership { summaries, facts, value_used }
}

/// The optimistic ⊥ summary for the fixpoint init: params `Copy`/`Borrowed`,
/// result `Fresh`, flow `Consumed`, spark clear (§3.2).
fn optimistic(params: &[(Symbol, ConcreteType)], copy: &CopyClassifier) -> ModeSummary {
    let n = params.len();
    ModeSummary {
        param_modes: params
            .iter()
            .map(|(_, ty)| if copy.is_copy(ty) { Mode::Copy } else { Mode::Borrowed })
            .collect(),
        result: cranelisp_types::ResultMode::Fresh,
        param_flow: vec![cranelisp_types::ParamFlow::Consumed; n],
        spark_ops: vec![false; n],
        result_unique: false,
    }
}

#[cfg(test)]
mod tests;
