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
            self.env.resolve_terminal_entry_and_home_scoped(&self.current_module, name.as_ref())?;
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
            self.env.resolve_terminal_entry_and_home_scoped(&self.current_module, name.as_ref())?;
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
///
/// **W0.b universe pin (`backend-keyed-consumer.md` §4 W0.b / §5).** After the
/// totalization flip EVERY codegen-reached entry carries a `codegen_view`
/// (ctor/accessor synthetic bodies + best-effort concrete defns now included),
/// so "has a view" no longer selects the analysable set. The ownership fixpoint
/// must run over EXACTLY the pre-flip universe — genuine strict-concrete bodies
/// — because pulling the new lenient/synthetic entries into the cluster fixpoint
/// perturbs every summary (adding a ctor/accessor callee summary flips a
/// caller's borrow/RC result), a codegen change the W0.b byte-identity gate
/// forbids. The pre-flip predicate was "`build_concrete_codegen_view` returned
/// `Some`" ⇔ strict `MonoExpr::from_expr` succeeds on the stored body; the
/// lenient/synthetic classes fail it (residual `Var` / `inferred_type: None`
/// nodes), so re-checking strict success on the entry's `ast` reproduces the
/// pre-flip set exactly — ctors (Constructor kind, `ConstrADT` un-typed body),
/// accessors (`(match self …)` un-typed body), and lenient-fallback concrete
/// defns all excluded, mono instances and genuine concrete defns retained.
fn collect_universe<C, L>(env: &TypeCheckEnv<C, L>, state: &CheckState) -> Vec<Callable>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    let read = env.current_symbol_table(state);
    let view = read.view();
    let empty = HashMap::new();
    let mut out = Vec::new();
    for (key, entry) in view.iter() {
        let Some(cv) = entry.codegen_view() else { continue };
        let ModuleEntry::Def { scheme, ast: Some(ast_variant), .. } = entry else { continue };
        // Pre-flip universe pin: only a STRICT-concrete body participates.
        if MonoExpr::from_expr(&ast_variant.body, &empty, &empty).is_err() {
            continue;
        }
        let params = param_types(&cv.params, Some(&scheme.ty));
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
    // Termination bound: each stratum's summary lattice height is O(params) per
    // callable, so O(universe × (maxp+4)) visits suffice; the cap is a defensive
    // guard (result-mode is not a clean lattice). Shared by both strata.
    let max_params = universe.iter().map(|c| c.params.len()).max().unwrap_or(0);
    let cap = universe.len().saturating_mul(max_params + 4) + 32;
    compute_cluster_with_cap(env, current_module, universe, cap)
}

/// [`compute_cluster`] with an explicit visit cap (the cap is a test seam:
/// `cap = 0` forces both strata to exhaust on the first visit, exercising the
/// conservative-⊤ reset — blocker 4).
fn compute_cluster_with_cap<C, L>(
    env: &TypeCheckEnv<C, L>,
    current_module: &ModuleFullPath,
    universe: &[Callable],
    cap: usize,
) -> ClusterOwnership
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    // CS-II-3: the `Copy` predicate DELEGATES to the single-sourced
    // `value_layout` carrier (never a local re-implementation) — the
    // soundness-coupled predicate the backend's `HeapCategory::Value` arm also
    // consumes (§14.5). **B3 CO-LAND (S103 Wave 3a):** the tables input is now
    // **`Some(env.modules())`** — the REAL type defs, so value-eligible
    // single-scalar single-ctor products classify `Copy` — landed in the SAME
    // change-set as the backend `HeapCategory::Value` flattening arm. The two
    // surfaces MUST grow precision together (the soundness couple): a `Copy`-moded
    // param the backend flattens is a by-value word (no RC needed); flattening
    // without the flip = dead flattening; flipping without flattening = a
    // by-value bit-copy of a still-heap object with no `rc_inc` — a
    // use-after-free (observed Wave-2: the web-poll reactor's poll-leaf handle
    // freed early ⇒ "leaf never completed"). Both edits land here + in the
    // backend, one commit. Under `CRANELISP_NO_OWNERSHIP` this pass does not run,
    // so no `Copy` mode is emitted AND the backend does not flatten — the couple
    // holds at both toggle polarities.
    let copy =
        CopyClassifier::new(|ty| cranelisp_types::value_layout(ty, Some(env.modules())).is_some());

    // Optimistic init: every param Borrowed/Copy, Fresh, Consumed, spark clear.
    let mut summaries: HashMap<Symbol, ModeSummary> = HashMap::new();
    for c in universe {
        summaries.insert(c.key.clone(), optimistic(&c.params, &copy));
    }

    let mut facts: HashMap<Symbol, SiteFacts> = HashMap::new();
    let mut deps: HashMap<Symbol, HashSet<FQSymbol>> = HashMap::new();
    let mut value_used: HashSet<Symbol> = HashSet::new();

    // Worklist — BFS, dedup via an in-queue set.
    let mut queue: VecDeque<Symbol> = universe.iter().map(|c| c.key.clone()).collect();
    let mut queued: HashSet<Symbol> = queue.iter().cloned().collect();
    let by_key: HashMap<&Symbol, &Callable> = universe.iter().map(|c| (&c.key, c)).collect();

    let mut visits = 0usize;
    while let Some(key) = queue.pop_front() {
        queued.remove(&key);
        visits += 1;
        if visits > cap {
            // Cap exhausted (defensive; unreachable under monotone convergence).
            // The partially-converged summaries are monotone-BELOW their true
            // fixpoint ⇒ too precise ⇒ UNSOUND to publish. Reset the whole
            // universe to the conservative ⊤ (all-Owned / Fresh / Retained /
            // spark-set) — the sound failure direction (blocker 4, §13.6).
            reset_to_top(&mut summaries, universe);
            // F3: the SITE FACTS are unsound too — a callable un(fully)visited
            // before the cap has no / too-low escape entries (an absent or
            // `false` escape reads below truth). Force every callable's escape
            // site-facts to ⊤ (true) and drop provenance (⇒ materialize).
            for c in universe {
                facts.insert(c.key.clone(), conservative_site_facts(&c.body));
            }
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

    // Confinement stratum (§5) over the converged summaries — a WORKLIST
    // FIXPOINT, not a single unordered pass (blocker 2). `spark_ops` is
    // interprocedural (a caller inherits a callee whose bit is set, §5.3): a
    // single hash-order pass reads a not-yet-computed callee bit (init `false`)
    // and never re-runs, under-reporting transitive `Crossing` as `Confined` and
    // making the result order-dependent. The fixpoint re-enters a callable's
    // callers (the same harvested `DepSet` edges the modes stratum uses) whenever
    // its `spark_ops` widens; monotone (bits only flip false→true) so it
    // converges in O(universe × maxp) visits.
    let mut cqueue: VecDeque<Symbol> = universe.iter().map(|c| c.key.clone()).collect();
    let mut cqueued: HashSet<Symbol> = cqueue.iter().cloned().collect();
    let mut cvisits = 0usize;
    while let Some(key) = cqueue.pop_front() {
        cqueued.remove(&key);
        cvisits += 1;
        if cvisits > cap {
            // Cap exhausted (defensive). Force every `spark_ops` to the
            // conservative ⊤ (all `true` = Crossing/atomic) — the sound failure
            // direction (blocker 4, mirroring the modes stratum).
            for c in universe {
                if let Some(s) = summaries.get_mut(&c.key) {
                    s.spark_ops = vec![true; c.params.len()];
                }
            }
            break;
        }
        let Some(c) = by_key.get(&key) else { continue };

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

        let changed = summaries.get(&c.key).map(|s| s.spark_ops != cr.spark_ops).unwrap_or(true);
        if let Some(s) = summaries.get_mut(&c.key) {
            s.spark_ops = cr.spark_ops;
        }
        if let Some(f) = facts.get_mut(&c.key) {
            f.confined = cr.confined;
        }
        if changed {
            // Re-enter callers: any callable whose harvested DepSet named this
            // key inherits the newly-widened spark_ops (§5.3 transitive).
            let this_fq = FQSymbol { module: current_module.clone(), symbol: key.clone() };
            for (other, dset) in &deps {
                if other != &key && dset.contains(&this_fq) && cqueued.insert(other.clone()) {
                    cqueue.push_back(other.clone());
                }
            }
        }
    }

    // Uniqueness stratum (§14.2, CS-II-1/2, increment II) — the THIRD stratum,
    // stratified after modes + confinement (nothing in them reads uniqueness, so
    // exact). A greatest fixpoint: `result_unique` is a MUST-property, init
    // optimistic-`true`, narrow to `false`. Conservative point = `false`
    // (degrades to the backend's dynamic rc==1 check). Toggle-off never reaches
    // here (the driver returned at entry); the modes/confinement cap-reset above
    // leaves `result_unique = false` on every summary (the `top`/optimistic
    // init), which the stratum re-derives from the conservative bodies.
    run_uniqueness_stratum(env, current_module, universe, &by_key, &deps, &mut summaries, &mut facts, cap);

    ClusterOwnership { summaries, facts, value_used }
}

/// The uniqueness-stratum callee-fact env: converged modes summaries + the
/// WORKING (mid-fixpoint) `result_unique` map + layout eligibility via
/// `value_layout`.
struct UniqClusterEnv<'e, 'a, C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore> {
    env: &'e TypeCheckEnv<'a, C, L>,
    current_module: ModuleFullPath,
    /// Converged modes summaries (param_modes / result / flow / spark_ops).
    summaries: &'e HashMap<Symbol, ModeSummary>,
    /// The mid-fixpoint `result_unique` working map for in-cluster callables.
    working_unique: &'e HashMap<Symbol, bool>,
}

impl<C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore> super::uniqueness::UniqEnv
    for UniqClusterEnv<'_, '_, C, L>
{
    fn terminal_kind(&self, name: &Symbol) -> Option<TerminalKind> {
        if self.summaries.contains_key(name) {
            return Some(TerminalKind::UserFnConcrete);
        }
        let (entry, _home) =
            self.env.resolve_terminal_entry_and_home_scoped(&self.current_module, name.as_ref())?;
        kind_of_entry(&entry)
    }

    fn summary_of(&self, name: &Symbol) -> Option<ModeSummary> {
        if let Some(s) = self.summaries.get(name) {
            return Some(s.clone());
        }
        let (entry, _home) =
            self.env.resolve_terminal_entry_and_home_scoped(&self.current_module, name.as_ref())?;
        entry.mode_summary().cloned()
    }

    fn result_unique_of(&self, name: &Symbol) -> bool {
        // In-cluster callee: read the WORKING map (mid-fixpoint chaining). An
        // import / declared leaf: its persisted summary bit (false by default).
        if let Some(v) = self.working_unique.get(name) {
            return *v;
        }
        self.env
            .resolve_terminal_entry_and_home_scoped(&self.current_module, name.as_ref())
            .and_then(|(entry, _)| entry.mode_summary().map(|s| s.result_unique))
            .unwrap_or(false)
    }

    fn layout_eligible(&self, ty: &ConcreteType) -> bool {
        // Reuse targets a heap object with an overwritable slot. A scalar or a
        // Copy-flattened value (`value_layout` returns `Some`) has no reusable
        // heap slot; a `String`/heap-ADT/`Vec` keeps its heap representation
        // (`value_layout` returns `None`) and IS reuse-eligible (§14.2 clause 3).
        matches!(ty, ConcreteType::String | ConcreteType::ADT(..))
            && cranelisp_types::value_layout(ty, Some(self.env.modules())).is_none()
    }
}

/// Run the uniqueness stratum's greatest-fixpoint (§14.2). Updates each
/// summary's `result_unique` bit and each callable's `unique` site facts.
#[allow(clippy::too_many_arguments)]
fn run_uniqueness_stratum<C, L>(
    env: &TypeCheckEnv<C, L>,
    current_module: &ModuleFullPath,
    universe: &[Callable],
    by_key: &HashMap<&Symbol, &Callable>,
    deps: &HashMap<Symbol, HashSet<FQSymbol>>,
    summaries: &mut HashMap<Symbol, ModeSummary>,
    facts: &mut HashMap<Symbol, SiteFacts>,
    cap: usize,
) where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    // Optimistic init: result_unique = true for every cluster member (greatest
    // fixpoint). Narrow to false; conservative point = false.
    let mut working_unique: HashMap<Symbol, bool> =
        universe.iter().map(|c| (c.key.clone(), true)).collect();

    let mut queue: VecDeque<Symbol> = universe.iter().map(|c| c.key.clone()).collect();
    let mut queued: HashSet<Symbol> = queue.iter().cloned().collect();
    let mut visits = 0usize;
    let mut exhausted = false;
    while let Some(key) = queue.pop_front() {
        queued.remove(&key);
        visits += 1;
        if visits > cap {
            // Cap exhausted: a partially-converged greatest-fixpoint sits ABOVE
            // its true fixpoint (too many `true`s) ⇒ unsound to publish. Reset
            // result_unique to `false` everywhere and drop every `unique_static`
            // site fact to `None` — the write-path analog of the modes ⊤-reset
            // (§14.2 cap-reset; §13.6(h)). The site-fact emission is SKIPPED
            // entirely below (a directly-fresh allocation would otherwise still
            // read `true` from `is_direct_fresh`), so `unique` stays empty.
            for c in universe {
                working_unique.insert(c.key.clone(), false);
            }
            exhausted = true;
            break;
        }
        let Some(c) = by_key.get(&key) else { continue };

        let uenv = UniqClusterEnv {
            env,
            current_module: current_module.clone(),
            summaries,
            working_unique: &working_unique,
        };
        let r = super::uniqueness::analyze_uniqueness(&c.params, &c.body, &uenv);

        // Monotone narrowing: only true→false. Re-enter callers on a change.
        let changed = working_unique.get(&key).copied().unwrap_or(true) != r.result_unique;
        working_unique.insert(key.clone(), r.result_unique);
        if changed {
            let this_fq = FQSymbol { module: current_module.clone(), symbol: key.clone() };
            for (other, dset) in deps {
                if other != &key && dset.contains(&this_fq) && queued.insert(other.clone()) {
                    queue.push_back(other.clone());
                }
            }
        }
    }

    // Commit the converged result_unique bits.
    for (key, u) in &working_unique {
        if let Some(s) = summaries.get_mut(key) {
            s.result_unique = *u;
        }
    }

    // Site facts (§13.6(b)): computed ONCE, post-convergence, with the converged
    // working_unique in hand — UNLESS the fixpoint exhausted its cap, in which
    // case every `unique_static` fact drops to `None` (skip emission entirely).
    if exhausted {
        return;
    }
    for c in universe {
        let uenv = UniqClusterEnv {
            env,
            current_module: current_module.clone(),
            summaries,
            working_unique: &working_unique,
        };
        let r = super::uniqueness::analyze_uniqueness(&c.params, &c.body, &uenv);
        if let Some(f) = facts.get_mut(&c.key) {
            f.unique = r.unique_sites;
        }
    }
}

/// The optimistic ⊥ summary for the fixpoint init: params `Copy`/`Borrowed`,
/// result `Fresh`, flow `Consumed`, spark clear (§3.2).
fn optimistic(params: &[(Symbol, ConcreteType)], copy: &CopyClassifier<'_>) -> ModeSummary {
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

/// The conservative ⊤ summary — the Decision-24 point widened on every axis:
/// params `Owned`, result `Fresh`, flow `Retained`, spark `true` (Crossing).
/// The sound value to publish for an unconverged callable on cap exhaustion
/// (blocker 4); `⊤ ⊒ true-fixpoint ⊒ any partial`.
fn top(params: &[(Symbol, ConcreteType)]) -> ModeSummary {
    let n = params.len();
    ModeSummary {
        param_modes: vec![Mode::Owned; n],
        result: cranelisp_types::ResultMode::Fresh,
        param_flow: vec![cranelisp_types::ParamFlow::Retained; n],
        spark_ops: vec![true; n],
        result_unique: false,
    }
}

/// Reset every callable in the universe to the conservative ⊤ ([`top`]). Called
/// when the modes worklist exhausts its cap: a partially-converged summary set is
/// monotone-below its true fixpoint, so ANY entry may be too precise — the only
/// sound recovery is to jump the whole universe to ⊤.
fn reset_to_top(summaries: &mut HashMap<Symbol, ModeSummary>, universe: &[Callable]) {
    for c in universe {
        summaries.insert(c.key.clone(), top(&c.params));
    }
}

/// The conservative ⊤ [`SiteFacts`] for a body: every escape-bearing node's span
/// marked `escapes=true`, provenance empty (⇒ Decision-24 materialize). The sound
/// facts to publish on cap exhaustion (F3): a partial transfer walk can leave a
/// node `escapes=false` (or absent) below its true `true`, which the backend
/// would trust to elide a retain ⇒ UAF. `true` everywhere is the safe ⊤. The
/// confined axis is left absent (⊤ = Crossing/atomic through the accessor).
fn conservative_site_facts(body: &MonoExpr) -> SiteFacts {
    let mut f = SiteFacts::default();
    collect_escape_spans(body, &mut f);
    f
}

/// Mark every escape-bearing node's span `escapes=true` (mirrors the node set
/// the transfer walk and `sites::annotate` touch), recursing into all children.
fn collect_escape_spans(expr: &MonoExpr, f: &mut SiteFacts) {
    match expr {
        MonoExpr::StringLit { span, .. } => {
            f.escapes.insert(*span, true);
        }
        MonoExpr::Lambda { span, body, .. } => {
            f.escapes.insert(*span, true);
            collect_escape_spans(body, f);
        }
        MonoExpr::Apply { span, callee, args, .. } => {
            f.escapes.insert(*span, true);
            collect_escape_spans(callee, f);
            for a in args {
                collect_escape_spans(a, f);
            }
        }
        MonoExpr::VecLit { span, elements, .. } => {
            f.escapes.insert(*span, true);
            for e in elements {
                collect_escape_spans(e, f);
            }
        }
        MonoExpr::ConstrADT { span, fields, .. } => {
            f.escapes.insert(*span, true);
            for x in fields {
                collect_escape_spans(x, f);
            }
        }
        MonoExpr::Let { bindings, body, .. } | MonoExpr::ParBind { bindings, body, .. } => {
            for (_, rhs) in bindings {
                collect_escape_spans(rhs, f);
            }
            collect_escape_spans(body, f);
        }
        MonoExpr::If { cond, then_branch, else_branch, .. } => {
            collect_escape_spans(cond, f);
            collect_escape_spans(then_branch, f);
            collect_escape_spans(else_branch, f);
        }
        MonoExpr::Match { scrutinee, arms, .. } => {
            collect_escape_spans(scrutinee, f);
            for arm in arms {
                collect_escape_spans(&arm.body, f);
            }
        }
        MonoExpr::Trace { body, .. } => collect_escape_spans(body, f),
        MonoExpr::LaunchContinue { launched, continuation, .. } => {
            collect_escape_spans(launched, f);
            collect_escape_spans(continuation, f);
        }
        MonoExpr::IntLit { .. }
        | MonoExpr::FloatLit { .. }
        | MonoExpr::BoolLit { .. }
        | MonoExpr::Var { .. } => {}
    }
}

#[cfg(test)]
mod tests;
