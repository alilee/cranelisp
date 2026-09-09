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
    Binding, CallableOrigin, ConcreteType, FQSymbol, Life, Mode, ModeSummary, ModuleFullPath,
    MonoExpr, Symbol, Type,
};

use crate::checker::{CheckState, TypeCheckEnv};

use super::classify::{CopyClassifier, TerminalKind};
use super::confinement::confine;
use super::transfer::{SiteFacts, TransferEnv, transfer};

/// One codegen-bound callable in the cluster universe.
struct Callable {
    key: Symbol,
    params: Vec<(Symbol, ConcreteType)>,
    residual_params: bool,
    body: MonoExpr,
}

/// The pass output for one cluster — consumed by [`super::publish`].
///
/// Its default is the REFUSAL-shaped value: nothing analysed, nothing to
/// publish. Every non-empty field here is the output of a transfer walk (§19.5)
/// — no seeded or literal summary can reach it.
#[derive(Default)]
pub(crate) struct ClusterOwnership {
    /// Converged summary per callable key.
    pub summaries: HashMap<Symbol, ModeSummary>,
    /// Site facts per callable key (escape + provenance + confined) — consumed
    /// by the CS-4 site-fact annotation walk + H5 trace.
    pub facts: HashMap<Symbol, SiteFacts>,
    /// Callable names referenced in value position anywhere in the cluster (§8.3).
    pub value_used: HashSet<Symbol>,
    /// Frames refused per-parameter seeding because their scheme still carried a
    /// residual parameter type (§18.2 O-1). Such a frame is never walked, so it
    /// publishes nothing (§19.6); this keyed set records which frames took that
    /// path, for the trace.
    pub residual_param_frames: HashSet<Symbol>,
    /// Set when a stratum exhausted the shared visit cap: the whole cluster is
    /// refused and publishes nothing (§19.5). Carried as a VALUE so both
    /// detection legs are assertable at the seam without capturing stderr.
    pub refusal: Option<Refusal>,
}

/// Which stratum exhausted the cap. Named rather than a bool so the trace line
/// says which analysis ran out, and so adding a stratum has to answer the
/// question.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Stratum {
    Modes,
    Confinement,
    Uniqueness,
}

impl std::fmt::Display for Stratum {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Stratum::Modes => "modes",
            Stratum::Confinement => "confinement",
            Stratum::Uniqueness => "uniqueness",
        })
    }
}

/// A cluster whose analysis did not converge (§19.5). The whole universe is
/// refused: no summary, no site fact, no value-use mark. That lands it on the
/// `CRANELISP_NO_OWNERSHIP` shape, whose end-to-end safety the differential
/// oracle already measures — rather than on a ⊤ literal, which is the
/// construction that decayed (root `CLAUDE.md` §Assurance, R11 and I-CT).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Refusal {
    pub stratum: Stratum,
    /// Visits consumed before the refusal — equal to `cap`, and recorded so the
    /// trace distinguishes "burned on an oscillation" from "cluster too large".
    pub visits: usize,
    pub cap: usize,
    pub universe: usize,
}

/// The real callee-fact environment: working in-cluster summaries first, then
/// chain-follow through the symbol table for imports / declared leaves.
struct ClusterEnv<'e, 'a, C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore> {
    env: &'e TypeCheckEnv<'a, C, L>,
    current_module: ModuleFullPath,
    working: &'e HashMap<Symbol, ModeSummary>,
    /// Every callable in this cluster's universe. A member with no `working`
    /// entry has no summary THIS compile (§19.6: a residual-parameter frame is
    /// never walked), and must read as ABSENT rather than fall through to the
    /// summary a PREVIOUS compile persisted on its entry.
    members: &'e HashSet<Symbol>,
}

impl<C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore> TransferEnv
    for ClusterEnv<'_, '_, C, L>
{
    fn terminal_kind(&self, name: &Symbol) -> Option<TerminalKind> {
        if self.members.contains(name) {
            return Some(TerminalKind::UserFnConcrete);
        }
        let (entry, _home) = self
            .env
            .resolve_terminal_entry_and_home_scoped(&self.current_module, name.as_ref())?;
        kind_of_entry(&entry)
    }

    fn summary_of(&self, name: &Symbol) -> Option<(FQSymbol, ModeSummary)> {
        if let Some(s) = self.working.get(name) {
            return Some((
                FQSymbol {
                    module: self.current_module.clone(),
                    symbol: name.clone(),
                },
                s.clone(),
            ));
        }
        if self.members.contains(name) {
            return None;
        }
        let (entry, home) = self
            .env
            .resolve_terminal_entry_and_home_scoped(&self.current_module, name.as_ref())?;
        entry.mode_summary().map(|s| {
            (
                FQSymbol {
                    module: home,
                    symbol: name.clone(),
                },
                s.clone(),
            )
        })
    }
}

/// Classify a chain-follow terminal entry into a [`TerminalKind`] (§2.1).
fn kind_of_entry<C: cranelisp_types::CodeStore>(entry: &Binding<C>) -> Option<TerminalKind> {
    let callable = entry.callable()?;
    match (&callable.origin, &callable.arm.life) {
        (CallableOrigin::Plain | CallableOrigin::TraitMethod { .. }, Life::Concrete { .. }) => {
            Some(TerminalKind::UserFnConcrete)
        }
        (
            CallableOrigin::RustPrimitive,
            Life::Concrete { .. } | Life::Inline { .. } | Life::HostPromised,
        ) => Some(TerminalKind::DeclaredLeaf),
        (CallableOrigin::Ctor { .. } | CallableOrigin::PlatformEffect { .. }, _) => {
            Some(TerminalKind::PinnedBoundary)
        }
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
/// nodes), so re-checking strict TYPE-concreteness on the entry's `ast`
/// reproduces the pre-flip set exactly — ctors (Constructor kind, `ConstrADT`
/// un-typed body), accessors (`(match self …)` un-typed body), and
/// lenient-fallback concrete defns all excluded, mono instances and genuine
/// concrete defns retained.
///
/// The membership probe is the single-sourced
/// [`cranelisp_types::is_strict_type_concrete`] — the pure TYPE half of the
/// `from_expr` gate, exported beside it (FIXME 0689). The S114 flip couples
/// type + resolution inside `from_expr` (a real-span reference with no
/// `var_refs`/`apply_refs` verdict fails `Unresolved` BEFORE its type is
/// examined), so calling `from_expr` with empty maps cannot answer the pure
/// type question; the exported predicate answers exactly it, and lives in
/// `mono_expr.rs` so this membership question cannot drift from `from_expr`'s
/// node handling (the pre-0689 local mirror was unfenced).
fn collect_universe<C, L>(env: &TypeCheckEnv<C, L>, state: &CheckState) -> Vec<Callable>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    let read = env.current_symbol_table(state);
    let view = read.view();
    let mut out = Vec::new();
    for (key, entry) in view.iter() {
        let Some(cv) = entry.codegen_view() else {
            continue;
        };
        let Some(callable) = entry.callable() else {
            continue;
        };
        let Life::Concrete {
            ast: Some(ast_variant),
            ..
        } = &callable.arm.life
        else {
            continue;
        };
        // Pre-flip universe pin: only a STRICT-TYPE-concrete body participates
        // (see the fn rustdoc above; the probe is the types-side single source).
        if !cranelisp_types::is_strict_type_concrete(&ast_variant.body) {
            continue;
        }
        let (params, residual_params) = param_types(&cv.params, Some(&callable.arm.scheme.ty));
        out.push(Callable {
            key: key.clone(),
            params,
            residual_params,
            body: cv.body.clone(),
        });
    }
    out
}

/// Derive `(name, ConcreteType)` per formal from the callable scheme's `Fn`
/// param list. Any non-`Fn` scheme, arity mismatch, or non-concrete param type
/// falls back to a non-scalar placeholder (`String`) — never mis-classified as
/// `Copy` (sound: a non-`Copy` param seeds `Borrowed`).
fn param_types(names: &[Symbol], scheme_ty: Option<&Type>) -> (Vec<(Symbol, ConcreteType)>, bool) {
    let Some(Type::Fn(ps, _)) = scheme_ty else {
        return (
            names
                .iter()
                .cloned()
                .map(|name| (name, ConcreteType::String))
                .collect(),
            true,
        );
    };
    if ps.len() != names.len() {
        return (
            names
                .iter()
                .cloned()
                .map(|name| (name, ConcreteType::String))
                .collect(),
            true,
        );
    }
    let concretes = ps
        .iter()
        .map(ConcreteType::from_type)
        .collect::<Result<Vec<_>, _>>();
    match concretes {
        Ok(concretes) => (names.iter().cloned().zip(concretes).collect(), false),
        Err(_) => (
            names
                .iter()
                .cloned()
                .map(|name| (name, ConcreteType::String))
                .collect(),
            true,
        ),
    }
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

fn checked_value_layout<C, L>(
    env: &TypeCheckEnv<C, L>,
    ty: &ConcreteType,
) -> Option<cranelisp_types::ValueLayout>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    cranelisp_types::value_layout_with_lookup(ty, &|module, key| {
        env.probe_module_entry_owned(module, key.as_ref())
    })
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
    // Copy and backend flattening must share the layout rule: a bit-copy of
    // an unflattened heap object omits its required reference-count increment.
    let copy = CopyClassifier::new(|ty| checked_value_layout(env, ty).is_some());

    // Every universe key, walkable or not: what `ClusterEnv` reads as in-cluster.
    let members: HashSet<Symbol> = universe.iter().map(|c| c.key.clone()).collect();
    let residual_param_frames: HashSet<Symbol> = universe
        .iter()
        .filter(|callable| callable.residual_params)
        .map(|callable| callable.key.clone())
        .collect();
    // §19.6 — a residual-parameter frame refuses per-parameter seeding (§18.2
    // O-1) and is never walked, so it is not seeded, not queued, and publishes
    // nothing. Its callers read it as absent, which is the Decision-24 lowering
    // it actually gets.
    let walkable: Vec<&Callable> = universe.iter().filter(|c| !c.residual_params).collect();
    let refused = |stratum: Stratum, visits: usize| ClusterOwnership {
        residual_param_frames: residual_param_frames.clone(),
        refusal: Some(Refusal {
            stratum,
            visits,
            cap,
            universe: universe.len(),
        }),
        ..ClusterOwnership::default()
    };

    // Optimistic init: every param Borrowed/Copy, Fresh, Consumed, spark clear.
    // This seed is the WORKING environment the walk reads — a guess, and the
    // pass's only `ModeSummary` construction besides a walk's own output.
    let mut working: HashMap<Symbol, ModeSummary> = walkable
        .iter()
        .map(|c| (c.key.clone(), optimistic(&c.params, &copy)))
        .collect();
    // The PUBLISHABLE map (§19.5). Its one write site is a completed transfer
    // walk's output below, so a seeded guess cannot reach a consumer even if a
    // walkable member were queued and never walked — that member is simply
    // absent, which is the conservative point. The seed map is dropped before
    // publication, so the two are never interchangeable at the seam.
    let mut walked: HashMap<Symbol, ModeSummary> = HashMap::new();

    let mut facts: HashMap<Symbol, SiteFacts> = HashMap::new();
    let mut deps: HashMap<Symbol, HashSet<FQSymbol>> = HashMap::new();
    let mut value_used: HashSet<Symbol> = HashSet::new();

    // Worklist — BFS, dedup via an in-queue set.
    let mut queue: VecDeque<Symbol> = walkable.iter().map(|c| c.key.clone()).collect();
    let mut queued: HashSet<Symbol> = queue.iter().cloned().collect();
    let by_key: HashMap<&Symbol, &Callable> = walkable.iter().map(|c| (&c.key, *c)).collect();

    let mut visits = 0usize;
    while let Some(key) = queue.pop_front() {
        queued.remove(&key);
        visits += 1;
        if visits > cap {
            // Cap exhausted: the analysis did not converge, so there is no walk
            // output to publish and no literal is allowed to stand in for one.
            // REFUSE the whole cluster (§19.5) — it then compiles on exactly the
            // `CRANELISP_NO_OWNERSHIP` shape.
            return refused(Stratum::Modes, visits - 1);
        }
        let Some(c) = by_key.get(&key) else { continue };

        let cluster_env = ClusterEnv {
            env,
            current_module: current_module.clone(),
            working: &working,
            members: &members,
        };
        let r = transfer(&c.params, &c.body, &cluster_env, &copy);

        deps.insert(key.clone(), r.deps.clone());
        facts.insert(key.clone(), r.facts);
        value_used.extend(r.value_uses);

        let changed = working.get(&key) != Some(&r.summary);
        #[cfg(test)]
        visit_log::record(&key, &r.summary);
        working.insert(key.clone(), r.summary.clone());
        walked.insert(key.clone(), r.summary);
        if changed {
            // Re-enter intra-cluster callers: any callable whose harvested
            // DepSet named this key (§13.3 self-describing re-entry), including
            // itself: its site facts were computed against its prior summary.
            let this_fq = FQSymbol {
                module: current_module.clone(),
                symbol: key.clone(),
            };
            for (other, dset) in &deps {
                if dset.contains(&this_fq) && queued.insert(other.clone()) {
                    queue.push_back(other.clone());
                }
            }
        }
    }

    // The seed has served its purpose: every later stratum reads and refines
    // walk outputs only, and nothing downstream can reach a guess.
    drop(working);
    let mut summaries = walked;

    // Confinement stratum (§5) over the converged summaries — a WORKLIST
    // FIXPOINT, not a single unordered pass (blocker 2). `spark_ops` is
    // interprocedural (a caller inherits a callee whose bit is set, §5.3): a
    // single hash-order pass reads a not-yet-computed callee bit (init `false`)
    // and never re-runs, under-reporting transitive `Crossing` as `Confined` and
    // making the result order-dependent. The fixpoint re-enters a callable's
    // callers (the same harvested `DepSet` edges the modes stratum uses) whenever
    // its `spark_ops` widens; monotone (bits only flip false→true) so it
    // converges in O(universe × maxp) visits.
    let mut cqueue: VecDeque<Symbol> = walkable.iter().map(|c| c.key.clone()).collect();
    let mut cqueued: HashSet<Symbol> = cqueue.iter().cloned().collect();
    let mut cvisits = 0usize;
    while let Some(key) = cqueue.pop_front() {
        cqueued.remove(&key);
        cvisits += 1;
        if cvisits > cap {
            // Cap exhausted: ONE refusal serves all three strata (§19.5). The
            // per-stratum recovery this replaces forced `spark_ops` to ⊤ while
            // leaving each site's already-written `confined` fact at whatever
            // partial value the interrupted pass had reached — an asymmetry the
            // single refusal removes without an argument about which partial
            // facts are salvageable.
            return refused(Stratum::Confinement, cvisits - 1);
        }
        let Some(c) = by_key.get(&key) else { continue };

        let param_modes: Vec<(Symbol, Mode)> = c
            .params
            .iter()
            .enumerate()
            .map(|(i, (n, _))| {
                (
                    n.clone(),
                    summaries
                        .get(&c.key)
                        .map(|s| s.param_mode(i))
                        .unwrap_or(Mode::Owned),
                )
            })
            .collect();
        let cluster_env = ClusterEnv {
            env,
            current_module: current_module.clone(),
            working: &summaries,
            members: &members,
        };
        let cr = confine(&param_modes, &c.body, &cluster_env);

        let changed = summaries
            .get(&c.key)
            .map(|s| s.spark_ops != cr.spark_ops)
            .unwrap_or(true);
        if let Some(s) = summaries.get_mut(&c.key) {
            s.spark_ops = cr.spark_ops;
        }
        if let Some(f) = facts.get_mut(&c.key) {
            f.confined = cr.confined;
        }
        if changed {
            // Re-enter callers: any callable whose harvested DepSet named this
            // key inherits the newly-widened spark_ops (§5.3 transitive).
            let this_fq = FQSymbol {
                module: current_module.clone(),
                symbol: key.clone(),
            };
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
    // here (the driver returned at entry); an earlier stratum exhausting the cap
    // refused the cluster outright, so this stratum only ever runs over converged
    // modes and confinement.
    if let Some(visits) = run_uniqueness_stratum(
        env,
        current_module,
        &walkable,
        &members,
        &by_key,
        &deps,
        &mut summaries,
        &mut facts,
        cap,
    ) {
        return refused(Stratum::Uniqueness, visits);
    }

    ClusterOwnership {
        summaries,
        facts,
        value_used,
        residual_param_frames,
        refusal: None,
    }
}

/// The uniqueness-stratum callee-fact env: converged modes summaries + the
/// WORKING (mid-fixpoint) `result_unique` map + layout eligibility via
/// `value_layout`.
struct UniqClusterEnv<'e, 'a, C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore> {
    env: &'e TypeCheckEnv<'a, C, L>,
    current_module: ModuleFullPath,
    /// Converged modes summaries (param_modes / result / flow / spark_ops).
    summaries: &'e HashMap<Symbol, ModeSummary>,
    /// Every callable in this cluster's universe — see [`ClusterEnv::members`].
    members: &'e HashSet<Symbol>,
    /// The mid-fixpoint `result_unique` working map for in-cluster callables.
    working_unique: &'e HashMap<Symbol, bool>,
}

impl<C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore> super::uniqueness::UniqEnv
    for UniqClusterEnv<'_, '_, C, L>
{
    fn terminal_kind(&self, name: &Symbol) -> Option<TerminalKind> {
        if self.members.contains(name) {
            return Some(TerminalKind::UserFnConcrete);
        }
        let (entry, _home) = self
            .env
            .resolve_terminal_entry_and_home_scoped(&self.current_module, name.as_ref())?;
        kind_of_entry(&entry)
    }

    fn summary_of(&self, name: &Symbol) -> Option<ModeSummary> {
        if let Some(s) = self.summaries.get(name) {
            return Some(s.clone());
        }
        if self.members.contains(name) {
            return None;
        }
        let (entry, _home) = self
            .env
            .resolve_terminal_entry_and_home_scoped(&self.current_module, name.as_ref())?;
        entry.mode_summary().cloned()
    }

    fn result_unique_of(&self, name: &Symbol) -> bool {
        // In-cluster callee: read the WORKING map (mid-fixpoint chaining). An
        // import / declared leaf: its persisted summary bit (false by default).
        if let Some(v) = self.working_unique.get(name) {
            return *v;
        }
        if self.members.contains(name) {
            // A cluster member with no working bit is a frame this compile never
            // walked (§19.6) — the conservative point, not a stale persisted one.
            return false;
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
            && checked_value_layout(self.env, ty).is_none()
    }
}

/// Run the uniqueness stratum's greatest-fixpoint (§14.2). Updates each
/// summary's `result_unique` bit and each callable's `unique` site facts.
///
/// Returns `Some(visits consumed)` when the stratum exhausted the cap — the
/// caller then refuses the whole cluster (§19.5, one refusal for all three
/// strata), rather than this stratum recovering on its own conservative point.
#[allow(clippy::too_many_arguments)]
#[must_use]
fn run_uniqueness_stratum<C, L>(
    env: &TypeCheckEnv<C, L>,
    current_module: &ModuleFullPath,
    universe: &[&Callable],
    members: &HashSet<Symbol>,
    by_key: &HashMap<&Symbol, &Callable>,
    deps: &HashMap<Symbol, HashSet<FQSymbol>>,
    summaries: &mut HashMap<Symbol, ModeSummary>,
    facts: &mut HashMap<Symbol, SiteFacts>,
    cap: usize,
) -> Option<usize>
where
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
    while let Some(key) = queue.pop_front() {
        queued.remove(&key);
        visits += 1;
        if visits > cap {
            // Cap exhausted: a partially-converged greatest-fixpoint sits ABOVE
            // its true fixpoint (too many `true`s) ⇒ unsound to publish, and no
            // literal may stand in for the walk that did not finish. Refuse the
            // cluster (§19.5).
            return Some(visits - 1);
        }
        let Some(c) = by_key.get(&key) else { continue };

        let uenv = UniqClusterEnv {
            env,
            current_module: current_module.clone(),
            summaries,
            members,
            working_unique: &working_unique,
        };
        let r = super::uniqueness::analyze_uniqueness(&c.params, &c.body, &uenv);

        // Monotone narrowing: only true→false. Re-enter callers on a change.
        let changed = working_unique.get(&key).copied().unwrap_or(true) != r.result_unique;
        working_unique.insert(key.clone(), r.result_unique);
        if changed {
            let this_fq = FQSymbol {
                module: current_module.clone(),
                symbol: key.clone(),
            };
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
    // working_unique in hand. A cap exhaustion returned above, refusing the
    // cluster, so there is no partial-emission case left to guard.
    for c in universe {
        let uenv = UniqClusterEnv {
            env,
            current_module: current_module.clone(),
            summaries,
            members,
            working_unique: &working_unique,
        };
        let r = super::uniqueness::analyze_uniqueness(&c.params, &c.body, &uenv);
        if let Some(f) = facts.get_mut(&c.key) {
            f.unique = r.unique_sites;
        }
    }
    None
}

/// The optimistic ⊥ summary for the fixpoint init: params `Copy`/`Borrowed`,
/// result `Fresh`, flow `Consumed`, spark clear (§3.2).
fn optimistic(params: &[(Symbol, ConcreteType)], copy: &CopyClassifier<'_>) -> ModeSummary {
    let n = params.len();
    ModeSummary {
        param_modes: params
            .iter()
            .map(|(_, ty)| {
                if copy.is_copy(ty) {
                    Mode::Copy
                } else {
                    Mode::Borrowed
                }
            })
            .collect(),
        result: cranelisp_types::ResultMode::Fresh,
        param_flow: vec![cranelisp_types::ParamFlow::Consumed; n],
        spark_ops: vec![false; n],
        result_unique: false,
    }
}

#[cfg(test)]
mod tests;

/// Test-only observation of the modes worklist's per-visit sequence.
///
/// The worklist hands back only its *final* state — a converged summary map, or
/// a refusal (§19.5) recording that the cap was exhausted but not what burned
/// it. The recorded sequence shows whether the visits went on an oscillation and
/// how many each callable consumed, which is the observation the S121
/// cap-exhaustion hypothesis is refutable by. Compiled only under `cfg(test)`; production builds contain
/// neither the buffer nor the call site.
#[cfg(test)]
pub(super) mod visit_log {
    use super::{ModeSummary, Symbol};
    use std::cell::RefCell;

    thread_local! {
        static LOG: RefCell<Option<Vec<(Symbol, ModeSummary)>>> = const { RefCell::new(None) };
    }

    /// Append one completed modes visit. A no-op unless [`capture`] armed the
    /// buffer on this thread.
    pub(super) fn record(key: &Symbol, summary: &ModeSummary) {
        LOG.with(|l| {
            if let Some(log) = l.borrow_mut().as_mut() {
                log.push((key.clone(), summary.clone()));
            }
        });
    }

    /// Run `f` with the visit log armed, returning its value and the ordered
    /// `(callable, published summary)` sequence the modes worklist produced.
    pub(crate) fn capture<R>(f: impl FnOnce() -> R) -> (R, Vec<(Symbol, ModeSummary)>) {
        LOG.with(|l| *l.borrow_mut() = Some(Vec::new()));
        let value = f();
        let log = LOG.with(|l| l.borrow_mut().take()).unwrap_or_default();
        (value, log)
    }
}
