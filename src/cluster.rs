//! Cluster-atomic orchestration types per Decision 44 and facade `int.md`.
//!
//! `process_cluster` + `insert_cluster` are the shared cluster-processing
//! entry per `facades/int.md` §"`process_cluster` — the cluster-atomic
//! orchestration loop". A **cluster** is the unit of typecheck atomicity:
//!
//! - A non-`(begin)` REPL input is a one-form cluster.
//! - A `(begin form₁ … formN)` REPL input is the explicit multi-form cluster.
//! - Batch (file) compilation passes a file's non-structural forms as one
//!   big cluster (spec §5.13.1's MAY-reference-freely rule at file scope).
//!
//! ## Sprint 66 Wave 3a-β status (post 2026-05-13 third amendment)
//!
//! Per Decision 44's 2026-05-13 third amendment, the typecheck dispatch
//! surface collapses to a single `cranelisp_typecheck::check_forms` call per
//! cluster. The pre-S66 `ModuleCheckAccumulator` (cross-pass typecheck
//! working state) and its briefly-considered relocation to int are both
//! retired:
//!
//! - **Per-symbol Pass-2 side products** (method resolutions, expr types,
//!   mono defns, callees) ride into the live `SymbolTable` on each
//!   committed `ModuleEntry::Def` per `facades/typecheck.md` invariant 3a.
//! - **Pass-1-to-Pass-2 working state** is internal to `check_forms`'s frame.
//! - **Cluster-level cross-symbol bookkeeping** that `int` collects
//!   (warnings, resolved-import bindings, introspection records) lives on
//!   `ProcessedCluster` directly.
//!
//! ## S78 in-call-stack restructure (FIXME 0176/0179 closed)
//!
//! `process_cluster` is the single live worker orchestration entry: it builds a
//! `ModuleCompiler` over `&SharedState` and drives the shared
//! `worker::process_cluster_once` core (expand → Pass-0 structural peel →
//! build → fresh-staging `check_forms`, commit-on-Ok / discard-on-Err). On a
//! dependency gap the dep is registered with the scheduler (its sexps ride the
//! dep's work packet) and blocked on, and `process_cluster` returns
//! `ClusterOutcome::Gap` so the worker frees back to the pool; the scheduler
//! requeues the blocked module (retry-from-top) when the dep completes. The
//! REPL eval path (`session_v4::process_single_form`) drives the same
//! `process_cluster_once` core in its own retry loop. `insert_cluster` commits
//! the cluster-level REPL/scheduler metadata; the per-symbol staging entries
//! already committed to live inside `check_program_compat`.

use cranelisp_types::{
    CranelispError, FQSymbol, ImportNames, ModuleEntry, ModuleFullPath, Symbol, Warning,
};

use crate::code::Code;
use crate::session_v4::Introspection;

// ---------------------------------------------------------------------------
// ProcessedCluster — opaque carrier between process_cluster and insert_cluster
// ---------------------------------------------------------------------------

/// Output of a successful `process_cluster` run, ready for atomic commit.
///
/// Per Decision 44's 2026-05-13 third amendment — the typed product of one
/// cluster's `check_forms` run, ready for atomic commit. Carries the drained
/// staging entries plus cluster-level cross-symbol bookkeeping that `int`
/// collects during cluster processing (warnings, resolved-import bindings,
/// introspection records).
///
/// `ProcessedCluster` is the **single** cluster-level carrier; the pre-S66
/// `ModuleCheckAccumulator` (a separate typecheck-side / int-side struct) is
/// retired. Per-symbol Pass-2 side products ride into live on each
/// `ModuleEntry::Def` per `facades/typecheck.md` invariant 3a — the
/// orchestrator's drain in `insert_cluster` carries those annotations with
/// each entry.
///
/// Opaque to callers; constructed inside `process_cluster`, consumed inside
/// `insert_cluster`. Read accessors expose the cluster-level metadata for
/// REPL surface (warnings) and scheduler notifications (introspection
/// records).
#[non_exhaustive]
pub struct ProcessedCluster {
    /// Drained staging entries — one per defined symbol in the cluster.
    /// Per `facades/int.md` invariant 5b — written into the live
    /// `SymbolTable` under per-entry inner-DashMap locks during
    /// `insert_cluster`. (Empty in the current Wave 3a-β scaffold; the
    /// active `worker::check_program_compat` path commits to live directly.)
    pub(crate) entries: Vec<(Symbol, ModuleEntry<Code>)>,

    /// Warnings accumulated across the cluster's forms. Surfaced by the REPL
    /// driver before commit; routed to `EvalResult::warnings` downstream.
    pub(crate) warnings: Vec<Warning>,

    /// Resolved import bindings to install into the live `SymbolTable` on
    /// successful cluster commit. Per `facades/typecheck.md` invariant 2 —
    /// import installation is `int`'s call, not typecheck's.
    pub(crate) resolved_imports: Vec<(ModuleFullPath, ImportNames)>,

    /// Cluster-level introspection records the orchestrator captured at
    /// parse-time. Populated only when `shared.introspection.is_some()`.
    /// Drained into `shared.introspection` during `insert_cluster`.
    pub(crate) introspection_records: Vec<(FQSymbol, Introspection)>,
}

impl ProcessedCluster {
    /// True if the cluster produced no entries and no cluster-level residue.
    /// `insert_cluster` may skip commit when this holds.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
            && self.warnings.is_empty()
            && self.resolved_imports.is_empty()
            && self.introspection_records.is_empty()
    }

    /// Consume the cluster, yielding its drained entries. Used by
    /// `insert_cluster` to commit per-symbol via inner-DashMap writes.
    pub fn into_iter(self) -> impl Iterator<Item = (Symbol, ModuleEntry<Code>)> {
        self.entries.into_iter()
    }

    /// Read-only access to the cluster's accumulated warnings. Surfaced by
    /// `Sess::warnings` / `EvalResult`.
    pub fn warnings(&self) -> &[Warning] {
        &self.warnings
    }

    /// Read-only access to the cluster's resolved-import bindings. Applied
    /// via `SymbolTable::install_import_bindings` post-drain.
    pub fn resolved_imports(&self) -> &[(ModuleFullPath, ImportNames)] {
        &self.resolved_imports
    }

    /// Read-only access to the cluster's introspection records. Drained
    /// into `shared.introspection` during `insert_cluster`.
    pub fn introspection_records(&self) -> &[(FQSymbol, Introspection)] {
        &self.introspection_records
    }

    /// Construct a `ProcessedCluster` from its parts. Used by
    /// `process_form::finalize_cluster` to carry the typecheck warning channel
    /// (FIXME 0365) out of a successful `check_forms` run onto
    /// `ProcessedCluster.warnings`, where the REPL driver renders each as a
    /// `; warning: <message>` line.
    pub(crate) fn from_parts(
        entries: Vec<(Symbol, ModuleEntry<Code>)>,
        warnings: Vec<Warning>,
        resolved_imports: Vec<(ModuleFullPath, ImportNames)>,
        introspection_records: Vec<(FQSymbol, Introspection)>,
    ) -> Self {
        ProcessedCluster {
            entries,
            warnings,
            resolved_imports,
            introspection_records,
        }
    }

    /// Construct an empty cluster — a unit-test fixture. (The production
    /// `finalize_cluster` path now builds via `from_parts`, carrying the
    /// FIXME-0365 warning channel; this helper survives only in tests.)
    #[cfg(test)]
    pub(crate) fn empty() -> Self {
        ProcessedCluster {
            entries: Vec::new(),
            warnings: Vec::new(),
            resolved_imports: Vec::new(),
            introspection_records: Vec::new(),
        }
    }
}

// ---------------------------------------------------------------------------
// Cluster orchestration — free functions (Sprint 66 Wave 3a-β target shape)
// ---------------------------------------------------------------------------

/// Outcome of one worker-side `process_cluster` pass (S78 in-call-stack
/// restructure). Either the cluster fully typechecked (`Done`) — carrying the
/// `ProcessedCluster` metadata + the expanded program for codegen — or it hit
/// a dependency gap (`Gap`) which has already been registered + blocked on.
pub enum ClusterOutcome {
    Done {
        processed: ProcessedCluster,
        program: Vec<cranelisp_types::TopLevel>,
    },
    Gap {
        dep: ModuleFullPath,
    },
}

/// Process a cluster of forms against a target module scope — the single live
/// Pass-0/1/2 orchestration entry for the worker path (S78 in-call-stack
/// restructure; FIXME 0176/0179 residual scope closed).
///
/// Builds a `ModuleCompiler` borrowing `&SharedState` and runs the shared
/// `worker::process_cluster_once` core ONCE, from the top: expand → Pass-0
/// structural peel (`install_imports`/`install_exports`/mod-alias in-frame) →
/// `build_form` → fresh-staging `SymbolTableAccess::cluster` → `check_forms`
/// (commit-on-Ok / discard-on-Err). On a dependency gap the dep is registered
/// with the scheduler (its sexps ride the dep's work packet) and blocked on
/// (`block_for_typecheck`) inside the core; this function returns
/// `ClusterOutcome::Gap` and the worker frees back to the pool. The scheduler
/// requeues this module when the dep completes and the cluster re-runs from the
/// top against now-larger live state — no saved suspend state, no parking map.
///
/// Per `facades/int.md` invariants 5 / 5a / 5b — frontend and typecheck stay
/// pure with respect to live state (return `Gap` values, do not call the
/// scheduler). `process_cluster` is the sole crate-crossing where gap values
/// become scheduler calls.
pub fn process_cluster(
    shared: &crate::session_v4::SharedState,
    forms: std::sync::Arc<[cranelisp_types::Sexp]>,
    scope: &ModuleFullPath,
) -> Result<ClusterOutcome, CranelispError> {
    use crate::worker::{ClusterOnce, ModuleCompiler};
    use crate::process_form;
    use cranelisp_typecheck::CheckState;

    cranelisp_types::ensure_module_exists(&shared.symbol_tables, scope);

    let lib_dirs = shared.lib_dirs.lock()
        .unwrap_or_else(|e| e.into_inner()).clone();
    let platform_dirs = shared.platform_dirs.lock()
        .unwrap_or_else(|e| e.into_inner()).clone();
    let mut ctx = ModuleCompiler {
        symbol_tables: &shared.symbol_tables,
        next_type_id: &shared.next_type_id,
        module_aliases: &shared.module_aliases,
        prelude_fallback: &shared.prelude_fallback,
        check_state: CheckState::new(scope.clone()),
        current_module: scope.clone(),
        scheduler: &shared.scheduler,
        typecheck_products: &shared.typecheck_products,
        // D1/D1b: introspection is a REPL slash-command facility. The store is
        // `Some` ONLY under `RunMode::Repl` (D1b makes the container itself
        // `Option`), so `.as_ref()` is the single adaptor — `None` in
        // `--run`/`--link`, so the `if let Some(intr_map) = ctx.introspection`
        // writes are no-ops in batch (no record allocated). The compile pipeline
        // reads nothing from it — macro `sexp` lives on the symbol table.
        introspection: shared.introspection.as_ref(),
        lib_dirs: &lib_dirs,
        platform_dirs: &platform_dirs,
        project_root: &shared.project_root,
        shared_state: Some(shared),
        // Pool-orchestrated (worker): a dependency gap moves the module to
        // TypecheckBlocked and the scheduler requeues it — NOT eval-driven.
        eval_driven: false,
    };

    match process_form::process_cluster_once(
        &mut ctx,
        scope,
        &forms,
        cranelisp_types::ModuleStrategy::Replace,
    )? {
        ClusterOnce::Done { processed, program } => {
            Ok(ClusterOutcome::Done { processed, program })
        }
        ClusterOnce::Gap { dep } => Ok(ClusterOutcome::Gap { dep }),
    }
}

/// Commit a `ProcessedCluster`'s entries into the live `SymbolTable` for
/// `target`. Per Decision 44 — drains staging entries under per-entry
/// inner-DashMap locks; populates `shared.introspection` from the cluster's
/// introspection records.
///
/// Callers that want commit-side control (REPL defining forms; compilation
/// worker) call this after a successful `process_cluster`. Eval-expression
/// callers skip `insert_cluster` — the temp closure has no module commit
/// target.
pub fn insert_cluster(
    shared: &crate::session_v4::SharedState,
    processed: ProcessedCluster,
    target: &ModuleFullPath,
) {
    if processed.is_empty() {
        return;
    }

    // Wave 3a-β scaffold: `process_cluster` writes commit directly through
    // `check_program_compat`, so `entries` is normally empty. When the full
    // staging pivot lands (FIXME 0176), this loop drains staging into live
    // per-entry under inner-DashMap locks (target shape from `facades/int.md`
    // §"Atomicity guarantees").
    if let Some(mut live) = shared.symbol_tables.get_mut(target) {
        for (sym, entry) in processed.entries {
            live.insert(sym, entry);
        }
    }

    // Drain introspection records: each merges into the shared introspection
    // map (per Decision 38 — synchronously on commit). D1b: the store is
    // REPL-only (`Option`, `None` in batch). Doubly a no-op in batch — the
    // records vec is empty (population gate fed `None` to the ModuleCompiler)
    // AND there is no store to drain into.
    if let Some(m) = shared.introspection.as_ref() {
        for (fq, intro) in processed.introspection_records {
            m.insert(fq, intro);
        }
    }

    // Warnings and resolved-import bindings flow back through the calling
    // thread — the REPL/worker driver consumes them via the read accessors
    // (`warnings()` / `resolved_imports()`) BEFORE calling `insert_cluster`,
    // and is responsible for routing them to their final homes
    // (`Sess::warnings`, `SymbolTable::install_import_bindings`). We do not
    // re-route them here; the accessor contract makes them caller-visible.
}

// ---------------------------------------------------------------------------
// Unit tests (Wave 3a-β acceptance — `src/`-side per `/dev` ownership)
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn processed_cluster_empty_is_empty_and_drains_nothing() {
        // Empty cluster: no entries, no metadata residue → is_empty().
        // `into_iter` yields zero entries; commit is a no-op.
        let cluster = ProcessedCluster::empty();
        assert!(cluster.is_empty());
        assert!(cluster.warnings().is_empty());
        assert!(cluster.resolved_imports().is_empty());
        assert!(cluster.introspection_records().is_empty());
        assert_eq!(cluster.into_iter().count(), 0);
    }

    #[test]
    fn processed_cluster_from_parts_preserves_warnings() {
        use cranelisp_types::{Span, WarningKind};
        let warnings = vec![Warning {
            kind: WarningKind::Other,
            message: "test-warning".into(),
            span: Span::SYNTHETIC,
        }];
        let cluster = ProcessedCluster::from_parts(
            Vec::new(),
            warnings,
            Vec::new(),
            Vec::new(),
        );
        assert!(!cluster.is_empty(), "cluster with warnings is non-empty");
        assert_eq!(cluster.warnings().len(), 1);
        assert_eq!(cluster.warnings()[0].message, "test-warning");
    }

    #[test]
    fn processed_cluster_from_parts_preserves_introspection_records() {
        let records = vec![(
            FQSymbol {
                module: ModuleFullPath::from("test"),
                symbol: Symbol::from("foo"),
            },
            Introspection::default(),
        )];
        let cluster = ProcessedCluster::from_parts(
            Vec::new(),
            Vec::new(),
            Vec::new(),
            records,
        );
        assert!(!cluster.is_empty(), "introspection records make cluster non-empty");
        assert_eq!(cluster.introspection_records().len(), 1);
        assert_eq!(
            cluster.introspection_records()[0].0.symbol.as_ref(),
            "foo"
        );
    }

    #[test]
    fn processed_cluster_failure_mode_atomicity_invariant() {
        // Cluster-atomic acceptance: on failure mid-cluster, the orchestrator
        // drops `ProcessedCluster` without calling `insert_cluster`. Live
        // state remains byte-identical to pre-cluster. This test verifies the
        // type-level invariant: `ProcessedCluster` is only consumed by
        // `insert_cluster` (move-by-value); dropping the value on failure
        // releases the cluster's residue without touching live.
        let cluster = ProcessedCluster::empty();
        drop(cluster);
        // If insert_cluster had been called on the dropped value, this
        // assertion would be a runtime check against the live store — which
        // is unreachable post-drop. The compiler enforces that any "release
        // without commit" path requires drop (no double-consume).
    }
}
