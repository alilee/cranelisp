//! `check_forms` — single-function cluster-typecheck entry surface.
//!
//! Per Decision 44 (amended FIXME 0167 — Approach B + `SymbolTableAccess`;
//! 2026-05-13 third amendment collapsing the two-pass split into one call):
//! the typecheck entry surface used by `int`'s shared `process_cluster` is
//! **one** free function per cluster — `check_forms`. The internal two-pass
//! discipline (Pass 1 register signatures, then Pass 2 check bodies — spec
//! §5.13.1) is preserved as an implementation-phase ordering inside
//! `check_forms`; it does not cross the facade. Pass-1-to-Pass-2 working
//! state (`defn_type_vars`, default-method-defn deferrals, etc.) lives in a
//! local `ModuleCheckAccumulator` on `check_forms`'s stack frame and never
//! crosses the facade.
//!
//! `check_forms` is pure with respect to live state; staging mutation flows
//! through the existing `current_symbol_table_mut` accessor in
//! `SymbolTableAccess` and is invisible to typecheck. Cluster atomicity is
//! preserved because staging is orchestrator-local and is committed (drained
//! into live) only on whole-cluster `Ok`.
//!
//! Per facade item 3a: per-symbol Pass-2 side products
//! (`method_resolutions`, `expr_types`, `mono_defns`, `callees`) land on the
//! staging `ModuleEntry::Def`'s existing fields (`callees`, `ast`
//! annotations, additional staged `Def` entries for mono specialisations).
//!
//! ## Staging redirection (cluster mode)
//!
//! When `ctx` is `SymbolTableAccess::Cluster { staging, current_module, .. }`,
//! `check_forms` extracts the `&mut SymbolTable` staging reference and wraps
//! it in a local `RefCell` whose `&` is passed to `TypeCheckEnv` via
//! `new_with_staging`. The env's `current_symbol_table_mut(state)` accessor
//! checks `state.current_module` against the staging module and returns
//! `SymbolTableMut::Staging(...)` (cluster) or `SymbolTableMut::Live(...)`
//! (other modules / live mode). This makes the register-call sites redirect
//! writes to staging transparently in cluster mode while remaining
//! semantically unchanged in live mode.
//!
//! Reads (`current_symbol_table`) use the staging-first union `View` in
//! cluster mode: the accessor returns `SymbolTableRead::Cluster { staging,
//! live }` whose `.view()` is `View::union(staging, live)` (staging-first),
//! and `SymbolTableRead::Live(...)` (`View::single(live)`) in live mode.
//! Intra-cluster forward references therefore work: Pass 2 reads a signature
//! Pass 1 wrote into staging, because the union view sees staging entries
//! ahead of live.

use std::cell::RefCell;

use cranelisp_types::{
    CodeStore, Defn, ErrorLocation, LinkerStore, ModuleAliases, ModuleStrategy, ParsedEntry,
    Span, SymbolTable, SymbolTables, TopLevel, Warning,
};

use crate::checker::{CheckState, PreludeFallback, TypeCheckEnv};
use crate::cluster::SymbolTableAccess;
use crate::program::{CheckPass, ModuleCheckAccumulator};
use crate::result::CheckError;

/// Cluster-atomic typecheck entry surface.
///
/// Drives both internal passes (signature registration, then body checking)
/// over the cluster's `parsed` list, holding a single local
/// `ModuleCheckAccumulator` across the two passes so Pass 1's
/// `defn_type_vars` flow into Pass 2.
///
/// `ctx` carries the staging-vs-live dispatch (see `SymbolTableAccess`); writes
/// flow through `ctx.current_symbol_table_mut()` — redirected to staging in
/// cluster mode, to live otherwise. Reads flow through
/// `ctx.current_symbol_table()`, which serves a staging-first union `View`
/// in cluster mode so intra-cluster forward references resolve. The
/// `symbol_tables` parameter is the shared-borrow universe of modules used
/// for cross-module FQ resolution.
///
/// Returns `Ok(warnings)` on success — the staging (or live) table carries
/// registered entries with Pass 2 annotations on `ModuleEntry::Def` fields,
/// and the returned `Vec<Warning>` carries the cluster's non-fatal diagnostics
/// (drained from the internal `CheckResult`). This is the **warning channel**
/// (FIXME 0365): the §5.2.6 accessor/binding collision guard records a
/// [`WarningKind::ShadowedName`] diagnostic during accessor synthesis, and the
/// int caller threads the returned warnings onto `ProcessedCluster.warnings`
/// so the REPL can render them as `; warning: <message>` lines. An empty `Vec`
/// means the cluster produced no diagnostics. (`Warning` is a `cranelisp-types`
/// boundary type, so the channel is purely additive at the typecheck edge.)
/// Returns `Err(CheckError::Gap(_))` when an FQ reference cannot be resolved
/// (orchestrator retries the whole `check_forms` call with the same
/// `parsed` list). Returns `Err(CheckError::TypeError { .. })` for
/// non-recoverable type errors; the orchestrator drops staging on the
/// function-frame return.
///
/// Cluster atomicity: the live table is byte-identical to its pre-cluster
/// state across any `Err` return. On `Ok`, the orchestrator drains staging
/// into live atomically.
///
/// [`WarningKind::ShadowedName`]: cranelisp_types::WarningKind::ShadowedName
pub fn check_forms<C, L>(
    parsed: Vec<ParsedEntry>,
    ctx: &mut SymbolTableAccess<'_, C, L>,
    symbol_tables: &SymbolTables<C, L>,
    module_aliases: &ModuleAliases,
    prelude_fallback: &PreludeFallback,
) -> Result<Vec<Warning>, CheckError>
where
    C: CodeStore,
    L: LinkerStore,
{
    let current_module = ctx.current_module().clone();

    // Ensure the current module's live table exists. The orchestrator's
    // staging precondition (Cluster mode) requires the live table to exist;
    // tests using Live mode also rely on this. `ensure_module_exists` is
    // idempotent. We use a fresh non-staging env for this seed step so the
    // ensure call hits live regardless of mode (staging is for cluster body
    // writes; the live table must exist before staging can shadow it).
    let next_id = std::sync::atomic::AtomicU32::new(0);
    {
        let env =
            TypeCheckEnv::<C, L>::new(symbol_tables, &next_id, module_aliases, prelude_fallback);
        env.ensure_module_exists(&current_module);
    }

    // Construct the working env. In cluster mode, route writes targeting
    // `current_module` to a LOCAL `RefCell<&mut SymbolTable>` whose inner
    // `&mut` reborrows the staging table out of the `SymbolTableAccess::Cluster`
    // variant. The local cell binds outer-borrow + inner-mut to the same
    // call-frame lifetime, satisfying the invariance constraint on
    // `new_with_staging`'s collapsed `'a == 'a` shape. SymbolTableAccess's own
    // internal `RefCell` is the same data viewed through a different label —
    // we hold `ctx` mutably exclusive across this call frame, so handing the
    // reborrowed inner pointer to the local cell preserves single-writer
    // discipline (only the local cell is hit during the env's lifetime; the
    // orchestrator-side cell becomes accessible again after `check_forms`
    // returns).
    //
    // Per Decision 44 (FIXME 0167 amendment): writes targeting
    // `current_module` route through this `RefCell`; writes to other modules
    // (e.g., cross-module trait-impl writes per Decision 0045) fall through
    // to live unchanged. This is Wave 3b-2c.1's write-redirection plumbing
    // — it makes `Cluster` mode actually stage instead of leaking writes to
    // live.
    let staging_cell: Option<RefCell<&mut SymbolTable<C, L>>> = match ctx {
        SymbolTableAccess::Cluster { staging, .. } => {
            // `staging: &mut RefCell<&'a mut SymbolTable<C, L>>` — take a
            // mutable handle through `get_mut`, then reborrow the inner
            // `&mut SymbolTable` into a fresh `&mut` scoped to this call
            // frame, then wrap in a local `RefCell`.
            // `staging.get_mut()` yields `&mut &mut SymbolTable<C, L>`;
            // auto-deref through both layers gives `&mut SymbolTable<C, L>`.
            let inner: &mut &mut SymbolTable<C, L> = staging.get_mut();
            let reborrow: &mut SymbolTable<C, L> = inner;
            Some(RefCell::new(reborrow))
        }
        SymbolTableAccess::Live { .. } => None,
    };

    let env = match &staging_cell {
        Some(cell) => TypeCheckEnv::<C, L>::new_with_staging(
            symbol_tables,
            &next_id,
            current_module.clone(),
            cell,
            module_aliases,
            prelude_fallback,
        ),
        None => {
            TypeCheckEnv::<C, L>::new(symbol_tables, &next_id, module_aliases, prelude_fallback)
        }
    };

    // Advance `next_id` past any type variable IDs already used in stored
    // schemes for the current module. Without this, fresh vars allocated by
    // this `check_forms` call (which constructs a function-local AtomicU32
    // starting at 0) collide with quantified vars from schemes registered by
    // a previous `check_forms` call. The collision manifests inside
    // `instantiate_scheme`: `inst_subst.insert(N, fresh_var())` may bind
    // `Var(N)` to `Var(N)`, and `apply(inst_subst, Var(N))` then recurses
    // forever on `Var(N) → Var(N)`. Pre-S66 the typecheck environment owned
    // a session-spanning AtomicU32 (carried via `TypeCheckEnv` from the
    // session); the S66 facade construction reset it per call, exposing
    // this collision in the cross-call constrained/parametric poly case.
    {
        let table = symbol_tables.get(&current_module);
        if let Some(guard) = table {
            crate::checker::advance_next_id_past_table(&next_id, &*guard);
        }
    }

    let mut state = CheckState::new(current_module.clone());
    let mut accumulator = ModuleCheckAccumulator::new();

    // Rehydrate cross-cluster multi-sig overload resolution state from the
    // live symbol table. Each REPL form is its own cluster, so `CheckState`
    // (built fresh per `check_forms` call, above) starts with empty
    // `overloads` / `resolved_overloads` maps. Those maps are populated only
    // during the cluster that ran the multi-clause `(defn f …)` — a later
    // cluster `(f 5)` would otherwise see empty maps: `infer_apply`'s
    // pending-overload gate (`state.overloads.contains_key`) misses, no
    // `SigDispatch` is recorded, and codegen calls the bodyless
    // `DefKind::Overloaded` base → "undefined function: f"; an arity-2 call
    // unifies against the base scheme (built from the arity-1 clause) →
    // "arity mismatch". `--run` is unaffected because the whole file is one
    // cluster (defn + callers share live overload state).
    //
    // This mirrors the `advance_next_id_past_table` walk above (which
    // rehydrates per-session `next_id` from the live table for the
    // constrained/parametric-poly cross-call case): both reconstruct
    // per-cluster `CheckState` from the durable live table. The
    // `DefKind::Overloaded { variants }` base entry carries everything both
    // maps need — `OverloadVariant { param_types, ret_type, mangled_name }`
    // reconstructs `resolved_overloads` directly, and the overload keys
    // populate `overloads` (only the key set is consulted, via the
    // `contains_key` gate — the `(internal_name, arity)` values are never
    // read downstream of registration).
    {
        let table = symbol_tables.get(&current_module);
        if let Some(guard) = table {
            for (name, entry) in guard.all_symbols() {
                if let cranelisp_types::ModuleEntry::Def { kind, .. } = entry
                    && let cranelisp_types::DefKind::Overloaded { variants } = kind.as_ref()
                    && !variants.is_empty()
                {
                    let resolved: Vec<(Vec<cranelisp_types::Type>, cranelisp_types::Type, cranelisp_types::Symbol)> =
                        variants
                            .iter()
                            .map(|v| {
                                (v.param_types.clone(), v.ret_type.clone(), v.mangled_name.clone())
                            })
                            .collect();
                    let overload_keys: Vec<(cranelisp_types::Symbol, usize)> = variants
                        .iter()
                        .map(|v| (v.mangled_name.clone(), v.param_types.len()))
                        .collect();
                    state.overloads.entry(name.clone()).or_insert(overload_keys);
                    state.resolved_overloads.entry(name.clone()).or_insert(resolved);
                }
            }
        }
    }

    // Convert the `ParsedEntry` list into the `TopLevel` shapes the existing
    // per-form dispatcher consumes. `Macro` and `Constructor` variants don't
    // yet map to a `TopLevel` form — they are dropped here and handled
    // outside the per-form dispatcher (pre-Wave-3a-β path; orchestrator
    // boundary). Filter them out to keep the working-program clean.
    let working_program: Vec<TopLevel> = parsed
        .into_iter()
        .filter_map(parsed_to_top_level)
        .collect();

    // Pass 1: register all forms in source order. The accumulator captures
    // `defn_type_vars` and default-method-defn deferrals for Pass 2.
    for form in &working_program {
        let result = env
            .check_form(&current_module, form, CheckPass::Register, &mut state, &mut accumulator)
            .map_err(|e| lift_error(e, &state))?;
        env.merge_form_result(&current_module, &mut state, &mut accumulator, result);
    }

    // Register default method defns generated during Pass 1 TraitImpl
    // processing. These need Pass 1 signature registration too.
    let defaults: Vec<Defn> = std::mem::take(&mut accumulator.default_method_defns);
    for defn in &defaults {
        let form = TopLevel::Defn(defn.clone());
        let result = env
            .check_form(&current_module, &form, CheckPass::Register, &mut state, &mut accumulator)
            .map_err(|e| lift_error(e, &state))?;
        env.merge_form_result(&current_module, &mut state, &mut accumulator, result);
    }
    // Put defaults back so finalize knows about them.
    accumulator.default_method_defns = defaults;

    // Pass 2: check bodies for all forms. The accumulator carries Pass 1's
    // `defn_type_vars` into Pass 2 — this is the state-threading hole that
    // pre-S66's two-function split exposed, closed here by construction
    // (single call frame).
    //
    // FIXME 0354 Bug A: snapshot the post-Pass-1 active_constraints (the
    // declared bound-param constraints `resolve_bound_param` recorded for every
    // form's binders) and restore that snapshot before each form's body check.
    // Without this, body-checking form A instantiates trait methods (e.g.
    // `show` → a `Display`-only fresh var), and those STALE instantiation
    // constraints survive into form B's generalize where they `apply`-resolve
    // onto B's scheme var and corrupt its bound run (`[Eq, Display, Display]`).
    // Restoring the Pass-1 snapshot keeps every binder's *declared* bounds while
    // discarding the prior form's body-instantiation residue. (The reset was
    // previously `#[cfg(test)]`-only; the production path leaked the residue.)
    let pass1_constraints = state.active_constraints.clone();
    for form in &working_program {
        state.active_constraints = pass1_constraints.clone();
        let result = env
            .check_form(&current_module, form, CheckPass::CheckBody, &mut state, &mut accumulator)
            .map_err(|e| lift_error(e, &state))?;
        env.merge_form_result(&current_module, &mut state, &mut accumulator, result);
    }

    // Check bodies of default method defns too.
    let defaults_for_body: Vec<Defn> = accumulator.default_method_defns.clone();
    for defn in &defaults_for_body {
        state.active_constraints = pass1_constraints.clone();
        let form = TopLevel::Defn(defn.clone());
        let result = env
            .check_form(&current_module, &form, CheckPass::CheckBody, &mut state, &mut accumulator)
            .map_err(|e| lift_error(e, &state))?;
        env.merge_form_result(&current_module, &mut state, &mut accumulator, result);
    }

    // Finalize: run post-passes (Phase 2 generalize, Phase 3 re-resolve,
    // Pass 2.5 multi-sig overloads, Pass 3 detect constrained, Pass 4 mono,
    // Pass 5 auto-curry, cross-defn AST annotation refinement). This writes
    // per-symbol Pass-2 side products onto staging `ModuleEntry::Def` fields
    // per invariant 3a. The returned `CheckResult` carries diagnostics
    // (warnings + display info); FIXME 0365 surfaces its `warnings` out of
    // this function on the `Ok` path (the warning channel) so int can render
    // them in the REPL. The `display` half is still not part of the contract
    // and is dropped.
    //
    // `ModuleStrategy::Additive` matches the cluster-atomic flow: the
    // staging table accumulates new entries beside whatever exists in live;
    // Replace strategy is a session-level concern handled outside
    // `check_forms`.
    let result = env
        .finalize_check_result(
            &current_module,
            &mut state,
            &mut accumulator,
            &working_program,
            ModuleStrategy::Additive,
        )
        .map_err(|e| lift_error(e, &state))?;

    Ok(result.warnings)
}

/// Typecheck a standalone type expression against a symbol-table view,
/// returning the concrete [`Type`].
///
/// `int`'s platform loader uses this to validate a `PlatformFn.type_sig`
/// (FIXME 0231 / 0233): leaf names in the sig — including schema-declared
/// ADTs like `Rectangle` in `(Fn [Rectangle] Int)` — resolve through the same
/// symbol-table view + resolution primitive (§1) that program forms use, so a
/// name not reachable from `current_module` is a [`CheckError`] (the host
/// surfaces it as a DLL-load error). Pairs with frontend's `parse_type_expr`
/// (FIXME 0230).
///
/// This is **not** new inference machinery — it is a thin wrapper over the
/// existing `resolve_annotation_type_expr_in_module` path (Principle 6: one
/// general TypeExpr resolver + thin typed entries; FIXME 0590 Step A). A
/// platform sig is a single type expression, not a program form, so there is no
/// body inference and no generalisation; free type variables (`:a`) each mint a
/// fresh `TypeId` on first sight (the sig is implicitly universally quantified
/// over them), co-referencing repeats.
///
/// In cluster mode (`ctx` is `SymbolTableAccess::Cluster`) the first-hop view
/// unions staging+live for `current_module`, exactly as the cluster entry's
/// resolution does; in live mode it reads the committed table.
pub fn check_type_expr<C, L>(
    expr: &cranelisp_types::TypeExpr,
    ctx: &mut SymbolTableAccess<'_, C, L>,
    symbol_tables: &SymbolTables<C, L>,
    module_aliases: &ModuleAliases,
    prelude_fallback: &PreludeFallback,
    current_module: &cranelisp_types::ModuleFullPath,
    span: Span,
) -> Result<cranelisp_types::Type, CheckError>
where
    C: CodeStore,
    L: LinkerStore,
{
    let next_id = std::sync::atomic::AtomicU32::new(0);

    // Ensure the resolution-root module's live table exists (mirrors
    // `check_forms`'s seed step; `resolve_type_expr_in_module`'s first-hop
    // view requires the table to be present).
    {
        let env =
            TypeCheckEnv::<C, L>::new(symbol_tables, &next_id, module_aliases, prelude_fallback);
        env.ensure_module_exists(current_module);
    }

    // Advance `next_id` past type-var IDs already used in the module's stored
    // schemes so the fresh vars allocated for this sig's `:a` names cannot
    // collide with quantified vars from registered entries (same hazard
    // `check_forms` guards against).
    if let Some(guard) = symbol_tables.get(current_module) {
        crate::checker::advance_next_id_past_table(&next_id, &guard);
    }

    // Build the working env, staging-aware in cluster mode (the same
    // local-`RefCell`-reborrow dance `check_forms` uses).
    let staging_cell: Option<RefCell<&mut SymbolTable<C, L>>> = match ctx {
        SymbolTableAccess::Cluster { staging, .. } => {
            let inner: &mut &mut SymbolTable<C, L> = staging.get_mut();
            let reborrow: &mut SymbolTable<C, L> = inner;
            Some(RefCell::new(reborrow))
        }
        SymbolTableAccess::Live { .. } => None,
    };
    let env = match &staging_cell {
        Some(cell) => TypeCheckEnv::<C, L>::new_with_staging(
            symbol_tables,
            &next_id,
            current_module.clone(),
            cell,
            module_aliases,
            prelude_fallback,
        ),
        None => {
            TypeCheckEnv::<C, L>::new(symbol_tables, &next_id, module_aliases, prelude_fallback)
        }
    };

    // FIXME 0590 Step A: mint a fresh `TypeId` for each free type-var name on
    // first sight (mint-on-miss), replacing the former `collect_type_var_ids`
    // pre-walk. The annotation resolver mints and records into `var_map`, so
    // multiple occurrences of one name in the sig co-refer (`(Fn [a] a)` shares
    // one id) — byte-identical to the deleted pre-walk's shared ids, without a
    // second `TypeExpr` traversal that could silently diverge (§4/§5). A
    // `/`-qualified name is a module-qualified reference and never mints
    // (F2/0589), falling to the `TypeNotFound` error.
    let mut var_map: std::collections::HashMap<cranelisp_types::Symbol, cranelisp_types::TypeId> =
        std::collections::HashMap::new();

    env.resolve_annotation_type_expr_in_module(expr, &mut var_map, current_module, span)
        .map_err(CheckError::from)
}

/// Lift a failed inner-dispatcher `CranelispError` to `CheckError`, promoting
/// it to `CheckError::Gap` when a cross-module resolution gap was recorded on
/// `state.pending_gap` by the resolution caller.
///
/// `resolve_qualified` reports a gap in-band (on its `(scheme, gap)` return)
/// when an alias-resolved target module is ABSENT from the session symbol
/// tables. Because resolution returns `(None, gap)` so the `lookup` fallback
/// chain can still satisfy the name via another candidate path, the
/// `&mut`-holding caller (`infer_var`) stores
/// the surviving gap on `state.pending_gap`. The gap surfaces here only once
/// the overall lookup fails and the per-form dispatcher reports a not-found
/// `TypeError`. At that point the pending gap (carrying the alias-resolved
/// target module) is the precise cross-module cause, so we lift to `Gap`;
/// otherwise the original `TypeError` stands.
fn lift_error(e: cranelisp_types::CranelispError, state: &CheckState) -> CheckError {
    if let Some(gap) = state.pending_gap.clone() {
        return CheckError::Gap(gap);
    }
    map_cranelisp_error(e)
}

/// Convert a `ParsedEntry` into the `TopLevel` shape that the existing
/// per-form dispatcher consumes.
///
/// Returns `None` for `Macro` and `Constructor` entries — they don't yet
/// map to a `TopLevel` variant. The pre-Wave-3a-β source path handles macros
/// and constructors at the orchestrator boundary, not through the per-form
/// dispatcher.
fn parsed_to_top_level(parsed: ParsedEntry) -> Option<TopLevel> {
    match parsed {
        ParsedEntry::Def { name, variants, visibility, docstring, span } => {
            Some(TopLevel::Defn(Defn {
                name,
                docstring,
                variants,
                visibility,
                span,
            }))
        }
        ParsedEntry::TypeDef { name, type_params, constructors, visibility, docstring, span } => {
            // `ParsedEntry::TypeDef::type_params` now `Vec<Symbol>` (S70 step 2A
            // newtype-discipline narrowing); pass through unchanged. The prior
            // `TypeName → Symbol` conversion shim is retired.
            Some(TopLevel::TypeDef {
                name,
                docstring,
                type_params,
                constructors,
                visibility,
                span,
            })
        }
        ParsedEntry::TraitDecl { decl } => Some(TopLevel::TraitDecl(decl)),
        ParsedEntry::TraitImpl { impl_ } => Some(TopLevel::TraitImpl(impl_)),
        ParsedEntry::Macro { .. } | ParsedEntry::Constructor { .. } => None,
        // `ParsedEntry` is `#[non_exhaustive]` (cranelisp-types), so the
        // compiler requires a catch-all. A NEW variant reaching here is a
        // frontend-contract break: every `ParsedEntry` must be either mapped
        // to a `TopLevel` or explicitly declined above (S87-3). Fail loudly
        // rather than silently dropping the entry.
        other => unreachable!(
            "parsed_to_top_level: unhandled ParsedEntry variant {other:?} — a new \
             frontend-contract variant must be mapped or explicitly declined here"
        ),
    }
}

/// Translate the legacy `CranelispError` produced by the inner per-form
/// dispatcher into `CheckError`. Type errors carry message + location;
/// other variants are wrapped with a synthetic span (the pre-S66 inner
/// path produces only `TypeError` shapes in practice, but we degrade
/// gracefully for forward compatibility).
fn map_cranelisp_error(e: cranelisp_types::CranelispError) -> CheckError {
    match e {
        cranelisp_types::CranelispError::TypeError { message, location } => {
            CheckError::TypeError { message, location }
        }
        other => CheckError::TypeError {
            message: format!("typecheck error: {other:?}"),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        },
    }
}

#[cfg(test)]
mod tests;
