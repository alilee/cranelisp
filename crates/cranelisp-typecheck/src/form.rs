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
    Span, SymbolTable, SymbolTables, TopLevel,
};

use crate::checker::{CheckState, TypeCheckEnv};
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
/// Returns `Ok(())` on success — the staging (or live) table carries
/// registered entries with Pass 2 annotations on `ModuleEntry::Def` fields.
/// Returns `Err(CheckError::Gap(_))` when an FQ reference cannot be resolved
/// (orchestrator retries the whole `check_forms` call with the same
/// `parsed` list). Returns `Err(CheckError::TypeError { .. })` for
/// non-recoverable type errors; the orchestrator drops staging on the
/// function-frame return.
///
/// Cluster atomicity: the live table is byte-identical to its pre-cluster
/// state across any `Err` return. On `Ok`, the orchestrator drains staging
/// into live atomically.
pub fn check_forms<C, L>(
    parsed: Vec<ParsedEntry>,
    ctx: &mut SymbolTableAccess<'_, C, L>,
    symbol_tables: &SymbolTables<C, L>,
    module_aliases: &ModuleAliases,
) -> Result<(), CheckError>
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
        let env = TypeCheckEnv::<C, L>::new(symbol_tables, &next_id, module_aliases);
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
        ),
        None => TypeCheckEnv::<C, L>::new(symbol_tables, &next_id, module_aliases),
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
    for form in &working_program {
        let result = env
            .check_form(&current_module, form, CheckPass::CheckBody, &mut state, &mut accumulator)
            .map_err(|e| lift_error(e, &state))?;
        env.merge_form_result(&current_module, &mut state, &mut accumulator, result);
    }

    // Check bodies of default method defns too.
    let defaults_for_body: Vec<Defn> = accumulator.default_method_defns.clone();
    for defn in &defaults_for_body {
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
    // per invariant 3a. The returned `CheckResult` carries only diagnostics
    // (warnings + display info) which are not part of `check_forms`'s
    // contract — discarded here.
    //
    // `ModuleStrategy::Additive` matches the cluster-atomic flow: the
    // staging table accumulates new entries beside whatever exists in live;
    // Replace strategy is a session-level concern handled outside
    // `check_forms`.
    let _result = env
        .finalize_check_result(
            &current_module,
            &mut state,
            &mut accumulator,
            &working_program,
            ModuleStrategy::Additive,
        )
        .map_err(|e| lift_error(e, &state))?;

    Ok(())
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
/// existing `resolve_type_expr_in_module` path (Principle 6: one general
/// TypeExpr resolver + thin typed entries). A platform sig is a single type
/// expression, not a program form, so there is no body inference and no
/// generalisation; free type variables (`:a`) are each given a fresh `TypeId`
/// (the sig is implicitly universally quantified over them).
///
/// In cluster mode (`ctx` is `SymbolTableAccess::Cluster`) the first-hop view
/// unions staging+live for `current_module`, exactly as the cluster entry's
/// resolution does; in live mode it reads the committed table.
pub fn check_type_expr<C, L>(
    expr: &cranelisp_types::TypeExpr,
    ctx: &mut SymbolTableAccess<'_, C, L>,
    symbol_tables: &SymbolTables<C, L>,
    module_aliases: &ModuleAliases,
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
        let env = TypeCheckEnv::<C, L>::new(symbol_tables, &next_id, module_aliases);
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
        ),
        None => TypeCheckEnv::<C, L>::new(symbol_tables, &next_id, module_aliases),
    };

    // Allocate a fresh `TypeId` for each free type-var name in the sig.
    let mut var_map: std::collections::HashMap<cranelisp_types::Symbol, cranelisp_types::TypeId> =
        std::collections::HashMap::new();
    collect_type_var_ids(expr, &env, &mut var_map);

    env.resolve_type_expr_in_module(expr, &var_map, current_module, span)
        .map_err(CheckError::from)
}

/// Walk a `TypeExpr` and allocate a fresh `TypeId` for each distinct free
/// type-variable name (`TypeExpr::TypeVar`), recording it in `var_map`. Used
/// by [`check_type_expr`] to quantify a standalone platform sig over its
/// type vars before leaf-name resolution.
fn collect_type_var_ids<C, L>(
    expr: &cranelisp_types::TypeExpr,
    env: &TypeCheckEnv<'_, C, L>,
    var_map: &mut std::collections::HashMap<cranelisp_types::Symbol, cranelisp_types::TypeId>,
) where
    C: CodeStore,
    L: LinkerStore,
{
    use cranelisp_types::TypeExpr;
    match expr {
        TypeExpr::TypeVar(name) => {
            var_map
                .entry(name.clone())
                .or_insert_with(|| env.fresh_var_id().1);
        }
        TypeExpr::FnType(params, ret) => {
            for p in params {
                collect_type_var_ids(p, env, var_map);
            }
            collect_type_var_ids(ret, env, var_map);
        }
        TypeExpr::Applied(_name, args) => {
            for a in args {
                collect_type_var_ids(a, env, var_map);
            }
        }
        TypeExpr::Named(_) | TypeExpr::SelfType => {}
    }
}

/// Lift a failed inner-dispatcher `CranelispError` to `CheckError`, promoting
/// it to `CheckError::Gap` when a cross-module resolution gap was recorded on
/// `state.pending_gap` by the resolution caller.
///
/// `resolve_qualified` reports a gap in-band (on its `(scheme, gap)` return)
/// when an alias-resolved target module is ABSENT from the session symbol
/// tables. Because resolution returns `(None, gap)` so the `lookup` fallback
/// chain can still satisfy the name via another candidate path, the
/// `&mut`-holding caller (`infer_var` / `lookup_constructor_scheme`) stores
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
        // Catch-all for #[non_exhaustive] forward-compatibility.
        _ => None,
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
mod tests {
    use super::*;
    use cranelisp_types::{
        ConstructorDef, DefKind, DefnVariant, Expr, FieldDef, ModuleEntry, ModuleFullPath, Span,
        Symbol, TraitDecl, TraitImpl, TypeExpr, TypeName, Visibility,
    };
    use dashmap::DashMap;
    use std::sync::Arc;

    fn module_path() -> ModuleFullPath {
        ModuleFullPath::from("test_form_mod")
    }

    fn no_aliases() -> ModuleAliases {
        ModuleAliases::new()
    }

    fn modules() -> Arc<DashMap<ModuleFullPath, SymbolTable<(), ()>>> {
        let m: DashMap<ModuleFullPath, SymbolTable<(), ()>> = DashMap::new();
        m.insert(module_path(), SymbolTable::<(), ()>::new_with_params(module_path()));
        Arc::new(m)
    }

    fn unit_body() -> Expr {
        Expr::IntLit {
            value: 0,
            span: Span::SYNTHETIC,
            inferred_type: None,
        }
    }

    fn one_variant_defn(name: &str) -> ParsedEntry {
        ParsedEntry::Def {
            name: Symbol::from(name),
            variants: vec![DefnVariant {
                params: vec![],
                body: unit_body(),
                span: Span::SYNTHETIC,
            }],
            visibility: Visibility::Private,
            docstring: None,
            span: Span::SYNTHETIC,
        }
    }

    fn empty_typedef(name: &str) -> ParsedEntry {
        ParsedEntry::TypeDef {
            name: TypeName::from(name),
            type_params: vec![],
            constructors: vec![ConstructorDef {
                name: Symbol::from(format!("{name}Ctor").as_str()),
                docstring: None,
                fields: vec![],
                span: Span::SYNTHETIC,
            }],
            visibility: Visibility::Private,
            docstring: None,
            span: Span::SYNTHETIC,
        }
    }

    fn empty_traitdecl(name: &str) -> ParsedEntry {
        ParsedEntry::TraitDecl {
            decl: TraitDecl {
                name: cranelisp_types::TraitName::from(name),
                type_params: vec![Symbol::from("a")],
                methods: vec![],
                docstring: None,
                visibility: Visibility::Private,
                span: Span::SYNTHETIC,
            },
        }
    }

    fn empty_traitimpl(trait_name: &str, type_name: &str) -> ParsedEntry {
        ParsedEntry::TraitImpl {
            impl_: TraitImpl {
                trait_name: cranelisp_types::TraitRef::new(None, cranelisp_types::TraitName::from(trait_name)),
                target: cranelisp_types::TypeExpr::Named(
                    cranelisp_types::TypeRef::new(None, TypeName::from(type_name)),
                ),
                type_constraints: vec![],
                methods: vec![],
                span: Span::SYNTHETIC,
            },
        }
    }

    fn macro_entry(name: &str) -> ParsedEntry {
        ParsedEntry::Macro {
            info: cranelisp_types::DefmacroInfo::new(
                Symbol::from(name),
                false,
                None,
                vec![],
                Span::SYNTHETIC,
            ),
        }
    }

    fn constructor_entry() -> ParsedEntry {
        ParsedEntry::Constructor {
            name: Symbol::from("Some"),
            of_type: TypeName::from("Option"),
            fields: vec![FieldDef {
                name: Symbol::from("val"),
                type_expr: TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("a"))),
                span: Span::SYNTHETIC,
            }],
            span: Span::SYNTHETIC,
        }
    }

    /// Single-defn round trip: Pass 1 registers, Pass 2 body-checks, the
    /// staging Def has Pass-2 annotations on `ast`.
    #[test]
    fn check_forms_single_defn_round_trip() {
        let modules = modules();
        let mut ctx: SymbolTableAccess<'_, (), ()> = SymbolTableAccess::live(&modules, module_path());
        let parsed = vec![one_variant_defn("solo")];
        check_forms::<(), ()>(parsed, &mut ctx, &modules, &no_aliases()).expect("clean check_forms");

        let guard = modules.get(&module_path()).expect("module exists");
        let entry = guard.get("solo").expect("solo registered");
        match entry {
            ModuleEntry::Def { ast, kind, .. } => {
                assert!(ast.is_some(), "Pass 2 should have annotated the AST");
                assert!(matches!(kind.as_ref(), DefKind::UserFn { .. }));
            }
            _ => panic!("expected Def entry, got {entry:?}"),
        }
    }

    /// `check_type_expr` (0231): a standalone type expression resolves its
    /// leaf names against the supplied symbol-table view and yields the
    /// concrete `Type`. A schema-declared ADT name reachable from the module
    /// resolves; an unreachable name is a `CheckError` (the +Neg facet — the
    /// host surfaces this as a DLL-load error).
    #[test]
    fn check_type_expr_resolves_known_adt_and_rejects_unknown() {
        use cranelisp_types::{FQTypeName, Type, TypeDefInfo, TypeRef};

        let modules = modules();
        // Seed a nullary ADT `Color` into the module's live table.
        {
            let mut guard = modules.get_mut(&module_path()).expect("module exists");
            guard.insert(
                Symbol::from("Color"),
                ModuleEntry::TypeDef {
                    info: TypeDefInfo {
                        name: FQTypeName::new(module_path(), TypeName::from("Color")),
                        type_params: vec![],
                        constructors: vec![],
                    },
                    visibility: Visibility::Public,
                    docstring: None,
                    constructor_scheme: None,
                },
            );
        }

        let mut ctx: SymbolTableAccess<'_, (), ()> =
            SymbolTableAccess::live(&modules, module_path());

        // Positive: a reachable ADT name resolves to its ADT type.
        let color = TypeExpr::Named(TypeRef::new(None, TypeName::from("Color")));
        let ty = check_type_expr::<(), ()>(
            &color,
            &mut ctx,
            &modules,
            &no_aliases(),
            &module_path(),
            Span::SYNTHETIC,
        )
        .expect("Color resolves");
        assert_eq!(
            ty,
            Type::ADT(FQTypeName::new(module_path(), TypeName::from("Color")), vec![])
        );

        // A function sig over the ADT resolves, and free type vars (`:a`) get
        // fresh ids rather than failing as unknown names.
        let fn_sig = TypeExpr::FnType(
            vec![TypeExpr::TypeVar(Symbol::from("a")), color.clone()],
            Box::new(TypeExpr::TypeVar(Symbol::from("a"))),
        );
        let fn_ty = check_type_expr::<(), ()>(
            &fn_sig,
            &mut ctx,
            &modules,
            &no_aliases(),
            &module_path(),
            Span::SYNTHETIC,
        )
        .expect("fn sig over Color + type var resolves");
        match fn_ty {
            Type::Fn(params, ret) => {
                assert_eq!(params.len(), 2);
                // Both `:a` occurrences map to the same fresh var.
                assert!(matches!(params[0], Type::Var(_)));
                assert_eq!(params[0], *ret, "both :a occurrences share one id");
            }
            other => panic!("expected Fn type, got {other:?}"),
        }

        // +Neg: an unreachable name is a CheckError, not a silent success.
        let nope = TypeExpr::Named(TypeRef::new(None, TypeName::from("Nope")));
        let err = check_type_expr::<(), ()>(
            &nope,
            &mut ctx,
            &modules,
            &no_aliases(),
            &module_path(),
            Span::SYNTHETIC,
        )
        .expect_err("unknown type name must be a CheckError");
        assert!(matches!(err, CheckError::TypeError { .. }));
    }

    /// Multi-form forward-reference: two defns where the second body
    /// references the first. Both signatures must register in Pass 1 before
    /// any body checks in Pass 2 — this is the Pass-1-to-Pass-2 state
    /// threading that pre-S66's two-function split broke.
    #[test]
    fn check_forms_forward_reference_works() {
        let modules = modules();
        let mut ctx: SymbolTableAccess<'_, (), ()> = SymbolTableAccess::live(&modules, module_path());

        // first: () -> Int = 0
        // second: () -> Int = first  (calls first)
        let first = one_variant_defn("first");
        let second = ParsedEntry::Def {
            name: Symbol::from("second"),
            variants: vec![DefnVariant {
                params: vec![],
                body: Expr::Apply {
                    callee: Box::new(Expr::var(Symbol::from("first"), Span::SYNTHETIC)),
                    args: vec![],
                    span: Span::SYNTHETIC,
                    inferred_type: None,
                    resolved_call: None,
                },
                span: Span::SYNTHETIC,
            }],
            visibility: Visibility::Private,
            docstring: None,
            span: Span::SYNTHETIC,
        };

        let parsed = vec![first, second];
        check_forms::<(), ()>(parsed, &mut ctx, &modules, &no_aliases()).expect("clean check_forms");

        let guard = modules.get(&module_path()).expect("module exists");
        assert!(guard.get("first").is_some(), "first registered");
        assert!(guard.get("second").is_some(), "second registered");
    }

    /// Pass 1 → Pass 2 state threading regression test. Pre-S66 the
    /// two-function shape created a fresh `ModuleCheckAccumulator` per call,
    /// so Pass 1's `defn_type_vars` did not flow to Pass 2 — Pass 2 failed
    /// with an internal "missing type vars" error. The single-function
    /// `check_forms` shape closes this hole by construction: the accumulator
    /// lives in `check_forms`'s frame and persists across both internal
    /// passes.
    #[test]
    fn check_forms_pass_state_threading_is_intact() {
        let modules = modules();
        let mut ctx: SymbolTableAccess<'_, (), ()> = SymbolTableAccess::live(&modules, module_path());
        let parsed = vec![one_variant_defn("twopass")];
        // Pre-S66: this would fail with "missing type vars" because Pass 1
        // and Pass 2 ran in separate calls with separate accumulators.
        // Post-S66: the accumulator persists; this succeeds.
        check_forms::<(), ()>(parsed, &mut ctx, &modules, &no_aliases())
            .expect("state threading should keep type vars alive across passes");
    }

    /// Mixed cluster: Defn → TypeDef → TraitDecl → TraitImpl → Macro all in
    /// one call. Macro entries are filtered out (handled at the orchestrator
    /// boundary); the rest land on the staging table.
    #[test]
    fn check_forms_handles_mixed_form_cluster() {
        let modules = modules();
        let mut ctx: SymbolTableAccess<'_, (), ()> = SymbolTableAccess::live(&modules, module_path());
        let parsed = vec![
            empty_typedef("MyT"),
            empty_traitdecl("MyTr"),
            empty_traitimpl("MyTr", "MyT"),
            one_variant_defn("noargs"),
            macro_entry("m"),
            constructor_entry(),
        ];
        let r = check_forms::<(), ()>(parsed, &mut ctx, &modules, &no_aliases());
        // The TypeDef + TraitDecl + Defn registrations should succeed; the
        // TraitImpl with an empty method set is also valid. Macros and
        // constructors are no-ops at this surface.
        assert!(r.is_ok(), "mixed cluster should typecheck: {r:?}");

        let guard = modules.get(&module_path()).expect("module exists");
        // Defn registered
        assert!(guard.get("noargs").is_some(), "Defn registered");
        // TypeDef registered (stored under Symbol::from(TypeName) per
        // `register_type_def` in adt.rs).
        assert!(
            matches!(guard.get("MyT"), Some(ModuleEntry::TypeDef { .. })),
            "TypeDef registered as ModuleEntry::TypeDef"
        );
    }

    /// Cluster mode: smoke test that the function is reachable in `Cluster`
    /// mode and returns a structured `Result`. Atomicity properties (live
    /// untouched, staging populated) are verified by
    /// `check_forms_cluster_mode_writes_go_to_staging` below.
    #[test]
    fn check_forms_cluster_mode_reachable() {
        let modules = modules();
        let mut staging = SymbolTable::<(), ()>::new_with_params(module_path());
        let mut ctx: SymbolTableAccess<'_, (), ()> =
            SymbolTableAccess::cluster(&modules, &mut staging, module_path());
        let parsed = vec![one_variant_defn("clustered")];
        let r = check_forms::<(), ()>(parsed, &mut ctx, &modules, &no_aliases());
        assert!(r.is_ok(), "cluster-mode check_forms returns structured Result: {r:?}");
    }

    /// Wave 3b-2c.1 acceptance test: in `SymbolTableAccess::Cluster` mode,
    /// `check_forms` writes go to the orchestrator-handed staging table,
    /// NOT to the per-module live table. This is the structural pre-S66
    /// guarantee that makes whole-cluster atomic commit-or-discard
    /// possible.
    ///
    /// Pre-Wave-3b-2c.1 the `let _ = ctx;` bypass in `check_forms` meant
    /// writes leaked to live regardless of mode. This test pins the
    /// post-bypass behaviour: live is byte-identical to its pre-call state,
    /// and staging carries the Defn registration.
    ///
    /// spec: Decision 44 (amended FIXME 0167) — orchestrator-owned staging;
    /// invariant 2: `check_forms` is pure with respect to live state.
    #[test]
    fn check_forms_cluster_mode_writes_go_to_staging() {
        let modules = modules();
        // Pre-call: live is empty (just whatever `modules()` seeded — which
        // is the empty SymbolTable for `module_path`). Snapshot its key set.
        let live_keys_before: std::collections::HashSet<Symbol> = {
            let guard = modules.get(&module_path()).expect("live module exists");
            guard.symbols.keys().cloned().collect()
        };

        let mut staging = SymbolTable::<(), ()>::new_with_params(module_path());
        {
            let mut ctx: SymbolTableAccess<'_, (), ()> =
                SymbolTableAccess::cluster(&modules, &mut staging, module_path());
            let parsed = vec![one_variant_defn("staged_defn")];
            check_forms::<(), ()>(parsed, &mut ctx, &modules, &no_aliases())
                .expect("cluster mode check_forms succeeds");
        }

        // Live is byte-identical (key set unchanged) — the write redirect to
        // staging worked. Pre-fix this assertion would fail because writes
        // leaked to live.
        let live_keys_after: std::collections::HashSet<Symbol> = {
            let guard = modules.get(&module_path()).expect("live module exists");
            guard.symbols.keys().cloned().collect()
        };
        assert_eq!(
            live_keys_before, live_keys_after,
            "live module must be untouched by cluster-mode check_forms"
        );
        let guard = modules.get(&module_path()).expect("live module exists");
        assert!(
            guard.get("staged_defn").is_none(),
            "staged_defn must NOT appear in live (it should be on staging)"
        );

        // Staging carries the registration.
        assert!(
            staging.get("staged_defn").is_some(),
            "staged_defn must be registered on the staging table"
        );
        match staging.get("staged_defn").unwrap() {
            ModuleEntry::Def { .. } => {}
            other => panic!("expected Def entry on staging, got {other:?}"),
        }
    }

    /// Wave 3b-2c.3 acceptance test (FIXME 0179): in `SymbolTableAccess::Cluster`
    /// mode, a write then a read-back from the SAME `check_forms` call finds
    /// the written entry — not via the live table (which is untouched per
    /// invariant 2), but through the staging-first read union plumbed via
    /// `TypeCheckEnv::current_symbol_table → View::union(staging, live)`.
    ///
    /// Concretely: register `first` and `second` as a two-form cluster where
    /// `second`'s body calls `first`. Pass 2's body check of `second` looks up
    /// `first` via `infer_var → lookup → lookup_in_current_module →
    /// probe_module_entry_owned` — that probe must consult staging first to
    /// see the just-registered `first` (which is in staging, not live).
    ///
    /// Pre-3b-2c.3: the live-only `current_symbol_table` accessor + direct
    /// `self.modules.get(&state.current_module)` calls in `lookup_in_current_module`
    /// would miss the staged `first`, and Pass 2 of `second` would fail with
    /// "undefined variable: first".
    ///
    /// spec: Decision 44 (third amendment) — cluster-mode reads dispatch
    /// `View::union(staging, live)` per FIXME 0179.
    #[test]
    fn check_forms_cluster_mode_intra_cluster_forward_ref_via_staging() {
        let modules = modules();
        let mut staging = SymbolTable::<(), ()>::new_with_params(module_path());
        {
            let mut ctx: SymbolTableAccess<'_, (), ()> =
                SymbolTableAccess::cluster(&modules, &mut staging, module_path());
            // first: () -> Int = 0
            // second: () -> Int = first  (calls first)
            let first = one_variant_defn("first");
            let second = ParsedEntry::Def {
                name: Symbol::from("second"),
                variants: vec![DefnVariant {
                    params: vec![],
                    body: Expr::Apply {
                        callee: Box::new(Expr::var(Symbol::from("first"), Span::SYNTHETIC)),
                        args: vec![],
                        span: Span::SYNTHETIC,
                        inferred_type: None,
                        resolved_call: None,
                    },
                    span: Span::SYNTHETIC,
                }],
                visibility: Visibility::Private,
                docstring: None,
                span: Span::SYNTHETIC,
            };
            let parsed = vec![first, second];
            check_forms::<(), ()>(parsed, &mut ctx, &modules, &no_aliases()).expect(
                "cluster-mode forward reference must resolve via staging read union",
            );
        }

        // Live is byte-identical (invariant 2 — cluster mode never writes to
        // live during the call). Both entries live on staging.
        let live_guard = modules.get(&module_path()).expect("live module exists");
        assert!(
            live_guard.get("first").is_none(),
            "first must NOT appear in live during cluster mode"
        );
        assert!(
            live_guard.get("second").is_none(),
            "second must NOT appear in live during cluster mode"
        );

        // Staging carries both registrations.
        assert!(staging.get("first").is_some(), "first staged");
        assert!(staging.get("second").is_some(), "second staged");
    }

    /// Live mode: writes target the live per-module table directly. The
    /// staged Def is observable on the modules map after the call.
    #[test]
    fn check_forms_live_mode_writes_visible_on_modules() {
        let modules = modules();
        let mut ctx: SymbolTableAccess<'_, (), ()> = SymbolTableAccess::live(&modules, module_path());
        let parsed = vec![one_variant_defn("livewrite")];
        check_forms::<(), ()>(parsed, &mut ctx, &modules, &no_aliases()).expect("live mode");
        let guard = modules.get(&module_path()).expect("module exists");
        assert!(guard.get("livewrite").is_some());
    }

    /// Pass 2 failure: the first error short-circuits the loop. Earlier
    /// forms' Pass 1 registrations may have landed (atomicity is the
    /// orchestrator's responsibility — the caller discards staging on Err).
    #[test]
    fn check_forms_macro_only_is_noop() {
        let modules = modules();
        let mut ctx: SymbolTableAccess<'_, (), ()> = SymbolTableAccess::live(&modules, module_path());
        let parsed = vec![macro_entry("m"), constructor_entry()];
        let r = check_forms::<(), ()>(parsed, &mut ctx, &modules, &no_aliases());
        assert!(r.is_ok(), "macro-only / constructor-only cluster is a no-op: {r:?}");
    }

    /// Repro: REPL `(defn id [x] x)` then `(id 7)` overflows the main-thread
    /// stack. This isolates the bug to the typecheck surface — no int
    /// orchestration, no frontend, no worker threads, no JIT involved. If
    /// this test overflows or hangs, the bug is owned by typecheck.
    ///
    /// Call 1 registers `id` as constrained-poly in live. Call 2 typechecks
    /// a caller that invokes `id` with an Int — `finalize_check_result`'s
    /// Additive strategy should pick `id` up from live, run Pass 4 mono,
    /// register `id$Int` once, and return.
    #[test]
    fn check_forms_cross_call_constrained_poly_mono_terminates() {
        let modules = modules();

        // Call 1: (defn id [x] x) — body `x` is the param, fully poly.
        // Spans must be unique across nested nodes — production source spans
        // are always unique by their byte ranges. `Span::SYNTHETIC` (0..0) is
        // not safe to share because `record_expr_type` is keyed on span and
        // shared spans cause inferred-type collisions (the outer defn's
        // Fn type overwrites the inner IntLit's Int).
        let id_defn = ParsedEntry::Def {
            name: Symbol::from("id"),
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("x"), None)],
                body: Expr::var(Symbol::from("x"), Span::new(11, 12)),
                span: Span::new(10, 13),
            }],
            visibility: Visibility::Private,
            docstring: None,
            span: Span::new(0, 14),
        };
        {
            let mut ctx: SymbolTableAccess<'_, (), ()> =
                SymbolTableAccess::live(&modules, module_path());
            check_forms::<(), ()>(vec![id_defn], &mut ctx, &modules, &no_aliases())
                .expect("call 1: register id as constrained-poly");
        }

        // Sanity: `id` registered. Note: pure parametric poly `(defn id [x] x)`
        // has no trait constraints, so `constrained_fn` will be `None`. That's
        // fine — what matters for this repro is that call 2's mono path
        // doesn't overflow.
        {
            let guard = modules.get(&module_path()).expect("module exists");
            assert!(guard.get("id").is_some(), "id registered after call 1");
        }

        // Call 2: (defn caller [] (id 7)) — wraps a bare expr `(id 7)` the
        // way int's `wrap_exprs_as_synthetic_defns` would for REPL input.
        let caller_defn = ParsedEntry::Def {
            name: Symbol::from("caller"),
            variants: vec![DefnVariant {
                params: vec![],
                body: Expr::Apply {
                    callee: Box::new(Expr::var(Symbol::from("id"), Span::new(101, 103))),
                    args: vec![Expr::IntLit {
                        value: 7,
                        span: Span::new(104, 105),
                        inferred_type: None,
                    }],
                    span: Span::new(100, 106),
                    inferred_type: None,
                    resolved_call: None,
                },
                span: Span::new(90, 107),
            }],
            visibility: Visibility::Private,
            docstring: None,
            span: Span::new(80, 110),
        };
        let mut ctx2: SymbolTableAccess<'_, (), ()> =
            SymbolTableAccess::live(&modules, module_path());
        check_forms::<(), ()>(vec![caller_defn], &mut ctx2, &modules, &no_aliases())
            .expect("call 2: monomorphise (id 7) — must not overflow");

        // Assert: `id$Int` mono entry is registered in live.
        let guard = modules.get(&module_path()).expect("module exists");
        assert!(
            guard.get("id$Int").is_some(),
            "id$Int should be registered after call 2 mono"
        );
    }

    /// A defn whose body references the qualified name `module/name`, where
    /// `module` is the absolute module path component of the reference.
    fn defn_referencing(name: &str, qualified_ref: &str) -> ParsedEntry {
        ParsedEntry::Def {
            name: Symbol::from(name),
            variants: vec![DefnVariant {
                params: vec![],
                body: Expr::var(
                    Symbol::from(qualified_ref),
                    Span::new(11, 11 + qualified_ref.len() as u32),
                ),
                span: Span::new(10, 40),
            }],
            visibility: Visibility::Private,
            docstring: None,
            span: Span::new(0, 41),
        }
    }

    /// Gap on a missing module (plain, no alias): an FQ value reference
    /// `some.mod/name` whose `some.mod` module is ABSENT from the session
    /// symbol tables surfaces `CheckError::Gap(SymbolTypechecked(fq))` with
    /// `fq.module == "some.mod"` — the named target module, not the local
    /// module.
    ///
    /// spec: facade `typecheck.md` invariant 8 (Gap) §"Enactment";
    /// `bounded-contexts.md` §7 (cross-module resolution); ResolutionGap.
    #[test]
    fn gap_on_missing_module_plain() {
        let modules = modules();
        let mut ctx: SymbolTableAccess<'_, (), ()> =
            SymbolTableAccess::live(&modules, module_path());
        // Body references `some.mod/thing`; `some.mod` is not in `modules`.
        let parsed = vec![defn_referencing("uses_missing", "some.mod/thing")];
        let r = check_forms::<(), ()>(parsed, &mut ctx, &modules, &no_aliases());
        match r {
            Err(CheckError::Gap(cranelisp_types::ResolutionGap::SymbolTypechecked(fq))) => {
                assert_eq!(
                    fq.module.as_ref(),
                    "some.mod",
                    "gap module must be the named (absent) target module"
                );
                assert_eq!(fq.symbol.as_ref(), "thing", "gap symbol is the local name");
            }
            other => panic!("expected Gap(SymbolTypechecked) for missing module, got {other:?}"),
        }
    }

    /// Gap on a missing module reached VIA an alias: an alias `m/real`
    /// (owner-prefixed key `<owner>.real`) targeting `real.target`, where
    /// `real.target` is ABSENT. A reference through the alias must FOLLOW the
    /// alias before deciding the gap — the gap's `fq.module` is the resolved
    /// target `real.target`, NOT the bare alias prefix. This proves §8.6.6
    /// alias substitution runs ahead of gap detection.
    ///
    /// spec: facade `typecheck.md` invariant 8 (Gap) §"Enactment";
    /// `bounded-contexts.md` §7 (§8.6.6 longest-prefix alias substitution).
    #[test]
    fn gap_on_missing_module_via_alias() {
        let modules = modules();
        // Alias table: key `r` -> target `real.target`. `lookup` probes the
        // child-of-current path (`<current_module>.r`) first, then the
        // ABSOLUTE module component `r`. The §8.6.6 longest-prefix-match
        // substitutes the alias on the absolute probe (`r` is a prefix of the
        // queried `r`), rewriting it to `real.target`. With `real.target`
        // absent the resolver records the gap carrying the resolved target.
        let aliases = ModuleAliases::new();
        aliases.insert(
            ModuleFullPath::from("r"),
            cranelisp_types::ModuleAliasEntry::new(
                ModuleFullPath::from("real.target"),
                Visibility::Public,
                Span::SYNTHETIC,
            ),
        );

        let mut ctx: SymbolTableAccess<'_, (), ()> =
            SymbolTableAccess::live(&modules, module_path());
        // Body references `r/thing`; `r` is an alias to `real.target` which is
        // absent. The gap must carry the RESOLVED target.
        let parsed = vec![defn_referencing("uses_alias", "r/thing")];
        let r = check_forms::<(), ()>(parsed, &mut ctx, &modules, &aliases);
        match r {
            Err(CheckError::Gap(cranelisp_types::ResolutionGap::SymbolTypechecked(fq))) => {
                assert_eq!(
                    fq.module.as_ref(),
                    "real.target",
                    "gap module must be the ALIAS-RESOLVED target, not the bare alias"
                );
                assert_eq!(fq.symbol.as_ref(), "thing", "gap symbol is the local name");
            }
            other => panic!(
                "expected Gap(SymbolTypechecked) with alias-resolved target, got {other:?}"
            ),
        }
    }

    /// Cross-cluster multi-sig overload dispatch (Sprint 76 Wave 4c, FIXME
    /// handed off by /dev int). Each REPL form is a separate `check_forms`
    /// cluster, so a multi-clause `(defn f ([x] x) ([x y] x))` registered in
    /// one cluster must still dispatch correctly from a *later* cluster's body
    /// `(f 5)`. Pre-fix the second cluster built a fresh `CheckState` with
    /// empty `overloads` maps, so `infer_apply`'s pending-overload gate missed
    /// → no `SigDispatch`, codegen hit the bodyless `Overloaded` base
    /// ("undefined function: f"). The fix rehydrates `overloads` /
    /// `resolved_overloads` from the live `DefKind::Overloaded` base entry at
    /// the top of `check_forms` (mirroring `advance_next_id_past_table`).
    ///
    /// spec: §5.13 multi-signature dispatch; REPL cross-input persistence.
    #[test]
    fn check_forms_cross_call_multi_sig_dispatch_resolves_to_variant() {
        use cranelisp_types::{DefKind, ModuleEntry, ResolvedCall};

        let modules = modules();

        // Cluster 1: register the multi-clause `f`.
        //   (defn f ([x] x) ([x y] x))
        let var_x = |sp: Span| Expr::var(Symbol::from("x"), sp);
        let multi_f = ParsedEntry::Def {
            name: Symbol::from("f"),
            variants: vec![
                DefnVariant {
                    params: vec![(Symbol::from("x"), None)],
                    body: var_x(Span::SYNTHETIC),
                    span: Span::SYNTHETIC,
                },
                DefnVariant {
                    params: vec![(Symbol::from("x"), None), (Symbol::from("y"), None)],
                    body: var_x(Span::SYNTHETIC),
                    span: Span::SYNTHETIC,
                },
            ],
            visibility: Visibility::Private,
            docstring: None,
            span: Span::SYNTHETIC,
        };
        {
            let mut ctx: SymbolTableAccess<'_, (), ()> =
                SymbolTableAccess::live(&modules, module_path());
            check_forms::<(), ()>(vec![multi_f], &mut ctx, &modules, &no_aliases())
                .expect("cluster 1 (multi-sig defn) checks clean");
        }
        // Sanity: the live base entry is `Overloaded` with both variants.
        {
            let guard = modules.get(&module_path()).expect("module exists");
            match guard.get("f").expect("f base registered") {
                ModuleEntry::Def { kind, .. } => match kind.as_ref() {
                    DefKind::Overloaded { variants } => {
                        assert_eq!(variants.len(), 2, "both clauses recorded on base");
                    }
                    other => panic!("expected Overloaded base, got {other:?}"),
                },
                other => panic!("expected Def, got {other:?}"),
            }
        }

        // Cluster 2 (a FRESH `CheckState`): a caller body `(f 5)`. The
        // arity-1 variant has an untyped param (mangles to `f$Var`); `5`
        // matches it (Var is compatible with Int).
        let call_span = Span::SYNTHETIC;
        let caller = ParsedEntry::Def {
            name: Symbol::from("caller"),
            variants: vec![DefnVariant {
                params: vec![],
                body: Expr::Apply {
                    callee: Box::new(Expr::var(Symbol::from("f"), Span::SYNTHETIC)),
                    args: vec![Expr::IntLit {
                        value: 5,
                        span: Span::SYNTHETIC,
                        inferred_type: None,
                    }],
                    span: call_span,
                    resolved_call: None,
                    inferred_type: None,
                },
                span: Span::SYNTHETIC,
            }],
            visibility: Visibility::Private,
            docstring: None,
            span: Span::SYNTHETIC,
        };
        {
            let mut ctx: SymbolTableAccess<'_, (), ()> =
                SymbolTableAccess::live(&modules, module_path());
            check_forms::<(), ()>(vec![caller], &mut ctx, &modules, &no_aliases())
                .expect("cluster 2 (caller body) checks clean across clusters");
        }

        // The caller's annotated AST must carry a `SigDispatch` to `f$Var` on
        // the `(f 5)` Apply — pre-fix this resolved to the bodyless base.
        let guard = modules.get(&module_path()).expect("module exists");
        let caller_entry = guard.get("caller").expect("caller registered");
        let ast = match caller_entry {
            ModuleEntry::Def { ast: Some(ast), .. } => ast,
            other => panic!("expected caller Def with annotated ast, got {other:?}"),
        };
        let resolved = match &ast.body {
            Expr::Apply { resolved_call: Some(rc), .. } => rc.as_ref(),
            other => panic!("expected annotated Apply body, got {other:?}"),
        };
        match resolved {
            ResolvedCall::SigDispatch { mangled_name } => {
                assert_eq!(
                    mangled_name.as_ref(),
                    "f$Var",
                    "cross-cluster (f 5) must dispatch to the arity-1 variant"
                );
            }
            other => panic!("expected SigDispatch across clusters, got {other:?}"),
        }
    }
}
