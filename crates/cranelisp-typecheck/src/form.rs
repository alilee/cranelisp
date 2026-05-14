//! `check_forms` — single-function cluster-typecheck entry surface.
//!
//! Per Decision 44 (amended FIXME 0167 — Approach B + `ClusterContext`;
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
//! `ClusterContext` and is invisible to typecheck. Cluster atomicity is
//! preserved because staging is orchestrator-local and is committed (drained
//! into live) only on whole-cluster `Ok`.
//!
//! Per facade item 3a: per-symbol Pass-2 side products
//! (`method_resolutions`, `expr_types`, `mono_defns`, `callees`) land on the
//! staging `ModuleEntry::Def`'s existing fields (`callees`, `ast`
//! annotations, additional staged `Def` entries for mono specialisations).
//!
//! ## Wave 3b-2c.1 (write-redirection plumbing)
//!
//! When `ctx` is `ClusterContext::Cluster { staging, current_module, .. }`,
//! `check_forms` extracts the `&mut SymbolTable` staging reference and wraps
//! it in a local `RefCell` whose `&` is passed to `TypeCheckEnv` via
//! `new_with_staging`. The env's `current_symbol_table_mut(state)` accessor
//! checks `state.current_module` against the staging module and returns
//! `SymbolTableMut::Staging(...)` (cluster) or `SymbolTableMut::Live(...)`
//! (other modules / live mode). This makes the 91 register-call sites
//! redirect to staging transparently in cluster mode while remaining
//! semantically unchanged in live mode.
//!
//! Reads (`current_symbol_table`) currently still hit live in both modes;
//! union reads (staging-first-then-live, per facade `View`) are Wave 3b-2c.1
//! follow-up — see `design/arch/fixmes/` for the read-union plumbing FIXME
//! filed by this change. Intra-cluster forward references (Pass 2 reads a
//! signature Pass 1 wrote into staging) therefore depend on the follow-up
//! and are not yet exercised by `check_forms` in cluster mode.

use std::cell::RefCell;

use dashmap::DashMap;

use cranelisp_types::{
    CodeStore, Defn, ErrorLocation, LinkerStore, ModuleFullPath, ModuleStrategy, ParsedEntry,
    Span, Symbol, SymbolTable, TopLevel,
};

use crate::checker::{CheckState, TypeCheckEnv};
use crate::cluster::ClusterContext;
use crate::program::{CheckPass, ModuleCheckAccumulator};
use crate::result::CheckError;

/// Cluster-atomic typecheck entry surface.
///
/// Drives both internal passes (signature registration, then body checking)
/// over the cluster's `parsed` list, holding a single local
/// `ModuleCheckAccumulator` across the two passes so Pass 1's
/// `defn_type_vars` flow into Pass 2.
///
/// `ctx` carries the staging-vs-live dispatch (see `ClusterContext`); writes
/// flow through `ctx.current_symbol_table_mut()` (currently writes go to live
/// in both modes — full staging redirection is Wave 3a-α follow-up). The
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
    ctx: &mut ClusterContext<'_, C, L>,
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
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
        let env = TypeCheckEnv::<C, L>::new(symbol_tables, &next_id);
        env.ensure_module_exists(&current_module);
    }

    // Extract the staging mutable reference up front so we can wrap it in a
    // `RefCell` for the duration of this call. The `RefCell` provides
    // interior mutability so the `&self`-flavoured `current_symbol_table_mut`
    // accessor on `TypeCheckEnv` can hand out a writable guard pointed at
    // staging. The `ctx` mutable borrow is consumed by this match (we
    // re-extract `staging` as a fresh `&mut` reborrow); we don't touch
    // `ctx` again after this point.
    //
    // Per Decision 44 (FIXME 0167 amendment): writes targeting
    // `current_module` route through this RefCell; writes to other modules
    // (e.g., cross-module trait-impl writes per Decision 0045) fall through
    // to live unchanged. This is Wave 3b-2c.1's write-redirection plumbing
    // — it makes the existing `Cluster` mode actually stage instead of
    // leaking writes to live.
    let staging_cell: Option<RefCell<&mut SymbolTable<C, L>>> = match ctx {
        ClusterContext::Cluster { staging, .. } => {
            // Reborrow the orchestrator's `&mut SymbolTable` into a fresh
            // mutable reference scoped to this call frame, then wrap.
            let reborrow: &mut SymbolTable<C, L> = staging;
            Some(RefCell::new(reborrow))
        }
        ClusterContext::Live { .. } => None,
    };

    // Construct the working env. In cluster mode, route writes targeting
    // `current_module` to staging via the RefCell. Reads via
    // `current_symbol_table` continue to hit live (intra-cluster forward-ref
    // visibility through staging is read-union follow-up).
    let env = match &staging_cell {
        Some(cell) => TypeCheckEnv::<C, L>::new_with_staging(
            symbol_tables,
            &next_id,
            current_module.clone(),
            cell,
        ),
        None => TypeCheckEnv::<C, L>::new(symbol_tables, &next_id),
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
            env.advance_next_id_past_table(&*guard);
        }
    }

    let mut state = CheckState::new(current_module.clone());
    let mut accumulator = ModuleCheckAccumulator::new();

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
            .map_err(map_cranelisp_error)?;
        env.merge_form_result(&current_module, &mut state, &mut accumulator, result);
    }

    // Register default method defns generated during Pass 1 TraitImpl
    // processing. These need Pass 1 signature registration too.
    let defaults: Vec<Defn> = std::mem::take(&mut accumulator.default_method_defns);
    for defn in &defaults {
        let form = TopLevel::Defn(defn.clone());
        let result = env
            .check_form(&current_module, &form, CheckPass::Register, &mut state, &mut accumulator)
            .map_err(map_cranelisp_error)?;
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
            .map_err(map_cranelisp_error)?;
        env.merge_form_result(&current_module, &mut state, &mut accumulator, result);
    }

    // Check bodies of default method defns too.
    let defaults_for_body: Vec<Defn> = accumulator.default_method_defns.clone();
    for defn in &defaults_for_body {
        let form = TopLevel::Defn(defn.clone());
        let result = env
            .check_form(&current_module, &form, CheckPass::CheckBody, &mut state, &mut accumulator)
            .map_err(map_cranelisp_error)?;
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
        .map_err(map_cranelisp_error)?;

    Ok(())
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
            // `ParsedEntry::TypeDef::type_params` is `Vec<TypeName>`;
            // `TopLevel::TypeDef` expects `Vec<Symbol>`. Reuse underlying string.
            let type_params: Vec<Symbol> =
                type_params.into_iter().map(|t| Symbol::from(t.as_ref())).collect();
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
        ConstructorDef, DefKind, DefnVariant, Expr, FieldDef, ModuleEntry, Span, TraitDecl,
        TraitImpl, TypeExpr, TypeName, Visibility,
    };
    use std::sync::Arc;

    fn module_path() -> ModuleFullPath {
        ModuleFullPath::from("test_form_mod")
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
                param_annotations: vec![],
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
                trait_name: cranelisp_types::TraitName::from(trait_name),
                target_type: TypeName::from(type_name),
                type_args: vec![],
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
                type_expr: TypeExpr::Named(TypeName::from("a")),
            }],
            span: Span::SYNTHETIC,
        }
    }

    /// Single-defn round trip: Pass 1 registers, Pass 2 body-checks, the
    /// staging Def has Pass-2 annotations on `ast`.
    #[test]
    fn check_forms_single_defn_round_trip() {
        let modules = modules();
        let mut ctx: ClusterContext<'_, (), ()> = ClusterContext::live(&modules, module_path());
        let parsed = vec![one_variant_defn("solo")];
        check_forms::<(), ()>(parsed, &mut ctx, &modules).expect("clean check_forms");

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

    /// Multi-form forward-reference: two defns where the second body
    /// references the first. Both signatures must register in Pass 1 before
    /// any body checks in Pass 2 — this is the Pass-1-to-Pass-2 state
    /// threading that pre-S66's two-function split broke.
    #[test]
    fn check_forms_forward_reference_works() {
        let modules = modules();
        let mut ctx: ClusterContext<'_, (), ()> = ClusterContext::live(&modules, module_path());

        // first: () -> Int = 0
        // second: () -> Int = first  (calls first)
        let first = one_variant_defn("first");
        let second = ParsedEntry::Def {
            name: Symbol::from("second"),
            variants: vec![DefnVariant {
                params: vec![],
                param_annotations: vec![],
                body: Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("first"),
                        span: Span::SYNTHETIC,
                        inferred_type: None,
                    }),
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
        check_forms::<(), ()>(parsed, &mut ctx, &modules).expect("clean check_forms");

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
        let mut ctx: ClusterContext<'_, (), ()> = ClusterContext::live(&modules, module_path());
        let parsed = vec![one_variant_defn("twopass")];
        // Pre-S66: this would fail with "missing type vars" because Pass 1
        // and Pass 2 ran in separate calls with separate accumulators.
        // Post-S66: the accumulator persists; this succeeds.
        check_forms::<(), ()>(parsed, &mut ctx, &modules)
            .expect("state threading should keep type vars alive across passes");
    }

    /// Mixed cluster: Defn → TypeDef → TraitDecl → TraitImpl → Macro all in
    /// one call. Macro entries are filtered out (handled at the orchestrator
    /// boundary); the rest land on the staging table.
    #[test]
    fn check_forms_handles_mixed_form_cluster() {
        let modules = modules();
        let mut ctx: ClusterContext<'_, (), ()> = ClusterContext::live(&modules, module_path());
        let parsed = vec![
            empty_typedef("MyT"),
            empty_traitdecl("MyTr"),
            empty_traitimpl("MyTr", "MyT"),
            one_variant_defn("noargs"),
            macro_entry("m"),
            constructor_entry(),
        ];
        let r = check_forms::<(), ()>(parsed, &mut ctx, &modules);
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
        let mut ctx: ClusterContext<'_, (), ()> =
            ClusterContext::cluster(&modules, &mut staging, module_path());
        let parsed = vec![one_variant_defn("clustered")];
        let r = check_forms::<(), ()>(parsed, &mut ctx, &modules);
        assert!(r.is_ok(), "cluster-mode check_forms returns structured Result: {r:?}");
    }

    /// Wave 3b-2c.1 acceptance test: in `ClusterContext::Cluster` mode,
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
            let mut ctx: ClusterContext<'_, (), ()> =
                ClusterContext::cluster(&modules, &mut staging, module_path());
            let parsed = vec![one_variant_defn("staged_defn")];
            check_forms::<(), ()>(parsed, &mut ctx, &modules)
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

    /// Wave 3b-2c.3 acceptance test (FIXME 0179): in `ClusterContext::Cluster`
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
            let mut ctx: ClusterContext<'_, (), ()> =
                ClusterContext::cluster(&modules, &mut staging, module_path());
            // first: () -> Int = 0
            // second: () -> Int = first  (calls first)
            let first = one_variant_defn("first");
            let second = ParsedEntry::Def {
                name: Symbol::from("second"),
                variants: vec![DefnVariant {
                    params: vec![],
                    param_annotations: vec![],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("first"),
                            span: Span::SYNTHETIC,
                            inferred_type: None,
                        }),
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
            check_forms::<(), ()>(parsed, &mut ctx, &modules).expect(
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
        let mut ctx: ClusterContext<'_, (), ()> = ClusterContext::live(&modules, module_path());
        let parsed = vec![one_variant_defn("livewrite")];
        check_forms::<(), ()>(parsed, &mut ctx, &modules).expect("live mode");
        let guard = modules.get(&module_path()).expect("module exists");
        assert!(guard.get("livewrite").is_some());
    }

    /// Pass 2 failure: the first error short-circuits the loop. Earlier
    /// forms' Pass 1 registrations may have landed (atomicity is the
    /// orchestrator's responsibility — the caller discards staging on Err).
    #[test]
    fn check_forms_macro_only_is_noop() {
        let modules = modules();
        let mut ctx: ClusterContext<'_, (), ()> = ClusterContext::live(&modules, module_path());
        let parsed = vec![macro_entry("m"), constructor_entry()];
        let r = check_forms::<(), ()>(parsed, &mut ctx, &modules);
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
                params: vec![Symbol::from("x")],
                param_annotations: vec![None],
                body: Expr::Var {
                    name: Symbol::from("x"),
                    span: Span::new(11, 12),
                    inferred_type: None,
                },
                span: Span::new(10, 13),
            }],
            visibility: Visibility::Private,
            docstring: None,
            span: Span::new(0, 14),
        };
        {
            let mut ctx: ClusterContext<'_, (), ()> =
                ClusterContext::live(&modules, module_path());
            check_forms::<(), ()>(vec![id_defn], &mut ctx, &modules)
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
                param_annotations: vec![],
                body: Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("id"),
                        span: Span::new(101, 103),
                        inferred_type: None,
                    }),
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
        let mut ctx2: ClusterContext<'_, (), ()> =
            ClusterContext::live(&modules, module_path());
        check_forms::<(), ()>(vec![caller_defn], &mut ctx2, &modules)
            .expect("call 2: monomorphise (id 7) — must not overflow");

        // Assert: `id$Int` mono entry is registered in live.
        let guard = modules.get(&module_path()).expect("module exists");
        assert!(
            guard.get("id$Int").is_some(),
            "id$Int should be registered after call 2 mono"
        );
    }
}
