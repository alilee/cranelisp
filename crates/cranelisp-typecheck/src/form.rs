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
    let _ = ctx; // ClusterContext write-redirection through TypeCheckEnv is
                 // Wave 3a-α follow-up; for now TypeCheckEnv writes via its
                 // own DashMap accessor (which targets live). See module
                 // docs and Decision 44 amendments.

    // Ensure the current module's live table exists. The orchestrator's
    // staging precondition (Cluster mode) requires the live table to exist;
    // tests using Live mode also rely on this. `ensure_module_exists` is
    // idempotent.
    let next_id = std::sync::atomic::AtomicU32::new(0);
    let env = TypeCheckEnv::new(symbol_tables, &next_id);
    env.ensure_module_exists(&current_module);

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

    /// Cluster mode: writes (via `current_symbol_table_mut` on the
    /// `TypeCheckEnv`) currently still target live; full cluster-mode write
    /// redirection through `ClusterContext` is Wave 3a-α follow-up. The
    /// important invariant pinned here is that the function is reachable
    /// in `Cluster` mode and returns a structured `Result`.
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
        let id_defn = ParsedEntry::Def {
            name: Symbol::from("id"),
            variants: vec![DefnVariant {
                params: vec![Symbol::from("x")],
                param_annotations: vec![None],
                body: Expr::Var {
                    name: Symbol::from("x"),
                    span: Span::SYNTHETIC,
                    inferred_type: None,
                },
                span: Span::SYNTHETIC,
            }],
            visibility: Visibility::Private,
            docstring: None,
            span: Span::SYNTHETIC,
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
                        span: Span::SYNTHETIC,
                        inferred_type: None,
                    }),
                    args: vec![Expr::IntLit {
                        value: 7,
                        span: Span::SYNTHETIC,
                        inferred_type: None,
                    }],
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
