use super::*;
use cranelisp_types::{
    Binding, CallableArmId, CallableOrigin, ConstructorDef, Decl, Defn, DefnVariant, Expr,
    FieldDef, Life, ModuleFullPath, Span, Symbol, TraitImpl, TypeExpr, TypeName, TypeRecord,
    Visibility,
};
use dashmap::DashMap;
use std::sync::Arc;

fn module_path() -> ModuleFullPath {
    ModuleFullPath::from("test_form_mod")
}

fn no_aliases() -> ModuleAliases {
    ModuleAliases::new()
}

/// Empty prelude-fallback map ⇒ every module's fallback bit is OFF, matching
/// the no-prelude unit-test envs. S78 §2.7.3: "Test call sites pass
/// `&PreludeFallback::default()` (empty ⇒ all-OFF)."
fn no_fallback() -> PreludeFallback {
    PreludeFallback::default()
}

fn modules() -> Arc<DashMap<ModuleFullPath, SymbolTable<(), ()>>> {
    let m: DashMap<ModuleFullPath, SymbolTable<(), ()>> = DashMap::new();
    m.insert(
        module_path(),
        SymbolTable::<(), ()>::new_with_params(module_path()),
    );
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

fn polymorphic_identity(name: &str) -> ParsedEntry {
    ParsedEntry::Def {
        name: Symbol::from(name),
        variants: vec![DefnVariant {
            params: vec![(Symbol::from("x"), None)],
            body: Expr::var(Symbol::from("x"), Span::new(20, 21)),
            span: Span::new(10, 22),
        }],
        visibility: Visibility::Private,
        docstring: None,
        span: Span::new(1, 23),
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

fn minimal_traitdecl(name: &str) -> ParsedEntry {
    ParsedEntry::TraitDecl {
        decl: crate::traits::test_helpers::parse_trait_decl(&format!(
            "(deftrait {name} (identity [x] self))"
        )),
    }
}

fn minimal_traitimpl(trait_name: &str, type_name: &str) -> ParsedEntry {
    ParsedEntry::TraitImpl {
        impl_: TraitImpl {
            head_con_var: None,
            trait_name: cranelisp_types::TraitRef::new(
                None,
                cranelisp_types::TraitName::from(trait_name),
            ),
            target: cranelisp_types::TypeExpr::Named(cranelisp_types::TypeRef::new(
                None,
                TypeName::from(type_name),
            )),
            type_constraints: vec![],
            methods: vec![Defn {
                name: Symbol::from("identity"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![(Symbol::from("x"), None)],
                    body: Expr::var(Symbol::from("x"), Span::new(120, 121)),
                    span: Span::new(110, 122),
                }],
                visibility: Visibility::Private,
                span: Span::new(100, 123),
            }],
            span: Span::new(90, 124),
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
    check_forms::<(), ()>(parsed, &mut ctx, &modules, &no_aliases(), &no_fallback())
        .expect("clean check_forms");

    let guard = modules.get(&module_path()).expect("module exists");
    let entry = guard.get("solo").expect("solo registered");
    let callable = entry.callable().expect("solo is callable");
    assert!(matches!(
        callable.arm.life,
        Life::Concrete { ast: Some(_), .. }
    ));
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
        guard
            .install_binding(
                Symbol::from("Color"),
                Binding::new(
                    Decl::Type(TypeRecord::Defined {
                        info: TypeDefInfo {
                            name: FQTypeName::new(module_path(), TypeName::from("Color")),
                            type_params: vec![],
                            constructors: vec![],
                        },
                        docstring: None,
                    }),
                    Visibility::Public,
                ),
            )
            .unwrap();
    }

    let mut ctx: SymbolTableAccess<'_, (), ()> = SymbolTableAccess::live(&modules, module_path());

    // Positive: a reachable ADT name resolves to its ADT type.
    let color = TypeExpr::Named(TypeRef::new(None, TypeName::from("Color")));
    let ty = check_type_expr::<(), ()>(
        &color,
        &mut ctx,
        &modules,
        &no_aliases(),
        &no_fallback(),
        &module_path(),
        Span::SYNTHETIC,
    )
    .expect("Color resolves");
    assert_eq!(
        ty,
        Type::ADT(
            FQTypeName::new(module_path(), TypeName::from("Color")),
            vec![]
        )
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
        &no_fallback(),
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
        &no_fallback(),
        &module_path(),
        Span::SYNTHETIC,
    )
    .expect_err("unknown type name must be a CheckError");
    assert!(matches!(err, CheckError::TypeError { .. }));
}

/// TX-10 (FIXME 0590 Step A): the platform-sig `check_type_expr` mints each
/// free type-var name on first sight (replacing the deleted
/// `collect_type_var_ids` pre-walk). The mint-on-miss must reproduce the
/// pre-walk's shared ids: two occurrences of `a` in one sig co-refer to ONE
/// id, while `a` and `b` stay DISTINCT.
// spec: spec/03-types.md §3.3 — free type-var co-reference within one sig
#[test]
fn check_type_expr_free_var_coreference_and_distinctness() {
    use cranelisp_types::Type;

    let modules = modules();
    let mut ctx: SymbolTableAccess<'_, (), ()> = SymbolTableAccess::live(&modules, module_path());

    // (Fn [a b a] b): the two `a` share one id; `a` and `b` are distinct.
    let sig = TypeExpr::FnType(
        vec![
            TypeExpr::TypeVar(Symbol::from("a")),
            TypeExpr::TypeVar(Symbol::from("b")),
            TypeExpr::TypeVar(Symbol::from("a")),
        ],
        Box::new(TypeExpr::TypeVar(Symbol::from("b"))),
    );
    let ty = check_type_expr::<(), ()>(
        &sig,
        &mut ctx,
        &modules,
        &no_aliases(),
        &no_fallback(),
        &module_path(),
        Span::SYNTHETIC,
    )
    .expect("free-var sig resolves");
    match ty {
        Type::Fn(params, ret) => {
            assert_eq!(params.len(), 3);
            assert!(matches!(params[0], Type::Var(_)));
            assert_eq!(params[0], params[2], "both `a` occurrences share one id");
            assert_eq!(params[1], *ret, "both `b` occurrences share one id");
            assert_ne!(params[0], params[1], "`a` and `b` must be distinct ids");
        }
        other => panic!("expected Fn type, got {other:?}"),
    }

    // A `/`-qualified name is a module-qualified reference, never a var, so
    // it does NOT mint — it falls to a resolution error (F2/0589).
    let qual = TypeExpr::TypeVar(Symbol::from("user/int"));
    let err = check_type_expr::<(), ()>(
        &qual,
        &mut ctx,
        &modules,
        &no_aliases(),
        &no_fallback(),
        &module_path(),
        Span::SYNTHETIC,
    )
    .expect_err("a `/`-qualified TypeVar must not mint");
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
    check_forms::<(), ()>(parsed, &mut ctx, &modules, &no_aliases(), &no_fallback())
        .expect("clean check_forms");

    let guard = modules.get(&module_path()).expect("module exists");
    assert!(guard.get("first").is_some(), "first registered");
    assert!(guard.get("second").is_some(), "second registered");
}

/// Pass 1 → Pass 2 state threading regression test. Pre-S66 the
/// two-function shape created a fresh `ModuleCheckAccumulator` per call,
/// so Pass 1's registered signature facts did not flow to Pass 2. The
/// single-function
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
    check_forms::<(), ()>(parsed, &mut ctx, &modules, &no_aliases(), &no_fallback())
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
        minimal_traitdecl("MyTr"),
        minimal_traitimpl("MyTr", "MyT"),
        one_variant_defn("noargs"),
        macro_entry("m"),
        constructor_entry(),
    ];
    let r = check_forms::<(), ()>(parsed, &mut ctx, &modules, &no_aliases(), &no_fallback());
    // The TypeDef + TraitDecl + TraitImpl + Defn registrations should succeed.
    // Macros and constructors are no-ops at this surface. Trait and impl both
    // carry a method because spec/07-traits.md §7.1 requires `method_sig+`.
    assert!(r.is_ok(), "mixed cluster should typecheck: {r:?}");

    let guard = modules.get(&module_path()).expect("module exists");
    // Defn registered
    assert!(guard.get("noargs").is_some(), "Defn registered");
    // TypeDef registered (stored under Symbol::from(TypeName) per
    // `register_type_def` in adt.rs).
    assert!(
        guard.get("MyT").and_then(Binding::type_def_info).is_some(),
        "TypeDef registered with its type facet"
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
    let r = check_forms::<(), ()>(parsed, &mut ctx, &modules, &no_aliases(), &no_fallback());
    assert!(
        r.is_ok(),
        "cluster-mode check_forms returns structured Result: {r:?}"
    );
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
        guard.all_symbols().map(|(name, _)| name.clone()).collect()
    };

    let mut staging = SymbolTable::<(), ()>::new_with_params(module_path());
    {
        let mut ctx: SymbolTableAccess<'_, (), ()> =
            SymbolTableAccess::cluster(&modules, &mut staging, module_path());
        let parsed = vec![one_variant_defn("staged_defn")];
        check_forms::<(), ()>(parsed, &mut ctx, &modules, &no_aliases(), &no_fallback())
            .expect("cluster mode check_forms succeeds");
    }

    // Live is byte-identical (key set unchanged) — the write redirect to
    // staging worked. Pre-fix this assertion would fail because writes
    // leaked to live.
    let live_keys_after: std::collections::HashSet<Symbol> = {
        let guard = modules.get(&module_path()).expect("live module exists");
        guard.all_symbols().map(|(name, _)| name.clone()).collect()
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
    assert!(staging.get("staged_defn").unwrap().callable().is_some());
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
        check_forms::<(), ()>(parsed, &mut ctx, &modules, &no_aliases(), &no_fallback())
            .expect("cluster-mode forward reference must resolve via staging read union");
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
    check_forms::<(), ()>(parsed, &mut ctx, &modules, &no_aliases(), &no_fallback())
        .expect("live mode");
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
    let r = check_forms::<(), ()>(parsed, &mut ctx, &modules, &no_aliases(), &no_fallback());
    assert!(
        r.is_ok(),
        "macro-only / constructor-only cluster is a no-op: {r:?}"
    );
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
        check_forms::<(), ()>(
            vec![id_defn],
            &mut ctx,
            &modules,
            &no_aliases(),
            &no_fallback(),
        )
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
    let mut ctx2: SymbolTableAccess<'_, (), ()> = SymbolTableAccess::live(&modules, module_path());
    check_forms::<(), ()>(
        vec![caller_defn],
        &mut ctx2,
        &modules,
        &no_aliases(),
        &no_fallback(),
    )
    .expect("call 2: monomorphise (id 7) — must not overflow");

    // Assert: the full-signature `id` mono entry is registered in live.
    let id_int = "(test_form_mod/id [primitives/Int] primitives/Int)";
    let guard = modules.get(&module_path()).expect("module exists");
    assert!(
        guard.get(id_int).is_some(),
        "{id_int} should be registered after call 2 mono"
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
// spec: design/typecheck/checked-body-publication.md §6;
//   tests/plan/s121-test-plan.md §3.8 LC-2.
#[test]
fn gap_on_missing_module_plain() {
    let modules = modules();
    let mut ctx: SymbolTableAccess<'_, (), ()> = SymbolTableAccess::live(&modules, module_path());
    // Body references `some.mod/thing`; `some.mod` is not in `modules`.
    let parsed = vec![defn_referencing("uses_missing", "some.mod/thing")];
    let r = check_forms::<(), ()>(parsed, &mut ctx, &modules, &no_aliases(), &no_fallback());
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

    // Cluster-mode retry reconstructs every attempt-local carrier, including
    // the body ledger. The first staging table is discarded with the Gap; the
    // same source is then checked from the top against a fresh staging table
    // after the dependency becomes available.
    let cluster_modules = crate::form::tests::modules();
    let retry_forms = vec![defn_referencing("uses_missing", "some.mod/thing")];
    let mut failed_staging = SymbolTable::<(), ()>::new_with_params(module_path());
    {
        let mut failed_ctx =
            SymbolTableAccess::cluster(&cluster_modules, &mut failed_staging, module_path());
        assert!(matches!(
            check_forms::<(), ()>(
                retry_forms.clone(),
                &mut failed_ctx,
                &cluster_modules,
                &no_aliases(),
                &no_fallback(),
            ),
            Err(CheckError::Gap(
                cranelisp_types::ResolutionGap::SymbolTypechecked(_)
            ))
        ));
    }
    assert!(
        cluster_modules
            .get(&module_path())
            .unwrap()
            .get("uses_missing")
            .is_none(),
        "the failed cluster attempt must not publish its registered body"
    );
    drop(failed_staging);

    seed_module(&cluster_modules, "some.mod", "thing");
    let mut retry_staging = SymbolTable::<(), ()>::new_with_params(module_path());
    {
        let mut retry_ctx =
            SymbolTableAccess::cluster(&cluster_modules, &mut retry_staging, module_path());
        check_forms::<(), ()>(
            retry_forms,
            &mut retry_ctx,
            &cluster_modules,
            &no_aliases(),
            &no_fallback(),
        )
        .expect("fresh attempt rebuilds and publishes the retried body once");
    }
    let callable = retry_staging
        .get("uses_missing")
        .and_then(Binding::callable)
        .expect("retry publishes exactly one callable");
    assert!(matches!(
        callable.arm.life,
        Life::Concrete { ast: Some(_), .. }
    ));
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
        cranelisp_types::module_alias_key(&module_path(), "r"),
        cranelisp_types::ModuleAliasEntry::new(
            ModuleFullPath::from("real.target"),
            Visibility::Public,
            Span::SYNTHETIC,
        ),
    );

    let mut ctx: SymbolTableAccess<'_, (), ()> = SymbolTableAccess::live(&modules, module_path());
    // Body references `r/thing`; `r` is an alias to `real.target` which is
    // absent. The gap must carry the RESOLVED target.
    let parsed = vec![defn_referencing("uses_alias", "r/thing")];
    let r = check_forms::<(), ()>(parsed, &mut ctx, &modules, &aliases, &no_fallback());
    match r {
        Err(CheckError::Gap(cranelisp_types::ResolutionGap::SymbolTypechecked(fq))) => {
            assert_eq!(
                fq.module.as_ref(),
                "real.target",
                "gap module must be the ALIAS-RESOLVED target, not the bare alias"
            );
            assert_eq!(fq.symbol.as_ref(), "thing", "gap symbol is the local name");
        }
        other => {
            panic!("expected Gap(SymbolTypechecked) with alias-resolved target, got {other:?}")
        }
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
    use cranelisp_types::{CallableTarget, ResolvedCall};

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
        check_forms::<(), ()>(
            vec![multi_f],
            &mut ctx,
            &modules,
            &no_aliases(),
            &no_fallback(),
        )
        .expect("cluster 1 (multi-sig defn) checks clean");
    }
    // Sanity: the live base entry is `Overloaded` with both variants.
    {
        let guard = modules.get(&module_path()).expect("module exists");
        match &guard.get("f").expect("f base registered").declaration {
            Decl::Overloaded(declaration) => {
                assert_eq!(declaration.arms.len(), 2, "both clauses recorded on base");
            }
            other => panic!("expected overloaded declaration, got {other:?}"),
        }
    }

    // Cluster 2 (a FRESH `CheckState`): a caller body `(f 5)`. The
    // arity-1 variant is a genuinely-polymorphic clause `([x] x)` — a
    // slot-less template owned by arm 0 (§11.4). `5` selects it
    // (arity 1), and the drain routes the template clause through
    // monomorphisation (§11.4 step 4), minting the concrete instance
    // `f__arm0$Int` and dispatching to it — NOT to the slot-less template.
    //
    // Distinct (non-synthetic) spans: `monomorphise_call` pins the CALL
    // span's return type, which under all-`SYNTHETIC` spans collides with the
    // caller's own recorded `(Fn ..)` type (a harness artefact, not a real
    // program shape).
    let call_span = Span::new(100, 110);
    let caller = ParsedEntry::Def {
        name: Symbol::from("caller"),
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::Apply {
                callee: Box::new(Expr::var(Symbol::from("f"), Span::new(101, 102))),
                args: vec![Expr::IntLit {
                    value: 5,
                    span: Span::new(103, 104),
                    inferred_type: None,
                }],
                span: call_span,
                resolved_call: None,
                inferred_type: None,
            },
            span: Span::new(90, 120),
        }],
        visibility: Visibility::Private,
        docstring: None,
        span: Span::new(85, 121),
    };
    {
        let mut ctx: SymbolTableAccess<'_, (), ()> =
            SymbolTableAccess::live(&modules, module_path());
        check_forms::<(), ()>(
            vec![caller],
            &mut ctx,
            &modules,
            &no_aliases(),
            &no_fallback(),
        )
        .expect("cluster 2 (caller body) checks clean across clusters");
    }

    // The caller's annotated AST must carry a `SigDispatch` to the MONO
    // INSTANCE of the arity-1 poly clause (`…/f__arm0$Int`) on the `(f 5)`
    // Apply — pre-S112 this resolved to the bodyless base; pre-§11.4 to the
    // slot-less private checking label.
    let guard = modules.get(&module_path()).expect("module exists");
    let caller_entry = guard.get("caller").expect("caller registered");
    let ast = match &caller_entry.callable().expect("caller callable").arm.life {
        Life::Concrete { ast: Some(ast), .. } => ast,
        other => panic!("expected caller with annotated ast, got {other:?}"),
    };
    let resolved = match &ast.body {
        Expr::Apply {
            resolved_call: Some(rc),
            ..
        } => rc.as_ref(),
        other => panic!("expected annotated Apply body, got {other:?}"),
    };
    match resolved {
        ResolvedCall::SigDispatch {
            target: CallableTarget::Binding(owner),
        } => {
            let arm_target = CallableTarget::OverloadArm {
                owner: FQSymbol {
                    module: module_path(),
                    symbol: Symbol::from("f"),
                },
                arm: CallableArmId::from_ordinal(0).expect("arm 0 is representable"),
            };
            let expected = cranelisp_types::concrete_callable_key(
                &FQSymbol {
                    module: module_path(),
                    symbol: Symbol::from("f"),
                },
                &cranelisp_types::ConcreteType::Fn(
                    vec![cranelisp_types::ConcreteType::Int],
                    Box::new(cranelisp_types::ConcreteType::Int),
                ),
            )
            .unwrap();
            assert_eq!(
                expected.as_ref(),
                "(test_form_mod/f [primitives/Int] primitives/Int)"
            );
            assert_eq!(owner.module, module_path());
            assert_eq!(owner.symbol, expected);
            let instance = guard
                .get(owner.symbol.as_ref())
                .expect("typed overload-arm instance is installed");
            assert!(matches!(
                &instance.callable().expect("instance callable").arm.life,
                Life::Concrete {
                    minted_from: Some(link),
                    ..
                } if link.template == arm_target
            ));
        }
        other => panic!("expected SigDispatch across clusters, got {other:?}"),
    }
}

/// A field accessor whose bare spelling is already a user binding coexists
/// with it: the cluster checks clean with no warning, the user `v` keeps its
/// binding, and the canonical `Box.v` is exposed under the same bare spelling
/// as a further candidate (`design/typecheck/fixme-0365-field-accessor-dotted.md`
/// §1.6.2).
///
/// Fixture: pre-register `v` as a user `defn`, then submit the **product**
/// type `(deftype Box [:Int v])` (single ctor, ctor-name == type-name) in
/// the same cluster.
///
/// spec: spec/05-definitions.md §5.2.6, spec/08-modules.md §8.6.5 — a shared
/// bare spelling is a candidate set resolved at each use.
#[test]
fn check_forms_preserves_binding_and_accessor_candidate() {
    use cranelisp_types::Type;

    let modules = modules();
    // Seed `Int` as an intrinsic type so the `:Int` field resolves in the
    // bare test module (the fixture seeds no scalar type names).
    {
        let mut guard = modules.get_mut(&module_path()).expect("module exists");
        guard
            .install_binding(
                Symbol::from("Int"),
                Binding::new(
                    Decl::Type(TypeRecord::Intrinsic {
                        ty: Type::Int,
                        docstring: None,
                    }),
                    Visibility::Public,
                ),
            )
            .unwrap();
    }

    // Pre-register a user binding named `v` — the accessor `v` synthesised
    // for `Box`'s field will collide with it (NON-accessor collision).
    let v_defn = one_variant_defn("v");
    // Product type `Box` with a single typed field `v` (ctor name == type
    // name ⇒ product ⇒ accessors are synthesised).
    let box_typedef = ParsedEntry::TypeDef {
        name: TypeName::from("Box"),
        type_params: vec![],
        constructors: vec![ConstructorDef {
            name: Symbol::from("Box"),
            docstring: None,
            fields: vec![FieldDef {
                name: Symbol::from("v"),
                type_expr: TypeExpr::Named(cranelisp_types::TypeRef::new(
                    None,
                    TypeName::from("Int"),
                )),
                span: Span::SYNTHETIC,
            }],
            span: Span::SYNTHETIC,
        }],
        visibility: Visibility::Private,
        docstring: None,
        span: Span::SYNTHETIC,
    };

    let mut ctx: SymbolTableAccess<'_, (), ()> = SymbolTableAccess::live(&modules, module_path());
    let warnings = check_forms::<(), ()>(
        vec![v_defn, box_typedef],
        &mut ctx,
        &modules,
        &no_aliases(),
        &no_fallback(),
    )
    .expect("cluster with an accessor collision still checks clean")
    .warnings;

    assert!(
        warnings.is_empty(),
        "coexisting candidates are not a collision"
    );

    // The local definition remains canonical while `Box.v` is exposed under
    // the same spelling for type-directed selection.
    let guard = modules.get(&module_path()).expect("module exists");
    let v = guard
        .get("v")
        .and_then(Binding::callable)
        .expect("v binding survives");
    assert!(matches!(v.origin, CallableOrigin::Plain));
    let candidates = guard.name_candidates(&Symbol::from("v"));
    assert_eq!(candidates.len(), 2);
    assert!(
        candidates
            .iter()
            .any(|candidate| candidate.source.symbol == "Box.v")
    );
}

// =====================================================================
// §8.6.4 module-scope candidate registration at the shared `check_forms`
// seam. A local definition over an imported, exported or prelude-provided
// spelling is accepted and joins that spelling's candidates; these pin the
// mode-uniform acceptance at the seam both REPL/Additive and batch/Replace
// call.
// =====================================================================

fn seed_module(modules: &DashMap<ModuleFullPath, SymbolTable<(), ()>>, module: &str, name: &str) {
    let m = ModuleFullPath::from(module);
    modules
        .entry(m.clone())
        .or_insert_with(|| SymbolTable::<(), ()>::new_with_params(m.clone()));
    modules
        .get_mut(&m)
        .unwrap()
        .install_host_promised(
            Symbol::from(name),
            cranelisp_types::Scheme {
                type_vars: vec![],
                constraints: std::collections::HashMap::new(),
                ty: cranelisp_types::Type::Int,
            },
            vec![],
            None,
            0,
            Visibility::Public,
        )
        .unwrap();
}

fn expose_import(
    table: &mut SymbolTable<(), ()>,
    local_name: &str,
    src_module: &str,
    name: &str,
    vis: Visibility,
) {
    table
        .expose_candidate(
            Symbol::from(local_name),
            cranelisp_types::FQSymbol {
                module: ModuleFullPath::from(src_module),
                symbol: Symbol::from(name),
            },
            vis,
        )
        .unwrap();
}

/// A `defn` over a name in scope via an explicit `(import …)` is accepted;
/// the spelling then has two candidates (spec §8.6.4).
#[test]
fn def_over_import_candidate_is_allowed() {
    let modules = modules();
    seed_module(&modules, "util", "measure");
    expose_import(
        &mut modules.get_mut(&module_path()).unwrap(),
        "measure",
        "util",
        "measure",
        Visibility::Private,
    );

    let mut ctx: SymbolTableAccess<'_, (), ()> = SymbolTableAccess::live(&modules, module_path());
    check_forms::<(), ()>(
        vec![one_variant_defn("measure")],
        &mut ctx,
        &modules,
        &no_aliases(),
        &no_fallback(),
    )
    .expect("a local definition may coexist with an imported candidate");
    let guard = modules.get(&module_path()).unwrap();
    assert!(guard.get("measure").is_some());
    assert_eq!(guard.name_candidates(&Symbol::from("measure")).len(), 2);
}

/// A `defn` over a name in scope via an explicit `(export …)` is accepted on
/// the same terms as an import (spec §8.6.4).
#[test]
fn def_over_export_candidate_is_allowed() {
    let modules = modules();
    seed_module(&modules, "util", "measure");
    expose_import(
        &mut modules.get_mut(&module_path()).unwrap(),
        "measure",
        "util",
        "measure",
        Visibility::Public,
    );

    let mut ctx: SymbolTableAccess<'_, (), ()> = SymbolTableAccess::live(&modules, module_path());
    check_forms::<(), ()>(
        vec![one_variant_defn("measure")],
        &mut ctx,
        &modules,
        &no_aliases(),
        &no_fallback(),
    )
    .expect("a local definition may coexist with an exported candidate");
}

/// A `defn` over a PRELUDE-provided public name is accepted exactly as over
/// an explicit import — the prelude is an implicit import (spec §8.6.4).
#[test]
fn def_over_prelude_fallback_is_allowed() {
    let modules = modules();
    seed_module(&modules, "prelude", "gulp");
    let fallback = PreludeFallback::default();
    fallback.insert(module_path(), true); // implicit prelude ON

    let mut ctx: SymbolTableAccess<'_, (), ()> = SymbolTableAccess::live(&modules, module_path());
    check_forms::<(), ()>(
        vec![one_variant_defn("gulp")],
        &mut ctx,
        &modules,
        &no_aliases(),
        &fallback,
    )
    .expect("a local definition shadows the implicit prelude fallback");
}

/// A module redefining its OWN prior `Def` (home == current module) is an
/// ordinary redefinition — the seam must let it through.
#[test]
fn own_redefinition_allowed_at_seam() {
    let modules = modules();
    // First define `solo` (fresh — clean).
    {
        let mut ctx: SymbolTableAccess<'_, (), ()> =
            SymbolTableAccess::live(&modules, module_path());
        check_forms::<(), ()>(
            vec![one_variant_defn("solo")],
            &mut ctx,
            &modules,
            &no_aliases(),
            &no_fallback(),
        )
        .expect("first defn clean");
    }
    // Redefine it — own prior Def, must NOT be rejected as a collision.
    let mut ctx: SymbolTableAccess<'_, (), ()> = SymbolTableAccess::live(&modules, module_path());
    check_forms::<(), ()>(
        vec![one_variant_defn("solo")],
        &mut ctx,
        &modules,
        &no_aliases(),
        &no_fallback(),
    )
    .expect("redefining the module's OWN def must NOT be rejected");
}

/// A fresh name that the prelude does NOT provide compiles cleanly even with
/// the prelude-fallback bit ON (the §8.8.3 not-loading / fresh-name case).
#[test]
fn def_of_fresh_name_with_prelude_on_allowed() {
    let modules = modules();
    seed_module(&modules, "prelude", "gulp");
    let fallback = PreludeFallback::default();
    fallback.insert(module_path(), true);

    let mut ctx: SymbolTableAccess<'_, (), ()> = SymbolTableAccess::live(&modules, module_path());
    check_forms::<(), ()>(
        vec![one_variant_defn("unrelated")],
        &mut ctx,
        &modules,
        &no_aliases(),
        &fallback,
    )
    .expect("a fresh name the prelude does not provide is free to define");
}

/// MODE PARITY: `check_forms` has no mode parameter — REPL/Additive and
/// batch/Replace call the IDENTICAL function, so candidate registration is
/// structurally mode-uniform. This pins that both `ctx` variants both
/// sessions use — `Live` (Replace-analog) AND `Cluster`/staging
/// (Additive-analog) — accept the same def-over-import binding.
#[test]
fn def_over_import_candidate_acceptance_is_mode_uniform() {
    // Live (Replace-analog).
    {
        let modules = modules();
        seed_module(&modules, "util", "measure");
        expose_import(
            &mut modules.get_mut(&module_path()).unwrap(),
            "measure",
            "util",
            "measure",
            Visibility::Private,
        );
        let mut ctx: SymbolTableAccess<'_, (), ()> =
            SymbolTableAccess::live(&modules, module_path());
        check_forms::<(), ()>(
            vec![one_variant_defn("measure")],
            &mut ctx,
            &modules,
            &no_aliases(),
            &no_fallback(),
        )
        .expect("Live-mode def-over-import candidate must coexist");
    }
    // Cluster/staging (Additive-analog) — the import lives in live, the def
    // stages; the union view sees the import; the seam accepts identically.
    {
        let modules = modules();
        seed_module(&modules, "util", "measure");
        expose_import(
            &mut modules.get_mut(&module_path()).unwrap(),
            "measure",
            "util",
            "measure",
            Visibility::Private,
        );
        let mut staging = SymbolTable::<(), ()>::new_with_params(module_path());
        let mut ctx: SymbolTableAccess<'_, (), ()> =
            SymbolTableAccess::cluster(&modules, &mut staging, module_path());
        check_forms::<(), ()>(
            vec![one_variant_defn("measure")],
            &mut ctx,
            &modules,
            &no_aliases(),
            &no_fallback(),
        )
        .expect("Cluster-mode def-over-import candidate must coexist identically");
    }
}

// spec: 12-runtime §12.2 — GOT exhaustion is a diagnosed compile error at the
// `check_forms` boundary. GE-3 (CS-2) stopped at the `result::got_exhausted_error`
// helper; the testing MISS was the `map_cranelisp_error` boundary where the hole
// hid (I-1): the pre-fix catch-all Debug-dumped the `CodegenError` variant, so the
// exhaustion surfaced as `typecheck error: CodegenError {…}` rather than its clean
// located message. This pins the boundary surface: a genuine GOT-exhaustion
// `CodegenError` lifts to a `CheckError::TypeError` preserving message + location.
#[test]
fn got_exhaustion_renders_clean_diagnosed_message_at_check_forms_boundary() {
    use cranelisp_types::{GOT_TABLE_SIZE, LifecycleError, Scheme, SlotMintError, Type};
    use std::collections::HashMap;

    // Exhaust a real module GOT to obtain a genuine `GotExhausted`, then route it
    // through the SAME helper every fallible `allocate_got_slot` caller uses.
    let mut st: SymbolTable<(), ()> = SymbolTable::new(ModuleFullPath::from("proj.widget"));
    let scheme = Scheme {
        type_vars: vec![],
        constraints: HashMap::new(),
        ty: Type::Int,
    };
    for index in 0..GOT_TABLE_SIZE {
        st.install_extern(
            Symbol::from(format!("f{index}")),
            scheme.clone(),
            vec![],
            None,
            0,
            None,
            None,
            Visibility::Private,
        )
        .expect("within-bounds allocation");
    }
    let LifecycleError::SlotMint(SlotMintError::Exhausted(exhausted)) = st
        .install_extern(
            Symbol::from("overflow"),
            scheme,
            vec![],
            None,
            0,
            None,
            None,
            Visibility::Private,
        )
        .expect_err("GOT must be exhausted")
    else {
        panic!("expected exhausted slot mint")
    };
    let codegen_err = crate::result::got_exhausted_error(exhausted);

    // The `check_forms` boundary mapper must preserve the diagnosed text, not
    // Debug-dump the variant.
    match map_cranelisp_error(codegen_err) {
        CheckError::TypeError { message, .. } => {
            assert!(
                message.contains("proj.widget") && message.contains("GOT slot table exhausted"),
                "boundary surface renders the clean diagnosed message: {message}"
            );
            assert!(
                !message.contains("CodegenError"),
                "must NOT Debug-dump the variant: {message}"
            );
        }
        other => panic!("expected a located TypeError at the boundary, got {other:?}"),
    }
}

// A GOT-exhaustion `CodegenError` that COINCIDES with a still-pending cross-module
// resolution gap must surface as its diagnosed self, NOT be masked into
// `CheckError::Gap` (CS-2 widened the class flowing through `lift_error`; the gap
// carrier is the retry signal — a GOT exhaustion is terminal).
#[test]
fn lift_error_does_not_mask_codegen_error_as_gap_when_a_gap_is_pending() {
    use cranelisp_types::{CranelispError, FQSymbol, ResolutionGap};

    let mut state = CheckState::new(module_path());
    state.pending_gap = Some(ResolutionGap::SymbolTypechecked(FQSymbol {
        module: ModuleFullPath::from("some.mod"),
        symbol: Symbol::from("later"),
    }));

    let codegen_err = CranelispError::CodegenError {
        message: "GOT slot table exhausted for module 'proj.widget'".to_string(),
        location: ErrorLocation::from_span(Span::SYNTHETIC),
    };
    match lift_error(codegen_err, &state) {
        CheckError::TypeError { message, .. } => {
            assert!(
                message.contains("GOT slot table exhausted"),
                "terminal error preserved: {message}"
            );
        }
        CheckError::Gap(_) => panic!("a terminal CodegenError must NOT be masked into Gap"),
    }

    // A genuine not-found `TypeError` DOES still lift to Gap (the retry path is
    // unchanged for the resolution class).
    let type_err = CranelispError::TypeError {
        message: "undefined variable: later".to_string(),
        location: ErrorLocation::from_span(Span::SYNTHETIC),
    };
    assert!(
        matches!(lift_error(type_err, &state), CheckError::Gap(_)),
        "a not-found TypeError with a pending gap still lifts to Gap"
    );
}

// spec: design/typecheck/monomorphisation.md §3.8 M-1/M-2 — reload demands seed
// the existing mono engine, mint the ordinary concrete instance, and dedup a
// repeated seed without moving its slot.
#[test]
fn instantiate_demands_mints_and_deduplicates_existing_instance() {
    let modules = modules();
    let aliases = no_aliases();
    let fallback = no_fallback();
    let mut ctx: SymbolTableAccess<'_, (), ()> = SymbolTableAccess::live(&modules, module_path());
    check_forms::<(), ()>(
        vec![polymorphic_identity("reload-id")],
        &mut ctx,
        &modules,
        &aliases,
        &fallback,
    )
    .expect("template registration succeeds");

    let demand = MonoDemand::from_type_args(
        cranelisp_types::CallableTarget::Binding(cranelisp_types::FQSymbol {
            module: module_path(),
            symbol: Symbol::from("reload-id"),
        }),
        vec![cranelisp_types::ConcreteType::Int],
        Span::new(800, 810),
    );
    let template_scheme = modules
        .get(&module_path())
        .and_then(|table| {
            table
                .get("reload-id")
                .and_then(Binding::callable)
                .map(|callable| callable.arm.scheme.clone())
        })
        .unwrap();
    let instance_key = demand.instance_key(&template_scheme).unwrap();
    assert_eq!(
        instance_key.as_ref(),
        "(test_form_mod/reload-id [primitives/Int] primitives/Int)"
    );
    let result = instantiate_demands(
        vec![demand.clone()],
        &mut ctx,
        &modules,
        &aliases,
        &fallback,
    )
    .expect("concrete reload demand succeeds");
    assert!(result.warnings.is_empty());

    let first_slot = modules
        .get(&module_path())
        .and_then(|table| {
            table
                .get(instance_key.as_ref())
                .and_then(Binding::callable_got_slot)
        })
        .expect("the ordinary mono engine installs a concrete instance");
    {
        let table = modules.get(&module_path()).expect("module exists");
        let instance = table
            .get(instance_key.as_ref())
            .expect("the concrete instance remains installed");
        let entry_summary = instance
            .mode_summary()
            .expect("a freshly demanded instance receives an ownership summary");
        let view_summary = instance
            .codegen_view()
            .and_then(|view| view.mode_summary.as_ref())
            .expect("the codegen view receives the same ownership summary");
        assert_eq!(entry_summary, view_summary);
    }
    let again = instantiate_demands(
        vec![demand.clone()],
        &mut ctx,
        &modules,
        &aliases,
        &fallback,
    )
    .expect("an already-realized demand deduplicates");
    assert!(again.warnings.is_empty());
    let second_slot = modules
        .get(&module_path())
        .and_then(|table| {
            table
                .get(instance_key.as_ref())
                .and_then(Binding::callable_got_slot)
        })
        .expect("the deduplicated instance remains installed");
    assert_eq!(first_slot, second_slot);
}

// spec: design/typecheck/monomorphisation.md §3.8.6 — demand-triggered ownership
// publication obeys the same cluster staging boundary as the minted instance.
#[test]
fn instantiate_demands_infers_ownership_in_cluster_staging_only() {
    let modules = modules();
    let aliases = no_aliases();
    let fallback = no_fallback();
    let mut live_ctx: SymbolTableAccess<'_, (), ()> =
        SymbolTableAccess::live(&modules, module_path());
    check_forms::<(), ()>(
        vec![polymorphic_identity("reload-id")],
        &mut live_ctx,
        &modules,
        &aliases,
        &fallback,
    )
    .expect("template registration succeeds");

    let demand = MonoDemand::from_type_args(
        cranelisp_types::CallableTarget::Binding(cranelisp_types::FQSymbol {
            module: module_path(),
            symbol: Symbol::from("reload-id"),
        }),
        vec![cranelisp_types::ConcreteType::Int],
        Span::new(820, 830),
    );
    let template_scheme = modules
        .get(&module_path())
        .and_then(|table| {
            table
                .get("reload-id")
                .and_then(Binding::callable)
                .map(|callable| callable.arm.scheme.clone())
        })
        .unwrap();
    let instance_key = demand.instance_key(&template_scheme).unwrap();
    let (live_keys_before, live_template_before) = {
        let table = modules.get(&module_path()).expect("live module exists");
        (
            table
                .all_symbols()
                .map(|(name, _)| name.clone())
                .collect::<std::collections::HashSet<_>>(),
            format!("{:?}", table.get("reload-id")),
        )
    };

    let mut staging = SymbolTable::<(), ()>::new_with_params(module_path());
    {
        let mut ctx = SymbolTableAccess::cluster(&modules, &mut staging, module_path());
        instantiate_demands(
            vec![demand.clone()],
            &mut ctx,
            &modules,
            &aliases,
            &fallback,
        )
        .expect("cluster demand succeeds");
    }

    let table = modules.get(&module_path()).expect("live module exists");
    let live_keys_after = table
        .all_symbols()
        .map(|(name, _)| name.clone())
        .collect::<std::collections::HashSet<_>>();
    assert_eq!(live_keys_before, live_keys_after);
    assert_eq!(
        live_template_before,
        format!("{:?}", table.get("reload-id"))
    );
    assert!(
        table.get(instance_key.as_ref()).is_none(),
        "the demanded instance must not leak into live"
    );
    drop(table);

    let instance = staging
        .get(instance_key.as_ref())
        .expect("the demanded instance is published to staging");
    let entry_summary = instance
        .mode_summary()
        .expect("the staged instance receives an ownership summary");
    let view_summary = instance
        .codegen_view()
        .and_then(|view| view.mode_summary.as_ref())
        .expect("the staged codegen view receives the same ownership summary");
    assert_eq!(entry_summary, view_summary);
}

// spec: 03-types §3.6.3 — a map-free demand reconstructs result-only substitutions.
#[test]
fn instantiate_demands_result_context_and_malformed_length() {
    use cranelisp_types::{ConcreteType, Type};
    let modules = modules();
    let aliases = no_aliases();
    let fallback = no_fallback();
    let mut ctx = SymbolTableAccess::live(&modules, module_path());
    let mut definition = polymorphic_identity("g");
    if let ParsedEntry::Def { variants, .. } = &mut definition {
        variants[0].params.clear();
        variants[0].body = Expr::Lambda {
            params: vec![(Symbol::from("y"), None)],
            body: Box::new(unit_body()),
            span: Span::new(20, 40),
            inferred_type: None,
        };
    }
    check_forms(vec![definition], &mut ctx, &modules, &aliases, &fallback).unwrap();
    let template_scheme = modules
        .get(&module_path())
        .and_then(|table| {
            table
                .get("g")
                .and_then(Binding::callable)
                .map(|callable| callable.arm.scheme.clone())
        })
        .unwrap();
    let target = cranelisp_types::CallableTarget::Binding(cranelisp_types::FQSymbol {
        module: module_path(),
        symbol: Symbol::from("g"),
    });
    let malformed = MonoDemand::from_type_args(target.clone(), vec![], Span::SYNTHETIC);
    let result = instantiate_demands(
        vec![malformed.clone()],
        &mut ctx,
        &modules,
        &aliases,
        &fallback,
    )
    .unwrap();
    assert_eq!(result.warnings.len(), 1);
    assert!(malformed.instance_key(&template_scheme).is_err());
    assert!(
        !modules
            .get(&module_path())
            .unwrap()
            .all_symbols()
            .any(|(_, binding)| matches!(
                binding.callable().map(|callable| &callable.arm.life),
                Some(Life::Concrete { minted_from: Some(link), .. })
                    if link == &malformed.instance_link()
            ))
    );
    let mut slots = Vec::new();
    for ty in [ConcreteType::Int, ConcreteType::String] {
        let demand =
            MonoDemand::from_type_args(target.clone(), vec![ty.clone()], Span::new(100, 110));
        for _ in 0..2 {
            let result = instantiate_demands(
                vec![demand.clone()],
                &mut ctx,
                &modules,
                &aliases,
                &fallback,
            )
            .unwrap();
            assert!(result.warnings.is_empty(), "{:?}", result.warnings);
            let table = modules.get(&module_path()).unwrap();
            let instance_key = demand.instance_key(&template_scheme).unwrap();
            let binding = table.get(instance_key.as_ref()).unwrap();
            assert_eq!(
                binding.callable().unwrap().arm.scheme.ty,
                Type::Fn(
                    vec![],
                    Box::new(Type::Fn(vec![ty.to_type()], Box::new(Type::Int)))
                )
            );
            slots.push(binding.callable_got_slot().unwrap());
        }
    }
    assert_eq!(slots[0], slots[1]);
    assert_eq!(slots[2], slots[3]);
    assert_ne!(slots[0], slots[2]);
}

// design/typecheck/monomorphisation.md §3.8 M-3/M-4 — a stale root is a
// synthetic warning and does not truncate later valid roots.
#[test]
fn instantiate_demands_declines_stale_root_and_drains_remaining_roots() {
    let modules = modules();
    let aliases = no_aliases();
    let fallback = no_fallback();
    let mut ctx: SymbolTableAccess<'_, (), ()> = SymbolTableAccess::live(&modules, module_path());
    check_forms::<(), ()>(
        vec![polymorphic_identity("reload-id")],
        &mut ctx,
        &modules,
        &aliases,
        &fallback,
    )
    .expect("template registration succeeds");

    let stale = MonoDemand::from_type_args(
        cranelisp_types::CallableTarget::Binding(cranelisp_types::FQSymbol {
            module: module_path(),
            symbol: Symbol::from("removed"),
        }),
        vec![cranelisp_types::ConcreteType::Int],
        Span::new(700, 710),
    );
    let valid = MonoDemand::from_type_args(
        cranelisp_types::CallableTarget::Binding(cranelisp_types::FQSymbol {
            module: module_path(),
            symbol: Symbol::from("reload-id"),
        }),
        vec![cranelisp_types::ConcreteType::Bool],
        Span::new(720, 730),
    );
    let result = instantiate_demands(
        vec![stale, valid.clone()],
        &mut ctx,
        &modules,
        &aliases,
        &fallback,
    )
    .expect("a stale root is declined rather than failing the batch");
    assert_eq!(result.warnings.len(), 1);
    assert_eq!(result.warnings[0].span, Span::SYNTHETIC);
    assert!(result.warnings[0].message.contains("removed"));
    let template_scheme = modules
        .get(&module_path())
        .and_then(|table| {
            table
                .get("reload-id")
                .and_then(Binding::callable)
                .map(|callable| callable.arm.scheme.clone())
        })
        .unwrap();
    let valid_key = valid.instance_key(&template_scheme).unwrap();
    assert!(
        modules
            .get(&module_path())
            .is_some_and(|table| table.get(valid_key.as_ref()).is_some()),
        "the valid root after a decline must still be realized"
    );
}

// design/typecheck/monomorphisation.md §3.8 M-3 — an absent template home
// is the orchestrator's ordinary load-and-retry gap, not a stale warning.
#[test]
fn instantiate_demands_absent_home_is_gap() {
    let modules = modules();
    let aliases = no_aliases();
    let fallback = no_fallback();
    let mut ctx: SymbolTableAccess<'_, (), ()> = SymbolTableAccess::live(&modules, module_path());
    let missing = MonoDemand::from_type_args(
        cranelisp_types::CallableTarget::Binding(cranelisp_types::FQSymbol {
            module: ModuleFullPath::from("not_loaded"),
            symbol: Symbol::from("reload-id"),
        }),
        vec![cranelisp_types::ConcreteType::Int],
        Span::new(900, 910),
    );

    assert!(matches!(
        instantiate_demands(vec![missing], &mut ctx, &modules, &aliases, &fallback),
        Err(CheckError::Gap(ResolutionGap::SymbolTypechecked(fq)))
            if fq.to_string() == "not_loaded/reload-id"
    ));
}

// design/typecheck/monomorphisation.md §3.8 M-3 — an engine/body invariant
// failure is not reclassified as a stale-root warning merely because reload
// demands use a synthetic call site.
#[test]
fn instantiate_demands_propagates_template_body_invariant_failure() {
    use cranelisp_types::{Scheme, TemplateBody, TemplateKind, Type};

    let modules = modules();
    let aliases = no_aliases();
    let fallback = no_fallback();
    let template_name = Symbol::from("invalid-template");
    modules
        .get_mut(&module_path())
        .expect("module exists")
        .install_template(
            template_name.clone(),
            Scheme {
                type_vars: vec![0],
                constraints: Default::default(),
                ty: Type::Fn(vec![Type::Var(0)], Box::new(Type::Var(0))),
            },
            vec![Symbol::from("x")],
            None,
            0,
            CallableOrigin::Plain,
            TemplateBody::Ast(DefnVariant {
                params: vec![(Symbol::from("x"), None)],
                // Deliberately contradicts the stored a -> a scheme. A reload
                // demand for Int must surface this engine invariant failure.
                body: Expr::BoolLit {
                    value: true,
                    span: Span::new(1020, 1024),
                    inferred_type: None,
                },
                span: Span::new(1000, 1025),
            }),
            TemplateKind::Parametric,
            vec![],
            Visibility::Private,
        )
        .expect("the lifecycle accepts a structurally valid template carrier");
    let demand = MonoDemand::from_type_args(
        cranelisp_types::CallableTarget::Binding(cranelisp_types::FQSymbol {
            module: module_path(),
            symbol: template_name,
        }),
        vec![cranelisp_types::ConcreteType::Int],
        Span::new(1100, 1110),
    );
    let mut ctx: SymbolTableAccess<'_, (), ()> = SymbolTableAccess::live(&modules, module_path());

    match instantiate_demands(vec![demand], &mut ctx, &modules, &aliases, &fallback) {
        Err(CheckError::TypeError { message, location }) => {
            assert!(message.contains("type mismatch"), "{message}");
            assert_eq!(location.span, Span::new(1000, 1025));
        }
        other => panic!("template-body invariant failure must propagate: {other:?}"),
    }
}
