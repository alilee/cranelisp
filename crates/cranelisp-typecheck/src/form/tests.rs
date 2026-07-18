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

    /// Empty prelude-fallback map ⇒ every module's fallback bit is OFF, matching
    /// the no-prelude unit-test envs. S78 §2.7.3: "Test call sites pass
    /// `&PreludeFallback::default()` (empty ⇒ all-OFF)."
    fn no_fallback() -> PreludeFallback {
        PreludeFallback::default()
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
        check_forms::<(), ()>(parsed, &mut ctx, &modules, &no_aliases(), &no_fallback()).expect("clean check_forms");

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
            &no_fallback(),
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
        let mut ctx: SymbolTableAccess<'_, (), ()> =
            SymbolTableAccess::live(&modules, module_path());

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
        check_forms::<(), ()>(parsed, &mut ctx, &modules, &no_aliases(), &no_fallback()).expect("clean check_forms");

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
            empty_traitdecl("MyTr"),
            empty_traitimpl("MyTr", "MyT"),
            one_variant_defn("noargs"),
            macro_entry("m"),
            constructor_entry(),
        ];
        let r = check_forms::<(), ()>(parsed, &mut ctx, &modules, &no_aliases(), &no_fallback());
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
        let r = check_forms::<(), ()>(parsed, &mut ctx, &modules, &no_aliases(), &no_fallback());
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
            check_forms::<(), ()>(parsed, &mut ctx, &modules, &no_aliases(), &no_fallback())
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
            check_forms::<(), ()>(parsed, &mut ctx, &modules, &no_aliases(), &no_fallback()).expect(
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
        check_forms::<(), ()>(parsed, &mut ctx, &modules, &no_aliases(), &no_fallback()).expect("live mode");
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
            check_forms::<(), ()>(vec![id_defn], &mut ctx, &modules, &no_aliases(), &no_fallback())
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
        check_forms::<(), ()>(vec![caller_defn], &mut ctx2, &modules, &no_aliases(), &no_fallback())
            .expect("call 2: monomorphise (id 7) — must not overflow");

        // Assert: `id$Int` mono entry is registered in live (home-qualified
        // `test_form_mod/id$Int`, FIXME 0519).
        let guard = modules.get(&module_path()).expect("module exists");
        assert!(
            guard.get("test_form_mod/id$Int").is_some(),
            "test_form_mod/id$Int should be registered after call 2 mono"
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
            check_forms::<(), ()>(vec![multi_f], &mut ctx, &modules, &no_aliases(), &no_fallback())
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
        // arity-1 variant is a genuinely-polymorphic clause `([x] x)` — a
        // slot-less `Polymorphic` TEMPLATE under `f$Var` (§11.4). `5` selects it
        // (arity 1), and the drain routes the template clause through
        // monomorphisation (§11.4 step 4), minting the concrete instance
        // `f$Var$Int` and dispatching to it — NOT to the slot-less template.
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
            check_forms::<(), ()>(vec![caller], &mut ctx, &modules, &no_aliases(), &no_fallback())
                .expect("cluster 2 (caller body) checks clean across clusters");
        }

        // The caller's annotated AST must carry a `SigDispatch` to the MONO
        // INSTANCE of the arity-1 poly clause (`…/f$Var$Int`) on the `(f 5)`
        // Apply — pre-S112 this resolved to the bodyless base; pre-§11.4 to the
        // slot-less `f$Var` template.
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
                let m = mangled_name.as_ref();
                assert!(
                    m.contains("f$Var") && m.contains("Int"),
                    "cross-cluster (f 5) must dispatch to the mono INSTANCE of the \
                     arity-1 poly clause (`…/f$Var$Int`), got {m}"
                );
            }
            other => panic!("expected SigDispatch across clusters, got {other:?}"),
        }
    }

    /// FIXME 0365 — the warning channel. When a synthesised field accessor
    /// (§5.2.6, FIXME 0351(a)) collides with a pre-existing NON-accessor
    /// binding, accessor synthesis records a `ShadowedName` warning and
    /// suppresses the accessor (the existing binding wins). Before FIXME 0365
    /// `check_forms` returned `Result<(), CheckError>` and DISCARDED its
    /// `CheckResult` — so the warning never reached the int caller and the REPL
    /// never rendered the `; warning:` line. This test pins the surfaced
    /// channel: `check_forms` now returns `Ok(Vec<Warning>)`, and the colliding
    /// accessor's `ShadowedName` diagnostic is reachable in that Vec carrying
    /// the collision message.
    ///
    /// Fixture: pre-register `v` as a user `defn`, then submit the **product**
    /// type `(deftype Box [:Int v])` (single ctor, ctor-name == type-name) in
    /// the same cluster. Synthesising the `v` accessor finds the pre-existing
    /// `v` defn (a NON-accessor collision) and defers the diagnostic.
    ///
    /// spec: spec/05-data-types.md §5.2.6 — accessor/binding collision safe
    /// disposition (warn, suppress, keep existing binding).
    #[test]
    fn check_forms_surfaces_accessor_collision_warning() {
        use cranelisp_types::{Type, WarningKind};

        let modules = modules();
        // Seed `Int` as an intrinsic type so the `:Int` field resolves in the
        // bare test module (the fixture seeds no scalar type names).
        {
            let mut guard = modules.get_mut(&module_path()).expect("module exists");
            guard.insert(
                Symbol::from("Int"),
                ModuleEntry::IntrinsicType {
                    ty: Type::Int,
                    visibility: Visibility::Public,
                    docstring: None,
                },
            );
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

        let mut ctx: SymbolTableAccess<'_, (), ()> =
            SymbolTableAccess::live(&modules, module_path());
        let warnings = check_forms::<(), ()>(
            vec![v_defn, box_typedef],
            &mut ctx,
            &modules,
            &no_aliases(),
            &no_fallback(),
        )
        .expect("cluster with an accessor collision still checks clean")
        .warnings;

        // The collision must surface as a ShadowedName warning whose message
        // names the colliding accessor `v` — this is the channel int threads
        // onto ProcessedCluster.warnings for the REPL `; warning:` line.
        let shadow = warnings
            .iter()
            .find(|w| w.kind == WarningKind::ShadowedName)
            .unwrap_or_else(|| {
                panic!("expected a ShadowedName warning, got {warnings:?}")
            });
        assert!(
            shadow.message.contains("accessor") && shadow.message.contains('v'),
            "warning message must name the colliding accessor: {:?}",
            shadow.message
        );

        // The pre-existing `v` defn is kept; the accessor is suppressed (the
        // safe disposition the warning records).
        let guard = modules.get(&module_path()).expect("module exists");
        match guard.get("v").expect("v binding survives") {
            ModuleEntry::Def { kind, .. } => {
                assert!(
                    matches!(kind.as_ref(), DefKind::UserFn { .. }),
                    "the original user defn `v` must win, not the accessor"
                );
            }
            other => panic!("expected the user defn for `v`, got {other:?}"),
        }
    }

    // =====================================================================
    // §8.6.4 definition-over-(import|export|prelude) rejection at the shared
    // `check_forms` Pass-1 seam (FIXME 0514). These pin the mode-uniform
    // rejection at the exact seam both REPL/Additive and batch/Replace call.
    // =====================================================================

    /// A public `Def` for `name` in a source module `src` — the terminal an
    /// explicit import/export edge chain-follows to, and a prelude-provided
    /// name's canonical entry.
    fn seeded_public_def() -> ModuleEntry<()> {
        ModuleEntry::def(
            cranelisp_types::Scheme {
                type_vars: vec![],
                constraints: std::collections::HashMap::new(),
                ty: cranelisp_types::Type::Int,
            },
            DefKind::UserFn {
                fn_state: cranelisp_types::UserFnState::Concrete {
                    got_slot: 0,
                    mode_summary: None,
                },
            },
        )
        .visibility(Visibility::Public)
        .build()
    }

    fn seed_module(
        modules: &DashMap<ModuleFullPath, SymbolTable<(), ()>>,
        module: &str,
        name: &str,
    ) {
        let m = ModuleFullPath::from(module);
        modules
            .entry(m.clone())
            .or_insert_with(|| SymbolTable::<(), ()>::new_with_params(m.clone()));
        modules
            .get_mut(&m)
            .unwrap()
            .insert(Symbol::from(name), seeded_public_def());
    }

    fn import_entry(src_module: &str, name: &str, vis: Visibility) -> ModuleEntry<()> {
        ModuleEntry::Import {
            source: cranelisp_types::FQSymbol {
                module: ModuleFullPath::from(src_module),
                symbol: Symbol::from(name),
            },
            visibility: vis,
        }
    }

    /// A `defn` over a name in scope via an explicit `(import …)` is rejected;
    /// the diagnostic names the symbol + the `module/name` FQ remedy.
    #[test]
    fn def_over_import_rejected_at_seam() {
        let modules = modules();
        seed_module(&modules, "util", "measure");
        modules
            .get_mut(&module_path())
            .unwrap()
            .insert(Symbol::from("measure"), import_entry("util", "measure", Visibility::Private));

        let mut ctx: SymbolTableAccess<'_, (), ()> =
            SymbolTableAccess::live(&modules, module_path());
        let err = check_forms::<(), ()>(
            vec![one_variant_defn("measure")],
            &mut ctx,
            &modules,
            &no_aliases(),
            &no_fallback(),
        )
        .expect_err("defn over an imported name MUST be rejected (§8.6.4)");
        let msg = match err {
            CheckError::TypeError { message, .. } => message,
            other => panic!("expected TypeError, got {other:?}"),
        };
        assert!(
            msg.to_lowercase().contains("conflict")
                && msg.contains("measure")
                && msg.contains("util/measure")
                && msg.contains("import"),
            "diagnostic must name the symbol + FQ remedy + kind; got: {msg}",
        );
        // The import remains the binding (staging dropped on Err — live is
        // byte-identical).
        let guard = modules.get(&module_path()).unwrap();
        assert!(matches!(guard.get("measure"), Some(ModuleEntry::Import { .. })));
    }

    /// A `defn` over a name in scope via an explicit `(export …)` — a Public
    /// inner-scope Import edge (§8.4.0) — is rejected on the same terms; the
    /// message names it an export.
    #[test]
    fn def_over_export_rejected_at_seam() {
        let modules = modules();
        seed_module(&modules, "util", "measure");
        modules
            .get_mut(&module_path())
            .unwrap()
            .insert(Symbol::from("measure"), import_entry("util", "measure", Visibility::Public));

        let mut ctx: SymbolTableAccess<'_, (), ()> =
            SymbolTableAccess::live(&modules, module_path());
        let err = check_forms::<(), ()>(
            vec![one_variant_defn("measure")],
            &mut ctx,
            &modules,
            &no_aliases(),
            &no_fallback(),
        )
        .expect_err("defn over an exported name MUST be rejected (§8.4.0/§8.6.4)");
        let msg = match err {
            CheckError::TypeError { message, .. } => message,
            other => panic!("expected TypeError, got {other:?}"),
        };
        assert!(
            msg.contains("export") && msg.contains("util/measure"),
            "diagnostic must name the export + FQ remedy; got: {msg}",
        );
    }

    /// The no-exception ruling (2026-07-04): a `defn` over a PRELUDE-provided
    /// public name is the same compile-time error — the prelude (an implicit
    /// import) is checked exactly like an explicit import.
    #[test]
    fn def_over_prelude_rejected_at_seam() {
        let modules = modules();
        seed_module(&modules, "prelude", "gulp");
        let fallback = PreludeFallback::default();
        fallback.insert(module_path(), true); // implicit prelude ON

        let mut ctx: SymbolTableAccess<'_, (), ()> =
            SymbolTableAccess::live(&modules, module_path());
        let err = check_forms::<(), ()>(
            vec![one_variant_defn("gulp")],
            &mut ctx,
            &modules,
            &no_aliases(),
            &fallback,
        )
        .expect_err("defn over a prelude-provided name MUST be rejected (§8.8.1/§8.6.4)");
        let msg = match err {
            CheckError::TypeError { message, .. } => message,
            other => panic!("expected TypeError, got {other:?}"),
        };
        assert!(
            msg.to_lowercase().contains("conflict")
                && msg.contains("prelude")
                && msg.contains("prelude/gulp"),
            "diagnostic must name the prelude source + FQ remedy; got: {msg}",
        );
    }

    /// A module redefining its OWN prior `Def` (home == current module) is an
    /// ordinary redefinition, NOT a collision — the seam must let it through.
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
        let mut ctx: SymbolTableAccess<'_, (), ()> =
            SymbolTableAccess::live(&modules, module_path());
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
    /// the prelude-fallback bit ON — the seam fires only on an actual in-scope
    /// binding (the §8.8.3 not-loading / fresh-name case).
    #[test]
    fn def_of_fresh_name_with_prelude_on_allowed() {
        let modules = modules();
        seed_module(&modules, "prelude", "gulp");
        let fallback = PreludeFallback::default();
        fallback.insert(module_path(), true);

        let mut ctx: SymbolTableAccess<'_, (), ()> =
            SymbolTableAccess::live(&modules, module_path());
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
    /// batch/Replace call the IDENTICAL function, so the rejection is
    /// structurally mode-uniform. This pins that both `ctx` variants both
    /// sessions use — `Live` (Replace-analog) AND `Cluster`/staging
    /// (Additive-analog) — reject the same def-over-import binding set.
    #[test]
    fn def_over_import_rejection_is_mode_uniform() {
        // Live (Replace-analog).
        {
            let modules = modules();
            seed_module(&modules, "util", "measure");
            modules.get_mut(&module_path()).unwrap().insert(
                Symbol::from("measure"),
                import_entry("util", "measure", Visibility::Private),
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
            .expect_err("Live-mode def-over-import MUST reject");
        }
        // Cluster/staging (Additive-analog) — the import lives in live, the def
        // stages; the union view sees the import; the seam rejects identically.
        {
            let modules = modules();
            seed_module(&modules, "util", "measure");
            modules.get_mut(&module_path()).unwrap().insert(
                Symbol::from("measure"),
                import_entry("util", "measure", Visibility::Private),
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
            .expect_err("Cluster-mode def-over-import MUST reject identically");
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
        use cranelisp_types::GOT_TABLE_SIZE;

        // Exhaust a real module GOT to obtain a genuine `GotExhausted`, then route it
        // through the SAME helper every fallible `allocate_got_slot` caller uses.
        let mut st: SymbolTable<(), ()> = SymbolTable::new(ModuleFullPath::from("proj.widget"));
        for _ in 0..GOT_TABLE_SIZE {
            st.allocate_got_slot().expect("within-bounds allocation");
        }
        let exhausted = st.allocate_got_slot().expect_err("GOT must be exhausted");
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
                assert!(message.contains("GOT slot table exhausted"), "terminal error preserved: {message}");
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
