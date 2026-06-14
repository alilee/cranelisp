    use super::*;
    use crate::builtins::FixtureBuilder;
    use cranelisp_types::{DefKind, ModuleEntry, ModuleFullPath,
        Span, Symbol, Visibility,
    };

    /// Empty fixture (FIXME 0243 narrowing). The module-locality / resolution /
    /// prelude-fallback tests in this file build their OWN modules and seed
    /// exactly the entries they need (via `seed_value` / direct inserts); the
    /// startup-negative tests assert the heavy world is NOT present. Neither
    /// consults the `full()` seeded primitives/macros/IO, so an empty builder
    /// is both minimal and the most honest starting position.
    fn tf() -> TestFixture {
        TestFixture::with_content(FixtureBuilder::new())
    }

    /// Fixture seeding the `IO` ADT in `primitives` (FIXME 0243 narrowing). The
    /// internal-constructor-gate tests publicly re-export `Bind` from
    /// `primitives` and chain-follow to read its `internal: true` discriminator,
    /// so the `primitives` `Bind` Constructor Def must actually exist —
    /// `with_io()` seeds it (and requires `with_builtin_type_names()` first,
    /// bootstrap order). Nothing heavier is consulted.
    fn tf_io() -> TestFixture {
        TestFixture::with_content(
            FixtureBuilder::new().with_builtin_type_names().with_io(),
        )
    }

    /// Fixture seeding builtin type names + the Ring 0/1/3 primitive `Def`s
    /// (FIXME 0243 narrowing). The trait-impl-resolution / dispatch-fallback
    /// tests glob-import `primitives` into a module and reference `add-i64` /
    /// `Int` in impl bodies, so both the builtin type name `Int` and the
    /// `add-i64` `Def` must exist in the `primitives` module.
    fn tf_prims() -> TestFixture {
        TestFixture::with_content(
            FixtureBuilder::new().with_builtin_type_names().with_primitives(),
        )
    }

    /// Fixture seeding the synthetic `macros` module (Sexp/SList ADTs +
    /// sconcat) — FIXME 0243 narrowing. The qualified-sum-ctor-resolution test
    /// resolves `macros/SCons`, so the `macros` module must be present;
    /// `with_macros_sexp()` requires `with_builtin_type_names()` first
    /// (bootstrap order — Sexp/SList fields reference builtin scalars).
    fn tf_macros() -> TestFixture {
        TestFixture::with_content(
            FixtureBuilder::new().with_builtin_type_names().with_macros_sexp(),
        )
    }

    // --- Module-scoped type environments ---

    // spec: 08-modules §8.13 — default REPL module is "user"
    #[test]
    fn test_default_module_is_user() {
        let tf = tf();
        assert_eq!(tf.state.current_module.as_ref(), "user");
    }

    // spec: 11-stdlib §11.1, 08-modules §8.9 — special-form metadata lives at
    // root `""` only (Principle 17 amendment, FIXME 0193). Regular modules
    // are empty after ensure_module_exists.
    #[test]
    fn test_bare_module_has_root_contents_only() {
        // This test VALIDATES the fully-seeded world: special forms at root
        // `""`, primitives + builtin type names in `primitives`, IO, and the
        // `macros` module — while asserting NONE of them leak into a bare
        // module. It must keep `full()` (FIXME 0243: explicitly NOT narrowed —
        // narrowing would defeat the test's purpose).
        let mut tf = TestFixture::new();
        tf.set_current_module(ModuleFullPath::from("bare"));

        // --- Special forms live at root `""` ---
        let root_path = ModuleFullPath::from("");
        let root_table = tf.modules.get(&root_path).expect("root \"\" should exist");
        assert!(root_table.get("if").is_some(), "if should be at root \"\"");
        assert!(root_table.get("let").is_some(), "let should be at root \"\"");
        assert!(root_table.get("defn").is_some(), "defn should be at root \"\"");
        assert!(root_table.get("fn").is_some(), "fn should be at root \"\"");
        assert!(root_table.get("match").is_some(), "match should be at root \"\"");
        assert!(root_table.get("deftype").is_some(), "deftype should be at root \"\"");
        assert!(root_table.get("deftrait").is_some(), "deftrait should be at root \"\"");
        assert!(root_table.get("impl").is_some(), "impl should be at root \"\"");
        assert!(root_table.get("defmacro").is_some(), "defmacro should be at root \"\"");
        drop(root_table);

        // --- Bare module is empty (no special forms seeded — FIXME 0193) ---
        assert!(tf.symbol_table().get("if").is_none(), "if not seeded into bare modules");
        assert!(tf.symbol_table().get("let").is_none(), "let not seeded into bare modules");

        // --- NOT available without import (spec §8.9.1) ---
        assert!(tf.symbol_table().get("Int").is_none(), "Int needs import");
        assert!(tf.symbol_table().get("Bool").is_none(), "Bool needs import");
        assert!(tf.symbol_table().get("Float").is_none(), "Float needs import");
        assert!(tf.symbol_table().get("String").is_none(), "String needs import");
        assert!(tf.symbol_table().get("add-i64").is_none(), "add-i64 needs import");
        assert!(tf.symbol_table().get("str-concat").is_none(), "str-concat needs import");
        assert!(tf.symbol_table().get("bind").is_none(), "bind needs import");
        assert!(tf.symbol_table().get("Pure").is_none(), "Pure needs import");
        assert!(tf.symbol_table().get("SexpSym").is_none(), "SexpSym needs import");
        assert!(tf.symbol_table().get("+").is_none(), "+ needs prelude");
        assert!(tf.symbol_table().get("TestResult").is_none(), "TestResult needs import");
        assert!(tf.symbol_table().get("discover-tests").is_none(), "discover-tests needs import");
        assert!(tf.symbol_table().get("run-test").is_none(), "run-test needs import");

        // Primitives ARE in the primitives synthetic module.
        let prims_path = ModuleFullPath::from("primitives");
        let prims_table = tf.modules.get(&prims_path).unwrap();
        assert!(prims_table.get("add-i64").is_some(), "add-i64 in primitives");
        assert!(prims_table.get("Int").is_some(), "Int in primitives");
        assert!(prims_table.get("Bool").is_some(), "Bool in primitives");
        // NOTE: TestResult / discover-tests / run-test are no longer seeded by
        // the typecheck test fixture — the test-infrastructure synthetic
        // assembly left typecheck's bounded context (facade §"Builtin
        // registration — removed from typecheck"; FIXME 0242). The `*-is-none`
        // assertions above still hold (they were never auto-imported into user).
    }

    // spec: 08-modules §8.9 — new modules are empty; special forms live at
    // root `""` (Principle 17 amendment, FIXME 0193).
    #[test]
    fn test_set_current_module_creates_new() {
        let mut tf = tf();
        tf.set_current_module(ModuleFullPath::from("math"));
        assert_eq!(tf.state.current_module.as_ref(), "math");
        assert!(tf.symbol_table().get("if").is_none(), "special forms at root \"\", not seeded");
        assert!(tf.symbol_table().get("Int").is_none());
        assert!(tf.symbol_table().get("add-i64").is_none());
        assert!(tf.symbol_table().get("+").is_none());
    }

    // spec: 08-modules §8.6 — switching modules preserves existing module state.
    // Per FIXME 0193 amendment: `user` has no special status.
    #[test]
    fn test_switch_back_to_user_preserves_builtins() {
        let mut tf = tf();
        tf.set_current_module(ModuleFullPath::from("other"));
        tf.set_current_module(ModuleFullPath::from("user"));
        assert!(tf.symbol_table().get("if").is_none(), "user not architecturally privileged");
        assert!(tf.symbol_table().get("add-i64").is_none());
    }

    // spec: 08-modules §8.6 — modules have independent symbol tables
    #[test]
    fn test_modules_are_independent() {
        let mut tf = tf();
        // Define something in user
        tf.symbol_table_mut().insert(
            Symbol::from("user-only"),
            ModuleEntry::def(
                crate::scheme::mono(Type::Int),
                DefKind::UserFn { constrained_fn: None },
            )
            .build(),
        );

        // Switch to another module — shouldn't see user-only
        tf.set_current_module(ModuleFullPath::from("other"));
        assert!(tf.symbol_table().get("user-only").is_none());

        // Switch back — should see it again
        tf.set_current_module(ModuleFullPath::from("user"));
        assert!(tf.symbol_table().get("user-only").is_some());
    }

    // --- Cross-module name resolution ---

    fn seed_module(tf: &mut TestFixture, path: &str, entries: Vec<(&str, Visibility)>) {
        tf.set_current_module(ModuleFullPath::from(path));
        for (name, vis) in entries {
            tf.symbol_table_mut().insert(
                Symbol::from(name),
                ModuleEntry::def(
                    crate::scheme::mono(Type::Int),
                    DefKind::UserFn { constrained_fn: None },
                )
                .visibility(vis)
                .build(),
            );
        }
    }

    /// Seed glob-import edges from `source` into the CURRENT module, mirroring
    /// what the orchestrator's import installer lands for a `(import [source
    /// [*]])`. Import registration is no longer a typecheck concern (facade
    /// `typecheck.md` §"Import/export registration is not a typecheck
    /// concern"); typecheck tests that need imports installed seed the edges
    /// directly. Inserts an `Import` binding for every PUBLIC symbol in
    /// `source` (private names are not glob-importable, spec §8.7).
    fn seed_glob_import(tf: &mut TestFixture, source: &ModuleFullPath) {
        let names: Vec<Symbol> = {
            let src = tf.modules.get(source).expect("source module exists for glob seed");
            src.all_symbols()
                .filter(|(_, e)| e.is_public())
                .map(|(n, _)| n.clone())
                .collect()
        };
        for name in names {
            tf.symbol_table_mut().insert(
                name.clone(),
                ModuleEntry::Import {
                    source: FQSymbol { module: source.clone(), symbol: name },
                    visibility: Visibility::Public,
                },
            );
        }
    }

    /// Seed specific-import edges for `names` from `source` into the CURRENT
    /// module (mirrors `(import [source [a b]])`). See `seed_glob_import`.
    fn seed_specific_import(tf: &mut TestFixture, source: &ModuleFullPath, names: &[&str]) {
        for name in names {
            tf.symbol_table_mut().insert(
                Symbol::from(*name),
                ModuleEntry::Import {
                    source: FQSymbol {
                        module: source.clone(),
                        symbol: Symbol::from(*name),
                    },
                    visibility: Visibility::Public,
                },
            );
        }
    }

    // spec: 08-modules §8.5 — qualified name resolves public symbol in target module
    #[test]
    fn test_resolve_qualified_public() {
        let mut tf = tf();
        seed_module(&mut tf, "math", vec![("add", Visibility::Public)]);
        tf.set_current_module(ModuleFullPath::from("user"));

        let result = tf.resolve_qualified(&ModuleFullPath::from("math"), "add").unwrap();
        assert!(result.is_some());
    }

    // spec: 08-modules §8.7 — private symbol access denied from outside module
    #[test]
    fn test_resolve_qualified_private_denied() {
        let mut tf = tf();
        seed_module(&mut tf, "math", vec![("internal", Visibility::Private)]);
        tf.set_current_module(ModuleFullPath::from("user"));

        let result = tf.resolve_qualified(&ModuleFullPath::from("math"), "internal");
        assert!(result.is_err());
        assert!(result.unwrap_err().message().contains("private"));
    }

    // spec: 08-modules §8.7 — private symbol accessible from child module in subtree
    #[test]
    fn test_resolve_qualified_private_allowed_in_subtree() {
        let mut tf = tf();
        seed_module(&mut tf, "math", vec![("internal", Visibility::Private)]);
        tf.set_current_module(ModuleFullPath::from("math.test"));

        let result = tf.resolve_qualified(&ModuleFullPath::from("math"), "internal").unwrap();
        assert!(result.is_some());
    }

    // spec: 08-modules §8.6 — qualified lookup returns None for nonexistent symbol
    #[test]
    fn test_resolve_qualified_not_found() {
        let mut tf = tf();
        seed_module(&mut tf, "math", vec![("add", Visibility::Public)]);
        tf.set_current_module(ModuleFullPath::from("user"));

        let result = tf.resolve_qualified(&ModuleFullPath::from("math"), "nonexistent").unwrap();
        assert!(result.is_none());
    }

    // spec: 08-modules §8.6 — qualified lookup on unknown module returns None
    #[test]
    fn test_resolve_qualified_unknown_module() {
        let tf = tf();
        let result = tf.resolve_qualified(&ModuleFullPath::from("unknown"), "foo").unwrap();
        assert!(result.is_none());
    }

    // --- Import processing ---
    //
    // Import/export *registration* is no longer a typecheck concern (facade
    // `typecheck.md` §"Import/export registration is not a typecheck
    // concern"). The orchestrator's import installer lands `ModuleEntry::Import`
    // edges and `ModuleAliases` entries directly; typecheck only *consumes*
    // them during resolution. The former glob/specific/ambiguity/alias-only
    // registration tests (`test_import_glob`, `test_import_specific`,
    // `test_import_specific_private_error`, `test_import_specific_not_found_error`,
    // `test_import_unknown_module_error`, `test_import_chain_resolution`,
    // `test_import_ambiguity`, `test_import_same_source_not_ambiguous`,
    // `test_import_alias_only`) exercised that deleted registration surface and
    // were removed with it. Consumption of already-installed import edges is
    // covered by `test_resolve_qualified_*` (below) and the chain-follow tests
    // elsewhere in this module.

    // --- subtree visibility (§8.7.3) ---
    //
    // The typecheck-local `is_in_subtree` helper retired at S76 — the
    // §8.7.3 visibility/subtree check now lives in the types-owned resolution
    // primitive (`cranelisp_types::resolve`), unit-tested there
    // (`resolve::tests::private_inaccessible_outside_subtree`). The
    // typecheck-side `resolve_qualified` path that consumes it is covered by
    // the alias-resolution tests below + the e2e module-resolution suite.

    // --- Alias resolution in resolve_qualified ---

    // spec: 08-modules §8.3 — qualified resolution follows module alias
    #[test]
    fn test_resolve_qualified_uses_alias() {
        let mut tf = tf();
        seed_module(&mut tf, "core.option", vec![("Some", Visibility::Public)]);
        tf.set_current_module(ModuleFullPath::from("main"));

        // §8.6.6 longest-prefix-match: the session alias table is keyed by the
        // full alias path; querying `opt` matches the `opt` key and substitutes
        // its target `core.option` before resolution restarts.
        tf.module_aliases.insert(
            ModuleFullPath::from("opt"),
            cranelisp_types::ModuleAliasEntry::new(
                ModuleFullPath::from("core.option"),
                Visibility::Public,
                Span::SYNTHETIC,
            ),
        );

        let result = tf.resolve_qualified(&ModuleFullPath::from("opt"), "Some").unwrap();
        assert!(result.is_some(), "resolve_qualified should resolve 'opt/Some' via alias");
    }

    // spec: 08-modules §8.5 — direct qualified path works without alias
    #[test]
    fn test_resolve_qualified_without_alias_unchanged() {
        let mut tf = tf();
        seed_module(&mut tf, "math", vec![("add", Visibility::Public)]);
        tf.set_current_module(ModuleFullPath::from("main"));

        let result = tf.resolve_qualified(&ModuleFullPath::from("math"), "add").unwrap();
        assert!(result.is_some());
    }

    // --- Builtin seeding in new modules ---

    // spec: 08-modules §8.9 — new module is empty (Principle 17 amendment,
    // FIXME 0193). Special forms at root `""`, not seeded.
    #[test]
    fn test_new_module_does_not_have_primitives() {
        let mut tf = tf();
        tf.set_current_module(ModuleFullPath::from("mymod"));
        assert!(tf.symbol_table().get("add-i64").is_none(), "add-i64 needs import");
        assert!(tf.symbol_table().get("bind").is_none(), "bind needs import");
        assert!(tf.symbol_table().get("if").is_none(), "special forms at root \"\"");
        assert!(tf.symbol_table().get("Int").is_none(), "Int needs import");
    }

    // --- Fresh variable generation ---

    // spec: pipeline-v3.md §3.4.3 — AtomicU32 TypeId allocation is monotonic
    #[test]
    fn test_fresh_var_ids_are_monotonic() {
        let tf = tf();
        let env = tf.env();
        let (_, id1) = env.fresh_var_id();
        let (_, id2) = env.fresh_var_id();
        let (_, id3) = env.fresh_var_id();
        assert!(id1 < id2);
        assert!(id2 < id3);
    }

    // spec: pipeline-v3.md §3.4.3 — fresh_var returns unique Var types
    #[test]
    fn test_fresh_var_returns_unique_vars() {
        let tf = tf();
        let env = tf.env();
        let v1 = env.fresh_var();
        let v2 = env.fresh_var();
        assert_ne!(v1, v2);
        assert!(matches!(v1, Type::Var(_)));
        assert!(matches!(v2, Type::Var(_)));
    }

    // -----------------------------------------------------------------
    // Sprint 61 Wave 3 step 3e'' — H6 atomic `ensure_module_exists`
    // -----------------------------------------------------------------
    //
    // These tests exercise the new `entry().or_insert_with(...)` +
    // hoisted-seed implementation per /arch mini-review §3d''.
    //
    // Per `design/int/heisenbug-race-closure.md §3d''` Test authoring
    // requirements (2): narrow regression guard for concurrent ensures
    // on the same path — exactly one thread builds, others observe
    // the pre-existing table intact.
    //
    // Tests use `TestFixture` which already populates `user` with
    // special forms so the seed clone is non-trivial.

    // Per Principle 17 amendment (FIXME 0193): `ensure_module_exists` creates
    // an empty `SymbolTable`. Special forms live at root `""` only.
    #[test]
    fn ensure_module_exists_creates_empty_table() {
        let tf = tf();
        let path = ModuleFullPath::from("fresh-mod-a");
        assert!(
            tf.modules.get(&path).is_none(),
            "precondition: module absent"
        );
        tf.env().ensure_module_exists(&path);
        let guard = tf.modules.get(&path).expect("module must be present");
        assert!(
            guard.get("if").is_none(),
            "special forms not seeded (FIXME 0193) — live at root \"\""
        );
        assert!(
            guard.get("defn").is_none(),
            "special forms not seeded (FIXME 0193) — live at root \"\""
        );
        assert!(
            guard.get("Int").is_none(),
            "builtin types must NOT leak via ensure"
        );
    }

    #[test]
    fn ensure_module_exists_on_populated_table_preserves_entries() {
        // Simulates the post-populate-then-ensure scenario that H6's
        // pre-fix code broke: another code path populated
        // `modules[helper]` with a real symbol; a concurrent
        // `ensure_module_exists(helper)` on the REPL thread must NOT
        // overwrite the table.
        let tf = tf();
        let path = ModuleFullPath::from("fresh-mod-b");

        // Pre-seed with a user-visible symbol (emulating what the
        // priority worker does in handle_typecheck_work_shared after
        // its own ensure + typecheck).
        tf.env().ensure_module_exists(&path);
        {
            let mut guard = tf.modules.get_mut(&path).unwrap();
            guard.insert(
                Symbol::from("helper-val"),
                ModuleEntry::def(
                    crate::scheme::mono(Type::Int),
                    DefKind::UserFn { constrained_fn: None },
                )
                .build(),
            );
        }

        // Second ensure — pre-fix, this OVERWROTE the populated table.
        // Post-fix, the `Entry::Occupied` path fires and the table is
        // left untouched.
        tf.env().ensure_module_exists(&path);

        let guard = tf.modules.get(&path).expect("module still present");
        assert!(
            guard.get("helper-val").is_some(),
            "pre-existing helper-val MUST NOT be overwritten by second ensure \
             (H6 regression guard — design/int/heisenbug-race-closure.md §8.3)"
        );
        // Per FIXME 0193: special forms NOT seeded into regular modules.
        assert!(
            guard.get("if").is_none(),
            "special forms live at root \"\", not seeded into regular modules"
        );
    }

    #[test]
    fn ensure_module_exists_concurrent_same_path_emits_exactly_one_created() {
        // Stress the atomicity: spawn N threads each calling
        // `ensure_module_exists(same_path)` concurrently. Exactly one
        // Created emission, N-1 AlreadyPresent emissions, and the
        // table ends up present with special forms seeded.
        //
        // Observability: install a test-local counting hook on the
        // trace slot. Because `install_symbol_table_ensure_hook` is
        // backed by a `OnceLock` (process-global, first-install wins),
        // the hook may already be installed by a sibling test or a
        // higher-level binary run. To make the assertion robust to
        // test-execution order we spy via a dedicated atomic counter
        // keyed off the module path in the forwarding hook below.

        use std::sync::Arc;
        use std::sync::atomic::{AtomicUsize, Ordering as AOrd};
        use std::thread;

        // Global counters: one per outcome, scoped to this test's path.
        static CREATED: AtomicUsize = AtomicUsize::new(0);
        static ALREADY_PRESENT: AtomicUsize = AtomicUsize::new(0);
        // Install a forwarding hook on first call. This is idempotent
        // on the OnceLock slot — subsequent tests' installs are
        // no-ops. Routing is keyed by a well-known path the test owns.
        fn test_counting_hook(
            module: &ModuleFullPath,
            outcome: crate::trace::SymbolTableEnsureOutcome,
        ) {
            if module.as_ref() == CONCURRENT_PATH {
                match outcome {
                    crate::trace::SymbolTableEnsureOutcome::Created => {
                        CREATED.fetch_add(1, AOrd::Relaxed);
                    }
                    crate::trace::SymbolTableEnsureOutcome::AlreadyPresent => {
                        ALREADY_PRESENT.fetch_add(1, AOrd::Relaxed);
                    }
                }
            }
        }
        const CONCURRENT_PATH: &str = "concurrent-ensure-path";
        crate::trace::install_symbol_table_ensure_hook(test_counting_hook);

        CREATED.store(0, AOrd::Relaxed);
        ALREADY_PRESENT.store(0, AOrd::Relaxed);

        // Concurrency test over `ensure_module_exists` only — needs no seeded
        // world (FIXME 0243 narrowing).
        let tf = Arc::new(tf());
        let path = ModuleFullPath::from(CONCURRENT_PATH);
        assert!(tf.modules.get(&path).is_none());

        const N: usize = 8;
        let barrier = Arc::new(std::sync::Barrier::new(N));
        let mut handles = Vec::with_capacity(N);
        for _ in 0..N {
            let tf_cl = tf.clone();
            let barrier_cl = barrier.clone();
            let path_cl = path.clone();
            handles.push(thread::spawn(move || {
                barrier_cl.wait();
                tf_cl.env().ensure_module_exists(&path_cl);
            }));
        }
        for h in handles {
            h.join().unwrap();
        }

        // Post-condition: the table is present and empty. Special forms
        // live at root `""` (FIXME 0193).
        let guard = tf.modules.get(&path).expect("module must be present");
        assert!(
            guard.get("if").is_none(),
            "special forms at root \"\", not seeded under concurrency"
        );

        // Sink invariants (only valid if our hook was the active
        // install — OnceLock ordering permitting). If another forwarding
        // hook had already won the install race in a prior test, the
        // counters stay at 0 and the invariant degrades to
        // "post-condition observed via the fixture". Guard with a
        // conditional assertion so the test remains deterministic
        // regardless of execution order.
        let created = CREATED.load(AOrd::Relaxed);
        let already = ALREADY_PRESENT.load(AOrd::Relaxed);
        if created + already > 0 {
            assert_eq!(
                created, 1,
                "exactly ONE Created emission for a concurrent ensure on the same \
                 path (H6 invariant — any >1 is the race signature). \
                 observed: created={created} already_present={already}"
            );
            assert_eq!(
                already,
                N - 1,
                "the other N-1 threads must each emit AlreadyPresent"
            );
        }
    }

    // -----------------------------------------------------------------
    // Wave 3a-α redo Sub-D — Pattern B trait-home + chain-follow tests
    // -----------------------------------------------------------------
    //
    // These tests guard Decision 45 (Pattern B) and Principle 17 (per-symbol
    // chain-follow as THE navigation primitive) for `TraitImpl` writes and
    // lookups. See `design/typecheck/implementation-slice-s66.md §5`.

    use cranelisp_types::{
        Defn, DefnVariant, Expr, FQSymbol, FQTypeName, TraitDecl, TraitImpl, TraitMethodSig,
        TraitName, TypeExpr, TypeName,
    };

    /// Make a unary trait `T` over type parameter `a` with one method `op`
    /// (`(Fn [a a] a)`). Used by Pattern B / chain-follow tests below.
    fn make_unary_trait_decl(name: &str, method: &str) -> TraitDecl {
        TraitDecl {
            name: TraitName::from(name),
            docstring: None,
            type_params: vec![Symbol::from("a")],
            methods: vec![TraitMethodSig {
                name: Symbol::from(method),
                docstring: None,
                params: vec![
                    (Symbol::from("lhs"), TypeExpr::TypeVar(Symbol::from("a"))),
                    (Symbol::from("rhs"), TypeExpr::TypeVar(Symbol::from("a"))),
                ],
                ret_type: TypeExpr::TypeVar(Symbol::from("a")),
                span: Span::SYNTHETIC,
                hkt_param_index: None,
                default_body: None,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        }
    }

    /// Make a concrete `(impl T Int (defn op [lhs rhs] (add-i64 lhs rhs)))`.
    fn make_int_op_impl(trait_name: &str, method: &str) -> TraitImpl {
        TraitImpl {
            trait_name: cranelisp_types::TraitRef::new(None, TraitName::from(trait_name)),
            target: cranelisp_types::TypeExpr::Named(
                cranelisp_types::TypeRef::new(None, TypeName::from("Int")),
            ),
            type_constraints: vec![],
            methods: vec![Defn {
                name: Symbol::from(method),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![(Symbol::from("lhs"), None), (Symbol::from("rhs"), None)],
                    body: Expr::Apply {
                        callee: Box::new(Expr::var(Symbol::from("add-i64"), Span::SYNTHETIC)),
                        args: vec![
                            Expr::var(Symbol::from("lhs"), Span::SYNTHETIC),
                            Expr::var(Symbol::from("rhs"), Span::SYNTHETIC),
                        ],
                        span: Span::SYNTHETIC,
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: Span::SYNTHETIC,
                }],
                visibility: Visibility::Public,
                span: Span::SYNTHETIC,
            }],
            span: Span::SYNTHETIC,
        }
    }

    // spec: arch Decision 45 Pattern B + slice §1.A α15 — `ModuleEntry::TraitImpl`
    // writes target the trait's defining module H, NOT the writer's module M.
    // Set up: trait T declared in H; M imports T from H; register impl from M's
    // perspective; assert the impl entry lands in H's symbol table and is
    // absent from M's.
    #[test]
    fn test_trait_impl_write_lands_in_trait_home_not_writer() {
        let mut tf = tf_prims();

        // Need primitives imported into M so the impl body (`add-i64`) and
        // the bare type name `Int` are resolvable.
        let home = ModuleFullPath::from("home_h");
        let writer = ModuleFullPath::from("writer_m");

        // 1. Declare trait T in H.
        tf.set_current_module(home.clone());
        seed_glob_import(&mut tf, &ModuleFullPath::from("primitives"));
        tf.register_trait_decl_self(&make_unary_trait_decl("PatternBTrait", "pb-op"))
            .unwrap();

        // 2. Switch to writer M; import T from H + primitives glob.
        tf.set_current_module(writer.clone());
        seed_glob_import(&mut tf, &ModuleFullPath::from("primitives"));
        seed_specific_import(&mut tf, &home, &["PatternBTrait", "pb-op"]);

        // Sanity: M sees T via Import binding (terminal resolves to TraitDecl in H).
        let (_term, term_home) = tf
            .env()
            .resolve_terminal_entry_and_home(&writer, "PatternBTrait")
            .expect("M's Import of PatternBTrait should chain-follow to H");
        assert_eq!(
            term_home, home,
            "chain-follow of `PatternBTrait` from writer M should land at trait home H"
        );

        // 3. Register impl from M's perspective.
        tf.register_trait_impl_self(&make_int_op_impl("PatternBTrait", "pb-op"))
            .unwrap();

        // 4. Assert ModuleEntry::TraitImpl lands in H, not M.
        let expected_key = Symbol::from("impl$primitives/Int$home_h/PatternBTrait");

        let home_table = tf
            .modules
            .get(&home)
            .expect("H's symbol table should exist");
        let h_entry = home_table.get(expected_key.as_ref());
        assert!(
            matches!(h_entry, Some(ModuleEntry::TraitImpl { .. })),
            "Pattern B: TraitImpl MUST be written to H (trait's home), \
             key `{expected_key}`; got {h_entry:?}"
        );
        if let Some(ModuleEntry::TraitImpl { trait_name, impl_type, .. }) = h_entry {
            assert_eq!(trait_name.module, home, "trait_name FQ module should be H");
            assert_eq!(trait_name.name.as_ref(), "PatternBTrait");
            assert_eq!(
                impl_type.module.as_ref(),
                "primitives",
                "Int resolves to primitives"
            );
            assert_eq!(impl_type.name.as_ref(), "Int");
        }
        drop(home_table);

        // Negative: writer M's table MUST NOT contain ANY TraitImpl entry
        // for PatternBTrait — and no synthetic `impl$...$home_h/PatternBTrait`
        // key in particular.
        let writer_table = tf
            .modules
            .get(&writer)
            .expect("M's symbol table should exist");
        assert!(
            writer_table.get(expected_key.as_ref()).is_none(),
            "Pattern A regression: TraitImpl MUST NOT appear in writer module M's table"
        );
        for (key, entry) in writer_table.all_symbols() {
            if let ModuleEntry::TraitImpl { trait_name, .. } = entry {
                panic!(
                    "writer M contains an unexpected TraitImpl entry `{key}` for trait `{trait_name}` \
                     — Pattern B requires it to live in the trait's home module H, not M"
                );
            }
        }
    }

    // spec: arch Decision 45 + Principle 17 + slice §1.A α5/α6/α7 — impl
    // resolution uses per-symbol chain-follow on `Import`/`Reexport`
    // bindings to find the trait's home, then probes ONLY that one module
    // for the synthetic `impl$...` key. No universe scan, no closure walk.
    //
    // Set up a re-export chain: L declares trait T; M imports T from L and
    // re-exports it; N imports T from M (so N's binding is an `Import`
    // pointing at M's `Reexport` pointing at L's `TraitDecl`). Place the
    // impl at L (trait's home, per Pattern B). Place "decoy" TraitImpl
    // entries in two unrelated modules (D1 and D2) that a universe scan
    // would erroneously pick up. From N's view, `has_impl_in_module(N, T,
    // Int)` MUST return true (chain-follow finds the L-resident impl), and
    // the decoys MUST be ignored.
    #[test]
    fn test_impl_resolution_chain_follows_not_universe_scans() {
        let mut tf = tf_prims();

        let l = ModuleFullPath::from("chain_l");
        let m = ModuleFullPath::from("chain_m");
        let n = ModuleFullPath::from("chain_n");
        let d1 = ModuleFullPath::from("decoy_d1");
        let d2 = ModuleFullPath::from("decoy_d2");

        // 1. L declares trait T (with primitives glob so the impl body
        //    can resolve add-i64).
        tf.set_current_module(l.clone());
        seed_glob_import(&mut tf, &ModuleFullPath::from("primitives"));
        tf.register_trait_decl_self(&make_unary_trait_decl("ChainTrait", "ch-op"))
            .unwrap();
        // L also owns the impl — write from L's perspective (Pattern B:
        // chain-follow is depth-zero because writer == trait home).
        tf.register_trait_impl_self(&make_int_op_impl("ChainTrait", "ch-op"))
            .unwrap();

        // 2. M imports T from L AND re-exports it. We construct the
        //    `Reexport` entry directly (matches what `register_exports`
        //    builds in the prod pipeline).
        tf.set_current_module(m.clone());
        seed_specific_import(&mut tf, &l, &["ChainTrait"]);
        // Overwrite the `Import` with a `Reexport` on M so N's import sees
        // a `Reexport` edge — the chain becomes N(Import) → M(Reexport) → L(TraitDecl).
        tf.symbol_table_mut().insert(
            Symbol::from("ChainTrait"),
            ModuleEntry::Import {
                source: FQSymbol {
                    module: l.clone(),
                    symbol: Symbol::from("ChainTrait"),
                },
                visibility: Visibility::Public,
            },
        );

        // 3. N imports T from M.
        tf.set_current_module(n.clone());
        seed_specific_import(&mut tf, &m, &["ChainTrait"]);

        // Sanity: from N, chain-follow lands at L (the trait's home).
        let (_term, home_via_n) = tf
            .env()
            .resolve_terminal_entry_and_home(&n, "ChainTrait")
            .expect("chain-follow from N should reach L");
        assert_eq!(
            home_via_n, l,
            "chain-follow of `ChainTrait` from N must terminate at L (chain length 2)"
        );

        // 4. Place decoy TraitImpl entries in D1 and D2. A universe scan
        //    would erroneously match these; chain-follow MUST ignore them
        //    because it probes ONLY the trait's home (L).
        let decoy_key = Symbol::from("impl$primitives/Int$chain_l/ChainTrait");
        for decoy_path in [&d1, &d2] {
            // Ensure the module exists so a write succeeds.
            tf.env().ensure_module_exists(decoy_path);
            let mut tbl = tf
                .modules
                .get_mut(decoy_path)
                .expect("decoy module just ensured");
            tbl.insert(
                decoy_key.clone(),
                ModuleEntry::TraitImpl {
                    trait_name: cranelisp_types::FQTraitName::new(
                        l.clone(),
                        TraitName::from("ChainTrait"),
                    ),
                    impl_type: FQTypeName::new(
                        ModuleFullPath::from("primitives"),
                        TypeName::from("Int"),
                    ),
                    methods: vec![Symbol::from("ch-op")],
                    visibility: Visibility::Public,
                },
            );
        }

        // 5. From N's view, has_impl_with_state MUST find the L-resident
        //    impl via chain-follow (positive). The decoy entries are
        //    structurally identical but live in unrelated modules; if the
        //    resolver were doing a universe scan it would still find one,
        //    so the positive does not by itself prove chain-follow. The
        //    negative below tightens the assertion.
        let n_state = CheckState::new(n.clone());
        let env = tf.env();
        assert!(
            env.has_impl_with_state(&n_state, &TraitName::from("ChainTrait"), &TypeName::from("Int")),
            "impl resolution from N should chain-follow N → M → L and find the L-resident impl"
        );

        // Negative: lookup against a trait name that DOES NOT have an
        // import binding in N MUST return false. If the resolver were
        // doing a universe scan over `self.modules`, the decoys (whose
        // synthetic key embeds `chain_l/ChainTrait`) could be matched by
        // name alone; chain-follow refuses because the starting module N
        // has no `UnknownTrait` binding to follow.
        assert!(
            !env.has_impl_with_state(
                &n_state,
                &TraitName::from("UnknownTrait"),
                &TypeName::from("Int")
            ),
            "no `UnknownTrait` import in N → chain-follow must fail and decoys MUST NOT be matched \
             (a universe scan would falsely hit the decoy entries)"
        );

        // Negative: probing the writer module N directly for the synthetic
        // impl key MUST find nothing — the entry lives in L only.
        let n_table = tf
            .modules
            .get(&n)
            .expect("N's symbol table should exist");
        assert!(
            n_table.get(decoy_key.as_ref()).is_none(),
            "N's symbol table MUST NOT carry the impl entry (it lives in L per Pattern B)"
        );
    }

    // spec: 08-modules §8.6.4 prelude-as-outer-scope + arch Decision 45 +
    // FIXME 0315 — trait-method dispatch + impl discovery fall back to the
    // implicit-prelude OUTER SCOPE. A bare operator (`+`) backed by a
    // prelude `deftrait Num` + `impl Num Int` must resolve from a user
    // module that does NOT import the trait, GATED on the per-module
    // prelude-fallback bit. With the bit OFF (prelude refusal / selective
    // import), resolution must fail — proving the fallback is the bit, not a
    // name-key.
    #[test]
    fn test_trait_method_dispatch_falls_back_to_prelude_outer_scope() {
        let mut tf = tf_prims();

        let prelude = ModuleFullPath::from("prelude");
        let user = ModuleFullPath::from("user");

        // 1. Prelude declares trait `Num` (method `+`) and `impl Num Int`.
        //    Glob primitives into prelude so the impl body (`add-i64`) and
        //    the bare type name `Int` resolve there.
        tf.set_current_module(prelude.clone());
        seed_glob_import(&mut tf, &ModuleFullPath::from("primitives"));
        tf.register_trait_decl_self(&make_unary_trait_decl("Num", "+"))
            .unwrap();
        tf.register_trait_impl_self(&make_int_op_impl("Num", "+"))
            .unwrap();

        // 2. Switch to `user`. It does NOT import `Num` — the only path to
        //    the trait is the implicit-prelude outer scope. Prove the
        //    pre-fallback state first: with the bit OFF, the bare `+` is
        //    invisible (this is the regression FIXME 0315 captured).
        tf.set_current_module(user.clone());
        assert!(
            tf.method_to_trait(&Symbol::from("+")).is_none(),
            "bit OFF: bare `+` must not resolve to a trait without an explicit \
             import or the prelude fallback"
        );
        assert!(
            !tf.has_impl(&TraitName::from("Num"), &TypeName::from("Int")),
            "bit OFF: `impl Num Int` lives in prelude and must be invisible \
             without the fallback"
        );

        // 3. Turn the prelude-fallback bit ON for `user` (what
        //    `inject_prelude_if_needed` does for an ordinary entry module).
        tf.prelude_fallback.insert(user.clone(), true);

        // method→trait origin now resolves via the outer scope.
        assert_eq!(
            tf.method_to_trait(&Symbol::from("+")),
            Some(TraitName::from("Num")),
            "bit ON: bare `+` resolves to prelude trait `Num` via the outer scope"
        );
        // impl discovery now finds the prelude-resident `impl Num Int`.
        assert!(
            tf.has_impl(&TraitName::from("Num"), &TypeName::from("Int")),
            "bit ON: `impl Num Int` is discovered through the prelude fallback"
        );

        // Full dispatch of `(+ Int Int)` resolves (the FIXME 0315 repro).
        let resolved = tf
            .try_resolve_trait_method_self(
                &Symbol::from("+"),
                &[Type::Int, Type::Int],
                Span::SYNTHETIC,
            )
            .expect("dispatch must not error")
            .expect("`(+ Int Int)` must resolve to a ResolvedCall via prelude");
        // (Num, +, Int) collapses to the inline primitive `add-i64`
        // (primitive_for_trait_method short-circuit) — the resolution
        // reaching this arm at all proves the prelude trait + impl were
        // both discovered through the fallback.
        match resolved {
            cranelisp_types::ResolvedCall::BuiltinFn { name } => {
                assert_eq!(name.as_ref(), "add-i64");
            }
            other => panic!(
                "expected BuiltinFn(add-i64) for (Num,+,Int); got {other:?}"
            ),
        }
    }

    // spec: arch Principle 17 + slice §1.A α1/α2/α3 — short-name lookup is
    // current-module-only. If `foo` is absent from the current module's
    // symbol table, the lookup fails — no fallback to primitives, no
    // closure walk, no universe scan. With a `(import [M [foo]])` binding
    // in N, the same lookup chain-follows the per-symbol Import edge to M.
    #[test]
    fn test_short_name_lookup_is_current_module_only() {
        let mut tf = tf();

        let m = ModuleFullPath::from("home_m");
        let n = ModuleFullPath::from("consumer_n");

        // 1. Register a TypeDef for `Foo` in M.
        tf.set_current_module(m.clone());
        tf.register_type_def_self(
            &TypeName::from("Foo"),
            &None,
            &[],
            &[cranelisp_types::ConstructorDef {
                name: Symbol::from("MkFoo"),
                docstring: None,
                fields: vec![],
                span: Span::SYNTHETIC,
            }],
            Visibility::Public,
            Span::SYNTHETIC,
        ).unwrap();

        // 2. From N (no import of M.Foo), short-name lookup of Foo MUST fail.
        tf.set_current_module(n.clone());
        let result_no_import = tf
            .env()
            .lookup_type_def_in_module(&n, &TypeName::from("Foo"));
        assert!(
            result_no_import.is_none(),
            "current-module-only short-name lookup MUST fail when `Foo` is not bound in N \
             (Principle 17: no fallback, no closure walk, no universe scan)"
        );

        // Negative: also confirm that short-name `lookup` (Scheme variant)
        // does not silently chain into M.
        let n_state = CheckState::new(n.clone());
        assert!(
            tf.env().lookup(&n_state, "Foo").0.is_none(),
            "Scheme-flavoured lookup of `Foo` from N MUST also fail without an Import"
        );

        // 3. Now inject a per-symbol Import binding into N for M.Foo.
        //    Manual insert mirrors what `register_imports` would build for
        //    a Specific import (TypeDef entries are public-by-default here).
        tf.symbol_table_mut().insert(
            Symbol::from("Foo"),
            ModuleEntry::Import {
                source: FQSymbol {
                    module: m.clone(),
                    symbol: Symbol::from("Foo"),
                },
                visibility: Visibility::Private,
            },
        );

        // 4. The same short-name lookup now chain-follows N(Import) → M(TypeDef)
        //    and succeeds — reach is per-binding, not per-resolver.
        let result_after_import = tf
            .env()
            .lookup_type_def_in_module(&n, &TypeName::from("Foo"));
        assert!(
            result_after_import.is_some(),
            "after injecting `ModuleEntry::Import {{ source: M/Foo }}` into N, \
             chain-follow should resolve `Foo` to M's TypeDef"
        );
        let info = result_after_import.unwrap();
        assert_eq!(info.name.module, m, "resolved Foo's FQ module should be M");
        assert_eq!(info.name.name.as_ref(), "Foo");
    }

    // spec: 03-types §3.5.1 — instantiation must rename bound vars apart from
    // the scheme's own bound vars even when the fresh-var counter has NOT been
    // advanced past them (FIXME 0279/0295 cross-module instantiation collision).
    //
    // The scheme `forall t1. (Fn [t1] t1)` (an imported polymorphic identity)
    // instantiated while `next_id == 1` previously built the identity self-map
    // `{1 -> Var(1)}`, which made `apply` recurse forever (compiler stack
    // overflow). The collision-free `fresh_instantiation_subst` must produce a
    // genuinely fresh, NON-colliding var instead.
    #[test]
    fn test_instantiate_no_self_map_when_counter_collides() {
        use std::collections::HashMap;
        let tf = tf();
        // Force the counter to collide with the scheme's bound var id (1).
        tf.set_next_id(1);

        let scheme = Scheme {
            type_vars: vec![1],
            constraints: HashMap::new(),
            ty: Type::Fn(vec![Type::Var(1)], Box::new(Type::Var(1))),
        };

        // Must terminate (no overflow) and produce a fresh, non-colliding var.
        let inst = tf.instantiate_scheme(&scheme);
        match inst {
            Type::Fn(params, ret) => {
                assert_eq!(params.len(), 1);
                let pv = match (&params[0], &*ret) {
                    (Type::Var(a), Type::Var(b)) if a == b => *a,
                    other => panic!("expected (Fn [tN] tN) with one shared var, got {other:?}"),
                };
                assert_ne!(
                    pv, 1,
                    "instantiated var must be renamed apart from the scheme's bound var (no self-map)"
                );
            }
            other => panic!("expected a function type, got {other}"),
        }
    }

    // --- S78 §2.7: implicit-prelude outer-scope fallback ---

    /// Seed a public value `name` (a zero-arg `UserFn` of type `Int`) into
    /// module `path`. Returns the fixture to the previously-current module is
    /// the caller's job.
    fn seed_value(tf: &mut TestFixture, path: &str, name: &str) {
        tf.set_current_module(ModuleFullPath::from(path));
        tf.symbol_table_mut().insert(
            Symbol::from(name),
            ModuleEntry::def(
                crate::scheme::mono(Type::Int),
                DefKind::UserFn { constrained_fn: None },
            )
            .visibility(Visibility::Public)
            .build(),
        );
    }

    /// Turn the prelude-fallback bit ON for `module`.
    fn set_fallback_on(tf: &TestFixture, module: &str) {
        tf.prelude_fallback.insert(ModuleFullPath::from(module), true);
    }

    // spec: 08-modules §8.6.4 / §8.8.1 — the implicit prelude is an OUTER SCOPE.
    // With the fallback bit ON, a bare name absent from module M's own table
    // resolves against the `prelude` module's table (value/scheme path).
    #[test]
    fn prelude_fallback_resolves_bare_value_when_bit_on() {
        let mut tf = tf();
        // prelude defines `map`; M does not.
        seed_value(&mut tf, "prelude", "map");
        let m = ModuleFullPath::from("app");
        tf.set_current_module(m.clone());
        set_fallback_on(&tf, "app");

        let state = CheckState::new(m.clone());
        let (scheme, _gap) = tf.env().lookup(&state, "map");
        assert!(
            scheme.is_some(),
            "bare `map` must resolve via the prelude outer-scope fallback when the bit is ON"
        );
    }

    // spec: 08-modules §8.6.4 — bit OFF ⇒ no implicit prelude fallback. A
    // module that refuses/references prelude (or simply has the bit unset)
    // does NOT see prelude names by bare reference.
    #[test]
    fn prelude_fallback_absent_when_bit_off() {
        let mut tf = tf();
        seed_value(&mut tf, "prelude", "map");
        let m = ModuleFullPath::from("app_off");
        tf.set_current_module(m.clone());
        // No `set_fallback_on` — bit is absent (== OFF).

        let state = CheckState::new(m.clone());
        let (scheme, _gap) = tf.env().lookup(&state, "map");
        assert!(
            scheme.is_none(),
            "bare `map` must NOT resolve when the prelude-fallback bit is OFF/absent"
        );
    }

    // spec: 08-modules §8.6.1 — a local/explicit definition shadows the
    // implicit prelude (inner scope consulted before the outer fallback).
    #[test]
    fn prelude_fallback_inner_definition_shadows_prelude() {
        let mut tf = tf();
        // Both prelude and M define `map`; M's own def must win (inner first).
        seed_value(&mut tf, "prelude", "map");
        let m = ModuleFullPath::from("app_shadow");
        seed_value(&mut tf, "app_shadow", "map");
        tf.set_current_module(m.clone());
        set_fallback_on(&tf, "app_shadow");

        // The entry path resolves to M's own Def (home == M), not prelude's.
        let state = CheckState::new(m.clone());
        let entry = tf
            .env()
            .resolve_entry_in_current_module(&state, "map")
            .expect("map resolves (inner def present)");
        // M's own entry is a canonical Def (not an Import to prelude).
        assert!(
            matches!(entry, ModuleEntry::Def { .. }),
            "inner definition must shadow the prelude outer scope"
        );
    }

    // spec: 08-modules §8.6.4 — primitives reach user code VIA prelude's
    // re-export, resolved THROUGH the fallback (not a name-key). prelude holds
    // an `Import` edge to a primitive; a bare reference in M falls back to
    // prelude, then chain-follows the re-export to the canonical entry.
    #[test]
    fn prelude_fallback_chain_follows_reexport_to_primitive() {
        let mut tf = tf();
        // `prims` defines the canonical `add-i64`.
        seed_value(&mut tf, "prims", "add-i64");
        // prelude re-exports it (an Import edge, like `(export [prims [*]])`).
        tf.set_current_module(ModuleFullPath::from("prelude"));
        tf.symbol_table_mut().insert(
            Symbol::from("add-i64"),
            ModuleEntry::Import {
                source: FQSymbol {
                    module: ModuleFullPath::from("prims"),
                    symbol: Symbol::from("add-i64"),
                },
                visibility: Visibility::Public,
            },
        );
        let m = ModuleFullPath::from("app_prim");
        tf.set_current_module(m.clone());
        set_fallback_on(&tf, "app_prim");

        // Value path: the scheme is extracted by chain-following prelude's
        // Import edge to the canonical `prims/add-i64` Def.
        let state = CheckState::new(m.clone());
        let (scheme, _gap) = tf.env().lookup(&state, "add-i64");
        assert!(
            scheme.is_some(),
            "bare `add-i64` must resolve through the prelude re-export chain via the fallback"
        );

        // Entry path: chain-follows to the terminal canonical Def in `prims`.
        let entry = tf
            .env()
            .resolve_entry_in_current_module(&state, "add-i64")
            .expect("add-i64 resolves to its terminal entry");
        assert!(
            matches!(entry, ModuleEntry::Def { .. }),
            "fallback + chain-follow must land on the canonical primitive Def, not the Import edge"
        );
    }

    // spec: 08-modules §8.6.6 — an explicit `mod/sym`-qualified reference names
    // its module directly and MUST NOT fall back to prelude. Even with the bit
    // ON, `prelude/absent` for a name prelude does not define stays unresolved
    // (no fallback re-entry), and a qualified name to a module that lacks the
    // symbol does not get rescued by prelude.
    #[test]
    fn prelude_fallback_qualified_never_falls_back() {
        let mut tf = tf();
        // prelude defines `helper`; module `other` does NOT.
        seed_value(&mut tf, "prelude", "helper");
        seed_module(&mut tf, "other", vec![("something_else", Visibility::Public)]);
        let m = ModuleFullPath::from("app_qual");
        tf.set_current_module(m.clone());
        set_fallback_on(&tf, "app_qual");

        // Qualified `other/helper` must NOT be rescued by the prelude fallback —
        // it names `other` directly, and `other` has no `helper`.
        let result = tf.resolve_qualified(&ModuleFullPath::from("other"), "helper").unwrap();
        assert!(
            result.is_none(),
            "qualified `other/helper` must not fall back to prelude (qualified names never fall back)"
        );
    }

    // spec: 08-modules §8.6.4 — the prelude module itself does not fall back
    // onto itself (no self-referential outer scope). A bare miss in `prelude`
    // with the bit (hypothetically) ON does not loop.
    #[test]
    fn prelude_module_does_not_fall_back_onto_itself() {
        let mut tf = tf();
        tf.set_current_module(ModuleFullPath::from("prelude"));
        // Even with the bit ON for prelude (which int never sets), a bare miss
        // must not recurse onto prelude again.
        tf.prelude_fallback.insert(ModuleFullPath::from("prelude"), true);

        let state = CheckState::new(ModuleFullPath::from("prelude"));
        let (scheme, _gap) = tf.env().lookup(&state, "definitely_absent");
        assert!(scheme.is_none(), "prelude must not fall back onto itself");
    }

    // spec: 08-modules §8.6.4 — the `resolve`-family chokepoint (resolve_type)
    // also falls back: a bare TYPE name absent from M resolves against prelude
    // when the bit is ON, and does not when OFF.
    #[test]
    fn prelude_fallback_resolves_bare_type_via_resolve_family() {
        use cranelisp_types::TypeName;
        let mut tf = tf();
        // prelude defines a nullary ADT `Maybe`.
        tf.set_current_module(ModuleFullPath::from("prelude"));
        tf.register_type_def_self(
            &TypeName::from("Maybe"),
            &None,
            &[],
            &[cranelisp_types::ConstructorDef {
                name: Symbol::from("Nothing"),
                docstring: None,
                fields: vec![],
                span: Span::SYNTHETIC,
            }],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();

        let m = ModuleFullPath::from("app_type");
        tf.set_current_module(m.clone());

        // Bit OFF: bare `Maybe` does not resolve from M.
        let state = CheckState::new(m.clone());
        assert!(
            tf.env().resolve_type(&state, &TypeName::from("Maybe"), Span::SYNTHETIC).is_err(),
            "bare type `Maybe` must NOT resolve via resolve_type when the bit is OFF"
        );

        // Bit ON: bare `Maybe` resolves to prelude's TypeDef.
        set_fallback_on(&tf, "app_type");
        let resolved = tf
            .env()
            .resolve_type(&state, &TypeName::from("Maybe"), Span::SYNTHETIC)
            .expect("bare type `Maybe` resolves via the prelude fallback when the bit is ON");
        assert_eq!(resolved.module.as_ref(), "prelude", "Maybe's home is prelude");
    }

    // --- S78 §2 / `/review` I-1: prelude private-symbol visibility ---
    //
    // The implicit-prelude OUTER SCOPE exposes only PUBLIC prelude bindings as
    // bare names in a user module. A Private top-level def in prelude's own
    // table must NOT be bare-reachable through the fallback (a future private
    // prelude helper would otherwise silently leak into every user module's
    // bare-name scope). PUBLIC prelude re-exports stay reachable (regression
    // guard). Covered across BOTH the value/`resolve`-family path and the
    // trait/chain-follow path.

    /// Seed a value `name` with explicit `vis` into module `path`.
    fn seed_value_vis(tf: &mut TestFixture, path: &str, name: &str, vis: Visibility) {
        tf.set_current_module(ModuleFullPath::from(path));
        tf.symbol_table_mut().insert(
            Symbol::from(name),
            ModuleEntry::def(
                crate::scheme::mono(Type::Int),
                DefKind::UserFn { constrained_fn: None },
            )
            .visibility(vis)
            .build(),
        );
    }

    // spec: 08-modules §8.7.3 — a PRIVATE prelude def is NOT reachable as a
    // bare name from a user module, even with the fallback bit ON. Value path
    // (`lookup`) AND entry path (`resolve_entry_in_current_module`) both miss.
    #[test]
    fn prelude_private_def_not_bare_reachable_value_path() {
        let mut tf = tf();
        // prelude has a PRIVATE helper `secret` (top-level defns default Private).
        seed_value_vis(&mut tf, "prelude", "secret", Visibility::Private);
        let m = ModuleFullPath::from("app_priv");
        tf.set_current_module(m.clone());
        set_fallback_on(&tf, "app_priv");

        let state = CheckState::new(m.clone());
        let (scheme, _gap) = tf.env().lookup(&state, "secret");
        assert!(
            scheme.is_none(),
            "a PRIVATE prelude def must NOT resolve as a bare name (I-1 visibility leak)"
        );
        assert!(
            tf.env().resolve_entry_in_current_module(&state, "secret").is_none(),
            "a PRIVATE prelude def must NOT resolve via the entry chokepoint either"
        );
    }

    // spec: 08-modules §8.7.3 — a PRIVATE prelude def must not SHADOW a user
    // module's own binding of the same name. With both a private prelude
    // `helper` and the user's own public `helper`, the bare name resolves to
    // the USER's binding (inner scope), never the private prelude one.
    #[test]
    fn prelude_private_def_does_not_shadow_user_binding() {
        let mut tf = tf();
        seed_value_vis(&mut tf, "prelude", "helper", Visibility::Private);
        let m = ModuleFullPath::from("app_own");
        seed_value(&mut tf, "app_own", "helper"); // user's own PUBLIC helper
        tf.set_current_module(m.clone());
        set_fallback_on(&tf, "app_own");

        let state = CheckState::new(m.clone());
        let entry = tf
            .env()
            .resolve_entry_in_current_module(&state, "helper")
            .expect("user's own `helper` resolves (inner scope)");
        // The user's own canonical Def wins; the private prelude binding is
        // neither returned nor consulted (inner hit before the fallback).
        let (_, home) = tf
            .env()
            .resolve_terminal_entry_or_prelude(&state, "helper")
            .expect("terminal resolves to the user's binding");
        assert_eq!(home, m, "bare `helper` resolves to the user module, not prelude");
        assert!(matches!(entry, ModuleEntry::Def { .. }));
    }

    // spec: 08-modules §8.7.3 (regression guard for the I-1 fix) — a PUBLIC
    // prelude re-export stays reachable through the fallback; the public-only
    // filter must NOT regress the legitimate case. prelude PUBLICLY re-exports
    // `prims/add-i64`; bare `add-i64` in a user module resolves through the
    // fallback + chain-follow to the canonical primitive Def.
    #[test]
    fn prelude_public_reexport_still_reachable_after_visibility_fix() {
        let mut tf = tf();
        seed_value(&mut tf, "prims", "add-i64"); // canonical, public
        tf.set_current_module(ModuleFullPath::from("prelude"));
        tf.symbol_table_mut().insert(
            Symbol::from("add-i64"),
            ModuleEntry::Import {
                source: FQSymbol {
                    module: ModuleFullPath::from("prims"),
                    symbol: Symbol::from("add-i64"),
                },
                visibility: Visibility::Public, // PUBLIC re-export
            },
        );
        let m = ModuleFullPath::from("app_pub");
        tf.set_current_module(m.clone());
        set_fallback_on(&tf, "app_pub");

        let state = CheckState::new(m.clone());
        assert!(
            tf.env().lookup(&state, "add-i64").0.is_some(),
            "a PUBLIC prelude re-export must stay reachable (no I-1 over-filter)"
        );
        let entry = tf
            .env()
            .resolve_entry_in_current_module(&state, "add-i64")
            .expect("public re-export resolves to its terminal Def");
        assert!(matches!(entry, ModuleEntry::Def { .. }));
    }

    // spec: 08-modules §8.7.3 — a PRIVATE prelude TYPE is NOT bare-reachable via
    // the `resolve`-family chokepoint (resolve_type), even with the bit ON; a
    // PUBLIC prelude type IS. Guards the post-filter on the `cranelisp_types::
    // resolve` retry path.
    #[test]
    fn prelude_private_type_not_reachable_via_resolve_family() {
        use cranelisp_types::TypeName;
        let mut tf = tf();
        // prelude defines a PRIVATE nullary ADT `Hidden`.
        tf.set_current_module(ModuleFullPath::from("prelude"));
        tf.register_type_def_self(
            &TypeName::from("Hidden"),
            &None,
            &[],
            &[cranelisp_types::ConstructorDef {
                name: Symbol::from("HiddenCtor"),
                docstring: None,
                fields: vec![],
                span: Span::SYNTHETIC,
            }],
            Visibility::Private,
            Span::SYNTHETIC,
        )
        .unwrap();

        let m = ModuleFullPath::from("app_hidden");
        tf.set_current_module(m.clone());
        set_fallback_on(&tf, "app_hidden");

        let state = CheckState::new(m.clone());
        assert!(
            tf.env().resolve_type(&state, &TypeName::from("Hidden"), Span::SYNTHETIC).is_err(),
            "a PRIVATE prelude type must NOT resolve via resolve_type through the fallback (I-1)"
        );
    }

    // spec: 08-modules §8.7.3 — a PRIVATE prelude `deftrait`'s method is NOT
    // discoverable as a bare operator through the trait/chain-follow fallback
    // (`resolve_terminal_entry_or_prelude` → `method_to_trait`). A PUBLIC
    // prelude trait's method IS (regression guard).
    #[test]
    fn prelude_private_trait_method_not_reachable() {
        let mut tf = tf();

        // PUBLIC prelude trait `PubT` with method `pub-op` — reachable.
        tf.set_current_module(ModuleFullPath::from("prelude"));
        tf.register_trait_decl_self(&make_unary_trait_decl("PubT", "pub-op"))
            .unwrap();
        // PRIVATE prelude trait `PrivT` with method `priv-op` — NOT reachable.
        let mut priv_decl = make_unary_trait_decl("PrivT", "priv-op");
        priv_decl.visibility = Visibility::Private;
        tf.register_trait_decl_self(&priv_decl).unwrap();

        let m = ModuleFullPath::from("app_trait");
        tf.set_current_module(m.clone());
        set_fallback_on(&tf, "app_trait");

        let state = CheckState::new(m.clone());
        let env = tf.env();
        assert_eq!(
            env.method_to_trait_with_state(&state, &Symbol::from("pub-op")),
            Some(TraitName::from("PubT")),
            "a PUBLIC prelude trait's method must resolve via the trait fallback"
        );
        assert!(
            env.method_to_trait_with_state(&state, &Symbol::from("priv-op")).is_none(),
            "a PRIVATE prelude trait's method must NOT leak as a bare operator (I-1)"
        );
    }

    // --- S78 §2 / FIXME 0317: constructor-resolution chokepoints fall back to
    // the implicit-prelude OUTER SCOPE ---
    //
    // The two ctor chokepoints the §2 work missed:
    //  - `lookup_constructor_type_with_state` (the pattern-ctor `exists` gate)
    //  - `is_internal_constructor_check_with_state` (the internal-ctor reject gate)
    // both rooted at `current_module` with no outer-scope retry. With the prelude
    // no longer flattened, a primitives ADT ctor re-exported through prelude is
    // not an Import entry in the user table, so these paths missed it.

    // spec: 08-modules §8.6.4 — (a) a PUBLIC prelude ctor resolves in PATTERN
    // position via the outer-scope fallback. A bare ctor name absent from the
    // user module resolves its parent type through the prelude fallback when the
    // bit is ON — exactly as it does in value position.
    #[test]
    fn prelude_fallback_resolves_pattern_ctor_when_bit_on() {
        use cranelisp_types::TypeName;
        let mut tf = tf();
        // prelude defines a PUBLIC sum ADT `Maybe2` with ctors `Nada`/`Just2`.
        tf.set_current_module(ModuleFullPath::from("prelude"));
        tf.register_type_def_self(
            &TypeName::from("Maybe2"),
            &None,
            &[],
            &[
                cranelisp_types::ConstructorDef {
                    name: Symbol::from("Nada"),
                    docstring: None,
                    fields: vec![],
                    span: Span::SYNTHETIC,
                },
                cranelisp_types::ConstructorDef {
                    name: Symbol::from("Just2"),
                    docstring: None,
                    fields: vec![],
                    span: Span::SYNTHETIC,
                },
            ],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();

        let m = ModuleFullPath::from("app_pat");
        tf.set_current_module(m.clone());
        let state = CheckState::new(m.clone());

        // Bit OFF: the bare ctor's parent type does not resolve from M.
        assert!(
            tf.env().lookup_constructor_type_with_state(&state, "Just2").is_none(),
            "bit OFF: bare pattern ctor `Just2` must NOT resolve without the fallback"
        );

        // Bit ON: the pattern-ctor `exists` gate falls back to prelude and finds
        // the parent type `Maybe2`.
        set_fallback_on(&tf, "app_pat");
        assert_eq!(
            tf.env().lookup_constructor_type_with_state(&state, "Just2"),
            Some(TypeName::from("Maybe2")),
            "bit ON: bare pattern ctor `Just2` resolves its parent type via the prelude fallback"
        );
    }

    // spec: 09-macros §9.3 + 08-modules §8.6.6 — FIXME 0321 Root A. A
    // module-QUALIFIED SUM ctor (`macros/SCons`) resolves in pattern position
    // from a user module that has NOT imported `macros`. This is the
    // macro-clause-body context: quasiquote macros lower their templates into
    // qualified `macros/SCons`/`macros/SNil` ctor patterns, and an FQ reference
    // bypasses import scope (spec §8.6.6) to root directly in the named module.
    //
    // The S79 Option-3a cascade deleted the `lookup_constructor_scheme`
    // product-fallback leg, which was the only path that split the qualified
    // name on `/`. Without that split, the pattern-ctor resolver looked up the
    // literal key `"macros/SCons"` in the current module + prelude, missed, and
    // raised "unknown constructor in pattern: macros/SCons" — taking out ~89
    // macro-dependent tests. `resolve_constructor_entry` restores the split: a
    // qualified ctor roots in its named module via `resolve_entry_in_module`,
    // resolving through its `Def { Constructor }` entry. SCons is a SUM ctor
    // (`type_def: None` + a separate `TypeDef`); this must NOT depend on the
    // product type facet.
    #[test]
    fn fq_sum_ctor_resolves_in_pattern_from_unimporting_module() {
        use cranelisp_types::TypeName;
        let mut tf = tf_macros();
        // A user module that has NOT imported `macros` — the clause-fn body's
        // resolution context. No prelude fallback bit is set, so the qualified
        // reference cannot leak in via the outer scope; it must resolve purely
        // through the FQ `module/name` split.
        let m = ModuleFullPath::from("user");
        tf.set_current_module(m.clone());
        let state = CheckState::new(m.clone());
        let env = tf.env();

        // Bare `SCons` does NOT resolve from this module (no import, no
        // fallback) — proving the qualified arm, not an ambient import, is what
        // makes the resolution succeed.
        assert!(
            env.resolve_constructor_entry(&state, "SCons").is_none(),
            "bare `SCons` must NOT resolve from a module that has not imported macros"
        );

        // Qualified `macros/SCons` resolves to the SUM ctor's `Def`.
        let entry = env
            .resolve_constructor_entry(&state, "macros/SCons")
            .expect("qualified `macros/SCons` must resolve via the FQ module split");
        match entry {
            ModuleEntry::Def { kind, .. } => match kind.as_ref() {
                DefKind::Constructor { type_name, type_def, .. } => {
                    assert_eq!(
                        type_name.name,
                        TypeName::from("SList"),
                        "macros/SCons is the SList SUM ctor"
                    );
                    assert!(
                        type_def.is_none(),
                        "a SUM ctor carries `type_def: None` (the separate TypeDef \
                         holds the type) — it must NOT be confused with a product facet"
                    );
                }
                other => panic!("expected Constructor Def, got {other:?}"),
            },
            other => panic!("expected ModuleEntry::Def, got {other:?}"),
        }
    }

    // spec: 10-io §10.1 + 08-modules §8.6.4 — (b) the internal-ctor reject gate
    // sees a PUBLIC-but-INTERNAL prelude ctor (`Bind`) through the fallback and
    // reports `internal: true`. `Bind` is registered `Visibility::Public` in
    // `primitives`; prelude PUBLICLY re-exports it; a user module reaching it via
    // the fallback must still have it rejected (its `internal: true` Constructor
    // discriminator, NOT its visibility, is the rejection).
    #[test]
    fn prelude_fallback_internal_ctor_gate_rejects_bind() {
        let mut tf = tf_io();
        // prelude PUBLICLY re-exports `Bind` from primitives (an Import edge,
        // like `(export [primitives [*]])`).
        tf.set_current_module(ModuleFullPath::from("prelude"));
        tf.symbol_table_mut().insert(
            Symbol::from("Bind"),
            ModuleEntry::Import {
                source: FQSymbol {
                    module: ModuleFullPath::from("primitives"),
                    symbol: Symbol::from("Bind"),
                },
                visibility: Visibility::Public,
            },
        );
        // Also re-export a NON-internal IO ctor `Pure` to prove the gate returns
        // false for a reachable-but-not-internal ctor (not just "unreachable").
        tf.symbol_table_mut().insert(
            Symbol::from("Pure"),
            ModuleEntry::Import {
                source: FQSymbol {
                    module: ModuleFullPath::from("primitives"),
                    symbol: Symbol::from("Pure"),
                },
                visibility: Visibility::Public,
            },
        );

        let m = ModuleFullPath::from("app_bind");
        tf.set_current_module(m.clone());
        let state = CheckState::new(m.clone());

        // Bit OFF: the user table has no `Bind`, so the gate misses it and (the
        // §2 regression) fails to reject — false.
        assert!(
            !tf.env().is_internal_constructor_check_with_state(&state, "Bind"),
            "bit OFF: `Bind` absent from the user table — gate cannot reject it"
        );

        // Bit ON: the gate falls back to prelude, chain-follows the re-export to
        // the canonical primitives Constructor Def, and reads `internal: true`.
        set_fallback_on(&tf, "app_bind");
        assert!(
            tf.env().is_internal_constructor_check_with_state(&state, "Bind"),
            "bit ON: `Bind` is rejected as internal through the prelude fallback"
        );
        // A reachable-but-non-internal ctor (`Pure`) is NOT rejected.
        assert!(
            !tf.env().is_internal_constructor_check_with_state(&state, "Pure"),
            "bit ON: `Pure` is reachable through the fallback but NOT internal"
        );
    }

    // spec: 08-modules §8.6.4 — (c) bit OFF ⇒ no fallback for the ctor
    // chokepoints. With the bit absent/OFF, neither the pattern-ctor gate nor the
    // internal-ctor gate consults prelude.
    #[test]
    fn prelude_fallback_ctor_chokepoints_off_when_bit_off() {
        use cranelisp_types::TypeName;
        let mut tf = tf();
        // prelude PUBLICLY re-exports `Bind`, and defines a public ctor `Solo`.
        tf.set_current_module(ModuleFullPath::from("prelude"));
        tf.symbol_table_mut().insert(
            Symbol::from("Bind"),
            ModuleEntry::Import {
                source: FQSymbol {
                    module: ModuleFullPath::from("primitives"),
                    symbol: Symbol::from("Bind"),
                },
                visibility: Visibility::Public,
            },
        );
        tf.register_type_def_self(
            &TypeName::from("SoloT"),
            &None,
            &[],
            &[cranelisp_types::ConstructorDef {
                name: Symbol::from("Solo"),
                docstring: None,
                fields: vec![],
                span: Span::SYNTHETIC,
            }],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();

        let m = ModuleFullPath::from("app_off_ctor");
        tf.set_current_module(m.clone());
        let state = CheckState::new(m.clone());
        // No `set_fallback_on` — bit is absent (== OFF).

        assert!(
            tf.env().lookup_constructor_type_with_state(&state, "Solo").is_none(),
            "bit OFF: pattern-ctor gate must NOT fall back to prelude"
        );
        assert!(
            !tf.env().is_internal_constructor_check_with_state(&state, "Bind"),
            "bit OFF: internal-ctor gate must NOT fall back to prelude"
        );
    }

    // spec: 08-modules §8.7.3 (I-1) — (d) a PRIVATE prelude ctor is NOT reachable
    // through the fallback. A private sum-ADT ctor in prelude's own table must
    // not resolve as a bare pattern ctor in a user module, even with the bit ON.
    #[test]
    fn prelude_private_ctor_not_reachable_via_fallback() {
        use cranelisp_types::TypeName;
        let mut tf = tf();
        // prelude defines a PRIVATE sum ADT `HiddenT` with ctor `HiddenC`.
        tf.set_current_module(ModuleFullPath::from("prelude"));
        tf.register_type_def_self(
            &TypeName::from("HiddenT"),
            &None,
            &[],
            &[cranelisp_types::ConstructorDef {
                name: Symbol::from("HiddenC"),
                docstring: None,
                fields: vec![],
                span: Span::SYNTHETIC,
            }],
            Visibility::Private,
            Span::SYNTHETIC,
        )
        .unwrap();

        let m = ModuleFullPath::from("app_priv_ctor");
        tf.set_current_module(m.clone());
        set_fallback_on(&tf, "app_priv_ctor");

        let state = CheckState::new(m.clone());
        assert!(
            tf.env().lookup_constructor_type_with_state(&state, "HiddenC").is_none(),
            "a PRIVATE prelude ctor must NOT resolve as a bare pattern ctor (I-1)"
        );
    }
