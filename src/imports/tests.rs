    use super::*;
    use cranelisp_types::{Scheme, Type};
    use std::collections::HashMap as StdHashMap;

    fn tables() -> SessionTables {
        SessionTables::new()
    }

    /// Empty prelude-fallback ⇒ every module's bit OFF (no implicit-prelude
    /// outer scope). The default for import-mechanics tests that do not
    /// exercise the distinct-terminal prelude-overlap poison (FIXME 0514).
    fn no_pf() -> PreludeFallback {
        PreludeFallback::default()
    }

    fn ensure(tables: &SessionTables, path: &str) {
        let p = ModuleFullPath::from(path);
        tables
            .entry(p.clone())
            .or_insert_with(|| SessionSymbolTable::new_with_params(p));
    }

    /// A public primitive Def, as `primitives` carries `add-i64`.
    fn primitive_def() -> ModuleEntry<Code> {
        ModuleEntry::def(
            Scheme {
                type_vars: vec![],
                constraints: StdHashMap::new(),
                ty: Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int)),
            },
            DefKind::primitive(0),
        )
        .visibility(Visibility::Public)
        .build()
    }

    fn glob_spec(module: &str) -> ImportSpec {
        ImportSpec {
            module_path: ModuleFullPath::from(module),
            alias: None,
            names: ImportNames::Glob,
            span: Span::SYNTHETIC,
        }
    }

    fn glob_export(module: &str) -> ExportSpec {
        ExportSpec {
            module_path: ModuleFullPath::from(module),
            names: ImportNames::Glob,
            span: Span::SYNTHETIC,
        }
    }

    // spec: 08-modules.md §8.7.3 — a glob import brings in only PUBLIC names.
    // A primitive that arrives in `prelude` as `(import [primitives [*]])`
    // (Private binding) MUST NOT flow on to `user` through the implicit
    // prelude glob. This is the int-side guard for FIXME 0263: the dominant
    // "undefined variable: add-i64" failure class is a fixture defect, not an
    // int wiring defect — the import installer is spec-correct.
    #[test]
    fn glob_import_does_not_re_expose_private_imports() {
        let tables = tables();
        ensure(&tables, "primitives");
        ensure(&tables, "prelude");
        ensure(&tables, "user");
        let aliases = ModuleAliases::default();

        // primitives carries a public Def for add-i64.
        tables
            .get_mut(&ModuleFullPath::from("primitives"))
            .unwrap()
            .insert(Symbol::from("add-i64"), primitive_def());

        // prelude does `(import [primitives [*]])` → Private bindings in prelude.
        install_imports(
            &tables,
            &ModuleFullPath::from("prelude"),
            &aliases,
            &no_pf(),
            &[glob_spec("primitives")],
        )
        .unwrap();

        // The prelude binding is present but Private.
        {
            let prelude = tables.get(&ModuleFullPath::from("prelude")).unwrap();
            let entry = prelude.get("add-i64").expect("prelude has the import");
            assert!(
                !entry.is_public(),
                "an `(import …)` binding MUST be Private (spec §8.7.3)",
            );
        }

        // user does the implicit `(import [prelude [*]])`.
        install_imports(
            &tables,
            &ModuleFullPath::from("user"),
            &aliases,
            &no_pf(),
            &[glob_spec("prelude")],
        )
        .unwrap();

        // user MUST NOT have received add-i64 — prelude's binding was Private.
        let user = tables.get(&ModuleFullPath::from("user")).unwrap();
        assert!(
            user.get("add-i64").is_none(),
            "Private prelude import MUST NOT flow through the user glob \
             (spec §8.7.3) — this is what produces `undefined variable: add-i64` \
             when a fixture uses `import` instead of `export` (FIXME 0263)",
        );
    }

    // spec: 08-modules.md §8.4 + §8.8 — a re-export (`export`) makes a name
    // PUBLIC in the re-exporting module, so it DOES flow through a downstream
    // glob. This is the spec-conformant prelude shape; the int installer
    // implements it correctly.
    #[test]
    fn glob_picks_up_re_exported_public_names() {
        let tables = tables();
        ensure(&tables, "primitives");
        ensure(&tables, "prelude");
        ensure(&tables, "user");
        let aliases = ModuleAliases::default();

        tables
            .get_mut(&ModuleFullPath::from("primitives"))
            .unwrap()
            .insert(Symbol::from("add-i64"), primitive_def());

        // prelude does `(export [primitives [*]])` → Public re-export bindings.
        install_exports(
            &tables,
            &ModuleFullPath::from("prelude"),
            &no_pf(),
            None,
            &[glob_export("primitives")],
        )
        .unwrap();

        {
            let prelude = tables.get(&ModuleFullPath::from("prelude")).unwrap();
            let entry = prelude.get("add-i64").expect("prelude re-exports it");
            assert!(
                entry.is_public(),
                "an `(export …)` re-export binding MUST be Public (spec §8.4)",
            );
        }

        // user's implicit prelude glob now picks it up.
        install_imports(
            &tables,
            &ModuleFullPath::from("user"),
            &aliases,
            &no_pf(),
            &[glob_spec("prelude")],
        )
        .unwrap();

        let user = tables.get(&ModuleFullPath::from("user")).unwrap();
        let entry = user
            .get("add-i64")
            .expect("re-exported primitive MUST flow through the user glob");
        match entry {
            ModuleEntry::Import { source, .. } => {
                // Provenance chain-follows to prelude (one hop); the terminal
                // resolve to primitives is the resolver's job, not the installer's.
                assert_eq!(source.module, ModuleFullPath::from("prelude"));
            }
            other => panic!("expected an Import binding, got {other:?}"),
        }
    }

    fn specific_spec(module: &str, name: &str) -> ImportSpec {
        ImportSpec {
            module_path: ModuleFullPath::from(module),
            alias: None,
            names: ImportNames::Specific(vec![Symbol::from(name)]),
            span: Span::SYNTHETIC,
        }
    }

    fn specific_export(module: &str, name: &str) -> ExportSpec {
        ExportSpec {
            module_path: ModuleFullPath::from(module),
            names: ImportNames::Specific(vec![Symbol::from(name)]),
            span: Span::SYNTHETIC,
        }
    }

    // spec: 08-modules.md §8.4 — a module that first `(import [base [x]])`s a
    // name (Private binding) and then `(export [base [x]])`s the SAME name MUST
    // end up with a PUBLIC binding for `x`. Both edges share the same source
    // (`base/x`); the installer's same-source dedup must NOT swallow the
    // Public re-export and leave the name Private. Defect A repro
    // (spec_09::cross_module_macro_transitive_via_reexport_chain): without the
    // visibility-upgrade branch a downstream importer of the re-exporting
    // module saw "'x' is not public in '<relay>'".
    #[test]
    fn import_then_export_same_source_upgrades_to_public() {
        let tables = tables();
        ensure(&tables, "base");
        ensure(&tables, "relay");
        ensure(&tables, "downstream");
        let aliases = ModuleAliases::default();

        // base defines a public `base-val`.
        tables
            .get_mut(&ModuleFullPath::from("base"))
            .unwrap()
            .insert(Symbol::from("base-val"), primitive_def());

        // relay: (import [base [base-val]]) → Private binding (source base/base-val).
        install_imports(
            &tables,
            &ModuleFullPath::from("relay"),
            &aliases,
            &no_pf(),
            &[specific_spec("base", "base-val")],
        )
        .unwrap();
        {
            let relay = tables.get(&ModuleFullPath::from("relay")).unwrap();
            assert!(
                !relay.get("base-val").unwrap().is_public(),
                "the bare import binding must start Private",
            );
        }

        // relay: (export [base [base-val]]) → same source, Public. MUST upgrade.
        install_exports(
            &tables,
            &ModuleFullPath::from("relay"),
            &no_pf(),
            None,
            &[specific_export("base", "base-val")],
        )
        .unwrap();
        {
            let relay = tables.get(&ModuleFullPath::from("relay")).unwrap();
            assert!(
                relay.get("base-val").unwrap().is_public(),
                "import-then-export of the same source MUST yield a Public \
                 binding (spec §8.4) — the same-source dedup must not swallow \
                 the re-export's visibility upgrade",
            );
        }

        // Downstream module can now import the re-exported name from relay.
        install_imports(
            &tables,
            &ModuleFullPath::from("downstream"),
            &aliases,
            &no_pf(),
            &[specific_spec("relay", "base-val")],
        )
        .expect(
            "a specific import of the re-exported name from relay MUST succeed \
             — it is now public there",
        );
    }

    // spec: 08-modules.md §8.4 — the reverse order (export before import, or a
    // second identical import after an export) MUST NOT DOWNGRADE an
    // already-public re-export back to Private. Guards the upgrade branch
    // against a visibility regression on a later same-source private import.
    #[test]
    fn export_then_import_same_source_stays_public() {
        let tables = tables();
        ensure(&tables, "base");
        ensure(&tables, "relay");
        let aliases = ModuleAliases::default();

        tables
            .get_mut(&ModuleFullPath::from("base"))
            .unwrap()
            .insert(Symbol::from("base-val"), primitive_def());

        // Public re-export first.
        install_exports(
            &tables,
            &ModuleFullPath::from("relay"),
            &no_pf(),
            None,
            &[specific_export("base", "base-val")],
        )
        .unwrap();
        // Then a (redundant) private import of the same source.
        install_imports(
            &tables,
            &ModuleFullPath::from("relay"),
            &aliases,
            &no_pf(),
            &[specific_spec("base", "base-val")],
        )
        .unwrap();

        let relay = tables.get(&ModuleFullPath::from("relay")).unwrap();
        assert!(
            relay.get("base-val").unwrap().is_public(),
            "a later same-source Private import MUST NOT downgrade an existing \
             Public re-export",
        );
    }

    // spec: 08-modules.md §8.6.4 — TERMINAL-source dedup at the installer seam.
    // `prim` defines `Foo`; `reexp` re-exports `prim/Foo`. A module that imports
    // `Foo` BOTH via a glob of `prim` (immediate source `prim`) AND specifically
    // from `reexp` (immediate source `reexp`) brings two bindings whose chains
    // terminate at the SAME `(prim, Foo)`. They MUST dedup silently — no error,
    // no `Ambiguous` sentinel. This pins the terminal-resolve logic at the seam
    // (the e2e proves the user path; this pins the chain-follow comparison).
    #[test]
    fn same_terminal_two_paths_dedup_no_ambiguity() {
        let tables = tables();
        ensure(&tables, "prim");
        ensure(&tables, "reexp");
        ensure(&tables, "main");
        let aliases = ModuleAliases::default();

        // prim defines a public `Foo`.
        tables
            .get_mut(&ModuleFullPath::from("prim"))
            .unwrap()
            .insert(Symbol::from("Foo"), primitive_def());

        // reexp re-exports prim/Foo (Public Import edge → prim).
        install_exports(
            &tables,
            &ModuleFullPath::from("reexp"),
            &no_pf(),
            None,
            &[specific_export("prim", "Foo")],
        )
        .unwrap();

        // main globs prim (brings Foo, source prim) ...
        install_imports(
            &tables,
            &ModuleFullPath::from("main"),
            &aliases,
            &no_pf(),
            &[glob_spec("prim")],
        )
        .expect("glob of prim installs Foo");

        // ... and specifically imports Foo from reexp (source reexp, terminal prim/Foo).
        install_imports(
            &tables,
            &ModuleFullPath::from("main"),
            &aliases,
            &no_pf(),
            &[specific_spec("reexp", "Foo")],
        )
        .expect(
            "a glob + a re-export of the same terminal definition MUST dedup \
             silently (spec §8.6.4 terminal-source comparison) — NOT error",
        );

        let main = tables.get(&ModuleFullPath::from("main")).unwrap();
        let entry = main.get("Foo").expect("Foo is installed");
        assert!(
            !matches!(entry, ModuleEntry::Ambiguous { .. }),
            "same-terminal dedup MUST NOT poison the name as Ambiguous; got {entry:?}",
        );
    }

    // spec: 08-modules.md §8.6.5 — distinct-terminal collision at the seam. `a`
    // and `b` each define their OWN, DIFFERENT `Bar`. Importing both bare MUST
    // error, and the diagnostic MUST name BOTH qualified alternatives (`a/Bar`,
    // `b/Bar`) so the user can disambiguate. The poison sentinel is also
    // installed (poison-on-reference model), but the eager error is what carries
    // the alternatives (the sentinel variant has no payload).
    #[test]
    fn distinct_terminals_error_naming_both_alternatives() {
        let tables = tables();
        ensure(&tables, "a");
        ensure(&tables, "b");
        ensure(&tables, "main");
        let aliases = ModuleAliases::default();

        tables
            .get_mut(&ModuleFullPath::from("a"))
            .unwrap()
            .insert(Symbol::from("Bar"), primitive_def());
        tables
            .get_mut(&ModuleFullPath::from("b"))
            .unwrap()
            .insert(Symbol::from("Bar"), primitive_def());

        // main imports a/Bar bare (no collision yet).
        install_imports(
            &tables,
            &ModuleFullPath::from("main"),
            &aliases,
            &no_pf(),
            &[specific_spec("a", "Bar")],
        )
        .expect("first bare import of Bar installs cleanly");

        // main imports b/Bar bare → distinct terminal → MUST error.
        let err = install_imports(
            &tables,
            &ModuleFullPath::from("main"),
            &aliases,
            &no_pf(),
            &[specific_spec("b", "Bar")],
        )
        .expect_err(
            "two DISTINCT terminal `Bar` definitions imported under the same \
             bare name MUST collide (spec §8.6.5 footgun protection)",
        );

        let msg = match &err {
            CranelispError::TypeError { message, .. } => message.clone(),
            other => panic!("expected a TypeError, got {other:?}"),
        };
        assert!(
            msg.to_lowercase().contains("ambiguous"),
            "the diagnostic MUST identify the conflict as ambiguous; got: {msg}",
        );
        assert!(
            msg.contains("a/Bar") && msg.contains("b/Bar"),
            "the diagnostic MUST name BOTH qualified alternatives \
             (`a/Bar` and `b/Bar`); got: {msg}",
        );

        // The poison sentinel is installed too (poison-on-reference model).
        let main = tables.get(&ModuleFullPath::from("main")).unwrap();
        assert!(
            matches!(main.get("Bar"), Some(ModuleEntry::Ambiguous { .. })),
            "the colliding name MUST be poisoned with the Ambiguous sentinel",
        );
    }

    // spec: 08-modules.md §8.11.2 (step 1) — install_imports resolves a BARE submodule
    // name current-module-relative (try as-is, then `<current>.<name>`), SYMMETRIC with
    // install_exports. A bare `(import [child [foo]])` inside a `(mod child)`-declaring
    // `shell` registers `foo` sourced from `shell.child`, not a root `child` (which
    // errored "unknown module 'child'"). This closes the import half of the mirror the
    // dependency.rs current-module-relative helper's own doc names (only the export
    // side was wired before). RED-on-revert: dropping the relative resolution in
    // install_imports makes this error.
    #[test]
    fn install_imports_resolves_bare_submodule_current_module_relative() {
        let tables = tables();
        ensure(&tables, "shell");
        ensure(&tables, "shell.child");
        let aliases = ModuleAliases::default();

        // The child submodule defines a public `foo`.
        tables
            .get_mut(&ModuleFullPath::from("shell.child"))
            .unwrap()
            .insert(Symbol::from("foo"), primitive_def());

        // shell does `(import [child [foo]])` — module_path is the BARE `child`.
        install_imports(
            &tables,
            &ModuleFullPath::from("shell"),
            &aliases,
            &no_pf(),
            &[specific_spec("child", "foo")],
        )
        .expect(
            "a bare submodule import must resolve current-module-relative to \
             shell.child (§8.11.2 step 1) — not error 'unknown module child'",
        );

        let shell = tables.get(&ModuleFullPath::from("shell")).unwrap();
        match shell.get("foo").expect("foo installed in shell") {
            ModuleEntry::Import { source, .. } => {
                assert_eq!(
                    source.module,
                    ModuleFullPath::from("shell.child"),
                    "foo must be sourced from the shell.child submodule, not root child",
                );
            }
            other => panic!("expected an Import binding for foo, got {other:?}"),
        }
    }

    // spec: 08-modules.md §8.11.2 — NEGATIVE: a bare import name with NO
    // current-module-relative candidate (no `<current>.<name>` table) still errors
    // "unknown module" — the relative resolution is a fallback that never masks a
    // genuinely-missing module.
    #[test]
    fn install_imports_bare_name_without_submodule_errors() {
        let tables = tables();
        ensure(&tables, "shell");
        let aliases = ModuleAliases::default();
        let err = install_imports(
            &tables,
            &ModuleFullPath::from("shell"),
            &aliases,
            &no_pf(),
            &[specific_spec("nope", "foo")],
        )
        .expect_err("a bare name with no submodule candidate must still error");
        match err {
            CranelispError::TypeError { message, .. } => assert!(
                message.contains("unknown module 'nope'"),
                "the error must name the genuinely-missing module; got: {message}",
            ),
            other => panic!("expected a TypeError, got {other:?}"),
        }
    }

    // -----------------------------------------------------------------------
    // install_module_session_env (S102 CS-D3a) — the cache-restore / blank-mod
    // env-companion recompute from a table's structural fields.
    // spec: spec/08-modules.md §8.8.1 (implicit prelude suppression) + §8.3.4
    // (import alias) + §8.2.6 (submodule short-name alias)
    // -----------------------------------------------------------------------

    fn env_maps() -> (ModuleAliases, cranelisp_typecheck::PreludeFallback) {
        (ModuleAliases::default(), cranelisp_typecheck::PreludeFallback::default())
    }

    fn set_imports(tables: &SessionTables, module: &str, imports: Vec<ImportSpec>) {
        let mut g = tables.get_mut(&ModuleFullPath::from(module)).unwrap();
        g.imports = imports;
    }

    // A plain module that does not reference prelude gets the fallback bit ON —
    // the structural mirror of `inject_prelude_if_needed`'s ON path, so a
    // cache-restored/blank module's next `/mod` turn compiles with the implicit
    // prelude (bare `+`/`:Int` resolve).
    #[test]
    fn session_env_plain_module_sets_prelude_bit_on() {
        let tables = tables();
        ensure(&tables, "m");
        let (aliases, fallback) = env_maps();
        install_module_session_env(&tables, &ModuleFullPath::from("m"), &aliases, &fallback);
        assert_eq!(
            fallback.get(&ModuleFullPath::from("m")).map(|b| *b),
            Some(true),
            "a module with no explicit prelude reference gets the fallback bit ON",
        );
    }

    // A module that imports prelude EXPLICITLY keeps the bit OFF (absence-is-OFF)
    // — the §8.8.1 suppression, structural half. Negative cell.
    #[test]
    fn session_env_explicit_prelude_import_keeps_bit_off() {
        let tables = tables();
        ensure(&tables, "m");
        set_imports(&tables, "m", vec![glob_spec("prelude")]);
        let (aliases, fallback) = env_maps();
        install_module_session_env(&tables, &ModuleFullPath::from("m"), &aliases, &fallback);
        assert!(
            fallback.get(&ModuleFullPath::from("m")).map(|b| *b) != Some(true),
            "a module importing prelude explicitly must NOT get the implicit-fallback bit",
        );
    }

    // The prelude module itself never gets the fallback bit (it IS the outer
    // scope). Negative cell.
    #[test]
    fn session_env_prelude_module_never_gets_bit() {
        let tables = tables();
        ensure(&tables, "prelude");
        let (aliases, fallback) = env_maps();
        install_module_session_env(&tables, &ModuleFullPath::from("prelude"), &aliases, &fallback);
        assert!(
            fallback.get(&ModuleFullPath::from("prelude")).is_none(),
            "prelude must not fall back to itself",
        );
    }

    // Import `as`-aliases are re-registered keyed `<module>.<alias>` — the alias
    // half of `install_imports`, restored from the serialized `imports` field.
    #[test]
    fn session_env_reregisters_import_alias() {
        let tables = tables();
        ensure(&tables, "m");
        let aliased = ImportSpec {
            module_path: ModuleFullPath::from("util"),
            alias: Some(cranelisp_types::ModuleName::from("u")),
            names: ImportNames::Glob,
            span: Span::SYNTHETIC,
        };
        set_imports(&tables, "m", vec![aliased]);
        let (aliases, fallback) = env_maps();
        install_module_session_env(&tables, &ModuleFullPath::from("m"), &aliases, &fallback);
        let entry = aliases.get(&ModuleFullPath::from("m.u"));
        assert!(entry.is_some(), "alias `<module>.<alias>` (m.u) must be registered");
        assert_eq!(
            entry.unwrap().target.as_ref(),
            "util",
            "the alias must point at the imported module",
        );
    }

    // Submodule short-name aliases are re-registered keyed by the bare name →
    // `<module>.<name>` — mirror of `register_submodule_alias`.
    #[test]
    fn session_env_reregisters_submodule_alias() {
        let tables = tables();
        ensure(&tables, "shell");
        {
            let mut g = tables.get_mut(&ModuleFullPath::from("shell")).unwrap();
            g.submodules = vec![cranelisp_types::ModDecl {
                name: cranelisp_types::ModuleName::from("child"),
                visibility: Visibility::Private,
                inline_body: None,
                span: Span::SYNTHETIC,
            }];
        }
        let (aliases, fallback) = env_maps();
        install_module_session_env(&tables, &ModuleFullPath::from("shell"), &aliases, &fallback);
        let entry = aliases.get(&ModuleFullPath::from("child"));
        assert!(entry.is_some(), "submodule short-name alias `child` must be registered");
        assert_eq!(
            entry.unwrap().target.as_ref(),
            "shell.child",
            "the short-name alias must point at the full submodule path",
        );
    }

    // Idempotent: re-running yields the same bit (a cache-restore install
    // followed by a `/mod` turn both call it).
    #[test]
    fn session_env_is_idempotent() {
        let tables = tables();
        ensure(&tables, "m");
        let (aliases, fallback) = env_maps();
        let m = ModuleFullPath::from("m");
        install_module_session_env(&tables, &m, &aliases, &fallback);
        install_module_session_env(&tables, &m, &aliases, &fallback);
        assert_eq!(fallback.get(&m).map(|b| *b), Some(true));
    }

    // =====================================================================
    // §8.6.4 (FIXME 0516) — the def/import symmetric collision is enforced at
    // ONE shared predicate (`cranelisp_types::check_binding_addition`), called
    // at BOTH binding events. The def-event fires at the typecheck `check_forms`
    // seam (a def registered over an installed import); the IMPORT-event fires
    // HERE (an import/export installed over an existing module-local def — the
    // #8 cross-cluster REPL case the def-seam cannot catch, because no def
    // registers in the import's cluster). Same rule, both events, all modes —
    // no dual path (the pre-0516 installer silently SKIPPED this direction,
    // which was the #8 mode-divergence hole).
    // =====================================================================

    // spec: 08-modules.md §8.6.4 — the IMPORT-event arm: an `import` that binds
    // a bare name already held by a module-LOCAL definition is a collision,
    // rejected via the shared predicate (the symmetric companion of
    // def-over-import; closes the #8 REPL separate-turn hole, FIXME 0516
    // Issue 2). The FQ remedy names the import's terminal.
    #[test]
    fn import_over_local_def_rejected_via_shared_predicate() {
        let tables = tables();
        ensure(&tables, "base");
        ensure(&tables, "user");
        let aliases = ModuleAliases::default();
        tables
            .get_mut(&ModuleFullPath::from("user"))
            .unwrap()
            .insert(Symbol::from("measure"), primitive_def());
        tables
            .get_mut(&ModuleFullPath::from("base"))
            .unwrap()
            .insert(Symbol::from("measure"), primitive_def());

        let err = install_imports(
            &tables,
            &ModuleFullPath::from("user"),
            &aliases,
            &no_pf(),
            &[specific_spec("base", "measure")],
        )
        .expect_err(
            "an import over an existing module-local def MUST reject \
             (§8.6.4 symmetric companion; FIXME 0516 #8)",
        );
        let msg = match &err {
            CranelispError::TypeError { message, .. } => message.to_lowercase(),
            other => panic!("expected a TypeError, got {other:?}"),
        };
        assert!(msg.contains("conflict"), "collision diagnostic: {msg}");
        assert!(msg.contains("base/measure"), "remedy FQ present: {msg}");
        // The local def stays the binding — the rejected import had no effect.
        let user = tables.get(&ModuleFullPath::from("user")).unwrap();
        assert!(matches!(user.get("measure"), Some(ModuleEntry::Def { .. })));
    }

    // spec: 08-modules.md §8.6.4/§8.4.0 — the EXPORT order: an `export` (a
    // Public inner Import edge) over an existing module-local def rejects
    // identically (the incoming Export vs existing Definition arm of the shared
    // predicate). Pins event-parity across import AND export incoming edges.
    #[test]
    fn export_over_local_def_rejected_via_shared_predicate() {
        let tables = tables();
        ensure(&tables, "base");
        ensure(&tables, "user");
        tables
            .get_mut(&ModuleFullPath::from("user"))
            .unwrap()
            .insert(Symbol::from("measure"), primitive_def());
        tables
            .get_mut(&ModuleFullPath::from("base"))
            .unwrap()
            .insert(Symbol::from("measure"), primitive_def());

        let err = install_exports(
            &tables,
            &ModuleFullPath::from("user"),
            &no_pf(),
            None,
            &[specific_export("base", "measure")],
        )
        .expect_err("an export over a module-local def MUST reject (§8.6.4)");
        let msg = match &err {
            CranelispError::TypeError { message, .. } => message.to_lowercase(),
            other => panic!("expected a TypeError, got {other:?}"),
        };
        assert!(msg.contains("conflict"), "collision diagnostic: {msg}");
        let user = tables.get(&ModuleFullPath::from("user")).unwrap();
        assert!(matches!(user.get("measure"), Some(ModuleEntry::Def { .. })));
    }

    /// A public local `deftrait` binding (`ModuleEntry::TraitDecl`) named `name`.
    fn trait_decl(name: &str) -> ModuleEntry<Code> {
        ModuleEntry::TraitDecl {
            info: cranelisp_types::TraitDeclInfo {
                name: TraitName::from(name),
                type_params: vec![],
                methods: vec![],
            },
            visibility: Visibility::Public,
            docstring: None,
        }
    }

    // spec: 08-modules.md §8.6.4 (S108 Wave-G CS2) — the local-definition arm of
    // the import-event seam now includes `TraitDecl`: an `import` binding a bare
    // name already held by a module-LOCAL `deftrait` is a §8.6.4 collision,
    // rejected via the shared predicate. Fail-on-revert: dropping `TraitDecl`
    // from the arm makes the import silently win (Ok), failing this expect_err.
    #[test]
    fn import_over_local_trait_decl_rejected_via_shared_predicate() {
        let tables = tables();
        ensure(&tables, "base");
        ensure(&tables, "user");
        let aliases = ModuleAliases::default();
        // user defines a local trait `Show`; base carries a distinct public one.
        tables
            .get_mut(&ModuleFullPath::from("user"))
            .unwrap()
            .insert(Symbol::from("Show"), trait_decl("Show"));
        tables
            .get_mut(&ModuleFullPath::from("base"))
            .unwrap()
            .insert(Symbol::from("Show"), trait_decl("Show"));

        let err = install_imports(
            &tables,
            &ModuleFullPath::from("user"),
            &aliases,
            &no_pf(),
            &[specific_spec("base", "Show")],
        )
        .expect_err(
            "an import over a module-local deftrait (TraitDecl) MUST reject \
             (§8.6.4 symmetric companion; CS2 TraitDecl widening)",
        );
        let msg = match &err {
            CranelispError::TypeError { message, .. } => message.to_lowercase(),
            other => panic!("expected a TypeError, got {other:?}"),
        };
        assert!(msg.contains("conflict"), "collision diagnostic: {msg}");
        // The local trait stays the binding — the rejected import had no effect.
        let user = tables.get(&ModuleFullPath::from("user")).unwrap();
        assert!(matches!(user.get("Show"), Some(ModuleEntry::TraitDecl { .. })));
    }

    // spec: 08-modules.md §8.4.0 — a module can USE a name it only EXPORTS.
    // `export` populates the exporting module's OWN bare scope (a resolvable
    // `ModuleEntry::Import` entry, Public), identically to `import` but Public.
    // Part A: no prior `(import …)` of the name is needed for it to be usable.
    #[test]
    fn export_only_binds_name_in_exporting_module_scope() {
        let tables = tables();
        ensure(&tables, "base");
        ensure(&tables, "user");
        tables
            .get_mut(&ModuleFullPath::from("base"))
            .unwrap()
            .insert(Symbol::from("helper"), primitive_def());

        // user does ONLY `(export [base [helper]])` — no import of `helper`.
        install_exports(
            &tables,
            &ModuleFullPath::from("user"),
            &no_pf(),
            None,
            &[specific_export("base", "helper")],
        )
        .unwrap();

        let user = tables.get(&ModuleFullPath::from("user")).unwrap();
        let entry = user
            .get("helper")
            .expect("export must bring the name into the exporting module's scope");
        // It is an Import edge (resolvable per §8.6.2 chain-follow → usable in
        // this module's own bodies) AND Public (part of the public API).
        assert!(
            matches!(entry, ModuleEntry::Import { .. }) && entry.is_public(),
            "an export-only name is a Public inner-scope Import edge (§8.4.0)",
        );
    }

    // spec: 08-modules.md §8.6.4 (terminal-source dedup) — the redundant
    // `(import [base [x]]) (export [base [x]])` pair is NOT a collision: both
    // edges name the same terminal (`base/x`), so they dedup (import → Public
    // upgrade), never reject. The critical negative for constraint #2.
    #[test]
    fn redundant_import_then_export_dedups_to_public() {
        let tables = tables();
        ensure(&tables, "base");
        ensure(&tables, "user");
        let aliases = ModuleAliases::default();
        tables
            .get_mut(&ModuleFullPath::from("base"))
            .unwrap()
            .insert(Symbol::from("x"), primitive_def());

        install_imports(
            &tables,
            &ModuleFullPath::from("user"),
            &aliases,
            &no_pf(),
            &[specific_spec("base", "x")],
        )
        .expect("import installs cleanly");
        // The SAME name via export — redundant, must dedup+upgrade, not reject.
        install_exports(
            &tables,
            &ModuleFullPath::from("user"),
            &no_pf(),
            None,
            &[specific_export("base", "x")],
        )
        .expect("redundant import+export of the same terminal must NOT collide");

        let user = tables.get(&ModuleFullPath::from("user")).unwrap();
        let entry = user.get("x").expect("x is bound");
        assert!(
            matches!(entry, ModuleEntry::Import { .. }) && entry.is_public(),
            "redundant pair upgrades to a Public import edge (§8.4.0)",
        );
    }

    // -----------------------------------------------------------------------
    // R7/0604 prelude-export-closure seam assert (index-worker-isolation.md §8)
    // -----------------------------------------------------------------------

    fn public_import_entry(src_module: &str, src_symbol: &str) -> ModuleEntry<Code> {
        ModuleEntry::Import {
            source: FQSymbol {
                module: ModuleFullPath::from(src_module),
                symbol: src_symbol.into(),
            },
            visibility: Visibility::Public,
        }
    }

    // A legitimate prelude re-export (`(export [primitives [*]])` bringing
    // `add-i64`, which primitives genuinely provides publicly) is closure-valid —
    // the assert is a no-op (no panic).
    // spec: index-worker-isolation.md §8.1 — prelude-export closure invariant.
    #[test]
    fn assert_prelude_closure_permits_legitimate_reexport() {
        let tables = tables();
        ensure(&tables, "primitives");
        ensure(&tables, "prelude");
        tables
            .get_mut(&ModuleFullPath::from("primitives"))
            .unwrap()
            .insert("add-i64".into(), primitive_def());
        // A public re-export edge into prelude whose source (primitives) really
        // provides `add-i64` — closure-valid, no panic.
        let entry = public_import_entry("primitives", "add-i64");
        assert_prelude_closure(
            &tables,
            &ModuleFullPath::from("prelude"),
            "add-i64",
            &entry,
        );
    }

    // Prelude's OWN definition (a non-`Import` public entry) is exported by §8.4 —
    // closure-valid regardless of source, no panic.
    // spec: index-worker-isolation.md §8.1.
    #[test]
    fn assert_prelude_closure_permits_prelude_own_definition() {
        let tables = tables();
        ensure(&tables, "prelude");
        let entry = primitive_def(); // a public non-Import Def
        assert_prelude_closure(&tables, &ModuleFullPath::from("prelude"), "map", &entry);
    }

    // A non-prelude target is never checked — the assert is a no-op even for a
    // bogus write (the invariant is prelude-specific).
    // spec: index-worker-isolation.md §8.1.
    #[test]
    fn assert_prelude_closure_ignores_non_prelude_module() {
        let tables = tables();
        ensure(&tables, "user");
        let entry = public_import_entry("primitives", "bit-and");
        assert_prelude_closure(&tables, &ModuleFullPath::from("user"), "bit-and", &entry);
    }

    // The PHANTOM: a public `bit-and → primitives/bit-and` written into prelude,
    // where primitives does NOT provide `bit-and` (it is homed in num.bits) — the
    // FIXME 0604 write mis-targeting prelude. The seam assert TRIPS (debug), so a
    // future firing NAMES the seam instead of a silent phantom.
    // spec: index-worker-isolation.md §8.1 — the phantom prelude write.
    #[test]
    #[should_panic(expected = "R7 prelude-export-closure breach")]
    fn assert_prelude_closure_trips_on_phantom_write() {
        let tables = tables();
        ensure(&tables, "primitives"); // exists but has NO bit-and
        ensure(&tables, "prelude");
        let entry = public_import_entry("primitives", "bit-and");
        assert_prelude_closure(
            &tables,
            &ModuleFullPath::from("prelude"),
            "bit-and",
            &entry,
        );
    }

    // -----------------------------------------------------------------------
    // FIXME 0604 — the promoted terminal-closure CHOKEPOINT (§2.2 / §4 item 1).
    //
    // The unconditional, generalized, DIAGNOSED sibling of the prelude-only
    // observability rider above: fires in EVERY build (returns `Err`, not a
    // debug-only panic) and for ANY module (not just prelude). Fail-on-revert:
    // deleting the gate call at a public-insert seam lets the phantom write land.
    // -----------------------------------------------------------------------

    /// A declared-export set `D(M)` that does NOT include `bit-and` (mirrors
    /// `stdlib/prelude.cl`'s curated specific-primitive re-export list — NOT a
    /// glob; `bit-and` is in none of prelude's export specs).
    fn declared_without_bit_and() -> HashSet<Symbol> {
        [Symbol::from("Int"), Symbol::from("Bool"), Symbol::from("Float"), Symbol::from("String")]
            .into_iter()
            .collect()
    }

    // A public re-export `bit-and → primitives/bit-and` written into a TERMINAL
    // prelude table whose DECLARED export closure D(prelude) does NOT include the
    // name is REJECTED + diagnosed — the chokepoint's core enforcement.
    // S115 (FIXME 0604): the predicate keys on the DESTINATION's declared exports
    // `D(M)`, not on source-provider existence (the S114 predicate was blind to
    // the live phantom because `bit-and` IS a bundled primitive — see the
    // provides-name-but-outside-declared-exports discriminating trigger below).
    // spec: prelude-table-write-isolation.md §2.2 — declared-export-closure gate.
    #[test]
    fn check_terminal_closure_rejects_out_of_closure_public_write() {
        let entry = public_import_entry("primitives", "bit-and");
        let d = declared_without_bit_and();
        let res = check_terminal_closure(
            &ModuleFullPath::from("prelude"),
            "bit-and",
            &entry,
            cranelisp_types::Span::SYNTHETIC,
            Some(&d),
        );
        let err = res.expect_err("out-of-closure public write (bit-and ∉ D(prelude)) must be rejected");
        // Diagnosed: names the breached module + source edge (a located defect,
        // not a quiet-environment hunt).
        let msg = format!("{err:?}");
        assert!(msg.contains("bit-and"), "diagnostic names the name: {msg}");
        assert!(msg.contains("0604"), "diagnostic attributes to FIXME 0604: {msg}");
    }

    // THE SYNTHESIZED-TRIGGER GUARD (FIXME 0604 §3.1 / tests/plan/s115-test-plan.md
    // §3.1) — the DISCRIMINATING cell the corrected predicate needs. The source
    // module `primitives` GENUINELY provides `bit-and` publicly (the live
    // phantom's exact shape — `cranelisp-primitives/src/lib.rs:412`), so the S114
    // PROVIDER-EXISTENCE predicate would PASS it. The corrected DECLARED-EXPORT-
    // CLOSURE predicate rejects it because `bit-and ∉ D(prelude)`. RED against the
    // old predicate by construction, GREEN with the correction, interleaving-
    // independent (a direct call against constructed tables, no session, no
    // threads) — the fail-on-revert guard for the CORRECTION (not just the gate).
    // spec: prelude-table-write-isolation.md §2.2 — provides-name-but-outside-D(M).
    // defect: class=shared-state-write-race locus=src/imports.rs::write_is_closure_valid found=S115 owner=/dev
    #[test]
    fn check_terminal_closure_rejects_provided_name_outside_declared_exports() {
        let tables = tables();
        // primitives REALLY provides bit-and publicly (the phantom's genuine
        // provider — provider-existence would pass).
        ensure(&tables, "primitives");
        tables
            .get_mut(&ModuleFullPath::from("primitives"))
            .unwrap()
            .insert(Symbol::from("bit-and"), primitive_def());
        // ...but bit-and is OUTSIDE prelude's declared export closure.
        let entry = public_import_entry("primitives", "bit-and");
        let d = declared_without_bit_and();
        let res = check_terminal_closure(
            &ModuleFullPath::from("prelude"),
            "bit-and",
            &entry,
            cranelisp_types::Span::SYNTHETIC,
            Some(&d),
        );
        let err = res.expect_err(
            "a public re-export whose source PROVIDES the name but whose name is \
             OUTSIDE D(prelude) must be rejected (the discriminating trigger the \
             old provider-existence predicate could not catch)",
        );
        let msg = format!("{err:?}");
        assert!(msg.contains("bit-and"), "diagnostic names the phantom: {msg}");
        assert!(msg.contains("0604"), "diagnostic attributes to FIXME 0604: {msg}");
    }

    // FALSE-FIRE FENCE (FIXME 0604 §3.1 item 2): a public re-export whose name IS
    // in D(M) passes — the corrected predicate must not reject the legal declared
    // population. Fail-on-revert of an over-strict correction.
    // spec: prelude-table-write-isolation.md §2.2 — name ∈ D(M) permits.
    #[test]
    fn check_terminal_closure_permits_name_in_declared_exports() {
        let entry = public_import_entry("primitives", "Int");
        let d = declared_without_bit_and(); // includes Int
        let res = check_terminal_closure(
            &ModuleFullPath::from("prelude"),
            "Int",
            &entry,
            cranelisp_types::Span::SYNTHETIC,
            Some(&d),
        );
        assert!(res.is_ok(), "a declared re-export (Int ∈ D(prelude)) must pass: {res:?}");
    }

    // The never-false-fire arm: an UNKNOWN D(M) (`None`, not yet recorded) permits
    // — a foreign write racing ahead of M's own export processing must never be
    // rejected on incomplete information (FIXME 0604 §2.2 unknown-permit arm).
    // spec: prelude-table-write-isolation.md §2.2 — D(M) unknown permits.
    #[test]
    fn check_terminal_closure_permits_when_declared_exports_unknown() {
        let entry = public_import_entry("primitives", "bit-and");
        let res = check_terminal_closure(
            &ModuleFullPath::from("prelude"),
            "bit-and",
            &entry,
            cranelisp_types::Span::SYNTHETIC,
            None,
        );
        assert!(res.is_ok(), "unknown D(M) must permit (never false-fire): {res:?}");
    }

    // GENERALIZATION vs the prelude-only rider: the phantom into a NON-prelude
    // terminal module is ALSO rejected (the rider ignores non-prelude modules;
    // the gate does not).
    // spec: prelude-table-write-isolation.md §2.2 — any terminal module.
    #[test]
    fn check_terminal_closure_generalizes_beyond_prelude() {
        // A non-prelude terminal module with a recorded D(M) that lacks the name.
        let entry = public_import_entry("primitives", "bit-and");
        let d: HashSet<Symbol> = [Symbol::from("something-else")].into_iter().collect();
        let res = check_terminal_closure(
            &ModuleFullPath::from("some.terminal"),
            "bit-and",
            &entry,
            cranelisp_types::Span::SYNTHETIC,
            Some(&d),
        );
        assert!(res.is_err(), "the gate generalizes to any module, not just prelude");
    }

    // A legitimate re-export whose name IS in the module's declared export
    // closure PASSES — the gate must not false-fire the build.
    // spec: prelude-table-write-isolation.md §2.2 — declared name permits.
    #[test]
    fn check_terminal_closure_permits_legitimate_reexport() {
        let entry = public_import_entry("primitives", "add-i64");
        let d: HashSet<Symbol> = [Symbol::from("add-i64")].into_iter().collect();
        let res = check_terminal_closure(
            &ModuleFullPath::from("prelude"),
            "add-i64",
            &entry,
            cranelisp_types::Span::SYNTHETIC,
            Some(&d),
        );
        assert!(res.is_ok(), "a declared re-export (add-i64 ∈ D) must pass: {res:?}");
    }

    // The module's OWN public definition (a non-`Import` entry) is exported by
    // §8.4 — always closure-valid.
    // spec: prelude-table-write-isolation.md §2.2 — own definition.
    #[test]
    fn check_terminal_closure_permits_own_definition() {
        let entry = primitive_def(); // public non-Import Def
        // Own-def arm returns Ok with NO map read — even with an empty D(M).
        let d: HashSet<Symbol> = HashSet::new();
        let res = check_terminal_closure(
            &ModuleFullPath::from("prelude"),
            "map",
            &entry,
            cranelisp_types::Span::SYNTHETIC,
            Some(&d),
        );
        assert!(res.is_ok(), "own public definition is exported by §8.4: {res:?}");
    }

    // A PRIVATE write (an `import` edge) is never a cross-module phantom — the
    // isolation invariant is PUBLIC-write-only, so the gate is a no-op even when
    // the source lacks the name (census legal-skip for `install_imports`).
    // spec: prelude-table-write-isolation.md §2.1 — private-only legal-skip.
    #[test]
    fn check_terminal_closure_noop_for_private_write() {
        let entry = ModuleEntry::Import {
            source: FQSymbol {
                module: ModuleFullPath::from("primitives"),
                symbol: "bit-and".into(),
            },
            visibility: Visibility::Private,
        };
        // Private edge short-circuits on !is_public BEFORE consulting D(M); an
        // empty D(M) that would otherwise reject a public edge must be a no-op here.
        let d: HashSet<Symbol> = HashSet::new();
        let res = check_terminal_closure(
            &ModuleFullPath::from("user"),
            "bit-and",
            &entry,
            cranelisp_types::Span::SYNTHETIC,
            Some(&d),
        );
        assert!(res.is_ok(), "a private import edge is not a public phantom: {res:?}");
    }
