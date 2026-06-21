    use super::*;
    use cranelisp_types::{Scheme, Type};
    use std::collections::HashMap as StdHashMap;

    fn tables() -> SessionTables {
        SessionTables::new()
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
            DefKind::Primitive { got_slot: 0 },
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
            &[specific_export("base", "base-val")],
        )
        .unwrap();
        // Then a (redundant) private import of the same source.
        install_imports(
            &tables,
            &ModuleFullPath::from("relay"),
            &aliases,
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
            &[specific_export("prim", "Foo")],
        )
        .unwrap();

        // main globs prim (brings Foo, source prim) ...
        install_imports(
            &tables,
            &ModuleFullPath::from("main"),
            &aliases,
            &[glob_spec("prim")],
        )
        .expect("glob of prim installs Foo");

        // ... and specifically imports Foo from reexp (source reexp, terminal prim/Foo).
        install_imports(
            &tables,
            &ModuleFullPath::from("main"),
            &aliases,
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
            &[specific_spec("a", "Bar")],
        )
        .expect("first bare import of Bar installs cleanly");

        // main imports b/Bar bare → distinct terminal → MUST error.
        let err = install_imports(
            &tables,
            &ModuleFullPath::from("main"),
            &aliases,
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
