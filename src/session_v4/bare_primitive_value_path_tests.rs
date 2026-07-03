    use super::*;
    // S87 §2: types formerly reached via the parent's `use cranelisp_types`/
    // `use crate::code` glob (the impl moved to `lifecycle.rs`); import them
    // directly now.
    use crate::code::Code;
    use cranelisp_types::{DefKind, ModuleEntry, Scheme, Sexp, Span, Symbol, Type, Visibility};
    use std::collections::HashMap as StdHashMap;

    /// Build a `ModuleEntry::Def` for a primitive (matches how
    /// `register_builtins` seeds `primitives/add-i64`).
    fn mk_primitive_def(ty: Type, docstring: Option<&str>) -> ModuleEntry<Code> {
        let mut builder = ModuleEntry::def(
            Scheme { type_vars: vec![], constraints: StdHashMap::new(), ty },
            DefKind::primitive(0),
        )
        .visibility(Visibility::Public);
        if let Some(doc) = docstring {
            builder = builder.docstring(doc);
        }
        builder.build()
    }

    /// Fresh session with empty lib_dirs and a temp project_root so no
    /// prelude.cl is auto-discovered. Caller populates `shared.symbol_tables`
    /// to stage the chain under test.
    fn isolated_session() -> (CompilerSession, PathBuf) {
        let stamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0);
        let pid = std::process::id();
        let tmp_root = std::env::temp_dir()
            .join(format!("cranelisp-s61-slice1-{}-{}", pid, stamp));
        std::fs::create_dir_all(&tmp_root).expect("create test project_root");
        let settings = SessionSettings {
            no_color: true,
            no_cache: true,
            codegen_behaviour: CodegenBehaviour::InMemoryAndObject,
            priority_workers: 0,
            nice_workers: 0,
            run_mode: RunMode::Repl,
        };
        let mut s = CompilerSession::new(settings, tmp_root.clone(), "user");
        s.set_lib_dirs(vec![]);
        (s, tmp_root)
    }

    fn stage_primitive_reexport_chain(
        s: &CompilerSession,
        primitive_name: &str,
        primitive_ty: Type,
        docstring: Option<&str>,
    ) {
        let primitives = ModuleFullPath::from("primitives");
        let prelude = ModuleFullPath::from("prelude");
        let user = ModuleFullPath::from("user");

        // Ensure primitives table exists and holds the Def.
        s.shared.symbol_tables.entry(primitives.clone())
            .or_insert_with(|| SessionSymbolTable::new_with_params(primitives.clone()));
        if let Some(mut st) = s.shared.symbol_tables.get_mut(&primitives) {
            st.insert(
                Symbol::from(primitive_name),
                mk_primitive_def(primitive_ty, docstring),
            );
        }

        // prelude: Reexport → primitives/<name>.
        s.shared.symbol_tables.entry(prelude.clone())
            .or_insert_with(|| SessionSymbolTable::new_with_params(prelude.clone()));
        if let Some(mut st) = s.shared.symbol_tables.get_mut(&prelude) {
            st.insert(
                Symbol::from(primitive_name),
                ModuleEntry::Import {
                    source: FQSymbol {
                        module: primitives.clone(),
                        symbol: Symbol::from(primitive_name),
                    },
                    visibility: Visibility::Public,
                },
            );
        }

        // user: Import → prelude/<name> (implicit prelude glob effect).
        if let Some(mut st) = s.shared.symbol_tables.get_mut(&user) {
            st.insert(
                Symbol::from(primitive_name),
                ModuleEntry::Import {
                    source: FQSymbol {
                        module: prelude.clone(),
                        symbol: Symbol::from(primitive_name),
                    },
                    visibility: Visibility::Private,
                },
            );
        }
    }

    // spec: repl/spec.md §1.1 + spec/08-modules.md §8.9 — bare-value path
    //       MUST resolve a re-exported primitive to its terminal Def and
    //       echo the introspection card. Before the fix, the one-hop
    //       resolver terminated on the `Reexport` intermediate and the
    //       match dropped through `_ => None`.
    #[test]
    fn bare_reexported_primitive_resolves_to_terminal_def() {
        let (mut s, root) = isolated_session();
        let add_i64_ty = Type::Fn(
            vec![Type::Int, Type::Int],
            Box::new(Type::Int),
        );
        stage_primitive_reexport_chain(
            &s,
            "add-i64",
            add_i64_ty.clone(),
            Some("Add two i64 values."),
        );

        // Simulate the bare-value path: look up in user's table and
        // resolve. This is the exact sequence performed inside
        // `check_bare_symbol_introspection`.
        let user = ModuleFullPath::from("user");
        let entry = s.shared.symbol_tables.get(&user)
            .and_then(|st| st.get("add-i64").cloned())
            .expect("user module must carry Import for add-i64");
        let (resolved_entry, resolved_module) =
            s.resolve_entry_for_display(&entry, &user);

        match &resolved_entry {
            ModuleEntry::Def { scheme, kind, .. } => {
                assert_eq!(
                    scheme.ty, add_i64_ty,
                    "terminal Def must carry the primitive's own type",
                );
                assert!(
                    matches!(kind.as_ref(), DefKind::Primitive { .. }),
                    "terminal entry must be a Primitive Def, got: {:?}", kind,
                );
            }
            other => panic!(
                "expected terminal ModuleEntry::Def after resolve, got: {:?}",
                other,
            ),
        }
        assert_eq!(
            resolved_module,
            ModuleFullPath::from("primitives"),
            "resolved_module MUST be `primitives` (spec §8.9 re-export provenance)",
        );

        s.shutdown();
        let _ = std::fs::remove_dir_all(&root);
    }

    // spec: repl/spec.md §1.1 — bare-value introspection output format
    //       `:Type name ; classification - docstring`. The `format_eval_result`
    //       pipeline must produce a qualified-module echo for a re-exported
    //       primitive; this is the user-visible string the REPL prints.
    #[test]
    fn bare_reexported_primitive_formats_as_primitives_qualified() {
        let (mut s, root) = isolated_session();
        let add_i64_ty = Type::Fn(
            vec![Type::Int, Type::Int],
            Box::new(Type::Int),
        );
        stage_primitive_reexport_chain(
            &s,
            "add-i64",
            add_i64_ty,
            Some("Add two i64 values."),
        );

        // Drive the bare-value introspection handler directly.
        let sexp = Sexp::Symbol("add-i64".to_string(), Span::SYNTHETIC);
        let result = s.check_bare_symbol_introspection(&sexp)
            .expect(
                "re-exported primitive MUST resolve on the bare-value path \
                 (S61 Slice 1 acceptance)",
            );

        let output = s.format_eval_result(&result);
        assert!(
            output.starts_with(":(Fn [primitives/Int primitives/Int] primitives/Int) primitives/add-i64"),
            "bare-value echo must carry the full qualified type + \
             `primitives/add-i64` name (spec §8.9 re-export provenance); got: {output}",
        );
        assert!(
            output.contains("; primitive"),
            "classification MUST be `; primitive` for a primitive Def \
             (spec §4.1.1); got: {output}",
        );
        assert!(
            output.contains(" - Add two i64 values."),
            "docstring first line MUST follow ` - ` after classification \
             (repl/spec.md §1.1); got: {output}",
        );

        s.shutdown();
        let _ = std::fs::remove_dir_all(&root);
    }

    // spec: repl/spec.md §1.1 — genuinely unknown bare symbols MUST NOT
    //       produce an introspection card. The bare-value path returns
    //       None so the caller's fall-through (typecheck → codegen error)
    //       produces the expected `undefined variable` diagnostic. This
    //       is the negative case proving the fix didn't over-broaden the
    //       match to swallow lookup failures.
    #[test]
    fn bare_unknown_symbol_returns_none_for_introspection() {
        let (mut s, root) = isolated_session();
        // Stage `add-i64` but NOT `unknown-primitive-xyz`.
        stage_primitive_reexport_chain(
            &s,
            "add-i64",
            Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int)),
            None,
        );

        let sexp = Sexp::Symbol(
            "unknown-primitive-xyz".to_string(),
            Span::SYNTHETIC,
        );
        let result = s.check_bare_symbol_introspection(&sexp);
        assert!(
            result.is_none(),
            "unknown bare symbol MUST return None so the caller falls \
             through to the normal `undefined variable` typecheck error \
             (repl/spec.md §1.1 — no introspection card for unknown names); \
             got: is_some={}", result.is_some(),
        );

        s.shutdown();
        let _ = std::fs::remove_dir_all(&root);
    }

    // Harvest T-S1-3 from tests/legacy/sprint61_bare_primitive.rs (FIXME 0147):
    // generalisation across the re-exported primitive surface. Every staged
    // primitive resolves identically through user → prelude → primitives to
    // its terminal Def attributed to `primitives`. The legacy test asserted
    // this over ≥5 primitives end-to-end; this is the int Rust-API equivalent.
    // spec: spec/08-modules.md §8.9 — re-export provenance; repl/spec.md §1.1
    #[test]
    fn bare_reexported_primitive_surface_resolves_identically_across_symbols() {
        let (mut s, root) = isolated_session();
        let int2_to_int = || Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int));
        let cases: &[(&str, Type)] = &[
            ("add-i64", int2_to_int()),
            ("mul-i64", int2_to_int()),
            ("sub-i64", int2_to_int()),
            ("eq-i64", Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Bool))),
            ("not", Type::Fn(vec![Type::Bool], Box::new(Type::Bool))),
            ("str-concat", Type::Fn(vec![Type::String, Type::String], Box::new(Type::String))),
        ];
        for (name, ty) in cases {
            stage_primitive_reexport_chain(&s, name, ty.clone(), None);
        }

        let user = ModuleFullPath::from("user");
        for (name, ty) in cases {
            let entry = s
                .shared
                .symbol_tables
                .get(&user)
                .and_then(|st| st.get(name).cloned())
                .unwrap_or_else(|| panic!("user must carry Import for {name}"));
            let (resolved_entry, resolved_module) = s.resolve_entry_for_display(&entry, &user);
            match &resolved_entry {
                ModuleEntry::Def { scheme, kind, .. } => {
                    assert_eq!(&scheme.ty, ty, "{name}: terminal Def carries its own type");
                    assert!(
                        matches!(kind.as_ref(), DefKind::Primitive { .. }),
                        "{name}: terminal entry must be a Primitive Def, got {kind:?}"
                    );
                }
                other => panic!("{name}: expected terminal Def, got {other:?}"),
            }
            assert_eq!(
                resolved_module,
                ModuleFullPath::from("primitives"),
                "{name}: MUST attribute to `primitives` (spec §8.9), not user/prelude"
            );
        }

        s.shutdown();
        let _ = std::fs::remove_dir_all(&root);
    }
