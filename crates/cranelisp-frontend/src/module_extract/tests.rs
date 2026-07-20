    use super::*;
    use cranelisp_types::{Sexp, Visibility};

    /// Helper: parse source text into sexps via the reader.
    fn parse(src: &str) -> Vec<Sexp> {
        crate::reader::parse(src).expect("parse failed")
    }

    fn extract(src: &str) -> (ExtractedDeclarations, Vec<Sexp>) {
        let sexps = parse(src);
        extract_module_declarations(
            &ModuleFullPath::from("test"),
            &sexps,
        )
        .expect("extraction failed")
    }

    // -- mod declarations --

    // spec: 08-modules §8.2.1 — public submodule declaration
    #[test]
    fn test_mod_public() {
        let (ms, remaining) = extract("(mod util)");
        assert_eq!(ms.mod_decls.len(), 1);
        assert_eq!(&*ms.mod_decls[0].name, "util");
        assert!(matches!(ms.mod_decls[0].visibility, Visibility::Public));
        assert!(ms.mod_decls[0].inline_body.is_none());
        assert!(remaining.is_empty());
    }

    // spec: 08-modules §8.2.3 — private submodule declaration
    #[test]
    fn test_mod_private() {
        let (ms, remaining) = extract("(mod- internal)");
        assert_eq!(ms.mod_decls.len(), 1);
        assert_eq!(&*ms.mod_decls[0].name, "internal");
        assert!(matches!(ms.mod_decls[0].visibility, Visibility::Private));
        assert!(ms.mod_decls[0].inline_body.is_none());
        assert!(remaining.is_empty());
    }

    // spec: 08-modules §8.2.2 — inline submodule declaration
    #[test]
    fn test_mod_inline() {
        let (ms, remaining) = extract(
            "(mod test (import [super [*]]) (defn test-add [] (+ 3 4)))",
        );
        assert_eq!(ms.mod_decls.len(), 1);
        assert_eq!(&*ms.mod_decls[0].name, "test");
        assert!(matches!(ms.mod_decls[0].visibility, Visibility::Public));
        let body = ms.mod_decls[0].inline_body.as_ref().unwrap();
        assert_eq!(body.len(), 2); // import + defn
        assert!(remaining.is_empty());
    }

    // -- import declarations --

    // spec: 08-modules §8.3.1 — specific name import
    #[test]
    fn test_import_specific_names() {
        let (ms, remaining) = extract("(import [core.option [Some None]])");
        assert_eq!(ms.import_specs.len(), 1);
        assert_eq!(&*ms.import_specs[0].module_path, "core.option");
        assert!(ms.import_specs[0].alias.is_none());
        match &ms.import_specs[0].names {
            ImportNames::Specific(names) => {
                assert_eq!(names.len(), 2);
                assert_eq!(&*names[0], "Some");
                assert_eq!(&*names[1], "None");
            }
            other => panic!("expected Specific, got {:?}", other),
        }
        assert!(remaining.is_empty());
    }

    // spec: 08-modules §8.3.2 — glob import
    #[test]
    fn test_import_glob() {
        let (ms, _) = extract("(import [core.math [*]])");
        assert_eq!(ms.import_specs.len(), 1);
        assert_eq!(&*ms.import_specs[0].module_path, "core.math");
        assert_eq!(ms.import_specs[0].names, ImportNames::Glob);
    }

    // spec: 08-modules §8.3.3 — member glob import
    #[test]
    fn test_import_member_glob() {
        let (ms, _) = extract("(import [core.fmt [Display.*]])");
        assert_eq!(ms.import_specs.len(), 1);
        assert_eq!(&*ms.import_specs[0].module_path, "core.fmt");
        match &ms.import_specs[0].names {
            ImportNames::MemberGlob(base) => assert_eq!(&**base, "Display"),
            other => panic!("expected MemberGlob, got {:?}", other),
        }
    }

    // spec: 08-modules §8.3.4 — aliased import
    #[test]
    fn test_import_alias() {
        let (ms, _) = extract("(import [(core.string str) [concat join]])");
        assert_eq!(ms.import_specs.len(), 1);
        assert_eq!(&*ms.import_specs[0].module_path, "core.string");
        assert_eq!(ms.import_specs[0].alias.as_ref().unwrap().as_ref(), "str");
        match &ms.import_specs[0].names {
            ImportNames::Specific(names) => {
                assert_eq!(names.len(), 2);
                assert_eq!(&*names[0], "concat");
                assert_eq!(&*names[1], "join");
            }
            other => panic!("expected Specific, got {:?}", other),
        }
    }

    // spec: 08-modules §8.3.5 — alias-only import (empty names list)
    #[test]
    fn test_import_alias_only() {
        let (ms, _) = extract("(import [(core.option opt) []])");
        assert_eq!(ms.import_specs.len(), 1);
        assert_eq!(&*ms.import_specs[0].module_path, "core.option");
        assert_eq!(ms.import_specs[0].alias.as_ref().unwrap().as_ref(), "opt");
        assert_eq!(ms.import_specs[0].names, ImportNames::None);
    }

    // spec: 05-definitions §5 binder-positions table + §8.3.4 — a module ALIAS is
    // a local binder, so a qualified spelling rejects; the module PATH (elems[0])
    // is a reference and a dotted/qualified path is permitted there. The bare
    // alias twin accepts.
    #[test]
    fn import_module_alias_qualified_rejected_bare_twin_accepts() {
        let sexps = parse("(import [(core.string a/b) [concat]])");
        let err = extract_module_declarations(&ModuleFullPath::from("test"), &sexps)
            .expect_err("a qualified module alias is rejected");
        assert!(
            err.to_string().contains("qualified name") && err.to_string().contains("binder"),
            "the alias reject names the qualified-binder rule; got: {err}"
        );
        // Bare alias twin accepts — and the DOTTED module PATH is permitted (it is
        // a reference, not a binder).
        let (ms, _) = extract("(import [(core.string str) [concat]])");
        assert_eq!(&*ms.import_specs[0].module_path, "core.string");
        assert_eq!(ms.import_specs[0].alias.as_ref().unwrap().as_ref(), "str");
    }

    // spec: 08-modules §8.3.7 — super import rewritten to parent module path
    //
    // Per the super-import arbitration (design/arch/super-import-arbitration.md),
    // `super` is rewritten at frontend capture time. After extraction,
    // `ImportSpec.module_path` never contains the literal string `"super"`.
    #[test]
    fn test_import_super_rewrites_to_parent() {
        let sexps = parse("(import [super [*]])");
        let (ms, _) = extract_module_declarations(
            &ModuleFullPath::from("math.test"),
            &sexps,
        )
        .expect("extraction failed");
        assert_eq!(ms.import_specs.len(), 1);
        // `super` inside `math.test` resolves to `math`.
        assert_eq!(&*ms.import_specs[0].module_path, "math");
        assert_eq!(ms.import_specs[0].names, ImportNames::Glob);
    }

    // spec: 08-modules §8.3.7 — nested super rewrite (a.b.c → a.b)
    #[test]
    fn test_import_super_rewrites_nested_parent() {
        let sexps = parse("(import [super [helper]])");
        let (ms, _) = extract_module_declarations(
            &ModuleFullPath::from("app.handler.test"),
            &sexps,
        )
        .expect("extraction failed");
        assert_eq!(ms.import_specs.len(), 1);
        assert_eq!(&*ms.import_specs[0].module_path, "app.handler");
    }

    // spec: 08-modules §8.3.7 — super at a top-level module is a compile-time error
    #[test]
    fn test_import_super_at_root_errors() {
        let sexps = parse("(import [super [*]])");
        let result = extract_module_declarations(
            &ModuleFullPath::from("root"),
            &sexps,
        );
        let err = result.expect_err("expected error for super at root module");
        match err {
            CranelispError::ModuleError { message, .. } => {
                assert!(
                    message.contains("super"),
                    "error message should mention super, got: {}",
                    message,
                );
                assert!(
                    message.contains("root"),
                    "error message should name the offending module, got: {}",
                    message,
                );
                assert!(
                    message.contains("no parent") || message.contains("top-level"),
                    "error message should explain the no-parent condition, got: {}",
                    message,
                );
            }
            other => panic!("expected ModuleError, got {:?}", other),
        }
    }

    // spec: 08-modules §8.3.8 — multiple modules in one import form
    #[test]
    fn test_import_multiple_modules() {
        let (ms, _) = extract("(import [core.option [Some None] core.math [*]])");
        assert_eq!(ms.import_specs.len(), 2);
        assert_eq!(&*ms.import_specs[0].module_path, "core.option");
        match &ms.import_specs[0].names {
            ImportNames::Specific(names) => assert_eq!(names.len(), 2),
            other => panic!("expected Specific, got {:?}", other),
        }
        assert_eq!(&*ms.import_specs[1].module_path, "core.math");
        assert_eq!(ms.import_specs[1].names, ImportNames::Glob);
    }

    // -- export declarations --

    // spec: 08-modules §8.4.2 — glob re-export
    #[test]
    fn test_export_glob() {
        let (ms, _) = extract("(export [core [*]])");
        assert_eq!(ms.export_specs.len(), 1);
        assert_eq!(&*ms.export_specs[0].module_path, "core");
        assert_eq!(ms.export_specs[0].names, ImportNames::Glob);
    }

    // spec: 08-modules §8.4.3 — multiple module re-export
    #[test]
    fn test_export_multiple() {
        let (ms, _) = extract("(export [core [*] primitives [vec-len]])");
        assert_eq!(ms.export_specs.len(), 2);
        assert_eq!(&*ms.export_specs[0].module_path, "core");
        assert_eq!(ms.export_specs[0].names, ImportNames::Glob);
        assert_eq!(&*ms.export_specs[1].module_path, "primitives");
        match &ms.export_specs[1].names {
            ImportNames::Specific(names) => {
                assert_eq!(names.len(), 1);
                assert_eq!(&*names[0], "vec-len");
            }
            other => panic!("expected Specific, got {:?}", other),
        }
    }

    // -- passthrough behavior --

    // spec: 08-modules §8.12.1 — non-mod/import/export sexps pass through
    #[test]
    fn test_passthrough() {
        let (ms, remaining) = extract("(defn add [x y] (+ x y))");
        assert!(ms.mod_decls.is_empty());
        assert!(ms.import_specs.is_empty());
        assert!(ms.export_specs.is_empty());
        assert_eq!(remaining.len(), 1);
    }

    // spec: 08-modules §8.2.6, §8.3.8, §8.4.5 — mixed forms partitioned correctly
    #[test]
    fn test_mixed_forms() {
        let src = r#"
            (mod util)
            (import [core.math [*]])
            (export [core [*]])
            (defn main [] 42)
            (mod- internal)
            (defn helper [x] x)
        "#;
        let (ms, remaining) = extract(src);
        assert_eq!(ms.mod_decls.len(), 2);
        assert_eq!(&*ms.mod_decls[0].name, "util");
        assert!(matches!(ms.mod_decls[0].visibility, Visibility::Public));
        assert_eq!(&*ms.mod_decls[1].name, "internal");
        assert!(matches!(ms.mod_decls[1].visibility, Visibility::Private));
        assert_eq!(ms.import_specs.len(), 1);
        assert_eq!(ms.export_specs.len(), 1);
        assert_eq!(remaining.len(), 2); // two defn forms
    }

    // spec: 08-modules §8.4.1 — specific re-export
    #[test]
    fn test_export_specific() {
        let (ms, _) = extract("(export [core.option [Option Some None]])");
        assert_eq!(ms.export_specs.len(), 1);
        assert_eq!(&*ms.export_specs[0].module_path, "core.option");
        match &ms.export_specs[0].names {
            ImportNames::Specific(names) => {
                assert_eq!(names.len(), 3);
                assert_eq!(&*names[0], "Option");
                assert_eq!(&*names[1], "Some");
                assert_eq!(&*names[2], "None");
            }
            other => panic!("expected Specific, got {:?}", other),
        }
    }

    // spec: 08-modules §8.2 — mod with no name is an error
    #[test]
    fn test_mod_missing_name() {
        let sexps = parse("(mod)");
        let result = extract_module_declarations(
            &ModuleFullPath::from("test"),
            &sexps,
        );
        assert!(result.is_err());
    }

    // spec: 05-definitions §5.8 — a `mod`/`mod-` name MUST be a simple symbol
    // (not qualified, not dotted). A `/` (module qualifier) or `.` (dotted path)
    // in the head is a compile-time error, located at the name element (audit
    // S113 finding 2 — enforcement was missing entirely). Both `mod` and `mod-`
    // route through the one `parse_mod_decl` seam; the simple twins accept.
    #[test]
    fn mod_head_must_be_simple_symbol_rejects_qualified_and_dotted() {
        let cases: &[&str] = &[
            "(mod foo/bar)",   // qualified
            "(mod- foo/bar)",  // qualified, private
            "(mod a.b)",       // dotted
            "(mod- a.b)",      // dotted, private
        ];
        for src in cases {
            let sexps = parse(src);
            let err = extract_module_declarations(&ModuleFullPath::from("test"), &sexps)
                .expect_err(&format!("`{src}` must be rejected (§5.8 simple-symbol rule)"));
            let msg = err.to_string();
            assert!(
                msg.contains("simple symbol") && msg.contains("§5.8"),
                "for `{src}` the reject names the simple-symbol rule; got: {msg}"
            );
        }
        // Simple-name twins (both visibilities) accept.
        let (pub_ms, _) = extract("(mod math)");
        assert_eq!(&*pub_ms.mod_decls[0].name, "math");
        let (priv_ms, _) = extract("(mod- internal)");
        assert_eq!(&*priv_ms.mod_decls[0].name, "internal");
    }

    // spec: 08-modules §8.3 — import with missing names list is an error
    #[test]
    fn test_import_missing_names() {
        let sexps = parse("(import [core.option])");
        let result = extract_module_declarations(
            &ModuleFullPath::from("test"),
            &sexps,
        );
        assert!(result.is_err());
    }

    // spec: 08-modules §8.1 — module path is preserved
    #[test]
    fn test_module_path_preserved() {
        let (ms, _) = extract_module_declarations(
            &ModuleFullPath::from("app.handler"),
            &[],
        )
        .unwrap();
        assert_eq!(&*ms.path, "app.handler");
    }

    // spec: 08-modules §8.3.8 — multiple import forms accumulate
    #[test]
    fn test_multiple_import_forms() {
        let src = r#"
            (import [core.option [Some None]])
            (import [core.math [*]])
        "#;
        let (ms, _) = extract(src);
        assert_eq!(ms.import_specs.len(), 2);
        assert_eq!(&*ms.import_specs[0].module_path, "core.option");
        assert_eq!(&*ms.import_specs[1].module_path, "core.math");
    }

    // -- platform declarations --

    // spec: 10-io §10.9.1 — platform declaration extracted from top-level forms
    #[test]
    fn test_platform_extracted() {
        let (ms, remaining) = extract("(platform stdio)");
        assert_eq!(ms.platform_specs.len(), 1);
        assert_eq!(ms.platform_specs[0].name, "stdio");
        assert!(remaining.is_empty());
    }

    // spec: 10-io §10.9.1 — multiple platform declarations accumulate
    #[test]
    fn test_multiple_platforms() {
        let src = r#"
            (platform stdio)
            (platform network)
            (defn main [] 42)
        "#;
        let (ms, remaining) = extract(src);
        assert_eq!(ms.platform_specs.len(), 2);
        assert_eq!(ms.platform_specs[0].name, "stdio");
        assert_eq!(ms.platform_specs[1].name, "network");
        assert_eq!(remaining.len(), 1); // defn passes through
    }

    // spec: 10-io §10.9.1 — platform with wrong arity is an error
    #[test]
    fn test_platform_wrong_arity() {
        let sexps = parse("(platform)");
        let result = extract_module_declarations(
            &ModuleFullPath::from("test"),
            &sexps,
        );
        assert!(result.is_err());
    }

    // spec: 10-io §10.9.1 + 05-definitions §5.10 — a `platform` name composes the
    // `platform.<name>` module path, so it MUST be a simple symbol: a qualified
    // (`/`) or dotted (`.`) name corrupts the path composition and is rejected
    // (0660 cell (c-platform); mirrors the §5.8 mod-head guard). The simple twin
    // accepts. (§5.10 needs the "not qualified, not dotted" prose — /spec rider,
    // FIXME 0660.)
    #[test]
    fn platform_name_must_be_simple_symbol_rejects_qualified_and_dotted() {
        for src in &["(platform io/stdio)", "(platform a.b)"] {
            let sexps = parse(src);
            let err = extract_module_declarations(&ModuleFullPath::from("test"), &sexps)
                .expect_err(&format!("`{src}` must be rejected (simple-symbol rule)"));
            let msg = err.to_string();
            assert!(
                msg.contains("simple symbol") && msg.contains("platform"),
                "for `{src}` the reject names the simple-symbol rule; got: {msg}"
            );
        }
        // Simple-name twin accepts.
        let (ms, _) = extract("(platform stdio)");
        assert_eq!(ms.platform_specs[0].name, "stdio");
    }

    // spec: 10-io §10.9.1 — platform forms don't appear in remaining sexps
    #[test]
    fn test_platform_not_in_remaining() {
        let src = "(platform stdio) (defn main [] 42)";
        let (ms, remaining) = extract(src);
        assert_eq!(ms.platform_specs.len(), 1);
        assert_eq!(remaining.len(), 1);
        // Verify the remaining form is the defn, not the platform
        if let Sexp::List(elems, _) = &remaining[0] {
            if let Sexp::Symbol(head, _) = &elems[0] {
                assert_eq!(head.as_str(), "defn");
            } else {
                panic!("expected defn symbol");
            }
        } else {
            panic!("expected list form");
        }
    }

    // -------------------------------------------------------------------
    // Rendered-diagnostic tier (FIXME 0500)
    //
    // `module_extract` emits ModuleError diagnostics for malformed
    // mod/import/export/platform declarations. This tier guards the P6
    // class (0485): a real source span, the offending construct named, and
    // NO Debug-format struct dump in user-facing text. Submodule ×
    // scenario-class per METHOD §2.2.
    // spec: repl/spec.md §"Self-documenting REPL" — no opaque errors.
    // -------------------------------------------------------------------
    mod rendered_diagnostics {
        use super::*;

        const SYNTHETIC_SPAN_BASE: u32 = 1_000_000;

        fn err(src: &str) -> CranelispError {
            let sexps = parse(src);
            extract_module_declarations(&ModuleFullPath::from("test"), &sexps)
                .expect_err("expected a module error")
        }

        fn assert_real_span(e: &CranelispError, src: &str) {
            let s = e.span();
            assert!(
                s.start < SYNTHETIC_SPAN_BASE && s.end < SYNTHETIC_SPAN_BASE,
                "module diagnostic carries a synthetic span {s}: {}",
                e.message(),
            );
            assert!(
                s.end as usize <= src.len(),
                "module span {s} exceeds source length {} for {src:?}",
                src.len(),
            );
        }

        fn assert_no_debug_artifacts(e: &CranelispError) {
            let m = e.message();
            assert!(!m.contains("Span {"), "message leaks a Debug span struct: {m}");
            assert!(!m.contains("ErrorLocation"), "message leaks ErrorLocation: {m}");
        }

        // -- positive: mod-without-name names the requirement, real span --

        // spec: 08-modules §8.2.1 — mod declaration requires a name.
        #[test]
        fn mod_missing_name_names_requirement_with_real_span() {
            let e = err("(mod)");
            assert!(
                e.message().contains("mod declaration requires a name"),
                "got: {}",
                e.message(),
            );
            assert_real_span(&e, "(mod)");
            assert_no_debug_artifacts(&e);
        }

        // -- edge: import missing names list echoes the module path --

        // spec: 08-modules §8.3 — import requires a names list.
        #[test]
        fn import_missing_names_echoes_module_path() {
            let e = err("(import [core.math])");
            assert!(
                e.message().contains("core.math"),
                "message should name the module: {}",
                e.message(),
            );
            assert_real_span(&e, "(import [core.math])");
            assert_no_debug_artifacts(&e);
        }

        // -- edge: platform wrong arity --

        // spec: 09-platform §9.2 — platform declaration takes exactly one name.
        #[test]
        fn platform_wrong_arity_is_diagnosed_cleanly() {
            let e = err("(platform)");
            assert!(
                e.message().contains("platform declaration"),
                "got: {}",
                e.message(),
            );
            assert_real_span(&e, "(platform)");
            assert_no_debug_artifacts(&e);
        }

        // -- negative: no internal artifacts leak across a spread of shapes --

        #[test]
        fn no_clean_module_diagnostic_leaks_debug_or_synthetic_span() {
            for src in ["(mod)", "(import [core.math])", "(platform)", "(export)"] {
                let e = err(src);
                assert_no_debug_artifacts(&e);
                assert_real_span(&e, src);
            }
        }

        // -- negative (FAILING-NOT-IGNORED): the live P6 exhibit --
        //
        // `expect_symbol` (module_extract.rs:533) renders a non-symbol form
        // with `{:?}`, dumping a Debug `Sexp` incl. a raw `Span { .. }` struct
        // into a user-facing message — the exact 0485/P6 class this tier
        // exists to catch. This test asserts the DESIRED behaviour (no Debug
        // struct dump) and is RED until the message renders the offending form
        // via Display / a form-kind description instead of `{:?}`. Do NOT
        // ignore — it is the durable record + the flip-to-green trigger for
        // the owning frontend fix. See FIXME 0500.
        // spec: repl/spec.md §"Self-documenting REPL" — no internal-leaking errors.
        #[test]
        fn mod_name_non_symbol_does_not_leak_debug_struct() {
            let e = err("(mod 42)");
            let m = e.message();
            assert!(
                m.contains("mod declaration name"),
                "message should name the context: {m}",
            );
            assert!(
                !m.contains("Span {"),
                "user-facing message leaks a Debug span struct dump: {m}",
            );
        }
    }
