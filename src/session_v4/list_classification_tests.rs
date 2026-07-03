    use super::*;
    // S87 §2: types formerly reached via the parent's `use cranelisp_types`
    // glob (the impl moved to `lifecycle.rs`); import them directly now.
    use cranelisp_types::{
        DefKind, FQTypeName, ModuleEntry, Scheme, Sexp, Span, Symbol, Type, Visibility,
    };
    use std::collections::HashMap as StdHashMap;

    // ══════════════════════════════════════════════════════════════════════
    // Harvest from tests/legacy/repl_negative_old.rs (FIXME 0124, S81 W-E
    // /dev int) — the `classify_entry` / `collect_list_categories` portion.
    //
    // The legacy helper replicated `handle_list`'s classification logic in
    // test code (reaching into `session.shared.symbol_tables`). The int-owned
    // surface is `CompilerSession::list_user_definitions`, which buckets a
    // module's symbols into `SymbolCategory`. This harvests the positive
    // classification AND the negatives the spec requires (repl/spec.md §3.3 /
    // tests/CLAUDE.md §Negative): a defmacro is a Macro NOT a Fn; an Import is
    // NOT listed (surfaced by `/imports`); a constructor is a Constructor.
    // The display-format + type-inference portions of repl_negative_old.rs
    // route to /backend (`display.rs`) + /typecheck (`checker.rs`), outside
    // int's narrow deployment.
    // ══════════════════════════════════════════════════════════════════════

    fn isolated_session() -> (CompilerSession, PathBuf) {
        let stamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0);
        let pid = std::process::id();
        let tmp_root = std::env::temp_dir()
            .join(format!("cranelisp-s64-list-{}-{}", pid, stamp));
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

    fn mono(ty: Type) -> Scheme {
        Scheme { type_vars: vec![], constraints: StdHashMap::new(), ty }
    }

    // spec: repl/spec.md §3.3 — `/list` buckets symbols by category; a defmacro
    //       MUST classify as Macro (NOT Fn), a constructor as Constructor, and
    //       imports MUST NOT appear (they are surfaced by `/imports`).
    #[test]
    fn list_user_definitions_classifies_and_excludes_imports() {
        let (mut s, root) = isolated_session();
        let user = ModuleFullPath::from("user");

        if let Some(mut st) = s.shared.symbol_tables.get_mut(&user) {
            // A plain function.
            st.insert(
                Symbol::from("f"),
                ModuleEntry::def(
                    mono(Type::Fn(vec![Type::Int], Box::new(Type::Int))),
                    DefKind::UserFn {
                        fn_state: cranelisp_types::UserFnState::Concrete { got_slot: 0, mode_summary: None },
                    },
                )
                .visibility(Visibility::Public)
                .build(),
            );
            // A macro.
            st.insert(
                Symbol::from("m"),
                ModuleEntry::def(
                    mono(Type::Int),
                    DefKind::Macro {
                        clauses_meta: vec![],
                        macro_sexp: Sexp::Symbol("m".to_string(), Span::SYNTHETIC),
                    },
                )
                .visibility(Visibility::Public)
                .build(),
            );
            // A constructor.
            st.insert(
                Symbol::from("Mk"),
                ModuleEntry::def(
                    mono(Type::Int),
                    DefKind::Constructor {
                        got_slot: 0,
                        type_name: FQTypeName {
                            module: user.clone(),
                            name: cranelisp_types::TypeName::from("T"),
                        },
                        tag: 0,
                        field_count: 0,
                        internal: false,
                        type_def: None,
                        mode_summary: None,
                    },
                )
                .visibility(Visibility::Public)
                .build(),
            );
            // An import — MUST NOT be listed by `/list`.
            st.insert(
                Symbol::from("imported"),
                ModuleEntry::Import {
                    source: FQSymbol {
                        module: ModuleFullPath::from("other"),
                        symbol: Symbol::from("imported"),
                    },
                    visibility: Visibility::Private,
                },
            );
        }

        let defs = s.list_user_definitions();
        let cat = |name: &str| defs.iter().find(|d| d.name.as_ref() == name).map(|d| d.category);

        assert_eq!(cat("f"), Some(SymbolCategory::Fn), "plain defn is a Fn");
        assert_eq!(
            cat("m"),
            Some(SymbolCategory::Macro),
            "defmacro MUST classify as Macro, NOT Fn (repl/spec.md §3.3 negative)"
        );
        assert_ne!(
            cat("m"),
            Some(SymbolCategory::Fn),
            "negative: defmacro MUST NOT be bucketed as a Fn"
        );
        assert_eq!(
            cat("Mk"),
            Some(SymbolCategory::Constructor),
            "constructor MUST classify as Constructor"
        );
        assert!(
            cat("imported").is_none(),
            "negative: imports MUST NOT appear in /list (surfaced by /imports)"
        );

        s.shutdown();
        let _ = std::fs::remove_dir_all(&root);
    }

    // spec: repl/spec.md §3.3 (negative) — `/list` shows USER definitions only.
    // Evaluating a bare top-level expression synthesises an internal zero-arg
    // `Defn` named `__expr` (see `wrap_exprs_as_defns`); that wrapper MUST NOT
    // leak into the listing — it is a compiler artifact, not a user definition,
    // and is filtered exactly like `$`-mangled internal names. Pins the seam
    // (`worker::is_internal_listing_name`) at the int surface that `handle_list`
    // and the e2e `list_neg_no_synthetic_expr_wrapper` repro both ride.
    #[test]
    fn list_user_definitions_excludes_synthetic_expr_wrapper() {
        let (mut s, root) = isolated_session();
        let user = ModuleFullPath::from("user");

        if let Some(mut st) = s.shared.symbol_tables.get_mut(&user) {
            // The synthetic `__expr` wrapper — a Public zero-arg UserFn, exactly
            // as `wrap_exprs_as_defns` builds it for a bare top-level Expr.
            st.insert(
                Symbol::from("__expr"),
                ModuleEntry::def(
                    mono(Type::Int),
                    DefKind::UserFn {
                        fn_state: cranelisp_types::UserFnState::Concrete { got_slot: 0, mode_summary: None },
                    },
                )
                .visibility(Visibility::Public)
                .build(),
            );
            // A `$`-mangled mono variant — also an internal artifact.
            st.insert(
                Symbol::from("add$Int+Int"),
                ModuleEntry::def(
                    mono(Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int))),
                    DefKind::UserFn {
                        fn_state: cranelisp_types::UserFnState::Concrete { got_slot: 0, mode_summary: None },
                    },
                )
                .visibility(Visibility::Public)
                .build(),
            );
            // A genuine user definition — MUST still appear.
            st.insert(
                Symbol::from("g"),
                ModuleEntry::def(
                    mono(Type::Fn(vec![Type::Int], Box::new(Type::Int))),
                    DefKind::UserFn {
                        fn_state: cranelisp_types::UserFnState::Concrete { got_slot: 0, mode_summary: None },
                    },
                )
                .visibility(Visibility::Public)
                .build(),
            );
        }

        let defs = s.list_user_definitions();
        let has = |name: &str| defs.iter().any(|d| d.name.as_ref() == name);

        assert!(
            !has("__expr"),
            "negative: the synthetic `__expr` wrapper MUST NOT appear in /list \
             (repl/spec.md §3.3 — not a user definition)"
        );
        assert!(
            !has("add$Int+Int"),
            "negative: `$`-mangled internal variants MUST NOT appear in /list"
        );
        assert!(
            has("g"),
            "positive: a genuine user definition MUST still be listed"
        );

        s.shutdown();
        let _ = std::fs::remove_dir_all(&root);
    }
