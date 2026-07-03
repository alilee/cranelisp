    use super::*;
    use crate::code::Code;
    use cranelisp_types::{DefKind, ModuleEntry, Scheme, Symbol, Type, UserFnState, Visibility};
    use std::collections::HashMap as StdHashMap;

    /// Fresh session with empty lib_dirs and a temp project_root so no
    /// prelude.cl is auto-discovered (mirrors
    /// `bare_primitive_value_path_tests::isolated_session`). Caller stages
    /// `shared.symbol_tables` + `shared.introspection` directly.
    fn isolated_session() -> (CompilerSession, PathBuf) {
        let stamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0);
        let pid = std::process::id();
        let tmp_root =
            std::env::temp_dir().join(format!("cranelisp-s101-info-src-{}-{}", pid, stamp));
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

    /// Stage a slotted concrete `UserFn` Def named `name` in `user`, plus an
    /// introspection record carrying its `source` text and `code_size`.
    fn stage_fn_with_source(
        s: &CompilerSession,
        name: &str,
        source: &str,
        code_size: Option<usize>,
    ) {
        let user = ModuleFullPath::from("user");
        s.shared
            .symbol_tables
            .entry(user.clone())
            .or_insert_with(|| SessionSymbolTable::new_with_params(user.clone()));
        if let Some(mut st) = s.shared.symbol_tables.get_mut(&user) {
            let slot = st.allocate_got_slot();
            let entry: ModuleEntry<Code> = ModuleEntry::def(
                Scheme {
                    type_vars: vec![],
                    constraints: StdHashMap::new(),
                    ty: Type::Fn(vec![Type::Int], Box::new(Type::Int)),
                },
                DefKind::UserFn {
                    fn_state: UserFnState::Concrete { got_slot: slot },
                },
            )
            .visibility(Visibility::Public)
            .build();
            st.insert(Symbol::from(name), entry);
        }
        s.shared
            .introspection
            .as_ref()
            .expect("REPL session populates introspection")
            .insert(
                FQSymbol {
                    module: user,
                    symbol: Symbol::from(name),
                },
                Introspection {
                    source: Some(source.to_string()),
                    code_size,
                    ..Default::default()
                },
            );
    }

    // spec: repl/spec.md §3.6 — `/info <name>` MUST display the definition
    // source (the worked example's second line, 2-space indented) between the
    // signature and the code stats. FIXME 0480: before the fix `handle_info`
    // emitted sig + `NN bytes` only.
    #[test]
    fn handle_info_healthy_includes_definition_source_before_stats() {
        let (mut s, root) = isolated_session();
        stage_fn_with_source(&s, "double", "(defn double [x] (mul-i64 x 2))", Some(8));

        let out = s.handle_info("double");
        assert!(
            out.contains("\n  (defn double [x] (mul-i64 x 2))"),
            "/info must render the definition source as a 2-space-indented \
             line (repl/spec.md §3.6); got:\n{out}"
        );
        assert!(out.contains("8 bytes"), "code stats still shown; got:\n{out}");
        let src_pos = out.find("(defn double").expect("source present");
        let bytes_pos = out.find("8 bytes").expect("stats present");
        assert!(
            src_pos < bytes_pos,
            "source precedes stats (§3.6 layout); got:\n{out}"
        );

        s.shutdown();
        let _ = std::fs::remove_dir_all(&root);
    }

    // spec: repl/spec.md §18.4 — `/info` on a BROKEN symbol MUST include the
    // primary line, the provenance comment line, AND the definition source —
    // and MUST NOT display code-size stats. FIXME 0480: the broken-arm
    // early-return inherited the §3.6 source omission.
    #[test]
    fn handle_info_broken_includes_source_and_provenance_no_stats() {
        let (mut s, root) = isolated_session();
        // code_size present in introspection so the no-stats leg is meaningful.
        stage_fn_with_source(&s, "g", "(defn g [y] (f y))", Some(16));
        let fq_g = FQSymbol {
            module: ModuleFullPath::from("user"),
            symbol: Symbol::from("g"),
        };
        let fq_f = FQSymbol {
            module: ModuleFullPath::from("user"),
            symbol: Symbol::from("f"),
        };
        let original_error = "type error: expected primitives/String, got primitives/Int";
        s.shared.broken.insert(
            fq_g.clone(),
            crate::redefine::BrokenInfo {
                broken_by: fq_f.clone(),
                original_error: original_error.to_string(),
                provenance: crate::redefine::compose_provenance(&fq_g, &fq_f, original_error),
            },
        );

        let out = s.handle_info("g");
        assert!(
            out.contains("; broken by the redefinition of user/f:"),
            "provenance comment line (§18.4); got:\n{out}"
        );
        assert!(
            out.contains("\n  (defn g [y] (f y))"),
            "/info on a broken symbol must show its definition source \
             (§18.4 third MUST component); got:\n{out}"
        );
        assert!(
            !out.contains("bytes"),
            "no code-size stats for a broken symbol (§18.4); got:\n{out}"
        );

        s.shutdown();
        let _ = std::fs::remove_dir_all(&root);
    }
