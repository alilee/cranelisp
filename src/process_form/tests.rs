    use super::*;


    // -----------------------------------------------------------------------
    // FQ auto-loading gap→load→retry mechanism (FIXME 0268, spec §8.5.4/§9.3.6)
    // -----------------------------------------------------------------------

    // spec: spec/08-modules.md §8.5.4 — the typecheck gap for an FQ value/fn
    // reference to an unloaded module (`SymbolTypechecked`) names the module
    // the orchestrator must load.
    #[test]
    fn gap_target_module_symbol_typechecked_names_module() {
        let gap = cranelisp_types::ResolutionGap::SymbolTypechecked(FQSymbol {
            module: ModuleFullPath::from("mac"),
            symbol: Symbol::from("helper"),
        });
        assert_eq!(gap_target_module(&gap), Some(ModuleFullPath::from("mac")));
    }

    // spec: spec/09-macros.md §9.3.6 — the expand-phase macro gap (`MacroInMem`)
    // also reduces to "load `fq.module`".
    #[test]
    fn gap_target_module_macro_in_mem_names_module() {
        let gap = cranelisp_types::ResolutionGap::MacroInMem(FQSymbol {
            module: ModuleFullPath::from("mac"),
            symbol: Symbol::from("twice"),
        });
        assert_eq!(gap_target_module(&gap), Some(ModuleFullPath::from("mac")));
    }

    // spec: spec/08-modules.md §8.5.4 — an FQ type reference to an unloaded
    // module (`Type`) names the module via its `FQTypeName`.
    #[test]
    fn gap_target_module_type_names_module() {
        let gap = cranelisp_types::ResolutionGap::Type(cranelisp_types::FQTypeName::new(
            ModuleFullPath::from("shapes"),
            cranelisp_types::TypeName::from("Point"),
        ));
        assert_eq!(gap_target_module(&gap), Some(ModuleFullPath::from("shapes")));
    }

    // spec: spec/09-macros.md §9.3.6 — `recognize` captures an FQ macro head
    // whose module is not loaded as a block signal (returns `Ok(None)` for the
    // aborted walk so the head flows on as an ordinary reference). This is the
    // expand-side half of the gap→load→retry mechanism: the captured module
    // drives `load_fq_dep_module`.
    #[test]
    fn recognize_captures_unloaded_fq_macro_module() {
        use crate::expander::MacroResolver;
        let module = ModuleFullPath::from("user");
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();
        symbol_tables.insert(
            module.clone(),
            crate::code::SessionSymbolTable::new_with_params(module.clone()),
        );
        let next_type_id = std::sync::atomic::AtomicU32::new(0);
        let scheduler = CompileScheduler::new();
        let typecheck_products = dashmap::DashMap::new();
        let module_aliases = cranelisp_types::ModuleAliases::default();
        let prelude_fallback = cranelisp_typecheck::PreludeFallback::default();
        let mut check_state = CheckState::new(module.clone());
        let mut accumulator = ModuleCheckAccumulator::new();

        let mut resolver = SymbolTableMacroResolver {
            symbol_tables: &symbol_tables,
            next_type_id: &next_type_id,
            check_state: &mut check_state,
            current_module: module.clone(),
            module_aliases: &module_aliases,
            prelude_fallback: &prelude_fallback,
            typecheck_products: &typecheck_products,
            accumulator: &mut accumulator,
            scheduler: &scheduler,
            shared_state: None,
            macro_defining_modules: Vec::new(),
            blocked_on_fq_module: None,
        };

        // `mac` is not loaded — recognising an FQ head `mac/twice` captures it.
        let r = resolver
            .recognize("mac/twice", Span::SYNTHETIC)
            .expect("recognition does not hard-error on an unloaded FQ module");
        assert!(r.is_none(), "aborted walk treats the head as a non-macro");
        assert_eq!(
            resolver.blocked_on_fq_module,
            Some(ModuleFullPath::from("mac")),
            "the unloaded FQ module is captured for the worker loop to load"
        );
    }

    // spec: spec/09-macros.md §9.3.6 — a bare (non-`/`) head is not an
    // FQ-module block signal even when unresolved.
    #[test]
    fn recognize_bare_head_is_not_fq_block() {
        use crate::expander::MacroResolver;
        let module = ModuleFullPath::from("user");
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();
        symbol_tables.insert(
            module.clone(),
            crate::code::SessionSymbolTable::new_with_params(module.clone()),
        );
        let next_type_id = std::sync::atomic::AtomicU32::new(0);
        let scheduler = CompileScheduler::new();
        let typecheck_products = dashmap::DashMap::new();
        let module_aliases = cranelisp_types::ModuleAliases::default();
        let prelude_fallback = cranelisp_typecheck::PreludeFallback::default();
        let mut check_state = CheckState::new(module.clone());
        let mut accumulator = ModuleCheckAccumulator::new();

        let mut resolver = SymbolTableMacroResolver {
            symbol_tables: &symbol_tables,
            next_type_id: &next_type_id,
            check_state: &mut check_state,
            current_module: module.clone(),
            module_aliases: &module_aliases,
            prelude_fallback: &prelude_fallback,
            typecheck_products: &typecheck_products,
            accumulator: &mut accumulator,
            scheduler: &scheduler,
            shared_state: None,
            macro_defining_modules: Vec::new(),
            blocked_on_fq_module: None,
        };

        let r = resolver
            .recognize("plain-fn", Span::SYNTHETIC)
            .expect("bare unresolved head is Ok(None)");
        assert!(r.is_none());
        assert_eq!(
            resolver.blocked_on_fq_module, None,
            "a bare head never triggers FQ-module auto-load"
        );
    }

    // spec: spec/09-macros.md §9.3.6 (FIXME 0322) — a `:`-prefixed symbol is a
    // TYPE ANNOTATION (`:primitives/Int`), never a module-qualified value/macro
    // reference. The FQ-autoload pre-scan in `recognize` must NOT split it on
    // `/` and treat `:primitives` as an unloaded module: doing so registers a
    // bogus `:primitives` block dep and contaminates resolution (the field type
    // then fails with `unknown type 'primitives' (from module '')`). The sibling
    // `qualify_expanded_sexp` already guards this with a `starts_with(':')` skip.
    #[test]
    fn recognize_skips_colon_prefixed_type_annotation() {
        use crate::expander::MacroResolver;
        let module = ModuleFullPath::from("user");
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();
        symbol_tables.insert(
            module.clone(),
            crate::code::SessionSymbolTable::new_with_params(module.clone()),
        );
        let next_type_id = std::sync::atomic::AtomicU32::new(0);
        let scheduler = CompileScheduler::new();
        let typecheck_products = dashmap::DashMap::new();
        let module_aliases = cranelisp_types::ModuleAliases::default();
        let prelude_fallback = cranelisp_typecheck::PreludeFallback::default();
        let mut check_state = CheckState::new(module.clone());
        let mut accumulator = ModuleCheckAccumulator::new();

        let mut resolver = SymbolTableMacroResolver {
            symbol_tables: &symbol_tables,
            next_type_id: &next_type_id,
            check_state: &mut check_state,
            current_module: module.clone(),
            module_aliases: &module_aliases,
            prelude_fallback: &prelude_fallback,
            typecheck_products: &typecheck_products,
            accumulator: &mut accumulator,
            scheduler: &scheduler,
            shared_state: None,
            macro_defining_modules: Vec::new(),
            blocked_on_fq_module: None,
        };

        // The FQ type annotation `:primitives/Int` must NOT be mis-split into a
        // `:primitives` block dep — it is a type leaf, not a value reference.
        let r = resolver
            .recognize(":primitives/Int", Span::SYNTHETIC)
            .expect("a `:`-prefixed annotation is Ok(None), not a hard error");
        assert!(r.is_none(), "a type annotation is never a macro head");
        assert_eq!(
            resolver.blocked_on_fq_module, None,
            "a `:`-prefixed type annotation must NOT register an FQ-module block \
             dep (FIXME 0322 — `:primitives` is not a module qualifier)"
        );

        // A bare `:Int` annotation (no `/`) is likewise inert.
        let r = resolver
            .recognize(":Int", Span::SYNTHETIC)
            .expect("a bare `:`-prefixed annotation is Ok(None)");
        assert!(r.is_none());
        assert_eq!(resolver.blocked_on_fq_module, None);
    }

    // §8.6.6 longest-prefix module-alias substitution is now exercised at its
    // canonical seam in `cranelisp_types::resolve::tests` (the int re-impl was
    // deleted in S81 W-G item 0303 — Principle 7 dedup). The int FQ-autoload
    // boundary calls `cranelisp_types::substitute_module_alias` directly.

    // -----------------------------------------------------------------
    // Layout-hash gate (platform-interface.md §5.5.4) — drives the WIRED
    // type-definition-drift detection (handle_platform) with mismatched and
    // matching (dll_hash, host_hash) pairs without dlopening a real DLL. The
    // dual gate: matching → Accept; mismatch in `--run`/`--link` → Refuse with
    // PlatformError::LayoutHashMismatch carrying both hashes; mismatch in the
    // REPL → WarnAndLoad (the regeneration bootstrap).
    // -----------------------------------------------------------------

    // spec: design/arch/platform-interface.md §5.5.4 — a stale schema in
    // `--run`/`--link` is REFUSED, carrying both hashes + the platform name so
    // the message directs the user to `/platform-schema` and rebuild.
    #[test]
    fn layout_hash_drift_refuses_in_run_mode() {
        let outcome = layout_hash_gate(
            "dll_baked_hash",
            "host_live_hash",
            "shapes",
            /* is_repl */ false,
            Span::SYNTHETIC,
        );
        match outcome {
            LayoutHashGate::Refuse(CranelispError::Platform(
                cranelisp_types::PlatformError::LayoutHashMismatch {
                    platform,
                    expected,
                    found,
                    ..
                },
            )) => {
                assert_eq!(platform, "shapes");
                // `expected` = host-regenerated (canonical) hash; `found` =
                // DLL-exported hash (error.rs PlatformError::LayoutHashMismatch).
                assert_eq!(expected, "host_live_hash");
                assert_eq!(found, "dll_baked_hash");
            }
            other => panic!(
                "expected Refuse(LayoutHashMismatch), got {}",
                match other {
                    LayoutHashGate::Accept => "Accept",
                    LayoutHashGate::WarnAndLoad(_) => "WarnAndLoad",
                    LayoutHashGate::Refuse(_) => "Refuse(other error)",
                }
            ),
        }
    }

    // spec: design/arch/platform-interface.md §5.5.4 — in the REPL a stale
    // schema WARNS and loads (the regeneration bootstrap), naming both hashes
    // and the `/platform-schema` rebuild guidance.
    #[test]
    fn layout_hash_drift_warns_and_loads_in_repl() {
        let outcome = layout_hash_gate(
            "dll_baked_hash",
            "host_live_hash",
            "shapes",
            /* is_repl */ true,
            Span::SYNTHETIC,
        );
        match outcome {
            LayoutHashGate::WarnAndLoad(msg) => {
                assert!(msg.contains("shapes"), "warning names the platform");
                assert!(msg.contains("dll_baked_hash"), "warning names the DLL hash");
                assert!(msg.contains("host_live_hash"), "warning names the host hash");
                assert!(
                    msg.contains("/platform-schema"),
                    "warning gives the rebuild guidance"
                );
            }
            _ => panic!("expected WarnAndLoad in REPL on mismatch"),
        }
    }

    // spec: design/arch/platform-interface.md §5.5.4 — a matching pair ACCEPTS
    // (no warning, no refusal), in both REPL and `--run`.
    #[test]
    fn layout_hash_match_accepts_in_both_modes() {
        for is_repl in [false, true] {
            assert!(
                matches!(
                    layout_hash_gate("same_hash", "same_hash", "shapes", is_repl, Span::SYNTHETIC),
                    LayoutHashGate::Accept
                ),
                "matching hashes must Accept (is_repl={is_repl})"
            );
        }
    }

    // spec: design/arch/platform-interface.md §5.5.4 — an empty host hash (the
    // host regenerated nothing: a scalar-only platform / first build / absent
    // schema) is TOLERATED — Accept, never Refuse, regardless of the DLL hash.
    #[test]
    fn layout_hash_empty_host_hash_accepts() {
        assert!(matches!(
            layout_hash_gate("dll_baked_hash", "", "shapes", false, Span::SYNTHETIC),
            LayoutHashGate::Accept
        ));
    }

    // spec: spec/08-modules.md §8.2.2 — parent-file rewrite (FIXME 0217). The
    // self-locating splice re-parses the CURRENT source, finds the live inline
    // `(mod child form…)` form, and replaces it with a bare `(mod child)`,
    // preserving surrounding forms + whitespace + comments.
    #[test]
    fn splice_inline_mod_rewrites_to_bare_reference() {
        let source = "(mod child (defn helper [] 7))\n(defn main [] 0)\n";
        let rewritten = splice_inline_mod_to_bare(source, "child")
            .expect("an inline (mod child …) form MUST be rewritten to bare");
        assert_eq!(
            rewritten,
            "(mod child)\n(defn main [] 0)\n",
            "the inline body MUST be spliced out, surrounding forms/whitespace \
             preserved (spec §8.2.2 step 2)",
        );
    }

    // spec: spec/08-modules.md §8.2.2 — idempotence. Re-running over a file
    // whose form is ALREADY the bare `(mod child)` reference MUST NOT rewrite
    // (returns None — no spurious mtime bump on reload of an extracted file).
    #[test]
    fn splice_inline_mod_is_idempotent_on_bare_reference() {
        let source = "(mod child)\n(defn main [] 0)\n";
        assert!(
            splice_inline_mod_to_bare(source, "child").is_none(),
            "an already-bare (mod child) reference MUST NOT be rewritten \
             (idempotence — spec §8.2.2 step 2)",
        );
    }

    // spec: spec/08-modules.md §8.2.2 — FIXME 0336 regression. The defect: the
    // S78 cluster retry-from-top re-runs Pass-0 and invokes the parent rewrite a
    // SECOND time. The old splice trusted the original-parse `decl.span` (e.g.
    // 0..30 over the 96-byte file); against the already-rewritten 77-byte file,
    // that stale range no longer addresses the `(mod child)` form, so the
    // idempotence guard MISSED and the splice overwrote the wrong range,
    // truncating the surrounding `main` form. The self-locating splice re-parses
    // the CURRENT content each call, so the second call finds NO inline form
    // (only a bare `(mod child)`) and is a no-op — the file stays valid.
    //
    // This test pins the exact seam: call the splice TWICE, feeding the output of
    // the first call (the already-rewritten content) into the second, simulating
    // the cluster-retry double-invocation. The second call MUST be a no-op and
    // MUST NOT corrupt the file.
    #[test]
    fn splice_inline_mod_double_invocation_is_idempotent_no_corruption() {
        let original = "(import [primitives [Pure]])\n\
                        (mod child (defn helper [] 7))\n\
                        (defn main [] (Pure (child/helper)))\n";

        // First call: the live inline form is located and spliced to bare.
        let after_first = splice_inline_mod_to_bare(original, "child")
            .expect("first call MUST rewrite the inline (mod child …) form");
        assert_eq!(
            after_first,
            "(import [primitives [Pure]])\n\
             (mod child)\n\
             (defn main [] (Pure (child/helper)))\n",
            "first rewrite splices out the inline body, preserving `main` intact",
        );

        // Second call (the cluster-retry re-invocation) against the ALREADY-
        // rewritten content. The self-locating splice finds no inline form, so
        // this is a no-op — the file is NOT corrupted (the 0336 defect).
        assert!(
            splice_inline_mod_to_bare(&after_first, "child").is_none(),
            "the second (cluster-retry) call MUST be a no-op — re-locating in \
             the current content finds only the bare (mod child), never the \
             stale original span (FIXME 0336)",
        );

        // The parent file content is unchanged after the second call — `main` is
        // fully preserved, the file still parses.
        assert!(
            cranelisp_frontend::parse(&after_first).is_ok(),
            "the rewritten parent MUST still parse after the double invocation",
        );
    }

    // spec: spec/08-modules.md §8.2.2 — multiple inline mods in one file. Each
    // named submodule's rewrite locates ITS OWN form; rewriting one leaves the
    // others' inline bodies intact for their own extraction pass.
    #[test]
    fn splice_inline_mod_handles_multiple_inline_mods() {
        let source = "(mod a (defn fa [] 1))\n(mod b (defn fb [] 2))\n(defn main [] 0)\n";
        let after_a = splice_inline_mod_to_bare(source, "a")
            .expect("the inline (mod a …) form MUST be rewritten");
        assert_eq!(
            after_a,
            "(mod a)\n(mod b (defn fb [] 2))\n(defn main [] 0)\n",
            "rewriting `a` leaves `b`'s inline body untouched",
        );
        let after_b = splice_inline_mod_to_bare(&after_a, "b")
            .expect("the inline (mod b …) form MUST be rewritten");
        assert_eq!(
            after_b,
            "(mod a)\n(mod b)\n(defn main [] 0)\n",
            "rewriting `b` afterward leaves the already-bare `a` untouched",
        );
        // Both bare now — further rewrites are no-ops.
        assert!(splice_inline_mod_to_bare(&after_b, "a").is_none());
        assert!(splice_inline_mod_to_bare(&after_b, "b").is_none());
    }

    // spec: spec/08-modules.md §8.2.2 — a source with no inline form for the
    // named submodule (or that does not parse) MUST leave the file untouched
    // rather than panicking or splicing at a bogus offset.
    #[test]
    fn splice_inline_mod_skips_when_no_inline_form() {
        // Bare reference only — no inline body.
        assert!(
            splice_inline_mod_to_bare("(mod child)", "child").is_none(),
            "a bare (mod child) reference is not an inline form — no-op",
        );
        // Inline form for a DIFFERENT submodule name — no-op for `child`.
        assert!(
            splice_inline_mod_to_bare("(mod other (defn f [] 0))", "child").is_none(),
            "an inline form for a different submodule name MUST NOT match",
        );
        // Unparseable source — best-effort no-op, no panic.
        assert!(
            splice_inline_mod_to_bare("(mod child (defn", "child").is_none(),
            "a source that does not parse MUST be a no-op (best-effort)",
        );
    }

    /// Minimal `ModuleCompiler` for exercising `handle_mod`'s Pass-0 behaviour.
    /// (Mirrors `worker::tests::mk_writer_test_ctx`, which is not visible here.)
    fn mk_mod_test_ctx<'a>(
        symbol_tables: &'a dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
        next_type_id: &'a std::sync::atomic::AtomicU32,
        scheduler: &'a CompileScheduler,
        typecheck_products: &'a dashmap::DashMap<ModuleFullPath, crate::session_v4::TypecheckProduct>,
        module: ModuleFullPath,
    ) -> ModuleCompiler<'a> {
        let module_aliases: &'static cranelisp_types::ModuleAliases =
            Box::leak(Box::new(cranelisp_types::ModuleAliases::default()));
        let prelude_fallback: &'static cranelisp_typecheck::PreludeFallback =
            Box::leak(Box::new(cranelisp_typecheck::PreludeFallback::default()));
        ModuleCompiler {
            symbol_tables,
            next_type_id,
            module_aliases,
            prelude_fallback,
            check_state: CheckState::new(module.clone()),
            current_module: module,
            scheduler,
            typecheck_products,
            introspection: None,
            lib_dirs: &[],
            platform_dirs: &[],
            project_root: Path::new("/"),
            shared_state: None,
        }
    }

    // FIXME 0342 — Pass-0 `handle_mod` MUST NOT register+block the submodule
    // for typecheck: it returns `Continue` (only the lightweight alias /
    // inline-write work happens in Pass 0). The submodule is driven AFTER
    // `finalize_cluster` commits the parent's symbols (so a `super` import of a
    // parent symbol resolves). This pins "no block during Pass-0".
    // spec: spec/08-modules.md §8.3.8
    #[test]
    fn handle_mod_pass0_returns_continue_no_block() {
        let module = ModuleFullPath::from("user");
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();
        symbol_tables.insert(
            module.clone(),
            crate::code::SessionSymbolTable::new_with_params(module.clone()),
        );
        let next_type_id = std::sync::atomic::AtomicU32::new(0);
        let scheduler = CompileScheduler::new();
        let typecheck_products = dashmap::DashMap::new();
        let mut ctx = mk_mod_test_ctx(
            &symbol_tables, &next_type_id, &scheduler, &typecheck_products,
            module.clone(),
        );

        // A bare `(mod test)` decl (no inline body — the inline-write path is
        // skipped, so no FS access). Pass-0 handling MUST return `Continue` —
        // it does NOT resolve the submodule file or block on its typecheck.
        let decl = cranelisp_types::ModDecl {
            name: "test".into(),
            visibility: Visibility::Public,
            inline_body: None,
            span: Span::SYNTHETIC,
        };
        let action = handle_mod(&mut ctx, &module, &decl)
            .expect("Pass-0 handle_mod must not error for a bare (mod test)");
        assert!(
            matches!(action, BlockAction::Continue),
            "Pass-0 handle_mod MUST return Continue (defer submodule drive to \
             post-finalize), got a Block",
        );
        // The submodule is NOT yet registered (drive is deferred).
        assert!(
            !symbol_tables.contains_key(&ModuleFullPath::from("user.test")),
            "Pass-0 handle_mod MUST NOT register the submodule (deferred to \
             drive_submodules after finalize)",
        );
    }
