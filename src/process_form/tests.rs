use super::*;

// -----------------------------------------------------------------------
// S102 CS-D1 — origin-uniform macro recording (Matrix E: the
// `record_macro_introspection` writer; design/int/s102-defect-wave.md §4.2)
// -----------------------------------------------------------------------

// spec: repl/spec.md §15.4 — invariant 7 (the authored form is the single
// regeneration authority). An expansion-produced defmacro records the
// ORIGINAL outer form as the regen-facing introspection `sexp`; the
// expanded artifact rides `.expanded`, and the entry's compile-path
// `macro_sexp` keeps the expanded defmacro (clause recompilation).
#[test]
fn record_macro_origin_is_regen_authority_for_expansion_artifact() {
    let module = ModuleFullPath::from("user");
    let introspection: dashmap::DashMap<FQSymbol, crate::session_v4::Introspection> =
        dashmap::DashMap::new();

    // Distinct spans: the original comes from one parse, the expanded
    // artifact from another (real expansion output carries synthetic
    // rewritten spans; span inequality is the discriminator).
    let original = cranelisp_frontend::parse("(mdef x 1)").unwrap().remove(0);
    let expanded = cranelisp_frontend::parse("      (defmacro x [] 1)")
        .unwrap()
        .remove(0);
    let info = cranelisp_frontend::parse_defmacro(&expanded).unwrap();

    form_dispatch::record_macro_introspection(
        Some(&introspection),
        &module,
        &info.name,
        &expanded,
        &original,
        Some("(mdef x 1)".to_string()),
    );

    let fq = FQSymbol {
        module: module.clone(),
        symbol: Symbol::from("x"),
    };
    let rec = introspection.get(&fq).expect("record created");
    assert_eq!(
        rec.sexp.as_ref().map(|s| s.format_flat()),
        Some(original.format_flat()),
        "regen-facing sexp is the AUTHORED original"
    );
    assert_eq!(
        rec.expanded.as_ref().map(|s| s.format_flat()),
        Some(expanded.format_flat()),
        "the expansion artifact rides .expanded"
    );
    assert_eq!(
        rec.source.as_deref(),
        Some("(mdef x 1)"),
        "the verbatim authored text is the recorded source (CS-D2)"
    );
}

// Negative twin: a DIRECT-authored defmacro (authored == sexp) records the
// defmacro form itself and sets NO `.expanded` (nothing was expanded).
// spec: repl/spec.md §15.4 — invariant 7
#[test]
fn record_direct_macro_has_no_expanded_artifact() {
    let module = ModuleFullPath::from("user");
    let introspection: dashmap::DashMap<FQSymbol, crate::session_v4::Introspection> =
        dashmap::DashMap::new();

    let direct = cranelisp_frontend::parse("(defmacro m [e] e)")
        .unwrap()
        .remove(0);
    let info = cranelisp_frontend::parse_defmacro(&direct).unwrap();
    form_dispatch::record_macro_introspection(
        Some(&introspection),
        &module,
        &info.name,
        &direct,
        &direct,
        None,
    );

    let fq = FQSymbol {
        module: module.clone(),
        symbol: Symbol::from("m"),
    };
    let rec = introspection.get(&fq).expect("record created");
    assert_eq!(
        rec.sexp.as_ref().map(|s| s.format_flat()),
        Some(direct.format_flat()),
    );
    assert!(
        rec.expanded.is_none(),
        "direct authorship has no expansion artifact"
    );
}

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

// spec: spec/08-modules.md §8.5.4 — I4 (0571.2). `module_has_no_member_error`
// is the SINGLE author of the "module X has no member Y" diagnostic (called
// only by the FQ-gap decision arm — no display-envelope mirror, Principle 7).
// It formats the message at the arm's located `<module>/<member>` reference.
#[test]
fn module_has_no_member_error_authors_message_and_locates_ref_span() {
    let program = build("(mathx/helper 1)");
    let module = ModuleFullPath::from("mathx");
    let span = gap_reference_span(
        &program,
        &GapReference {
            module: &module,
            member: "helper",
            referring_module: &user_module(),
            module_aliases: &ModuleAliases::default(),
        },
    );

    let err = module_has_no_member_error(&module, "helper", span);
    assert!(
        err.to_string()
            .contains("module 'mathx' has no member 'helper'"),
        "message: {}",
        err
    );
    // The reference is located in the program, so the diagnostic carries a
    // real source span rather than the SYNTHETIC fallback.
    assert_ne!(
        err.span(),
        Span::SYNTHETIC,
        "the `mathx/helper` reference span must be located"
    );
}

// spec: spec/08-modules.md §8.5.4 — a member reference absent from the
// program falls back to the SYNTHETIC span (still a well-formed message).
#[test]
fn module_has_no_member_error_falls_back_to_synthetic_span_when_ref_absent() {
    let module = ModuleFullPath::from("m");
    let span = gap_reference_span(
        &[],
        &GapReference {
            module: &module,
            member: "x",
            referring_module: &user_module(),
            module_aliases: &ModuleAliases::default(),
        },
    );
    let err = module_has_no_member_error(&module, "x", span);
    assert!(err.to_string().contains("module 'm' has no member 'x'"));
    assert_eq!(err.span(), Span::SYNTHETIC);
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
    assert_eq!(
        gap_target_module(&gap),
        Some(ModuleFullPath::from("shapes"))
    );
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
    let scheduler = CompileScheduler::new();
    let module_aliases = cranelisp_types::ModuleAliases::default();
    let prelude_fallback = cranelisp_typecheck::PreludeFallback::default();

    let mut resolver = SymbolTableMacroResolver {
        symbol_tables: &symbol_tables,
        current_module: module.clone(),
        module_aliases: &module_aliases,
        prelude_fallback: &prelude_fallback,
        scheduler: &scheduler,
        shared_state: None,
        macro_defining_modules: Vec::new(),
        blocked_on_fq_module: None,
        macro_lookup_dependencies: Default::default(),
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
    let scheduler = CompileScheduler::new();
    let module_aliases = cranelisp_types::ModuleAliases::default();
    let prelude_fallback = cranelisp_typecheck::PreludeFallback::default();

    let mut resolver = SymbolTableMacroResolver {
        symbol_tables: &symbol_tables,
        current_module: module.clone(),
        module_aliases: &module_aliases,
        prelude_fallback: &prelude_fallback,
        scheduler: &scheduler,
        shared_state: None,
        macro_defining_modules: Vec::new(),
        blocked_on_fq_module: None,
        macro_lookup_dependencies: Default::default(),
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
    let scheduler = CompileScheduler::new();
    let module_aliases = cranelisp_types::ModuleAliases::default();
    let prelude_fallback = cranelisp_typecheck::PreludeFallback::default();

    let mut resolver = SymbolTableMacroResolver {
        symbol_tables: &symbol_tables,
        current_module: module.clone(),
        module_aliases: &module_aliases,
        prelude_fallback: &prelude_fallback,
        scheduler: &scheduler,
        shared_state: None,
        macro_defining_modules: Vec::new(),
        blocked_on_fq_module: None,
        macro_lookup_dependencies: Default::default(),
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
            assert!(
                msg.contains("host_live_hash"),
                "warning names the host hash"
            );
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
        rewritten, "(mod child)\n(defn main [] 0)\n",
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
        after_a, "(mod a)\n(mod b (defn fb [] 2))\n(defn main [] 0)\n",
        "rewriting `a` leaves `b`'s inline body untouched",
    );
    let after_b = splice_inline_mod_to_bare(&after_a, "b")
        .expect("the inline (mod b …) form MUST be rewritten");
    assert_eq!(
        after_b, "(mod a)\n(mod b)\n(defn main [] 0)\n",
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

// FIXME 0423 (path-resolution half): an inline `(mod …)` backing file MUST
// be written next to the PARENT module's own on-disk file (lib-dir-relative
// when the parent lives in a lib-dir), NEVER under the process CWD /
// project root. Before the fix `write_inline_mod_to_disk` joined
// `project_root` to the dotted module path, producing stray
// `<cwd>/<module>/<name>.cl` trees outside the lib-dir. (The e2e guard is
// tests/spec_08_modules.rs::inline_mod_test_extraction_writes_lib_dir_relative_not_cwd.)
// spec: spec/08-modules.md §8.2.2 — extraction writes {parent_dir}/{stem}/{name}.cl
#[test]
fn write_inline_mod_resolves_lib_dir_relative_not_project_root() {
    let project_root = tempfile::tempdir().expect("project root tmpdir");
    let lib = tempfile::tempdir().expect("lib tmpdir");

    // Parent module `accum` lives in the lib-dir (NOT the project root).
    std::fs::write(lib.path().join("accum.cl"), "(defn double [x] x)\n").unwrap();

    let body = cranelisp_frontend::parse("(defn check [x] x)").unwrap();
    let lib_dirs = vec![lib.path().to_path_buf()];
    write_inline_mod_to_disk(
        &ModuleFullPath::from("accum"),
        &cranelisp_types::ModuleName::from("test"),
        &body,
        project_root.path(),
        &lib_dirs,
    )
    .expect("write inline mod");

    // CORRECT: backing file next to parent in the lib-dir.
    assert!(
        lib.path().join("accum/test.cl").is_file(),
        "backing file MUST be written lib-dir-relative at <lib>/accum/test.cl"
    );
    // NEGATIVE: no stray write under the project root (the 0423 symptom).
    assert!(
        !project_root.path().join("accum/test.cl").exists(),
        "NO stray backing file may appear under the project root (CWD) — FIXME 0423"
    );
}

// The "prefer recognizing an existing backing file" half (FIXME 0423 point
// 2): if an extraction-stable backing file already exists, it is read, not
// re-emitted (the call is a no-op that leaves the canonical copy intact).
// spec: spec/08-modules.md §8.2.2
#[test]
fn write_inline_mod_prefers_existing_backing_file() {
    let project_root = tempfile::tempdir().expect("project root tmpdir");
    let lib = tempfile::tempdir().expect("lib tmpdir");
    std::fs::write(lib.path().join("accum.cl"), "(defn double [x] x)\n").unwrap();

    // A canonical backing file already exists.
    std::fs::create_dir_all(lib.path().join("accum")).unwrap();
    let backing = lib.path().join("accum/test.cl");
    std::fs::write(&backing, "(defn canonical [] 7)\n").unwrap();

    let body = cranelisp_frontend::parse("(defn regenerated [x] x)").unwrap();
    let lib_dirs = vec![lib.path().to_path_buf()];
    write_inline_mod_to_disk(
        &ModuleFullPath::from("accum"),
        &cranelisp_types::ModuleName::from("test"),
        &body,
        project_root.path(),
        &lib_dirs,
    )
    .expect("write inline mod");

    // Untouched — the canonical copy is recognized, not overwritten.
    assert_eq!(
        std::fs::read_to_string(&backing).unwrap(),
        "(defn canonical [] 7)\n",
        "an existing extraction-stable backing file MUST be preferred, not re-emitted"
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
        reload_demands: std::sync::Arc::from([]),
        eval_driven: false,
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
        &symbol_tables,
        &next_type_id,
        &scheduler,
        &typecheck_products,
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

fn null_import_spec(target: &str, alias: Option<&str>) -> cranelisp_types::ImportSpec {
    cranelisp_types::ImportSpec {
        module_path: ModuleFullPath::from(target),
        alias: alias.map(cranelisp_types::ModuleName::from),
        names: cranelisp_types::ImportNames::None,
        span: Span::SYNTHETIC,
    }
}

/// Runs Pass-0 `handle_import` for one name-less spec in module `user`, whose
/// project root holds no `b.cl`, so any load attempt would fail.
fn run_null_import(spec: cranelisp_types::ImportSpec) -> ModuleAliasProbe {
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
        &symbol_tables,
        &next_type_id,
        &scheduler,
        &typecheck_products,
        module.clone(),
    );
    let action = handle_import(&mut ctx, &module, vec![spec])
        .expect("a name-less import must not attempt to load its target");
    ModuleAliasProbe {
        continued: matches!(action, BlockAction::Continue),
        target_registered: symbol_tables.contains_key(&ModuleFullPath::from("b")),
        aliases: ctx
            .module_aliases
            .iter()
            .map(|entry| (entry.key().clone(), entry.value().target.clone()))
            .collect(),
    }
}

struct ModuleAliasProbe {
    continued: bool,
    target_registered: bool,
    aliases: Vec<(ModuleFullPath, ModuleFullPath)>,
}

// spec: spec/08-modules.md §8.3.6 — an alias-only import registers its alias for
// qualified access (§8.6.6 step 1) without loading the target; loading is left
// to the qualified reference (§8.5.4).
#[test]
fn alias_only_import_registers_alias_without_loading() {
    let probe = run_null_import(null_import_spec("b", Some("bb")));
    assert!(probe.continued);
    assert!(!probe.target_registered);
    assert_eq!(
        probe.aliases,
        vec![(
            cranelisp_types::module_alias_key(&ModuleFullPath::from("user"), "bb"),
            ModuleFullPath::from("b"),
        )],
        "`(import [(b bb) []])` must register `bb` as user's alias for `b`"
    );
}

// spec: spec/08-modules.md §8.3.7 — NEGATIVE: a plain null import registers no
// alias and loads nothing.
#[test]
fn null_import_registers_no_alias_and_loads_nothing() {
    let probe = run_null_import(null_import_spec("b", None));
    assert!(probe.continued);
    assert!(!probe.target_registered);
    assert!(probe.aliases.is_empty(), "got {:?}", probe.aliases);
}

// -----------------------------------------------------------------------
// 0571 member-not-found diagnostic: the span-attribution walker
// (`gap_reference_span`) that gives the "module X has no member Y" error a
// real source location at the user's reference site instead of `0..0`.
// -----------------------------------------------------------------------

fn var(name: &str, start: u32, end: u32) -> Expr {
    Expr::Var {
        name: Symbol::from(name),
        span: Span::new(start, end),
        resolved_call: None,
        inferred_type: None,
    }
}

fn int_lit(value: i64) -> Expr {
    Expr::IntLit {
        value,
        span: Span::new(0, 1),
        inferred_type: None,
    }
}

/// Locate the value gap `module/member` in `program` from an alias-free `user`.
fn unaliased_value_span(program: &[TopLevel], module: &str, member: &str) -> Span {
    gap_reference_span(
        program,
        &GapReference {
            module: &ModuleFullPath::from(module),
            member,
            referring_module: &user_module(),
            module_aliases: &ModuleAliases::default(),
        },
    )
}

// The reference-span is found through the `Apply` callee — the exact
// `(primitives/nosuchfn 1 2)` shape 0490 diagnoses.
#[test]
fn gap_reference_span_locates_qualified_callee() {
    let apply = Expr::Apply {
        callee: Box::new(var("primitives/nosuchfn", 1, 20)),
        args: vec![int_lit(1), int_lit(2)],
        span: Span::new(0, 25),
        resolved_call: None,
        inferred_type: None,
    };
    assert_eq!(
        unaliased_value_span(&[TopLevel::Expr(apply)], "primitives", "nosuchfn"),
        Span::new(1, 20),
    );
}

// A non-matching name yields the SYNTHETIC fallback rather than
// mis-attributing.
#[test]
fn gap_reference_span_synthetic_for_absent_name() {
    let apply = Expr::Apply {
        callee: Box::new(var("primitives/nosuchfn", 1, 20)),
        args: vec![int_lit(1)],
        span: Span::new(0, 25),
        resolved_call: None,
        inferred_type: None,
    };
    assert_eq!(
        unaliased_value_span(&[TopLevel::Expr(apply)], "some", "other"),
        Span::SYNTHETIC,
    );
}

// The walker recurses through a defn body (the reference need not be a bare
// top-level expression).
#[test]
fn gap_reference_span_recurses_defn_body() {
    let body = Expr::If {
        cond: Box::new(var("cond", 0, 4)),
        then_branch: Box::new(var("core/absent", 10, 21)),
        else_branch: Box::new(int_lit(0)),
        span: Span::new(0, 30),
        inferred_type: None,
    };
    let defn = TopLevel::Defn(cranelisp_types::Defn {
        name: Symbol::from("f"),
        docstring: None,
        variants: vec![cranelisp_types::DefnVariant {
            params: vec![],
            body,
            span: Span::new(0, 40),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 40),
    });
    assert_eq!(
        unaliased_value_span(&[defn], "core", "absent"),
        Span::new(10, 21),
    );
}

// -----------------------------------------------------------------------
// Gap reference site (design/int/int.md §6.3.1): one lookup over value and
// type positions, matching the written qualifier after alias substitution.
// -----------------------------------------------------------------------

fn build(src: &str) -> Vec<TopLevel> {
    crate::worker::build_program_compat(&cranelisp_frontend::parse(src).unwrap()).unwrap()
}

fn user_module() -> ModuleFullPath {
    ModuleFullPath::from("user")
}

fn type_gap(module: &str, name: &str) -> cranelisp_types::ResolutionGap {
    cranelisp_types::ResolutionGap::Type(cranelisp_types::FQTypeName::new(
        ModuleFullPath::from(module),
        cranelisp_types::TypeName::from(name),
    ))
}

/// `user` registers `(import [(zz z) …])`: the alias `z → zz`.
fn z_alias_for_user() -> ModuleAliases {
    let aliases = ModuleAliases::default();
    aliases.insert(
        cranelisp_types::module_alias_key(&user_module(), "z"),
        cranelisp_types::ModuleAliasEntry::new(
            ModuleFullPath::from("zz"),
            Visibility::Private,
            Span::SYNTHETIC,
        ),
    );
    aliases
}

/// Locate `gap` in `program` as the gap arm does, from module `user`.
fn locate(
    program: &[TopLevel],
    gap: &cranelisp_types::ResolutionGap,
    aliases: &ModuleAliases,
) -> Span {
    let module = gap_target_module(gap).unwrap();
    let member = gap_member(gap);
    gap_reference_span(
        program,
        &GapReference {
            module: &module,
            member: &member,
            referring_module: &user_module(),
            module_aliases: aliases,
        },
    )
}

fn text(src: &str, span: Span) -> &str {
    &src[span.start as usize..span.end as usize]
}

fn only_defn_variant_span(program: &[TopLevel]) -> Span {
    match program {
        [TopLevel::Defn(d)] => d.variants[0].span,
        other => panic!("expected one defn, got {other:?}"),
    }
}

// spec: spec/08-modules.md §8.5.4 — edge 3 (FT-4's seam): a type-only
// reference to a missing module is reported at the defn variant that carries
// the parameter annotation.
#[test]
fn gap_reference_span_locates_type_param_annotation_at_defn_variant() {
    let src = "(defn h [:zz/T t] 7)";
    let program = build(src);
    let span = locate(&program, &type_gap("zz", "T"), &ModuleAliases::default());
    assert_eq!(span, only_defn_variant_span(&program));
    assert!(text(src, span).contains(":zz/T"), "{span:?}");
}

// spec: spec/08-modules.md §8.5.4 — edge 3: a `deftype` field type is
// reported at its field, the innermost spanned carrier.
#[test]
fn gap_reference_span_locates_type_in_deftype_field() {
    let src = "(deftype Box [:Int n :zz/T v])";
    let program = build(src);
    let TopLevel::TypeDef {
        constructors, span, ..
    } = &program[0]
    else {
        panic!("expected a deftype, got {:?}", program[0]);
    };
    let field_span = constructors[0].fields[1].span;
    assert_ne!(field_span, *span, "the field is inside the deftype");

    let located = locate(&program, &type_gap("zz", "T"), &ModuleAliases::default());
    assert_eq!(located, field_span);
    // The frontend spans a field by its name.
    assert_eq!(text(src, located), "v");
}

// spec: spec/08-modules.md §8.6.6 — the gap names the alias-substituted
// module, so an alias-spelled reference is located through the same walk,
// in type and value position alike.
#[test]
fn gap_reference_span_resolves_alias_qualifier_for_type_and_value() {
    let aliases = z_alias_for_user();

    let type_src = "(defn h [:z/T t] 7)";
    let type_program = build(type_src);
    let span = locate(&type_program, &type_gap("zz", "T"), &aliases);
    assert_eq!(span, only_defn_variant_span(&type_program));

    let value_src = "(defn g [] (z/f 1))";
    let value_gap = cranelisp_types::ResolutionGap::SymbolTypechecked(FQSymbol {
        module: ModuleFullPath::from("zz"),
        symbol: Symbol::from("f"),
    });
    let span = locate(&build(value_src), &value_gap, &aliases);
    assert_eq!(text(value_src, span), "z/f");
}

// spec: spec/08-modules.md §8.5.4 — edge 3: the member-absent value gap names
// the qualifier as written, so an alias-spelled reference to a missing member
// of a loaded module is located at that reference.
#[test]
fn gap_reference_span_locates_alias_spelled_member_absent_value_gap() {
    let src = "(defn g [] (z/f 1))";
    let gap = cranelisp_types::ResolutionGap::SymbolTypechecked(FQSymbol {
        module: ModuleFullPath::from("z"),
        symbol: Symbol::from("f"),
    });
    let span = locate(&build(src), &gap, &z_alias_for_user());
    assert_eq!(text(src, span), "z/f", "{span:?}");
}

// spec: spec/08-modules.md §8.5.4 — negative: a reference matches only when
// its resolved qualifier AND its member are the gap's; otherwise the
// diagnostic falls back to SYNTHETIC rather than mis-attributing.
#[test]
fn gap_reference_span_neg_unaliased_qualifier_or_other_member_does_not_match() {
    let gap = type_gap("zz", "T");
    let no_aliases = ModuleAliases::default();

    let unaliased = build("(defn h [:z/T t] 7)");
    assert_eq!(locate(&unaliased, &gap, &no_aliases), Span::SYNTHETIC);

    let other_member = build("(defn h [:zz/U t] 7)");
    assert_eq!(locate(&other_member, &gap, &no_aliases), Span::SYNTHETIC);
}

// spec: spec/08-modules.md §8.5.4 — edge 3 over the remaining type carriers:
// each reports its innermost spanned node; a signature-tail symbol reports
// its own span.
#[test]
fn gap_reference_span_locates_each_remaining_type_carrier() {
    let gap = type_gap("zz", "T");
    let no_aliases = ModuleAliases::default();
    let cases = [
        (
            "lambda parameter",
            "(defn g [] (fn [:zz/T t] t))",
            "(fn [:zz/T t] t)",
        ),
        ("inline annotation", "(defn g [x] :zz/T x)", ":zz/T x"),
        ("trait signature tail", "(deftrait Tr (m [x] zz/T))", "zz/T"),
        (
            "impl target",
            "(impl Tr zz/T (defn m [x] 1))",
            "(impl Tr zz/T (defn m [x] 1))",
        ),
    ];
    for (carrier, src, expected) in cases {
        let span = locate(&build(src), &gap, &no_aliases);
        assert_eq!(text(src, span), expected, "{carrier}: {span:?}");
    }

    let param_src = "(deftrait Tr (m [:zz/T x] Int))";
    let param_program = build(param_src);
    let TopLevel::TraitDecl(decl) = &param_program[0] else {
        panic!("expected a deftrait, got {:?}", param_program[0]);
    };
    assert_eq!(
        locate(&param_program, &gap, &no_aliases),
        decl.methods[0].span
    );

    let applied = build("(defn h [:(Vec zz/T) t] 7)");
    assert_eq!(
        locate(&applied, &gap, &no_aliases),
        only_defn_variant_span(&applied)
    );

    let fn_typed = build("(defn h [:(Fn [zz/T] Int) t] 7)");
    assert_eq!(
        locate(&fn_typed, &gap, &no_aliases),
        only_defn_variant_span(&fn_typed)
    );
}

// spec: spec/08-modules.md §8.5.4 — edge 3: a value reference inside an impl
// method body is located at the reference itself.
#[test]
fn gap_reference_span_locates_value_reference_in_impl_method_body() {
    let src = "(impl Tr Int (defn m [x] (zz/f x)))";
    let gap = cranelisp_types::ResolutionGap::SymbolTypechecked(FQSymbol {
        module: ModuleFullPath::from("zz"),
        symbol: Symbol::from("f"),
    });
    let span = locate(&build(src), &gap, &ModuleAliases::default());
    assert_eq!(text(src, span), "zz/f", "{span:?}");
}

// spec: spec/08-modules.md §8.5.4 — negative: trait references (an impl's
// trait, stacked bounds) raise no gap and are not reference sites.
#[test]
fn gap_reference_span_neg_trait_references_are_not_sites() {
    let gap = type_gap("zz", "T");
    let no_aliases = ModuleAliases::default();
    for src in ["(impl zz/T Int (defn m [x] 1))", "(defn h [:zz/T :Eq t] 7)"] {
        assert_eq!(
            locate(&build(src), &gap, &no_aliases),
            Span::SYNTHETIC,
            "{src}"
        );
    }
}

// -----------------------------------------------------------------------
// FIXME 0650 — macro-route diagnostic re-anchoring (macro-diagnostic-reanchoring.md)
// -----------------------------------------------------------------------

// A diagnostic over macro-expansion output carrying a SYNTHETIC location (the
// ≥1M rewrite band) re-anchors to the origin form's real span and APPENDS the
// "in expansion of …" context — the frontend message stays verbatim.
// spec: spec/05-definitions.md §5 — macro-route reject span points at the written form.
#[test]
fn reanchor_synthetic_diagnostic_relocates_and_appends_context() {
    use cranelisp_types::Span;
    let origin = cranelisp_frontend::parse("(mkbad)").unwrap().remove(0);
    let origin_span = origin.span();
    // Synthetic location: the `rewrite_spans_unique` ≥1M unique band.
    let synth = Span {
        start: 1_000_037,
        end: 1_000_044,
    };
    let err = CranelispError::ParseError {
        message: "qualified head not allowed in a binder".to_string(),
        location: ErrorLocation::from_span(synth),
    };
    let out = reanchor_expansion_diagnostic(err, origin_span, &origin);
    assert_eq!(
        out.span(),
        origin_span,
        "the synthetic location MUST re-anchor to the origin form's real span"
    );
    assert!(
        out.message()
            .contains("qualified head not allowed in a binder"),
        "the frontend message MUST be preserved verbatim: {}",
        out.message()
    );
    assert!(
        out.message().contains("in expansion of `(mkbad)`"),
        "expansion context naming the WRITTEN form MUST be appended: {}",
        out.message()
    );
}

// The degenerate `Span::SYNTHETIC` = (0,0) flavour is caught by the same
// "outside the origin extent" predicate (no hard-coded 1M constant).
// spec: spec/05-definitions.md §5 — macro-route reject span points at the written form.
#[test]
fn reanchor_catches_degenerate_zero_width_synthetic() {
    use cranelisp_types::Span;
    let origin = cranelisp_frontend::parse("(def y 1)").unwrap().remove(0);
    let origin_span = origin.span();
    let err = CranelispError::ParseError {
        message: "reject".to_string(),
        location: ErrorLocation::from_span(Span::SYNTHETIC),
    };
    let out = reanchor_expansion_diagnostic(err, origin_span, &origin);
    assert_eq!(
        out.span(),
        origin_span,
        "the (0,0) synthetic span must re-anchor"
    );
}

// A NATIVE-form diagnostic (a real span WITHIN the origin extent) passes
// through UNCHANGED — the predicate must not touch already-located errors.
// spec: macro-diagnostic-reanchoring.md §6 — native-form pass-through.
#[test]
fn reanchor_leaves_native_span_diagnostic_untouched() {
    use cranelisp_types::Span;
    let origin = cranelisp_frontend::parse("(defn f [] x)")
        .unwrap()
        .remove(0);
    let origin_span = origin.span();
    // A real sub-form error located within [start, end).
    let real = Span {
        start: origin_span.start + 1,
        end: origin_span.start + 3,
    };
    let err = CranelispError::TypeError {
        message: "undefined variable: x".to_string(),
        location: ErrorLocation::from_span(real),
    };
    let out = reanchor_expansion_diagnostic(err, origin_span, &origin);
    assert_eq!(
        out.span(),
        real,
        "a diagnostic already located within the origin extent MUST pass through"
    );
    assert!(
        !out.message().contains("in expansion of"),
        "no expansion context is appended to a native-form error: {}",
        out.message()
    );
}

// FIXME 0650 §2.1 — the FINALIZE/typecheck application site. A synthetic-
// located TYPECHECK error over a single-form `def`/`const` cluster re-anchors
// to that origin form + appends `in expansion of` (a def/const typecheck
// error is a different CLASS than the frontend binder reject — which is why
// the transform keys on the synthetic-LOCATION predicate, not the error class).
// spec: macro-diagnostic-reanchoring.md §2.1 — finalize-path re-anchor.
#[test]
fn reanchor_finalize_typecheck_error_relocates_to_single_origin_form() {
    use cranelisp_types::Span;
    let origin = cranelisp_frontend::parse("(def z (bad-op 1))")
        .unwrap()
        .remove(0);
    let synth = Span {
        start: 1_000_012,
        end: 1_000_020,
    };
    let err = CranelispError::TypeError {
        message: "type mismatch: expected Int, found String".to_string(),
        location: ErrorLocation::from_span(synth),
    };
    let out = reanchor_finalize_error(err, std::slice::from_ref(&origin));
    assert_eq!(
        out.span(),
        origin.span(),
        "a synthetic finalize error MUST re-anchor to the origin form"
    );
    assert!(
        out.message().contains("type mismatch"),
        "the typecheck message MUST be preserved verbatim: {}",
        out.message()
    );
    assert!(
        out.message().contains("in expansion of"),
        "expansion context MUST be appended at the finalize site: {}",
        out.message()
    );
}

// A NATIVE finalize error (its span within some origin form's real extent)
// passes through unchanged — even in a multi-form cluster.
// spec: macro-diagnostic-reanchoring.md §2.1 — native pass-through.
#[test]
fn reanchor_finalize_leaves_native_error_untouched() {
    use cranelisp_types::Span;
    let forms = cranelisp_frontend::parse("(defn a [] 1)\n(defn b [] x)").unwrap();
    // A real span landing within the SECOND form's extent.
    let second = &forms[1];
    let real = Span {
        start: second.span().start + 1,
        end: second.span().start + 3,
    };
    let err = CranelispError::TypeError {
        message: "undefined variable: x".to_string(),
        location: ErrorLocation::from_span(real),
    };
    let out = reanchor_finalize_error(err, &forms);
    assert_eq!(
        out.span(),
        real,
        "a located native finalize error MUST pass through"
    );
    assert!(!out.message().contains("in expansion of"));
}

// Multi-form cluster whose synthetic node cannot be attributed to one form:
// fall back to the FIRST origin form (a real, if coarse, location beats a
// no-source-byte one).
// spec: macro-diagnostic-reanchoring.md §2.1 — multi-form fallback.
#[test]
fn reanchor_finalize_multi_form_falls_back_to_first_origin() {
    use cranelisp_types::Span;
    let forms = cranelisp_frontend::parse("(const p 1)\n(const q 2)").unwrap();
    let err = CranelispError::TypeError {
        message: "reject".to_string(),
        location: ErrorLocation::from_span(Span::SYNTHETIC),
    };
    let out = reanchor_finalize_error(err, &forms);
    assert_eq!(
        out.span(),
        forms[0].span(),
        "synthetic multi-form error falls back to the first origin form's span"
    );
}

// -----------------------------------------------------------------------
// Qualified lookup dependencies — int's macro-head producer and the
// checkpoint and finalize publications (design/int/int.md §7.6.2).
// Each row compiles a module from files in a scratch project through a real
// session, so the pool worker's continuation holder is on the path.
// -----------------------------------------------------------------------

mod lookup_dependencies {
    use std::path::PathBuf;

    use crate::session_v4::{CompilerSession, RunMode, SessionSettings};
    use cranelisp_types::{CodegenBehaviour, ModuleFullPath};

    struct Project {
        session: CompilerSession,
        root: PathBuf,
        _dir: tempfile::TempDir,
    }

    impl Project {
        fn new(files: &[(&str, &str)]) -> Self {
            let dir = tempfile::tempdir().unwrap();
            let root = dir.path().to_path_buf();
            for (name, source) in files {
                std::fs::write(root.join(name), source).unwrap();
            }
            let settings = SessionSettings {
                no_color: true,
                no_cache: true,
                codegen_behaviour: CodegenBehaviour::InMemoryAndObject,
                priority_workers: 1,
                nice_workers: 0,
                run_mode: RunMode::Repl,
            };
            let mut session = CompilerSession::new(settings, root.clone(), "user")
                .expect("test session bootstrap");
            session.set_lib_dirs(Vec::new());
            Project {
                session,
                root,
                _dir: dir,
            }
        }

        /// Compile `module` from `source`; an error is returned rendered.
        fn compile(&mut self, module: &str, source: &str) -> Result<(), String> {
            let path = self.root.join(format!("{module}.cl"));
            self.session
                .register_module_with_source(module, source, &path)
                .map(|_| ())
                .map_err(|error| error.to_string())
        }

        fn lookup_dependencies(&self, module: &str) -> Vec<String> {
            self.session
                .shared
                .symbol_tables
                .get(&ModuleFullPath::from(module))
                .map(|table| table.lookup_dependencies().map(|m| m.to_string()).collect())
                .unwrap_or_default()
        }
    }

    impl Drop for Project {
        fn drop(&mut self) {
            self.session.shutdown();
        }
    }

    const MACRO_B: (&str, &str) = ("b.cl", "(defmacro m [] `11)\n");

    // spec: design/int/int.md §7.6.2 — int records a qualified macro head's
    // module after alias substitution, never the alias.
    #[test]
    fn alias_qualified_macro_head_publishes_the_target_module() {
        let mut project = Project::new(&[MACRO_B]);
        project
            .compile("a", "(import [(b bb) []])\n(defn g [] (bb/m))\n")
            .unwrap();
        assert_eq!(project.lookup_dependencies("a"), ["b"]);
    }

    // spec: design/int/int.md §7.6.2 — a bare macro head records nothing.
    #[test]
    fn bare_macro_head_publishes_nothing() {
        let mut project = Project::new(&[MACRO_B]);
        project
            .compile("a", "(import [b [m]])\n(defn g [] (m))\n")
            .unwrap();
        assert!(project.lookup_dependencies("a").is_empty());
    }

    // spec: design/int/int.md §7.6.2 — the carry: `g`'s head is expanded,
    // then `k`'s reference to the unloaded `e` gaps. The retry resumes the
    // expanded prefix, which no longer names `b`.
    #[test]
    fn macro_head_module_survives_a_later_dependency_gap() {
        let mut project = Project::new(&[MACRO_B, ("e.cl", "(defn f [] 0)\n")]);
        project
            .compile("a", "(defn g [] (b/m))\n(defn k [] (e/f))\n")
            .unwrap();
        assert_eq!(project.lookup_dependencies("a"), ["b", "e"]);
    }

    // spec: design/int/int.md §7.6.2 — clause staging: a qualified reference
    // in a macro clause body reaches the published macro table.
    #[test]
    fn qualified_reference_in_macro_clause_body_reaches_the_macro_table() {
        let mut project = Project::new(&[(
            "r.cl",
            "(import [macros [SexpInt]])\n(defn f [] (SexpInt 7))\n",
        )]);
        project.compile("a", "(defmacro m [] (r/f))\n").unwrap();
        // The synthesized clause also names the compiler-owned `macros`;
        // recording is unfiltered and the edge consumer drops it.
        let recorded = project.lookup_dependencies("a");
        assert!(recorded.iter().any(|module| module == "r"), "{recorded:?}");
    }

    // spec: design/int/int.md §7.6.2 — a failed cluster check drops the
    // attempt, so nothing is published (Principle 26).
    #[test]
    fn failed_cluster_check_publishes_no_lookup_dependency() {
        let mut project = Project::new(&[MACRO_B]);
        let result = project.compile(
            "a",
            "(import [primitives [Int]])\n(defn g [] (b/m))\n(defn h [:Int x] :Int true)\n",
        );
        let error = result.expect_err("the cluster must fail its check");
        assert!(error.contains("type mismatch"), "{error}");
        assert!(project.lookup_dependencies("a").is_empty());
    }
}
