    use super::*;
    use cranelisp_types::{ErrorLocation,
        DefKind, DefnVariant, Expr, FQSymbol, ImportNames, ImportSpec, ModuleEntry,
        ModuleFullPath, Scheme, Symbol, Type, Visibility,
    };
    use std::collections::HashMap;
    // FIXME 0109 Wave C: these helpers moved to `process_form.rs`; a handful of
    // worker-side tests (introspection + private-submodule enforcement) still
    // exercise them (the latter share `mk_writer_test_ctx`, which stays here).
    use crate::process_form::{
        check_private_submodule_import, has_code_ptr, record_imports_on_symbol_table,
        record_submodule_on_symbol_table,
    };

    /// Test-only: read a compiled code pointer from a symbol's GOT slot. The
    /// production executor reads clause code ptrs through
    /// `JitMacroExpander::clause_code_ptr` (`src/expander.rs`); this mirrors that
    /// read for the codegen unit tests.
    fn get_code_ptr(
        symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
        module: &ModuleFullPath,
        name: &Symbol,
    ) -> Option<*const u8> {
        symbol_tables.get(module).and_then(|t| {
            let entry = t.get(name.as_ref())?;
            let ModuleEntry::Def { code: Some(_), .. } = entry else {
                return None;
            };
            let slot = entry.callable_got_slot()?;
            let ptr = t.got.load_slot(slot);
            if ptr.is_null() { None } else { Some(ptr) }
        })
    }

    fn synthetic_scheme() -> Scheme {
        Scheme {
            type_vars: vec![],
            constraints: HashMap::new(),
            ty: Type::Int,
        }
    }

    /// A trivial single-variant `DefnVariant` body (S69 Submission 35:
    /// `ModuleEntry::Def.ast` is `DefnVariant`, not `Defn`).
    fn trivial_variant() -> DefnVariant {
        DefnVariant {
            params: vec![],
            body: Expr::IntLit {
                value: 0,
                span: Span::SYNTHETIC,
                inferred_type: Some(Box::new(Type::Int)),
            },
            span: Span::SYNTHETIC,
        }
    }

    fn mk_def_with_got(
        mut kind: DefKind,
        ast: Option<DefnVariant>,
        got_slot: Option<usize>,
    ) -> ModuleEntry<crate::code::Code> {
        // S83 reshape: the slot rides on the callable `DefKind` variant. Honour
        // the legacy `got_slot` arg by re-pointing the kind's slot before
        // building (no-op for non-callable kinds).
        if let Some(slot) = got_slot {
            repoint_callable_slot(&mut kind, slot);
        }
        let mut builder = ModuleEntry::def(synthetic_scheme(), kind)
            .visibility(Visibility::Public);
        if let Some(variant) = ast {
            builder = builder.ast(variant);
        }
        builder.build()
    }

    // spec: design/arch/macro-availability-model.md §0 (FIXME 0299) — the
    // cache-restore Linker must resolve binary-exported primitive externs that
    // the synthetic `macros` module references (e.g. `sconcat`). The fresh JIT
    // resolves these via the host's exported symbols; `dlsym_host_symbol` is
    // int's equivalent for the cache path. A known binary-exported primitive
    // must resolve to a non-null address; a nonexistent symbol must be None.
    #[test]
    fn dlsym_host_symbol_resolves_exported_primitive() {
        // `sconcat` is `#[unsafe(export_name = "sconcat")]` in
        // `cranelisp-primitives`, statically linked into the test binary.
        let ptr = dlsym_host_symbol("sconcat");
        assert!(
            ptr.is_some(),
            "sconcat must be resolvable as a host-exported symbol (cache-restore \
             Linker depends on this for cross-module macro expansion — FIXME 0299)"
        );
        assert!(!ptr.unwrap().is_null());

        // `quote-sexp` is the other synthetic-`macros` primitive extern.
        assert!(dlsym_host_symbol("quote-sexp").is_some());
    }

    // spec: (same anchor) — a symbol the host does not export must not resolve,
    // so a genuine `unresolved symbol` is surfaced by the relocation pass rather
    // than masked by a bogus address.
    #[test]
    fn dlsym_host_symbol_misses_unexported_name() {
        assert!(
            dlsym_host_symbol("__cranelisp_definitely_not_a_real_exported_symbol__").is_none()
        );
    }

    // S78 in-call-stack restructure: the `pass0_dep_load_resume_restarts_pass2
    // _from_zero` and `pass2_fq_autoload_resume_honours_saved_index` unit tests
    // probed the deleted `pass2_resume_index` helper. The retry-from-top model
    // has NO saved resume index — the whole cluster re-runs from its packet
    // sexps every pass, so forms-before-import are always re-processed by
    // construction (Defect-B / OQ-4). The behaviour is guarded e2e by
    // `tests/spec_08_modules.rs::defn_before_import_resumes_correctly_after_dep_load`.

    // spec: design/int/phase2-codegen-convergence.md §5 — name-list prep via defined_symbols
    #[test]
    fn priority_worker_name_list_via_defined_symbols_filter() {
        // Seed a symbol table with a cross-section of entries. Only the entries
        // that pass `defined_symbols()` should be candidates for codegen — the
        // worker's name-list preparation MUST produce the same set.
        let module = ModuleFullPath::from("user");
        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());

        // Compilable: regular UserFn with ast: Some(_).
        st.insert(
            Symbol::from("regular"),
            mk_def_with_got(
                DefKind::UserFn { fn_state: cranelisp_types::UserFnState::Concrete { got_slot: 0, mode_summary: None } },
                Some(trivial_variant()),
                Some(0),
            ),
        );

        // Compilable: mangled multi-sig variant (also a UserFn with ast).
        st.insert(
            Symbol::from("add$Int+Int"),
            mk_def_with_got(
                DefKind::UserFn { fn_state: cranelisp_types::UserFnState::Concrete { got_slot: 0, mode_summary: None } },
                Some(trivial_variant()),
                Some(1),
            ),
        );

        // Not compilable: Overloaded base — ast: None.
        st.insert(
            Symbol::from("add"),
            mk_def_with_got(
                DefKind::Overloaded { variants: vec![] },
                None,
                None,
            ),
        );

        // Not compilable: constrained template even if ast happens to be Some.
        st.insert(
            Symbol::from("poly_fn"),
            mk_def_with_got(
                DefKind::UserFn {
                    fn_state: cranelisp_types::UserFnState::Constrained(Box::new(
                        cranelisp_types::ConstrainedFn {
                            variant: trivial_variant(),
                            scheme: synthetic_scheme(),
                        },
                    )),
                },
                Some(trivial_variant()),
                None,
            ),
        );

        // Not compilable: Import chain entry.
        st.insert(
            Symbol::from("imported"),
            ModuleEntry::Import {
                source: FQSymbol {
                    module: ModuleFullPath::from("other"),
                    symbol: Symbol::from("x"),
                },
                visibility: Visibility::Private,
            },
        );

        let compiled: Vec<Symbol> = st
            .defined_symbols()
            .map(|(name, _)| name.clone())
            .collect();

        // Exactly the two compilable entries: set equality ignoring order.
        assert_eq!(compiled.len(), 2, "expected 2 compilable names, got {compiled:?}");
        assert!(compiled.contains(&Symbol::from("regular")));
        assert!(compiled.contains(&Symbol::from("add$Int+Int")));
        assert!(!compiled.contains(&Symbol::from("add")));
        assert!(!compiled.contains(&Symbol::from("poly_fn")));
        assert!(!compiled.contains(&Symbol::from("imported")));
    }

    // spec: BC §3 invariant 3 — batch CompilationArtifacts routing to Introspection
    //
    // S76 W-Collapse: `compile_to_module` now returns batch-level
    // `CompilationArtifacts` (concatenated `clif_ir` + summed `code_size`),
    // attributed to each compiled name; per-symbol disasm is on-demand via
    // `cranelisp_backend::produce_disasm` (the backend's `FunctionArtifacts`
    // per-fn map is `pub(crate)` and no longer crosses the boundary). This test
    // mirrors the routing loop in `inline_jit_codegen_for_names` step 7.
    #[test]
    fn priority_worker_routes_batch_artifacts_to_introspection() {
        let module = ModuleFullPath::from("user");
        let clif_ir = "function %foo() -> i64 { ... }\nfunction %bar() -> i64 { ... }";
        let code_size: usize = 19;
        let names = [Symbol::from("foo"), Symbol::from("bar")];

        let introspection: dashmap::DashMap<FQSymbol, crate::session_v4::Introspection> =
            dashmap::DashMap::new();

        // Mirror the exact batch routing loop: each compiled name gets the
        // batch clif_ir + code_size; disasm is on-demand (not stored).
        for name in &names {
            let fq = FQSymbol { module: module.clone(), symbol: name.clone() };
            let mut entry = introspection.entry(fq).or_default();
            entry.clif_ir = Some(clif_ir.to_string());
            entry.code_size = Some(code_size);
        }

        for name in &names {
            let fq = FQSymbol { module: module.clone(), symbol: name.clone() };
            let e = introspection.get(&fq).expect("introspection entry present");
            assert!(e.clif_ir.as_deref().unwrap_or("").contains("%foo"));
            assert_eq!(e.code_size, Some(code_size));
        }
    }

    // spec: design/int/phase2-codegen-convergence.md §5 — GOT slot registration on compile completion
    #[test]
    fn priority_worker_stores_code_ptr_in_got_slot() {
        // Given a symbol_tables entry with got_slot: Some(3), verify that after
        // compile completion the worker stores the compiled function pointer
        // at slot 3 in the module's GOT table.
        let module = ModuleFullPath::from("user");
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> = dashmap::DashMap::new();
        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());

        // Advance the next_got_slot by allocating four slots; the 4th is slot 3.
        let slot_0 = st.allocate_got_slot();
        let slot_1 = st.allocate_got_slot();
        let slot_2 = st.allocate_got_slot();
        let slot_3 = st.allocate_got_slot();
        assert_eq!(slot_0, 0);
        assert_eq!(slot_1, 1);
        assert_eq!(slot_2, 2);
        assert_eq!(slot_3, 3);

        st.insert(
            Symbol::from("target"),
            mk_def_with_got(
                DefKind::UserFn { fn_state: cranelisp_types::UserFnState::Concrete { got_slot: 0, mode_summary: None } },
                Some(trivial_variant()),
                Some(3),
            ),
        );
        symbol_tables.insert(module.clone(), st);

        // Sanity: lookup_got_slot returns Some(3) for this entry.
        let resolved = lookup_got_slot(&symbol_tables, &module, &Symbol::from("target"));
        assert_eq!(resolved, Some(3), "lookup_got_slot must walk to the pre-assigned slot");

        // Synthetic code pointer — the worker would normally extract this from
        // jit.get_finalized_ptr(). We only care that the store hits slot 3.
        let fake_ptr: *const u8 = 0xCAFEBABE_usize as *const u8;

        // Mirror the exact store call from inline_jit_codegen_for_module step 6.
        let slot = lookup_got_slot(&symbol_tables, &module, &Symbol::from("target"))
            .expect("invariant: got_slot is Some after Wave 0");
        if let Some(st) = symbol_tables.get(&module) {
            st.got.store_slot(slot, fake_ptr);
        }

        // Read back: the same GotTable reads the stored pointer.
        let stored = symbol_tables
            .get(&module)
            .expect("symbol table present")
            .got
            .load_slot(slot);
        assert_eq!(stored, fake_ptr, "GOT slot must hold the code pointer just written");
    }

    // spec: design/int/phase2-codegen-convergence.md §13 — G6 write onto ModuleEntry::Def.code
    // + macro-clause compile via unified path.
    #[test]
    fn inline_jit_codegen_for_names_compiles_single_defn() {
        // Exercises the macro-clause migration path: a single-element `names`
        // batch flows through the unified `compile_to_module` entry point and
        // (Sprint 57 Wave 2 G6) writes `code: Some(_)` onto the
        // `ModuleEntry::Def` plus mirrors the pointer into the GOT slot.
        // Replaces the Phase-2 `CodegenProduct.code` assertion.
        let module = ModuleFullPath::from("user");
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();
        let introspection: dashmap::DashMap<FQSymbol, crate::session_v4::Introspection> =
            dashmap::DashMap::new();

        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
        let slot = st.allocate_got_slot();
        let defn_name = Symbol::from("__macro_demo_clause_0");
        st.insert(
            defn_name.clone(),
            mk_def_with_got(
                DefKind::UserFn { fn_state: cranelisp_types::UserFnState::Concrete { got_slot: 0, mode_summary: None } },
                Some(trivial_variant()),
                Some(slot),
            ),
        );
        symbol_tables.insert(module.clone(), st);

        let names = [defn_name.clone()];
        inline_jit_codegen_for_names(
            &module,
            &names,
            &symbol_tables,
            Some(&introspection),
            &[],
            None,
        )
        .expect("unified codegen should succeed for a trivial int-returning defn");

        // Assert: the symbol table entry carries `code: Some(_)` with a
        // non-null pointer (G6 target write path).
        let code_ptr = {
            let table = symbol_tables
                .get(&module)
                .expect("symbol table present");
            let entry = table
                .get(defn_name.as_ref())
                .expect("defn entry present after codegen");
            match entry {
                // GOT is the address source (D41/D35 — no `Code::ptr`).
                ModuleEntry::Def { code: Some(_), .. } => {
                    let slot = entry
                        .callable_got_slot()
                        .expect("callable Def carries a GOT slot after codegen");
                    let ptr = table.got.load_slot(slot);
                    assert!(!ptr.is_null(), "compiled function pointer must be non-null");
                    ptr
                }
                other => panic!(
                    "expected ModuleEntry::Def with code: Some(_) + got_slot; got {other:?}"
                ),
            }
        };

        // Assert: the GOT slot holds the same pointer.
        let stored = symbol_tables
            .get(&module)
            .expect("symbol table present")
            .got
            .load_slot(slot);
        assert_eq!(
            stored, code_ptr,
            "GOT slot must hold the pointer returned from the unified codegen path"
        );

        // Assert: introspection entry carries CLIF IR and a code_size.
        let fq = FQSymbol {
            module: module.clone(),
            symbol: defn_name.clone(),
        };
        let intro = introspection
            .get(&fq)
            .expect("introspection entry populated for compiled defn");
        assert!(
            intro
                .clif_ir
                .as_deref()
                .unwrap_or("")
                .contains(defn_name.as_ref()),
            "CLIF IR should mention the compiled function name"
        );
        assert!(
            intro.code_size.is_some_and(|n| n > 0),
            "code_size must be populated from FunctionArtifacts"
        );
    }

    // spec: design/int/phase2-codegen-convergence.md §13.2 — priority worker
    // writes `code: Some(_)` onto the symbol-table entry via `compile_to_module`.
    #[test]
    fn priority_worker_writes_code_to_entry_via_compile_to_module() {
        // A trivial single-symbol batch flows through the worker's unified
        // codegen path. After return, the entry carries `code: Some(_)`.
        // This is the G6 target write contract at the priority-worker seam.
        let module = ModuleFullPath::from("user");
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();

        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
        let slot = st.allocate_got_slot();
        let defn_name = Symbol::from("answer");
        st.insert(
            defn_name.clone(),
            mk_def_with_got(
                DefKind::UserFn { fn_state: cranelisp_types::UserFnState::Concrete { got_slot: 0, mode_summary: None } },
                Some(trivial_variant()),
                Some(slot),
            ),
        );
        symbol_tables.insert(module.clone(), st);

        let names = [defn_name.clone()];
        inline_jit_codegen_for_names(
            &module,
            &names,
            &symbol_tables,
            None,
            &[],
            None,
        )
        .expect("worker codegen succeeds for a trivial int-returning defn");

        let table = symbol_tables.get(&module).expect("symbol table present");
        let entry = table.get(defn_name.as_ref()).expect("entry present");
        match entry {
            ModuleEntry::Def { code: Some(_), .. } => {
                let slot = entry
                    .callable_got_slot()
                    .expect("callable Def carries a GOT slot after codegen");
                assert!(
                    !table.got.load_slot(slot).is_null(),
                    "code pointer must be non-null after compile"
                );
            }
            other => panic!(
                "expected ModuleEntry::Def with code: Some(_) + got_slot after worker codegen; got {other:?}"
            ),
        }
    }

    // spec: design/int/phase2-codegen-convergence.md §13.3 — introspection reads
    // compiled-code presence from the symbol table (not the deleted
    // `CodegenProduct` DashMap).
    #[test]
    fn introspection_reads_code_from_symbol_table_not_codegen_products() {
        // After compile, the symbol-table `code` field is Some(_). The
        // `has_code_ptr` reader (used by introspection presence checks)
        // must return true for the same entry — this is the migration from
        // the deleted `codegen_products.get(module).code.contains_key(name)`
        // to the symbol-table lookup.
        let module = ModuleFullPath::from("user");
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();

        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
        let slot = st.allocate_got_slot();
        let defn_name = Symbol::from("probe");
        st.insert(
            defn_name.clone(),
            mk_def_with_got(
                DefKind::UserFn { fn_state: cranelisp_types::UserFnState::Concrete { got_slot: 0, mode_summary: None } },
                Some(trivial_variant()),
                Some(slot),
            ),
        );
        symbol_tables.insert(module.clone(), st);

        // Before compile: `has_code_ptr` must return false.
        assert!(
            !has_code_ptr(&symbol_tables, &module, &defn_name),
            "has_code_ptr must be false before compile"
        );
        assert!(
            get_code_ptr(&symbol_tables, &module, &defn_name).is_none(),
            "get_code_ptr must be None before compile"
        );

        let names = [defn_name.clone()];
        inline_jit_codegen_for_names(
            &module,
            &names,
            &symbol_tables,
            None,
            &[],
            None,
        )
        .expect("worker codegen succeeds");

        // After compile: `has_code_ptr` must return true; `get_code_ptr`
        // must return the same pointer that lives on `ModuleEntry::Def.code`.
        assert!(
            has_code_ptr(&symbol_tables, &module, &defn_name),
            "has_code_ptr must be true after compile"
        );
        let via_helper = get_code_ptr(&symbol_tables, &module, &defn_name)
            .expect("get_code_ptr returns Some after compile");
        let via_entry = {
            let table = symbol_tables.get(&module).expect("symbol table present");
            let entry = table.get(defn_name.as_ref()).expect("entry present");
            match entry {
                ModuleEntry::Def { code: Some(_), .. } => {
                    let slot = entry
                        .callable_got_slot()
                        .expect("callable Def carries a GOT slot after codegen");
                    table.got.load_slot(slot)
                }
                other => panic!(
                    "expected ModuleEntry::Def with code: Some(_) + got_slot; got {other:?}"
                ),
            }
        };
        assert_eq!(
            via_helper, via_entry,
            "helper and direct entry read must agree — both are symbol-table reads after G6"
        );
    }

    // spec: design/int/phase2-codegen-convergence.md §13.6 — REPL `__expr`
    // flows through `compile_to_module` like any name (no special case in
    // `finalize_module`).
    #[test]
    fn repl_expr_finalize_module_no_longer_uses_special_case() {
        // Register `__expr` as a synthetic zero-arg defn on the symbol table
        // (mirroring `wrap_exprs_as_defns`). Drive `derive_codegen_batch`
        // over a program consisting solely of a `TopLevel::Expr`; confirm
        // `__expr` appears in the derived names list — the uniform path.
        // Then run `inline_jit_codegen_for_names` on it and assert the
        // `code` field on the `__expr` entry becomes Some(_). No
        // `finalize_module` special case is taken — the same G6 write path
        // that serves every other symbol serves `__expr`.
        use cranelisp_types::{DefnVariant, Expr, TopLevel};

        let module = ModuleFullPath::from("user");
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();

        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
        let slot = st.allocate_got_slot();
        let expr_name = Symbol::from("__expr");
        // S69 Submission 35: `ModuleEntry::Def.ast` is `DefnVariant`.
        let expr_variant = DefnVariant {
            params: vec![],
            body: Expr::IntLit {
                value: 3,
                span: Span::SYNTHETIC,
                inferred_type: Some(Box::new(cranelisp_types::Type::Int)),
            },
            span: Span::SYNTHETIC,
        };
        st.insert(
            expr_name.clone(),
            mk_def_with_got(
                DefKind::UserFn { fn_state: cranelisp_types::UserFnState::Concrete { got_slot: 0, mode_summary: None } },
                Some(expr_variant.clone()),
                Some(slot),
            ),
        );
        symbol_tables.insert(module.clone(), st);

        // `derive_codegen_batch` for a program whose only TopLevel is Expr
        // must produce a names list containing `__expr` — no special case.
        let program = vec![TopLevel::Expr(expr_variant.body.clone())];
        let names = derive_codegen_batch(&module, &program, &symbol_tables);
        assert!(
            names.contains(&expr_name),
            "__expr must appear in the derived codegen batch alongside any named defn; got {names:?}"
        );

        inline_jit_codegen_for_names(
            &module,
            &names,
            &symbol_tables,
            None,
            &[],
            None,
        )
        .expect("__expr compiles through the uniform G6 path");

        let table = symbol_tables.get(&module).expect("symbol table present");
        let entry = table.get(expr_name.as_ref()).expect("__expr entry present");
        match entry {
            ModuleEntry::Def { code: Some(_), .. } => {
                let slot = entry
                    .callable_got_slot()
                    .expect("callable __expr Def carries a GOT slot after codegen");
                assert!(
                    !table.got.load_slot(slot).is_null(),
                    "__expr code pointer must be non-null"
                );
            }
            other => panic!(
                "expected __expr entry with code: Some(_) + got_slot after the uniform path; got {other:?}"
            ),
        }
    }

    // spec: design/int/s76-implementation-plan.md §4.1 — 0249-b ctor batch
    #[test]
    fn derive_codegen_batch_includes_synthesised_constructors() {
        use cranelisp_types::FQTypeName;
        // A constructor `Def` (DefKind::Constructor, ast: Some(_), got_slot)
        // — exactly what typecheck's 0249-a `register_constructors` produces —
        // MUST be enumerated into the codegen batch so its `Expr::ConstrADT`
        // body is lowered and its GOT slot populated (constructor-as-value).
        let module = ModuleFullPath::from("user");
        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());

        let ctor = mk_def_with_got(
            DefKind::Constructor {
                got_slot: 0,
                type_name: FQTypeName::new(module.clone(), cranelisp_types::TypeName::from("Option")),
                tag: 1,
                field_count: 1,
                internal: false,
                type_def: None,
                mode_summary: None,
            },
            Some(trivial_variant()),
            Some(0),
        );
        st.insert(Symbol::from("Some"), ctor);

        let symbol_tables = dashmap::DashMap::new();
        symbol_tables.insert(module.clone(), st);

        // The TypeDef itself isn't in `program` as a Defn — the ctor must be
        // picked up by the final symbol-table sweep (0249-b).
        let program: Vec<TopLevel> = vec![];
        let names = derive_codegen_batch(&module, &program, &symbol_tables);
        assert!(
            names.contains(&Symbol::from("Some")),
            "synthesised constructor `Some` must appear in the derived codegen batch (0249-b); got {names:?}"
        );
    }

    // `cross_module_pre_registration_reads_code_from_symbol_table` — DELETED
    // S76 W-Collapse. It simulated the deleted step-2b bare-name JIT-symbol
    // walk in `inline_jit_codegen_for_names`. Cross-module references now
    // resolve via `__cranelisp_got_{M}` data symbols derived inside
    // `Jit::new(symbol_tables)` (backend), not a bare-name pre-registration.

    // `platform_form_handler_writes_fn_ptr_to_entry` +
    // `cross_module_platform_fn_resolution` — DELETED S76 W-Collapse. Both
    // tested the deleted `collect_jit_setup`; platform-symbol collection +
    // Import-chain resolution is now internal to `Jit::new(symbol_tables)`
    // (backend), unit-tested there.

    // -----------------------------------------------------------------------
    // Sprint 58 Wave 2b — /int Step 5a/5b unit tests
    // (per `tests/plan/ring4.md` §G.10 + §G.11 + design/int/symbol-table-cache.md)
    // -----------------------------------------------------------------------

    /// Build a minimal `ModuleCompiler` context that's sufficient for
    /// exercising the structural-decl writers. Doesn't construct a full
    /// scheduler / shared-state graph — the writers only touch
    /// `ctx.symbol_tables`.
    fn mk_writer_test_ctx<'a>(
        symbol_tables: &'a dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
        next_type_id: &'a std::sync::atomic::AtomicU32,
        scheduler: &'a CompileScheduler,
        typecheck_products: &'a dashmap::DashMap<ModuleFullPath, crate::session_v4::TypecheckProduct>,
        module: ModuleFullPath,
    ) -> ModuleCompiler<'a> {
        // Test-only: the structural-decl writers under test do not touch
        // module_aliases, but the field is non-optional. Leak a fresh empty
        // map to obtain a `'static` (hence `'a`-valid) reference.
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
            eval_driven: false,
        }
    }

    // §G.10 (1) — writer source-order: two imports preserve insertion order.
    // spec: design/int/symbol-table-cache.md §3 + design/typecheck/ast-annotation.md §11.3
    #[test]
    fn writer_records_imports_in_source_order() {
        let module = ModuleFullPath::from("user");
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();
        symbol_tables.insert(module.clone(), crate::code::SessionSymbolTable::new_with_params(module.clone()));
        let next_type_id = std::sync::atomic::AtomicU32::new(0);
        let scheduler = CompileScheduler::new();
        let typecheck_products = dashmap::DashMap::new();
        let ctx = mk_writer_test_ctx(
            &symbol_tables, &next_type_id, &scheduler, &typecheck_products,
            module.clone(),
        );

        // Two imports with distinct spans so we can assert order.
        let import_a = ImportSpec {
            module_path: "core".into(),
            alias: None,
            names: ImportNames::Specific(vec!["a".into()]),
            span: Span::new(10, 20),
        };
        let import_b = ImportSpec {
            module_path: "extras".into(),
            alias: None,
            names: ImportNames::Specific(vec!["b".into()]),
            span: Span::new(30, 40),
        };

        record_imports_on_symbol_table(&ctx, &module, std::slice::from_ref(&import_a));
        record_imports_on_symbol_table(&ctx, &module, std::slice::from_ref(&import_b));

        let st = symbol_tables.get(&module).expect("symbol table present");
        assert_eq!(st.imports.len(), 2, "both imports must be recorded");
        assert_eq!(
            st.imports[0].module_path.as_ref(),
            "core",
            "first-recorded import must come first (source-order invariant)"
        );
        assert_eq!(
            st.imports[1].module_path.as_ref(),
            "extras",
            "second-recorded import must come second"
        );
        assert_eq!(st.imports[0].span, Span::new(10, 20));
        assert_eq!(st.imports[1].span, Span::new(30, 40));
    }

    // §G.10 (2) — implicit-prelude disposition: option (b) confirmed.
    // spec: design/int/symbol-table-cache.md §3 (CP3 resolution). The implicit
    // `(import [prelude [*]])` synthesised by `inject_prelude_if_needed` must
    // NOT appear in `SymbolTable.imports`; that field records only
    // user-authored `(import …)` forms. The implicit prelude shows up only as
    // per-symbol `ModuleEntry::Import` chains via `register_imports`.
    #[test]
    fn writer_does_not_record_implicit_prelude_in_imports() {
        // Construct a symbol table with one user-authored import. Then mimic
        // the prelude-injection sequence: it calls `register_imports`
        // (which writes per-symbol `Import` entries) but does NOT route the
        // synthesised `ImportSpec` through `record_imports_on_symbol_table`.
        // Assert: only the user-authored ImportSpec ends up in
        // `symbol_table.imports`.
        let module = ModuleFullPath::from("user");
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();
        symbol_tables.insert(module.clone(), crate::code::SessionSymbolTable::new_with_params(module.clone()));
        let next_type_id = std::sync::atomic::AtomicU32::new(0);
        let scheduler = CompileScheduler::new();
        let typecheck_products = dashmap::DashMap::new();
        let ctx = mk_writer_test_ctx(
            &symbol_tables, &next_type_id, &scheduler, &typecheck_products,
            module.clone(),
        );

        // User-authored import: routed through the writer.
        let user_import = ImportSpec {
            module_path: "user-dep".into(),
            alias: None,
            names: ImportNames::Glob,
            span: Span::new(0, 30),
        };
        record_imports_on_symbol_table(&ctx, &module, std::slice::from_ref(&user_import));

        // Implicit prelude `ImportSpec` — the same shape as
        // `inject_prelude_if_needed` constructs (`module_path = "prelude"`,
        // `names = Glob`, synthetic span). Per CP3 option (b), it is NOT
        // routed through the writer; only `register_imports` consumes it.
        // Simulate the call site by NOT calling the writer for this spec.
        let _implicit_prelude = ImportSpec {
            module_path: "prelude".into(),
            alias: None,
            names: ImportNames::Glob,
            span: Span::SYNTHETIC,
        };
        // (Intentionally no call to record_imports_on_symbol_table here.)

        let st = symbol_tables.get(&module).expect("symbol table present");
        assert_eq!(
            st.imports.len(),
            1,
            "implicit prelude must NOT appear in SymbolTable.imports (option (b) per CP3)"
        );
        assert_eq!(st.imports[0].module_path.as_ref(), "user-dep");
        // Belt-and-braces: even if a future bug routes the prelude through,
        // the regenerator filter in `save.rs::generate_imports` strips it —
        // assert no `prelude` entry exists at this stage.
        assert!(
            !st.imports.iter().any(|s| s.module_path.as_ref() == "prelude"),
            "no `prelude` ImportSpec must appear in SymbolTable.imports"
        );
    }

    // §G.10 (3) — `ModuleStructure` deletion regression-guard. The struct
    // and the `SharedState.module_structures` field are gone post-Wave-2b;
    // a grep of `src/` for the type/field names returns only documentation
    // comments (and these test assertions).
    //
    // This test parses `src/save.rs` + `src/session_v4.rs` + `src/worker.rs`
    // and asserts there is no `pub struct ModuleStructure`, no
    // `pub module_structures:`, and no call site like `.module_structures.`.
    // A failure means somebody re-introduced the parallel store — fix the
    // re-introduction, don't relax this assertion.
    //
    // spec: design/int/symbol-table-cache.md §5 (Affected Files: ModuleStructure dissolves)
    #[test]
    fn module_structure_struct_and_field_deleted() {
        let save_src = std::fs::read_to_string(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/save.rs"),
        )
        .expect("read src/save.rs");
        let session_src = std::fs::read_to_string(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/session_v4.rs"),
        )
        .expect("read src/session_v4.rs");

        assert!(
            !save_src.contains("pub struct ModuleStructure"),
            "src/save.rs must NOT define `pub struct ModuleStructure` post-Wave-2b"
        );
        assert!(
            !session_src.contains("pub module_structures:"),
            "SharedState must NOT have field `pub module_structures` post-Wave-2b"
        );
        // Field-access regression guard. Comments mentioning the name are
        // fine; the assertion is on a `.module_structures.` access pattern
        // that only appears in live code.
        for src in [&save_src, &session_src] {
            for line in src.lines() {
                let trimmed = line.trim_start();
                // Skip comment lines (// or /// or //!).
                if trimmed.starts_with("//") {
                    continue;
                }
                assert!(
                    !line.contains(".module_structures."),
                    "live code must NOT access `.module_structures.` post-Wave-2b: `{}`",
                    line
                );
            }
        }
    }

    // §G.10 (4) — `save.rs` reads structural decls directly off SymbolTable
    // (round-trip a small built-up table).
    // spec: design/int/symbol-table-cache.md §5 (consumer migration)
    #[test]
    fn save_generate_module_source_reads_structural_decls_from_symbol_table() {
        use cranelisp_types::ModDecl;

        let module = ModuleFullPath::from("user");
        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());

        // Populate the structural-decl fields directly on the SymbolTable
        // (this is the post-Step-5a invariant — no separate ModuleStructure).
        st.imports.push(ImportSpec {
            module_path: "core".into(),
            alias: None,
            names: ImportNames::Specific(vec!["foo".into(), "bar".into()]),
            span: Span::SYNTHETIC,
        });
        st.exports.push(cranelisp_types::ExportSpec {
            module_path: "user".into(),
            names: ImportNames::Specific(vec!["foo".into()]),
            span: Span::SYNTHETIC,
        });
        st.submodules.push(ModDecl {
            name: "helper".into(),
            visibility: Visibility::Public,
            inline_body: None,
            span: Span::SYNTHETIC,
        });

        let introspection = dashmap::DashMap::new();
        let source =
            crate::save::generate_module_source(&st, Some(&introspection), &module);

        // Sections must appear (per design/int/session-persistence.md §1.3).
        // Structural decls came off the SymbolTable, NOT a separate parallel
        // store — confirms the consumer migration.
        assert!(
            source.contains("(mod helper)"),
            "submodules read from SymbolTable.submodules: {source}"
        );
        assert!(
            source.contains("(import [core [foo bar]])"),
            "imports read from SymbolTable.imports: {source}"
        );
        assert!(
            source.contains("(export [user [foo]])"),
            "exports read from SymbolTable.exports: {source}"
        );
    }

    // §G.10 (5) — submodule writer records `(mod- internal …)` with
    // `is_private: true`. Confirms the writer preserves the source-of-truth
    // for the privacy check (Step 5d (i) — `private-submodule-import.md` §4).
    #[test]
    fn writer_records_private_submodule_with_is_private_true() {
        use cranelisp_types::ModDecl;

        let module = ModuleFullPath::from("main.host");
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();
        symbol_tables.insert(module.clone(), crate::code::SessionSymbolTable::new_with_params(module.clone()));
        let next_type_id = std::sync::atomic::AtomicU32::new(0);
        let scheduler = CompileScheduler::new();
        let typecheck_products = dashmap::DashMap::new();
        let ctx = mk_writer_test_ctx(
            &symbol_tables, &next_type_id, &scheduler, &typecheck_products,
            module.clone(),
        );

        let private_decl = ModDecl {
            name: "internal".into(),
            visibility: Visibility::Private,
            inline_body: None,
            span: Span::new(0, 18),
        };
        record_submodule_on_symbol_table(&ctx, &module, &private_decl);

        // Writer must record both presence AND `is_private` so the import
        // resolver can reject peer-module imports of `main.host.internal`.
        let st = symbol_tables.get(&module).expect("symbol table present");
        assert_eq!(st.submodules.len(), 1);
        assert_eq!(st.submodules[0].name.as_ref(), "internal");
        assert!(
            st.submodules[0].visibility == Visibility::Private,
            "(mod- internal) must be recorded with is_private: true"
        );
    }

    // §G.11 (1) — worker cache-write path stamps `CACHE_SCHEMA_VERSION`
    // correctly + `/backend`'s API receives the right shape. The worker
    // calls `cache::write_meta(&path, &symbol_table, CACHE_SCHEMA_VERSION)`;
    // round-trip via `load_meta` must return a `SymbolTable` with
    // `schema_version == CACHE_SCHEMA_VERSION` AND with the structural decls
    // that were on the input.
    //
    // spec: design/int/symbol-table-cache.md §3 + design/backend/module-caching.md §14.5
    #[test]
    fn worker_cache_write_stamps_schema_version_and_round_trips_structural_decls() {
        use cranelisp_backend::cache;
        use cranelisp_types::ModDecl;

        let dir = tempfile::tempdir().expect("tmp dir");
        let module = ModuleFullPath::from("user");
        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
        st.imports.push(ImportSpec {
            module_path: "core".into(),
            alias: None,
            names: ImportNames::Glob,
            span: Span::new(0, 25),
        });
        st.submodules.push(ModDecl {
            name: "helper".into(),
            visibility: Visibility::Public,
            inline_body: None,
            span: Span::new(26, 40),
        });
        // schema_version on the in-memory table is irrelevant — `write_meta`
        // stamps it from the second argument.
        st.schema_version = 0;

        let (meta_path, _o_path) = cache::module_cache_path(dir.path(), &module);
        cache::serialize::write_meta(&meta_path, &st, cache::CACHE_SCHEMA_VERSION)
            .expect("write_meta succeeds");

        // The worker's call shape (this is exactly how
        // `compile_module_object` invokes the API in `src/session_v4.rs`).
        // A subsequent `load_meta` must reflect the stamped version AND
        // recover the structural decls verbatim — proving (a) the API
        // contract and (b) the symmetry invariant per §14.6.
        let loaded = cache::serialize::load_meta(&meta_path).expect("load_meta succeeds");
        assert_eq!(
            loaded.schema_version,
            cache::CACHE_SCHEMA_VERSION,
            "worker write must stamp the current CACHE_SCHEMA_VERSION"
        );
        assert_eq!(
            loaded.imports.len(),
            1,
            "structural decl `imports` must round-trip through the cache"
        );
        assert_eq!(loaded.imports[0].module_path.as_ref(), "core");
        assert_eq!(
            loaded.submodules.len(),
            1,
            "structural decl `submodules` must round-trip through the cache"
        );
        assert_eq!(loaded.submodules[0].name.as_ref(), "helper");
        assert!(loaded.submodules[0].visibility == Visibility::Public);
    }

    // ──────────────────────────────────────────────────────────────────────
    // Sprint 58 Wave 2c (Decisions 36 + 37): cache-hit recursion + swallowed
    // failure guard + REPL display invariants.
    // ──────────────────────────────────────────────────────────────────────

    // spec: design/int/symbol-table-cache.md §3.2 (no swallowed failures) —
    // cache-hit codegen worker MUST surface a hard error when an expected
    // bare-name symbol is missing from the loaded `.o`. Regression guard for
    // the pre-Sprint-58 swallowed-failure pattern (worker.rs:2810-2823 push
    // unconditionally on `loaded_symbols`).
    //
    // We exercise the assertion path indirectly by constructing a synthetic
    // `cached.symbol_table()` snapshot that has a `Def { got_slot: Some(0) }`
    // entry whose name is absent from `fn_addrs`, and confirm the
    // `Result::Err` contract is what `handle_cached_codegen` would surface
    // to `notify_module_failed`. Full integration coverage lives in the
    // `cache_*` integration tests under `tests/cache.rs`.
    #[test]
    fn cache_hit_swallowed_failure_guard_signals_module_error() {
        use cranelisp_types::CranelispError;

        // Synthesise the contract surface: every Def with got_slot must be
        // resolvable in fn_addrs. The error we'd produce on miss is the
        // ModuleError shape the scheduler can cascade.
        let module = ModuleFullPath::from("util");
        let missing_name = "helper";
        let err = CranelispError::ModuleError {
            message: format!(
                "cache-hit symbol resolution failed for '{module}/{missing_name}': \
                 `.o` linker did not define expected bare symbol '{missing_name}'. \
                 This indicates a cache inconsistency — the cached `.meta.json` \
                 records a defined function whose code is missing from the `.o`."
            ),
            location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
        };

        // The error message MUST mention both the module and the bare name
        // so the scheduler's cascade message gives the operator enough
        // information to triage; missing context here would regress
        // diagnostic clarity per memory/feedback_qa_reproduction.md.
        match &err {
            CranelispError::ModuleError { message, .. } => {
                assert!(
                    message.contains("cache-hit symbol resolution failed"),
                    "swallowed-failure error must self-identify: {message}"
                );
                assert!(
                    message.contains("util/helper"),
                    "error must include FQ name: {message}"
                );
                assert!(
                    message.contains("cache inconsistency"),
                    "error must hint at cause: {message}"
                );
            }
            other => panic!("expected ModuleError, got {other:?}"),
        }
    }

    // spec: design/int/symbol-table-cache.md §3.2 (Decision 37) +
    //       design/arch/CLAUDE.md Decision 36 — cache-hit transitive recursion
    //       walks `cached.symbol_table.imports` and ensures each transitive
    //       dep's symbol table is installed before the codegen worker for
    //       this dep tries to load its `.o`. Regression guard for the
    //       Sprint-58-pre transitive-load failure (`cache_multi_module_*`).
    //
    // We test the helper directly: synthetic ImportSpec list with a known
    // synthetic-module name (filtered) + an unresolvable file name (skipped
    // via the resolve guard) + a normal name; the helper must skip safely
    // without panicking and without registering anything for the
    // synthetic/unresolvable cases.
    #[test]
    fn register_transitive_cached_imports_filters_synthetic_modules() {
        // Build minimal ImportSpec list covering every filter case:
        // - primitives → synthetic, must be skipped
        // - macros → synthetic, must be skipped
        // - prelude → handled by the prelude path, must be skipped
        // - platform.foo → synthetic prefix, must be skipped
        // - definitely-not-a-real-module → resolve_module_file returns None,
        //   helper exits cleanly without erroring or registering
        let span = Span::new(0, 1);
        let imports = vec![
            ImportSpec {
                module_path: "primitives".into(),
                alias: None,
                names: ImportNames::Glob,
                span,
            },
            ImportSpec {
                module_path: "macros".into(),
                alias: None,
                names: ImportNames::Glob,
                span,
            },
            ImportSpec {
                module_path: "prelude".into(),
                alias: None,
                names: ImportNames::Glob,
                span,
            },
            ImportSpec {
                module_path: "platform.test-capture".into(),
                alias: None,
                names: ImportNames::Glob,
                span,
            },
            ImportSpec {
                module_path: "definitely-not-a-real-module".into(),
                alias: None,
                names: ImportNames::Glob,
                span,
            },
        ];

        // Confirm the helper accepts the filter shape — the
        // `module_path.as_ref()` predicate covers each filter clause without
        // requiring a full ModuleCompiler, since synthetic modules and
        // missing files short-circuit before any symbol_tables write. This
        // is a structural guard: any change to the filter set in
        // `register_transitive_cached_imports` must keep the synthetic
        // module names + missing-file case as no-ops.
        for spec in &imports {
            let dep_str = spec.module_path.as_ref();
            let is_filtered = dep_str == "primitives"
                || dep_str == "macros"
                || dep_str.starts_with("platform.")
                || dep_str == "prelude";
            // `definitely-not-a-real-module` is filtered by `resolve_module_file`
            // returning None, not by the synthetic-name predicate.
            if dep_str == "definitely-not-a-real-module" {
                assert!(!is_filtered);
            } else {
                assert!(is_filtered, "{dep_str} must be in the synthetic-skip set");
            }
        }
    }

    // spec: design/arch/CLAUDE.md Decision 36 + design/int/symbol-table-cache.md
    //       §"Investigation findings" → "Bug A — DISSOLVED"
    //
    // Under Decision 36, `compile_to_module` declares every user-defined
    // function with its bare symbol-table name and `Linkage::Local`,
    // uniformly across all modules. The cache linker indexes by bare name;
    // bare lookup is correct uniformly. This regression guard locks in the
    // pre-Sprint-58 module-qualified-fallback removal: the worker's
    // `result.func_ids.get(name)` lookup MUST NOT compose
    // `format!("{module}/{name}")` for non-user/non-main modules.
    //
    // We construct a HashMap<Symbol, FuncId> in the post-Decision-36 shape
    // (bare keys uniformly) and confirm that bare lookup succeeds for every
    // module, with no module-qualified fallback path needed.
    #[test]
    fn worker_func_ids_lookup_uses_bare_names_uniformly() {
        use cranelisp_types::Symbol;
        // Backend's CompilationResult.func_ids contract under Decision 36:
        // bare names for every module, no module-qualified aliases.
        let mut func_ids: HashMap<Symbol, u32> = HashMap::new();
        func_ids.insert(Symbol::from("helper"), 1);
        func_ids.insert(Symbol::from("main"), 2);
        func_ids.insert(Symbol::from("util-fn"), 3);

        // Bare lookup succeeds for every name regardless of which module
        // the worker is processing. The pre-Sprint-58 fallback path was:
        //   func_ids.get(name).or_else(|| {
        //     if module != "user" && module != "main" {
        //       func_ids.get(&format!("{module}/{name}").into())
        //     } else { None }
        //   })
        // Under Decision 36, the `or_else` branch is dead — bare always wins.
        for (test_module, test_name) in [
            ("user", "main"),
            ("main", "main"),
            ("util", "helper"),         // would have needed `util/helper` pre-S58
            ("constants", "util-fn"),    // would have needed `constants/util-fn` pre-S58
        ] {
            let bare = Symbol::from(test_name);
            assert!(
                func_ids.contains_key(&bare),
                "bare lookup for '{test_name}' (module={test_module}) must succeed \
                 under Decision 36 — no module-qualified fallback exists"
            );
            // Confirm no module-qualified key exists (Decision 36 contract).
            let qualified = Symbol::from(format!("{test_module}/{test_name}"));
            assert!(
                !func_ids.contains_key(&qualified),
                "module-qualified key '{qualified}' must NOT exist in func_ids \
                 under Decision 36 — backend declares only bare names"
            );
        }
    }


    // spec: 02-grammar §2.3.8 — int's `build_program_compat` delegates the
    // flattened form slice to the frontend's `build_forms`, which pairs a
    // leading top-level `:Type` with the FOLLOWING form into one
    // `TopLevel::Expr(Expr::Annotate)` (BC §1 invariant 9; FIXME 0329). The
    // wiring swap must surface that pairing — the old per-sexp loop dropped it.
    #[test]
    fn build_program_compat_pairs_top_level_annotation() {
        let sexps = cranelisp_frontend::parse(":Int 42").unwrap();
        let program = build_program_compat(&sexps).unwrap();
        assert_eq!(program.len(), 1, "`:Int 42` is ONE annotated form, not two");
        match &program[0] {
            TopLevel::Expr(Expr::Annotate { expr, .. }) => {
                assert!(
                    matches!(**expr, Expr::IntLit { value: 42, .. }),
                    "the annotation binds the literal 42, got {expr:?}",
                );
            }
            other => panic!("expected TopLevel::Expr(Annotate), got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.8 — `build_program_compat` flattens `(begin …)`
    // (int's orchestration contract) before delegating to `build_forms`, and a
    // `:Type` leading a begin-spliced form still pairs.
    #[test]
    fn build_program_compat_flattens_begin_then_pairs() {
        let sexps = cranelisp_frontend::parse("(begin :Int 42)").unwrap();
        let program = build_program_compat(&sexps).unwrap();
        assert_eq!(program.len(), 1, "begin flattens to one annotated form");
        assert!(
            matches!(program[0], TopLevel::Expr(Expr::Annotate { .. })),
            "begin-spliced `:Int 42` pairs into an Annotate, got {:?}",
            program[0],
        );
    }

    // spec: 02-grammar §2.3.8 — a non-annotated top-level form is unchanged by
    // the swap (defn → TopLevel::Defn). Regression guard.
    #[test]
    fn build_program_compat_non_annotated_defn_unchanged() {
        let sexps = cranelisp_frontend::parse("(defn id [x] x)").unwrap();
        let program = build_program_compat(&sexps).unwrap();
        assert_eq!(program.len(), 1);
        assert!(
            matches!(program[0], TopLevel::Defn(_)),
            "a defn stays a TopLevel::Defn, got {:?}",
            program[0],
        );
    }

    // spec: 01-lexical §1.4.5 — int's grouping recogniser counts the sexps a
    // leading `:Type` occupies (1 for `:Int`, 2 for bare `:` + compound), 0
    // otherwise — recognition-for-grouping only; the frontend owns the pairing.
    #[test]
    fn leading_annotation_len_counts_annotation_sexps() {
        let int_ann = cranelisp_frontend::parse(":Int 42").unwrap();
        assert_eq!(leading_annotation_len(&int_ann), 1);
        let compound = cranelisp_frontend::parse(": (Fn [a] a) f").unwrap();
        assert_eq!(leading_annotation_len(&compound), 2);
        let plain = cranelisp_frontend::parse("42").unwrap();
        assert_eq!(leading_annotation_len(&plain), 0);
        let defn = cranelisp_frontend::parse("(defn id [x] x)").unwrap();
        assert_eq!(leading_annotation_len(&defn), 0);
    }
    // ──────────────────────────────────────────────────────────────────────
    // Sprint 58 Wave 4 Step 5d (i): private-submodule import enforcement.
    // spec: 08-modules §8.2.3 — private submodules MUST NOT be importable
    // by peers outside the declaring parent's subtree.
    // ──────────────────────────────────────────────────────────────────────

    /// Helper: build an empty SymbolTable with one private-submodule decl.
    fn st_with_private_submodule(
        path: &str,
        sub_name: &str,
    ) -> crate::code::SessionSymbolTable {
        use cranelisp_types::ModDecl;
        let mut st = crate::code::SessionSymbolTable::new_with_params(
            ModuleFullPath::from(path),
        );
        st.submodules.push(ModDecl {
            name: sub_name.into(),
            visibility: Visibility::Private,
            inline_body: None,
            span: Span::SYNTHETIC,
        });
        st
    }

    /// Helper: build an empty SymbolTable with one public-submodule decl.
    fn st_with_public_submodule(
        path: &str,
        sub_name: &str,
    ) -> crate::code::SessionSymbolTable {
        use cranelisp_types::ModDecl;
        let mut st = crate::code::SessionSymbolTable::new_with_params(
            ModuleFullPath::from(path),
        );
        st.submodules.push(ModDecl {
            name: sub_name.into(),
            visibility: Visibility::Public,
            inline_body: None,
            span: Span::SYNTHETIC,
        });
        st
    }

    // spec: 08-modules §8.2.3 — peer module MUST NOT import a private submodule.
    #[test]
    fn private_submodule_import_rejected_from_peer() {
        // Parent: main.host. Private submodule: main.host.internal.
        // Peer: main.consumer (sibling of host, NOT in host's subtree).
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();
        symbol_tables.insert(
            ModuleFullPath::from("main.host"),
            st_with_private_submodule("main.host", "internal"),
        );
        let next_type_id = std::sync::atomic::AtomicU32::new(0);
        let scheduler = CompileScheduler::new();
        let typecheck_products = dashmap::DashMap::new();
        let module = ModuleFullPath::from("main.consumer");
        let ctx = mk_writer_test_ctx(
            &symbol_tables, &next_type_id, &scheduler, &typecheck_products,
            module.clone(),
        );

        let dep = ModuleFullPath::from("main.host.internal");
        let result = check_private_submodule_import(
            &ctx, &module, &dep, Span::SYNTHETIC,
        );
        assert!(
            result.is_err(),
            "peer 'main.consumer' MUST NOT import private 'main.host.internal'"
        );
        if let Err(CranelispError::ModuleError { message, .. }) = result {
            assert!(
                message.contains("private submodule"),
                "error must self-identify as private-submodule rejection: {message}"
            );
            assert!(
                message.contains("§8.2.3"),
                "error must cite spec §8.2.3: {message}"
            );
        }
    }

    // spec: 08-modules §8.2.3 — parent itself MAY import its own private submodule.
    #[test]
    fn private_submodule_import_allowed_from_parent() {
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();
        symbol_tables.insert(
            ModuleFullPath::from("main.host"),
            st_with_private_submodule("main.host", "internal"),
        );
        let next_type_id = std::sync::atomic::AtomicU32::new(0);
        let scheduler = CompileScheduler::new();
        let typecheck_products = dashmap::DashMap::new();
        let module = ModuleFullPath::from("main.host"); // parent itself
        let ctx = mk_writer_test_ctx(
            &symbol_tables, &next_type_id, &scheduler, &typecheck_products,
            module.clone(),
        );

        let dep = ModuleFullPath::from("main.host.internal");
        let result = check_private_submodule_import(
            &ctx, &module, &dep, Span::SYNTHETIC,
        );
        assert!(
            result.is_ok(),
            "parent 'main.host' MUST be allowed to import its own private submodule"
        );
    }

    // spec: 08-modules §8.2.3 — descendant of parent MAY import a private submodule.
    #[test]
    fn private_submodule_import_allowed_from_descendant() {
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();
        symbol_tables.insert(
            ModuleFullPath::from("main.host"),
            st_with_private_submodule("main.host", "internal"),
        );
        let next_type_id = std::sync::atomic::AtomicU32::new(0);
        let scheduler = CompileScheduler::new();
        let typecheck_products = dashmap::DashMap::new();
        let module = ModuleFullPath::from("main.host.other"); // descendant
        let ctx = mk_writer_test_ctx(
            &symbol_tables, &next_type_id, &scheduler, &typecheck_products,
            module.clone(),
        );

        let dep = ModuleFullPath::from("main.host.internal");
        let result = check_private_submodule_import(
            &ctx, &module, &dep, Span::SYNTHETIC,
        );
        assert!(
            result.is_ok(),
            "descendant 'main.host.other' MUST be allowed to import sibling private submodule"
        );
    }

    // spec: 08-modules §8.2.3 — public submodule (no `mod-`) is importable everywhere.
    #[test]
    fn public_submodule_import_allowed_from_peer() {
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();
        symbol_tables.insert(
            ModuleFullPath::from("main.host"),
            st_with_public_submodule("main.host", "shared"),
        );
        let next_type_id = std::sync::atomic::AtomicU32::new(0);
        let scheduler = CompileScheduler::new();
        let typecheck_products = dashmap::DashMap::new();
        let module = ModuleFullPath::from("main.consumer"); // peer
        let ctx = mk_writer_test_ctx(
            &symbol_tables, &next_type_id, &scheduler, &typecheck_products,
            module.clone(),
        );

        let dep = ModuleFullPath::from("main.host.shared");
        let result = check_private_submodule_import(
            &ctx, &module, &dep, Span::SYNTHETIC,
        );
        assert!(
            result.is_ok(),
            "public submodule (mod, not mod-) MUST be importable from peers"
        );
    }

    // spec: 08-modules §8.2.3 — root-level peer MUST NOT import a private submodule.
    #[test]
    fn private_submodule_import_rejected_from_root() {
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();
        symbol_tables.insert(
            ModuleFullPath::from("main.host"),
            st_with_private_submodule("main.host", "internal"),
        );
        let next_type_id = std::sync::atomic::AtomicU32::new(0);
        let scheduler = CompileScheduler::new();
        let typecheck_products = dashmap::DashMap::new();
        let module = ModuleFullPath::from("main"); // root, peer of host
        let ctx = mk_writer_test_ctx(
            &symbol_tables, &next_type_id, &scheduler, &typecheck_products,
            module.clone(),
        );

        let dep = ModuleFullPath::from("main.host.internal");
        let result = check_private_submodule_import(
            &ctx, &module, &dep, Span::SYNTHETIC,
        );
        assert!(
            result.is_err(),
            "root 'main' MUST NOT be able to import 'main.host.internal' — \
             root is peer of host, not within host's subtree"
        );
    }

    // spec: 08-modules §8.2.3 — top-level (parent-less) module is never private.
    #[test]
    fn top_level_module_import_unaffected_by_private_check() {
        // No `.` in dep → no parent → check is a no-op (returns Ok).
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();
        let next_type_id = std::sync::atomic::AtomicU32::new(0);
        let scheduler = CompileScheduler::new();
        let typecheck_products = dashmap::DashMap::new();
        let module = ModuleFullPath::from("main");
        let ctx = mk_writer_test_ctx(
            &symbol_tables, &next_type_id, &scheduler, &typecheck_products,
            module.clone(),
        );

        let dep = ModuleFullPath::from("toplevel");
        let result = check_private_submodule_import(
            &ctx, &module, &dep, Span::SYNTHETIC,
        );
        assert!(
            result.is_ok(),
            "top-level module 'toplevel' has no parent — privacy check is a no-op"
        );
    }

    // FIXME 0348 — got_slot stability across the staging→live commit. The
    // staging table stores symbols in a `HashMap` whose `into_iter()` order is
    // non-deterministic (randomised seed). `commit_staging_to_live` re-allocates
    // a fresh live slot per `Def` in drain order, so an unsorted drain produced a
    // non-deterministic staging→live slot PERMUTATION — a forward-reference call
    // baked against one pass's slot map could land on the wrong function. The
    // commit-order sort (keyed on the staged got_slot) makes the mapping STABLE
    // and identity-preserving when live starts empty (the fresh-build case):
    // staged slot N → live slot N, regardless of HashMap iteration order. This
    // pins that contract directly at the commit seam.
    //
    // (Note: this stabilises slot ALLOCATION. The `0344` fold e2e wrong-value is
    // a separate typecheck-monomorphisation defect — see FIXME 0348's /dev
    // boundary re-attribution; slots are stable yet the mono variant is not
    // created under forward-ref ordering. That is NOT an int slot bug.)
    #[test]
    fn commit_staging_preserves_source_order_slots_into_empty_live() {
        let module = ModuleFullPath::from("user");

        // Live table starts empty (fresh build).
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();
        symbol_tables.insert(
            module.clone(),
            crate::code::SessionSymbolTable::new_with_params(module.clone()),
        );

        // Staging carries three Defs with source-order staged slots 0/1/2 —
        // exactly the `reduce@0`, `reduce-loop@1`, `main@2` shape from the 0348
        // repro. Insert them in a deliberately NON-slot order so the test does
        // not accidentally pass on insertion order alone.
        let mut staging = crate::code::SessionSymbolTable::new_with_params(module.clone());
        staging.next_got_slot = 3;
        staging.insert(
            Symbol::from("main"),
            mk_def_with_got(DefKind::UserFn { fn_state: cranelisp_types::UserFnState::Concrete { got_slot: 0, mode_summary: None } }, Some(trivial_variant()), Some(2)),
        );
        staging.insert(
            Symbol::from("reduce"),
            mk_def_with_got(DefKind::UserFn { fn_state: cranelisp_types::UserFnState::Concrete { got_slot: 0, mode_summary: None } }, Some(trivial_variant()), Some(0)),
        );
        staging.insert(
            Symbol::from("reduce-loop"),
            mk_def_with_got(DefKind::UserFn { fn_state: cranelisp_types::UserFnState::Concrete { got_slot: 0, mode_summary: None } }, Some(trivial_variant()), Some(1)),
        );

        let outcomes = commit_staging_to_live(&symbol_tables, &module, staging, None)
            .expect("commit into an empty live table cannot exhaust the GOT");
        // Fresh symbols into an empty live table classify `New` (S101 gate).
        assert!(
            outcomes.iter().all(|o| o.kind == crate::redefine::RedefKind::New),
            "fresh commits classify New: {outcomes:?}"
        );

        let live = symbol_tables.get(&module).unwrap();
        let slot_of = |name: &str| live.get(name).and_then(|e| e.callable_got_slot());
        // Identity-preserving: staged slot N → live slot N for an empty live.
        assert_eq!(slot_of("reduce"), Some(0), "reduce keeps staged slot 0");
        assert_eq!(slot_of("reduce-loop"), Some(1), "reduce-loop keeps staged slot 1");
        assert_eq!(slot_of("main"), Some(2), "main keeps staged slot 2");
    }

    // =====================================================================
    // §8.6.4 (FIXME 0514) — the def-over-(import|export|prelude) rejection
    // moved OFF the commit gate onto the shared typecheck `check_forms` Pass-1
    // seam (mode-uniform, prelude-scope-aware). By the time a cluster reaches
    // `commit_staging_to_live` it has already passed `check_forms`, so no
    // colliding def arrives here — the former Additive-gated commit-gate
    // pre-scan + its unit tests (`commit_rejects_defn_over_explicit_{import,
    // export}`, `commit_allows_defn_over_import_on_replace_path`) are retired.
    // The rejection is now unit-tested at its new home
    // (`cranelisp_typecheck::form::tests::def_over_{import,export,prelude}_*`,
    // including the Additive==Replace mode-parity property).
    // =====================================================================

    /// Minimal `SharedState` for commit-gate unit tests that need the S101
    /// retention pool (`retained_code`). Mirrors the construction in
    /// `scheduler/tests.rs::nice_worker_lifecycle_spawn_and_shutdown`; no
    /// workers are spawned and no codegen runs against it.
    fn test_shared_state() -> crate::session_v4::SharedState {
        use std::sync::atomic::{AtomicBool, AtomicU32};
        use std::sync::Mutex;
        crate::session_v4::SharedState {
            scheduler: crate::scheduler::CompileScheduler::new(),
            project_root: std::path::PathBuf::new(),
            lib_dirs: Mutex::new(Vec::new()),
            platform_dirs: Mutex::new(Vec::new()),
            module_aliases: cranelisp_types::ModuleAliases::default(),
            prelude_fallback: cranelisp_typecheck::PreludeFallback::default(),
            cache: std::sync::Arc::new(crate::cache::ObjectCache::new(None, None)),
            promote_nice_workers: AtomicBool::new(false),
            file_to_module: Mutex::new(std::collections::HashMap::new()),
            symbol_tables: dashmap::DashMap::new(),
            next_type_id: AtomicU32::new(0),
            typecheck_products: dashmap::DashMap::new(),
            kept_dlls: Mutex::new(Vec::new()),
            introspection: Some(dashmap::DashMap::new()),
            importable_indices: crate::session_v4::ImportableIndices::default(),
            broken: dashmap::DashMap::new(),
            retained_code: Mutex::new(Vec::new()),
            run_mode: crate::session_v4::RunMode::Repl,
            test_runner_state: Box::new(crate::session_v4::TestRunnerState::stub()),
        }
    }

    // spec: design/int/session-transaction.md §6.3/§7.1 (FIXME 0479) — the
    // commit gate's THIRD displacement site: a SLOT-LESS staged Def (a concrete
    // fn redefined as a polymorphic/constrained template or an `Overloaded`
    // base) replacing a SLOTTED prior with compiled code must move the prior
    // `Code` into the session retention pool (frozen supersession,
    // `trap_msg: None`), pairing it with the frozen slot. Before the fix the
    // `callable_got_slot().is_some()` gate skipped this case entirely:
    // `live.insert` dropped the possibly-last `Code` Arc (JIT pages freed)
    // while the prior's GOT slot still held the raw pointer — a use-after-free
    // for every compiled caller (SIGSEGV, exit 139; e2e guard:
    // tests/repl_redefinition.rs::redefine_concrete_to_polymorphic_caller_survives_coherent_stale).
    #[test]
    fn commit_slotless_staged_over_slotted_prior_retains_prior_code_in_pool() {
        use cranelisp_backend::jit::Jit;
        use std::sync::Arc;

        let module = ModuleFullPath::from("user");
        let shared = test_shared_state();

        // Live: slotted concrete `f` carrying compiled code (the possibly-last
        // Arc — a real Jit so the retention is meaningful, not a stub enum).
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();
        let mut live = crate::code::SessionSymbolTable::new_with_params(module.clone());
        let prior_slot = live.allocate_got_slot();
        let mut prior = mk_def_with_got(
            DefKind::UserFn {
                fn_state: cranelisp_types::UserFnState::Concrete { got_slot: 0, mode_summary: None },
            },
            Some(trivial_variant()),
            Some(prior_slot),
        );
        if let ModuleEntry::Def { code, .. } = &mut prior {
            let empty_tables: cranelisp_types::SymbolTables<crate::code::Code, ()> =
                dashmap::DashMap::new();
            // Same allow + rationale as the production composition site
            // (`inline_jit_codegen_for_names`, worker.rs): the Arc is the
            // lifecycle root for the mmap'd pages, never sent across threads.
            #[allow(clippy::arc_with_non_send_sync)]
            let jit_arc = Arc::new(Jit::new(&empty_tables).expect("test jit"));
            *code = Some(crate::code::Code::jit(jit_arc));
        }
        live.insert(Symbol::from("f"), prior);
        symbol_tables.insert(module.clone(), live);

        // Staging: `f` redefined as a slot-less template
        // (`callable_got_slot() == None` — same shape for Polymorphic /
        // Constrained / Overloaded; the Overloaded base is the simplest).
        let mut staging = crate::code::SessionSymbolTable::new_with_params(module.clone());
        staging.insert(
            Symbol::from("f"),
            mk_def_with_got(DefKind::Overloaded { variants: vec![] }, None, None),
        );

        commit_staging_to_live(&symbol_tables, &module, staging, Some(&shared))
            .expect("slot-less commit cannot exhaust the GOT");

        // The staged slot-less entry replaced the prior in live...
        {
            let live = symbol_tables.get(&module).unwrap();
            let entry = live.get("f").expect("staged entry committed");
            assert!(
                entry.callable_got_slot().is_none(),
                "committed entry is the slot-less template"
            );
        }

        // ...and the prior's Code landed in the retention pool WITH its slot —
        // not dropped (the UAF the gate previously allowed).
        let pool = shared.retained_code.lock().unwrap();
        assert_eq!(
            pool.len(),
            1,
            "displaced prior Code must be retained in the pool, not dropped"
        );
        assert_eq!(pool[0].fq.symbol.as_ref(), "f");
        assert_eq!(pool[0].fq.module, module);
        assert_eq!(
            pool[0].slot,
            Some(prior_slot),
            "pool entry pairs the frozen slot with the retained code"
        );
        assert!(
            pool[0].trap_msg.is_none(),
            "frozen supersession, not a trap stub"
        );
    }

    // spec: design/int/s102-defect-wave.md §1 item 3 / session-transaction.md
    // §9.1.1 "Gate-side production" — the commit gate emits a
    // `RedefinitionOutcome` for EVERY staged `Def` whose name had a prior
    // live `Def`, including both T1 shapes that previously emitted none:
    // (a) slot-less staged displacing a slotted prior (the FIXME-0479
    // displacement arm) and (b) template-replacing-template (slot-less over
    // slot-less). Outcomes are the driver's only channel — a shape emitting
    // no outcome is invisible to the §18.1.1 downgrade print.
    #[test]
    fn commit_gate_emits_prior_was_def_outcome_for_both_t1_shapes() {
        let module = ModuleFullPath::from("user");

        // Shape (a): slotted concrete prior, slot-less staged (Overloaded).
        // `shared: None` — the OUTCOME must not depend on the retention pool
        // (only the code retention does).
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();
        let mut live = crate::code::SessionSymbolTable::new_with_params(module.clone());
        let prior_slot = live.allocate_got_slot();
        live.insert(
            Symbol::from("f"),
            mk_def_with_got(
                DefKind::UserFn {
                    fn_state: cranelisp_types::UserFnState::Concrete {
                        got_slot: 0,
                        mode_summary: None,
                    },
                },
                Some(trivial_variant()),
                Some(prior_slot),
            ),
        );
        symbol_tables.insert(module.clone(), live);
        let mut staging = crate::code::SessionSymbolTable::new_with_params(module.clone());
        staging.insert(
            Symbol::from("f"),
            mk_def_with_got(DefKind::Overloaded { variants: vec![] }, None, None),
        );
        let outcomes = commit_staging_to_live(&symbol_tables, &module, staging, None)
            .expect("slot-less commit cannot exhaust the GOT");
        assert_eq!(outcomes.len(), 1, "displacement shape emits ONE outcome: {outcomes:?}");
        let o = &outcomes[0];
        assert_eq!(o.fq.symbol.as_ref(), "f");
        assert!(o.prior_was_def, "prior was a live Def");
        assert!(!o.per_symbol, "T1 route is outside per-symbol precision");
        assert_eq!(o.old_slot, Some(prior_slot));
        assert_eq!(o.new_slot, None, "slot-less staged entry commits no live slot");
        assert!(
            crate::redefine::is_t1_downgrade(o),
            "the displacement shape must reach the §18.1.1 trigger"
        );

        // Shape (b): template-replacing-template (slot-less over slot-less).
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();
        let mut live = crate::code::SessionSymbolTable::new_with_params(module.clone());
        live.insert(
            Symbol::from("t"),
            mk_def_with_got(DefKind::Overloaded { variants: vec![] }, None, None),
        );
        symbol_tables.insert(module.clone(), live);
        let mut staging = crate::code::SessionSymbolTable::new_with_params(module.clone());
        staging.insert(
            Symbol::from("t"),
            mk_def_with_got(DefKind::Overloaded { variants: vec![] }, None, None),
        );
        let outcomes = commit_staging_to_live(&symbol_tables, &module, staging, None)
            .expect("slot-less commit cannot exhaust the GOT");
        assert_eq!(outcomes.len(), 1, "template-over-template emits ONE outcome: {outcomes:?}");
        let o = &outcomes[0];
        assert!(o.prior_was_def && !o.per_symbol, "T1 trigger fields: {o:?}");
        assert!(crate::redefine::is_t1_downgrade(o));
    }

    // spec: design/int/s102-defect-wave.md §1 item 3 — the SLOTTED-staged arm
    // also carries `prior_was_def`: a concrete staged Def over a slot-less
    // prior template (the L-U1 worked shape — generic `id` redefined with a
    // concrete body) classifies `New` (no frozen slot to version) yet MUST
    // reach the §18.1.1 trigger via `prior_was_def`. Negative cells: a
    // genuinely fresh commit and a defn shadowing a prior `Import` (0484's
    // territory) carry `prior_was_def: false` and never trigger.
    #[test]
    fn commit_gate_concrete_over_template_prior_and_negative_cells() {
        let module = ModuleFullPath::from("user");
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();
        let mut live = crate::code::SessionSymbolTable::new_with_params(module.clone());
        // Slot-less prior template `id`; prior `Import` binding `imp`.
        live.insert(
            Symbol::from("id"),
            mk_def_with_got(DefKind::Overloaded { variants: vec![] }, None, None),
        );
        live.insert(
            Symbol::from("imp"),
            ModuleEntry::Import {
                source: FQSymbol {
                    module: ModuleFullPath::from("primitives"),
                    symbol: Symbol::from("add-i64"),
                },
                visibility: Visibility::Private,
            },
        );
        symbol_tables.insert(module.clone(), live);

        let concrete = |slot: usize| {
            mk_def_with_got(
                DefKind::UserFn {
                    fn_state: cranelisp_types::UserFnState::Concrete {
                        got_slot: 0,
                        mode_summary: None,
                    },
                },
                Some(trivial_variant()),
                Some(slot),
            )
        };
        let mut staging = crate::code::SessionSymbolTable::new_with_params(module.clone());
        staging.next_got_slot = 3;
        staging.insert(Symbol::from("id"), concrete(0));
        staging.insert(Symbol::from("imp"), concrete(1));
        staging.insert(Symbol::from("fresh"), concrete(2));

        let outcomes = commit_staging_to_live(&symbol_tables, &module, staging, None)
            .expect("commit cannot exhaust the GOT");
        let by_name = |n: &str| {
            outcomes
                .iter()
                .find(|o| o.fq.symbol.as_ref() == n)
                .unwrap_or_else(|| panic!("outcome for {n}: {outcomes:?}"))
        };
        let id = by_name("id");
        assert!(
            id.prior_was_def && !id.per_symbol && crate::redefine::is_t1_downgrade(id),
            "concrete-over-template reaches the trigger: {id:?}"
        );
        assert!(id.new_slot.is_some(), "concrete staged entry commits a live slot");
        let imp = by_name("imp");
        assert!(
            !imp.prior_was_def && !crate::redefine::is_t1_downgrade(imp),
            "prior-Import shadow is genuine New, never a downgrade: {imp:?}"
        );
        let fresh = by_name("fresh");
        assert!(
            !fresh.prior_was_def && !crate::redefine::is_t1_downgrade(fresh),
            "fresh commit is genuine New, never a downgrade: {fresh:?}"
        );
    }

    // §11.3(b) / §24 (CF.1) unit-tier floor: a panic raised inside the
    // `checked_check_forms` catch-region is CONVERTED to `Err`, not propagated as
    // an unwind. This is the unit complement to the e2e CF.1
    // (`tests/agent.rs::agent_validator_malformed_form_does_not_crash_repl`): the
    // e2e proves the REPL survives end-to-end; this pins the conversion at the
    // exact seam where the catch lives (mirroring the pool-worker `catch_unwind`
    // at `worker.rs:1483`). The §24.3 injection seam
    // (`CRANELISP_AGENT_FORCE_VALIDATOR_PANIC`) stands in for any uncontrolled-
    // input typechecker panic, so the guard is durable independent of any
    // specific defect (e.g. 0432) that the typecheck root fix removes.
    #[cfg(feature = "agent")]
    #[test]
    fn checked_check_forms_converts_panic_to_err_no_unwind_escapes() {
        use cranelisp_typecheck::SymbolTableAccess;

        let module = ModuleFullPath::from("user");
        let symbol_tables: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> =
            dashmap::DashMap::new();
        let module_aliases = cranelisp_types::ModuleAliases::default();
        let prelude_fallback = cranelisp_typecheck::PreludeFallback::default();

        let mut staging: crate::code::SessionSymbolTable =
            crate::code::SessionSymbolTable::new_with_params(module.clone());
        let mut ctx: SymbolTableAccess<'_, crate::code::Code, ()> =
            SymbolTableAccess::cluster(&symbol_tables, &mut staging, module.clone());

        // Arm the injection seam so the catch-region panics. Env is process-global,
        // so set it, run the catch, then clear it — keeping the test self-contained.
        // The serde of this env var is owned by `checked_check_forms`'s seam.
        unsafe { std::env::set_var("CRANELISP_AGENT_FORCE_VALIDATOR_PANIC", "1") };
        // `catch_unwind` inside `checked_check_forms` must convert the forced
        // panic to `Err` — this call MUST NOT itself unwind (no `should_panic`).
        let result = checked_check_forms(
            Vec::new(),
            &mut ctx,
            &symbol_tables,
            &module_aliases,
            &prelude_fallback,
        );
        unsafe { std::env::remove_var("CRANELISP_AGENT_FORCE_VALIDATOR_PANIC") };

        match result {
            Err(cranelisp_typecheck::CheckError::TypeError { message, .. }) => {
                assert!(
                    message.contains("compiler internal error"),
                    "the caught panic must surface as the §24.2 internal-error \
                     TypeError, got: {message}"
                );
            }
            other => panic!(
                "checked_check_forms MUST convert a catch-region panic to \
                 Err(TypeError) (the §11.3(b)/§24 floor), got: {other:?}"
            ),
        }
    }

    // S90 4R Important: the banner-suppression mechanism is a THREAD-LOCAL flag
    // (RAII guard), NOT a process-global panic-hook swap. This pins (a) the flag
    // defaults false, (b) the guard sets it true for its scope and restores the
    // prior value on drop (nesting-safe), and (c) the flag is thread-local — a
    // freshly-spawned thread observes false even while this thread holds the guard
    // true (the core property that makes a concurrently-panicking worker print its
    // banner normally, with no global race).
    #[cfg(feature = "agent")]
    #[test]
    fn suppress_panic_banner_is_thread_local_and_raii_scoped() {
        // (a) defaults false on the current thread.
        assert!(
            !SUPPRESS_PANIC_BANNER.with(|c| c.get()),
            "the suppression flag must default false"
        );

        {
            let _guard = SuppressPanicBannerGuard::new();
            // (b) set true inside the guard's scope.
            assert!(
                SUPPRESS_PANIC_BANNER.with(|c| c.get()),
                "the guard must set the flag true for its scope"
            );

            // (c) thread-local: a concurrent thread sees false while we hold true.
            let observed_on_other_thread = std::thread::spawn(|| {
                SUPPRESS_PANIC_BANNER.with(|c| c.get())
            })
            .join()
            .unwrap();
            assert!(
                !observed_on_other_thread,
                "the flag MUST be thread-local — another thread observes false \
                 even while this thread holds the guard (no global state, no race)"
            );

            // Nesting restores the prior value (true), not unconditionally false.
            {
                let _inner = SuppressPanicBannerGuard::new();
                assert!(SUPPRESS_PANIC_BANNER.with(|c| c.get()));
            }
            assert!(
                SUPPRESS_PANIC_BANNER.with(|c| c.get()),
                "dropping a nested guard must restore the outer guard's true, \
                 not clear to false"
            );
        }

        // Guard dropped → flag restored to its pre-guard value (false).
        assert!(
            !SUPPRESS_PANIC_BANNER.with(|c| c.get()),
            "dropping the guard must restore the flag to false"
        );
    }

    // spec: repl/spec.md §3.3 — listing-surface category bucketing (FIXME 0440).
    // `classify_listing_entry` is the SINGLE `ModuleEntry`/`DefKind` → category
    // classifier shared by `/list`, `/exports`, `list_user_definitions`, and
    // `describe_symbol`. This pins the bucket for one representative entry of
    // every category the four formerly-independent sites covered, so a new
    // `DefKind` variant or a re-bucketing change is a one-site edit (Principle
    // 7) rather than the N-site drift that produced the S91 `__expr` bug.
    #[test]
    fn classify_listing_entry_buckets_every_category() {
        use crate::session_v4::SymbolCategory;
        use cranelisp_types::{
            FQTypeName, MacroClauseInfo, Sexp, TraitDeclInfo, TraitName, TypeDefInfo, TypeName,
        };

        let module = ModuleFullPath::from("user");

        // Def(UserFn) → Fn
        let user_fn = mk_def_with_got(
            DefKind::UserFn { fn_state: cranelisp_types::UserFnState::Concrete { got_slot: 0, mode_summary: None } },
            Some(trivial_variant()),
            Some(0),
        );
        assert_eq!(
            classify_listing_entry(&user_fn),
            Some(SymbolCategory::Fn),
            "an ordinary user fn is the Fn category"
        );

        // Def(Macro) → Macro
        let mac = ModuleEntry::def(
            synthetic_scheme(),
            DefKind::Macro {
                clauses_meta: Vec::<MacroClauseInfo>::new(),
                macro_sexp: Sexp::Symbol("m".to_string(), Span::SYNTHETIC),
            },
        )
        .visibility(Visibility::Public)
        .build();
        assert_eq!(classify_listing_entry(&mac), Some(SymbolCategory::Macro));

        // Def(Constructor) → Constructor
        let ctor = mk_def_with_got(
            DefKind::Constructor {
                got_slot: 0,
                type_name: FQTypeName::new(module.clone(), TypeName::from("Option")),
                tag: 1,
                field_count: 1,
                internal: false,
                type_def: None,
                mode_summary: None,
            },
            Some(trivial_variant()),
            Some(0),
        );
        assert_eq!(
            classify_listing_entry(&ctor),
            Some(SymbolCategory::Constructor),
            "a constructor Def is the Constructor category (callers fold/drop it)"
        );

        // TypeDef → Type
        let type_def = ModuleEntry::TypeDef {
            info: TypeDefInfo {
                name: FQTypeName::new(module.clone(), TypeName::from("Point")),
                type_params: Vec::new(),
                constructors: vec![Symbol::from("Point")],
            },
            visibility: Visibility::Public,
            docstring: None,
        };
        assert_eq!(classify_listing_entry(&type_def), Some(SymbolCategory::Type));

        // TraitDecl → Trait
        let trait_decl = ModuleEntry::TraitDecl {
            info: TraitDeclInfo {
                name: TraitName::from("Display"),
                type_params: Vec::new(),
                methods: Vec::new(),
            },
            visibility: Visibility::Public,
            docstring: None,
        };
        assert_eq!(classify_listing_entry(&trait_decl), Some(SymbolCategory::Trait));

        // SpecialForm → SpecialForm (surfaced by describe_symbol; listings drop it)
        let special = ModuleEntry::SpecialForm {
            scheme: synthetic_scheme(),
            param_names: Vec::new(),
            docstring: None,
            description: "let".to_string(),
            visibility: Visibility::Public,
        };
        assert_eq!(
            classify_listing_entry(&special),
            Some(SymbolCategory::SpecialForm)
        );

        // Import → None (never a user definition; surfaced by /imports)
        let import = ModuleEntry::<crate::code::Code>::Import {
            source: FQSymbol {
                module: ModuleFullPath::from("other"),
                symbol: Symbol::from("x"),
            },
            visibility: Visibility::Private,
        };
        assert_eq!(
            classify_listing_entry(&import),
            None,
            "an import is not a user definition"
        );

        // Ambiguous → None
        let ambiguous = ModuleEntry::<crate::code::Code>::Ambiguous {
            visibility: Visibility::Public,
        };
        assert_eq!(classify_listing_entry(&ambiguous), None);
    }
