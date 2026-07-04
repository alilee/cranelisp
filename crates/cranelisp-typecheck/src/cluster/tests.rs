    use super::*;
    use cranelisp_types::{ModuleEntry, Symbol};
    use std::sync::Arc;

    fn module_path() -> ModuleFullPath {
        ModuleFullPath::from("test_mod")
    }

    fn empty_modules() -> Arc<DashMap<ModuleFullPath, SymbolTable<(), ()>>> {
        let modules: DashMap<ModuleFullPath, SymbolTable<(), ()>> = DashMap::new();
        modules.insert(module_path(), SymbolTable::<(), ()>::new_with_params(module_path()));
        Arc::new(modules)
    }

    fn dummy_module_entry() -> ModuleEntry<()> {
        ModuleEntry::Import {
            source: cranelisp_types::FQSymbol {
                module: ModuleFullPath::from("other"),
                symbol: Symbol::from("x"),
            },
            visibility: cranelisp_types::Visibility::Private,
        }
    }

    #[test]
    fn live_mode_routes_to_live_table() {
        let modules = empty_modules();
        let mut ctx: SymbolTableAccess<'_, (), ()> = SymbolTableAccess::live(&modules, module_path());
        // Initially empty
        {
            let r = ctx.current_symbol_table();
            let v = r.view();
            assert!(v.lookup(&Symbol::from("absent")).is_none());
        }
        // Write through accessor
        {
            let mut w = ctx.current_symbol_table_mut();
            w.insert(Symbol::from("present"), dummy_module_entry());
        }
        // Read back via accessor (and via live table directly)
        {
            let r = ctx.current_symbol_table();
            let v = r.view();
            assert!(v.lookup(&Symbol::from("present")).is_some());
        }
        let live_guard = modules.get(&module_path()).unwrap();
        assert!(live_guard.get("present").is_some());
    }

    #[test]
    fn cluster_mode_writes_go_to_staging_not_live() {
        let modules = empty_modules();
        let mut staging = SymbolTable::<(), ()>::new_with_params(module_path());
        {
            let mut ctx: SymbolTableAccess<'_, (), ()> =
                SymbolTableAccess::cluster(&modules, &mut staging, module_path());
            let mut w = ctx.current_symbol_table_mut();
            w.insert(Symbol::from("staged"), dummy_module_entry());
        }
        // Staging carries the entry
        assert!(staging.get("staged").is_some());
        // Live table is untouched
        let live_guard = modules.get(&module_path()).unwrap();
        assert!(live_guard.get("staged").is_none());
    }

    #[test]
    fn cluster_mode_reads_union_staging_and_live() {
        let modules = empty_modules();
        // Seed live with one entry
        {
            let mut live = modules.get_mut(&module_path()).unwrap();
            live.insert(Symbol::from("live_only"), dummy_module_entry());
        }
        let mut staging = SymbolTable::<(), ()>::new_with_params(module_path());
        staging.insert(Symbol::from("staging_only"), dummy_module_entry());

        let ctx: SymbolTableAccess<'_, (), ()> =
            SymbolTableAccess::cluster(&modules, &mut staging, module_path());
        let r = ctx.current_symbol_table();
        let v = r.view();
        assert!(v.lookup(&Symbol::from("live_only")).is_some());
        assert!(v.lookup(&Symbol::from("staging_only")).is_some());
        assert!(v.lookup(&Symbol::from("absent")).is_none());
    }

    #[test]
    fn cluster_mode_staging_shadows_live() {
        let modules = empty_modules();
        // Seed live with placeholder entry
        {
            let mut live = modules.get_mut(&module_path()).unwrap();
            live.insert(Symbol::from("name"), dummy_module_entry());
        }
        let mut staging = SymbolTable::<(), ()>::new_with_params(module_path());
        // Stage a shadowing entry with a distinguishable source
        staging.insert(
            Symbol::from("name"),
            ModuleEntry::Import {
                source: cranelisp_types::FQSymbol {
                    module: ModuleFullPath::from("shadowing"),
                    symbol: Symbol::from("shadow"),
                },
                visibility: cranelisp_types::Visibility::Private,
            },
        );

        let ctx: SymbolTableAccess<'_, (), ()> =
            SymbolTableAccess::cluster(&modules, &mut staging, module_path());
        let r = ctx.current_symbol_table();
        let v = r.view();
        let entry = v.lookup(&Symbol::from("name")).expect("name resolves");
        match entry {
            ModuleEntry::Import { source, .. } => {
                assert_eq!(source.module.as_ref(), "shadowing");
            }
            _ => panic!("expected Import entry"),
        }
    }

    #[test]
    fn current_module_returns_active_path() {
        let modules = empty_modules();
        let ctx: SymbolTableAccess<'_, (), ()> = SymbolTableAccess::live(&modules, module_path());
        assert_eq!(ctx.current_module(), &module_path());
    }

    // -------------------------------------------------------------------
    // Negative / edge cells (S102 FIXME 0497 gap-fill — cluster.rs was
    // happy-path-only). The read accessors carry an unconditional precondition
    // (the current module MUST be present in `modules`); these pin the
    // precondition-violation panic + the empty-staging union edge.
    // -------------------------------------------------------------------

    // NEGATIVE: in Live mode, reading the current symbol table when the current
    // module is absent from `modules` is a precondition violation (the module
    // graph must always carry the scoped module) — the accessor panics rather
    // than silently returning an empty table.
    #[test]
    #[should_panic(expected = "not present in live modules")]
    fn live_mode_absent_current_module_panics() {
        let modules = empty_modules();
        let ctx: SymbolTableAccess<'_, (), ()> =
            SymbolTableAccess::live(&modules, ModuleFullPath::from("absent_mod"));
        // `absent_mod` was never inserted → precondition violated.
        let _ = ctx.current_symbol_table();
    }

    // NEGATIVE: the same precondition holds in Cluster mode — the LIVE table for
    // the current module must exist even though writes go to staging (reads
    // union staging over live).
    #[test]
    #[should_panic(expected = "cluster precondition")]
    fn cluster_mode_absent_current_module_panics() {
        let modules = empty_modules();
        let mut staging =
            SymbolTable::<(), ()>::new_with_params(ModuleFullPath::from("absent_mod"));
        let ctx: SymbolTableAccess<'_, (), ()> =
            SymbolTableAccess::cluster(&modules, &mut staging, ModuleFullPath::from("absent_mod"));
        let _ = ctx.current_symbol_table();
    }

    // EDGE: an EMPTY staging table unions to exactly the live entries — nothing
    // is shadowed or hidden, and a genuinely-absent name still resolves to None.
    #[test]
    fn cluster_mode_empty_staging_reads_live_only() {
        let modules = empty_modules();
        {
            let mut live = modules.get_mut(&module_path()).unwrap();
            live.insert(Symbol::from("live_only"), dummy_module_entry());
        }
        // Staging is empty.
        let mut staging = SymbolTable::<(), ()>::new_with_params(module_path());
        let ctx: SymbolTableAccess<'_, (), ()> =
            SymbolTableAccess::cluster(&modules, &mut staging, module_path());
        let r = ctx.current_symbol_table();
        let v = r.view();
        assert!(
            v.lookup(&Symbol::from("live_only")).is_some(),
            "empty staging → live entry still visible through the union"
        );
        assert!(v.lookup(&Symbol::from("absent")).is_none());
    }
