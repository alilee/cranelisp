// spec: design/int/int.md §7.6 — the dependency record's edge set and the
// settled-state builder (S122 CL-D). Session state is constructed directly;
// the real restore path that stores a restored member's record is observed
// e2e by `tests/cache.rs` CL-C.

use std::collections::HashSet;
use std::sync::Arc;

use cranelisp_types::{ImportNames, ModuleName, Span, Visibility};

use super::*;
use crate::cache::ObjectCache;
use crate::session_setup::CacheState;

fn m(path: &str) -> ModuleFullPath {
    ModuleFullPath::from(path)
}

fn import(target: &str, alias: Option<&str>, names: ImportNames) -> ImportSpec {
    ImportSpec {
        module_path: m(target),
        alias: alias.map(ModuleName::from),
        names,
        span: Span::SYNTHETIC,
    }
}

fn named_import(target: &str) -> ImportSpec {
    import(target, None, ImportNames::Specific(vec!["f".into()]))
}

fn reexport(target: &str) -> ExportSpec {
    ExportSpec {
        module_path: m(target),
        names: ImportNames::Glob,
        span: Span::SYNTHETIC,
    }
}

fn child(name: &str) -> ModDecl {
    ModDecl {
        name: ModuleName::from(name),
        visibility: Visibility::Private,
        inline_body: None,
        span: Span::SYNTHETIC,
    }
}

fn edges_of(
    imports: &[ImportSpec],
    exports: &[ExportSpec],
    children: &[ModDecl],
    fallback: bool,
) -> Vec<String> {
    let ModuleEdges(edges) =
        ModuleEdges::of_declarations(&m("m"), imports, exports, children, fallback);
    edges.into_iter().map(|edge| edge.to_string()).collect()
}

fn record_of(outcome: RecordOutcome) -> Vec<(String, String)> {
    let RecordOutcome::Settled(record) = outcome else {
        panic!("expected a settled record, got {outcome:?}");
    };
    record
        .members()
        .map(|(member, hash)| (member.to_string(), hash.to_string()))
        .collect()
}

// ---------------------------------------------------------------------------
// Edge kinds
// ---------------------------------------------------------------------------

#[test]
fn every_edge_kind_is_a_member() {
    let alias_only = [import("d", Some("dd"), ImportNames::None)];
    let null = [import("d", None, ImportNames::None)];
    let cases: [(&str, Vec<String>, &str); 6] = [
        (
            "named import",
            edges_of(&[named_import("d")], &[], &[], false),
            "d",
        ),
        (
            "alias-only import",
            edges_of(&alias_only, &[], &[], false),
            "d",
        ),
        ("null import", edges_of(&null, &[], &[], false), "d"),
        (
            "re-export target",
            edges_of(&[], &[reexport("d")], &[], false),
            "d",
        ),
        (
            "declared child",
            edges_of(&[], &[], &[child("kid")], false),
            "m.kid",
        ),
        (
            "prelude with the fallback bit",
            edges_of(&[], &[], &[], true),
            "prelude",
        ),
    ];
    for (kind, edges, expected) in cases {
        assert_eq!(edges, [expected], "{kind}");
    }
}

#[test]
fn prelude_is_not_an_edge_when_the_fallback_bit_is_clear() {
    assert!(
        edges_of(&[named_import("d")], &[], &[], false)
            .iter()
            .all(|edge| edge != "prelude")
    );
}

#[test]
fn compiler_owned_modules_and_the_module_itself_are_not_edges() {
    let edges = edges_of(
        &[
            named_import("primitives"),
            named_import("macros"),
            named_import("platform.io"),
            named_import("m"),
        ],
        &[reexport("primitives")],
        &[],
        false,
    );
    assert!(edges.is_empty(), "{edges:?}");
}

// ---------------------------------------------------------------------------
// Builder over session state
// ---------------------------------------------------------------------------

/// Session state with caching enabled and no modules loaded.
struct Session {
    shared: crate::session_v4::SharedState,
    _cache_dir: tempfile::TempDir,
}

impl Session {
    fn new() -> Self {
        use std::sync::Mutex;
        use std::sync::atomic::{AtomicBool, AtomicU32};
        let cache_dir = tempfile::tempdir().unwrap();
        let cache = ObjectCache::new(
            Some(cache_dir.path().to_path_buf()),
            Some(CacheState::new(cache_dir.path().to_path_buf())),
        );
        let shared = crate::session_v4::SharedState {
            scheduler: crate::scheduler::CompileScheduler::new(),
            project_root: PathBuf::new(),
            lib_dirs: Mutex::new(Vec::new()),
            platform_dirs: Mutex::new(Vec::new()),
            module_aliases: cranelisp_types::ModuleAliases::default(),
            prelude_fallback: cranelisp_typecheck::PreludeFallback::default(),
            declared_exports: crate::imports::DeclaredExports::default(),
            cache: Arc::new(cache),
            promote_nice_workers: AtomicBool::new(false),
            file_to_module: Mutex::new(HashMap::new()),
            symbol_tables: dashmap::DashMap::new(),
            next_type_id: AtomicU32::new(0),
            typecheck_products: dashmap::DashMap::new(),
            kept_dlls: Mutex::new(Vec::new()),
            introspection: None,
            importable_indices: crate::session_v4::ImportableIndices::default(),
            retained_code: Mutex::new(Vec::new()),
            fresh_jit_drop_glues: dashmap::DashMap::new(),
            run_mode: crate::session_v4::RunMode::Run,
            test_runner_state: Box::new(crate::session_v4::TestRunnerState::stub()),
        };
        Session {
            shared,
            _cache_dir: cache_dir,
        }
    }

    fn install_table(&self, module: &str, imports: &[&str]) {
        let mut table = SessionSymbolTable::new_with_params(m(module));
        table.imports = imports.iter().map(|target| named_import(target)).collect();
        self.shared.symbol_tables.insert(m(module), table);
    }

    /// A fresh registration whose typecheck has completed.
    fn fresh(&self, module: &str, hash: &str, imports: &[&str]) {
        self.install_table(module, imports);
        drop(
            self.shared
                .scheduler
                .register_module_cached(m(module), HashSet::new()),
        );
        self.shared
            .cache
            .record_source_hash(&m(module), hash.to_string());
    }

    /// A cache restore that validated under `record`; its table's imports
    /// are deliberately unloaded, so walking them would be unsettled.
    fn restored(&self, module: &str, hash: &str, record: &[(&str, &str)]) {
        self.install_table(module, &["never-loaded"]);
        drop(
            self.shared
                .scheduler
                .register_module_cached(m(module), HashSet::new()),
        );
        let record = DependencyRecord(
            record
                .iter()
                .map(|(member, hash)| (m(member), hash.to_string()))
                .collect(),
        );
        self.shared
            .cache
            .record_cache_hit(&m(module), hash.to_string(), record);
    }

    fn build(&self, module: &str, imports: &[&str]) -> RecordOutcome {
        let imports: Vec<ImportSpec> = imports.iter().map(|target| named_import(target)).collect();
        build_dependency_record(
            &self.shared,
            &m(module),
            ModuleEdges::of_declarations(&m(module), &imports, &[], &[], false),
        )
    }
}

fn pairs(expected: &[(&str, &str)]) -> Vec<(String, String)> {
    expected
        .iter()
        .map(|(member, hash)| (member.to_string(), hash.to_string()))
        .collect()
}

#[test]
fn fresh_chain_records_the_transitive_member() {
    let session = Session::new();
    session.fresh("e", "hash-e", &[]);
    session.fresh("d", "hash-d", &["e"]);
    assert_eq!(
        record_of(session.build("m", &["d"])),
        pairs(&[("d", "hash-d"), ("e", "hash-e")])
    );
}

#[test]
fn restored_member_contributes_its_stored_record_without_walking_its_table() {
    let session = Session::new();
    session.restored("d", "hash-d", &[("e", "hash-e")]);
    assert_eq!(
        record_of(session.build("m", &["d"])),
        pairs(&[("d", "hash-d"), ("e", "hash-e")])
    );
}

#[test]
fn hashes_are_the_versions_this_session_loaded() {
    let session = Session::new();
    // `e` reaches `m` both directly (loaded fresh) and through restored `d`'s
    // record; the loaded version wins, and no file is read to decide it.
    session.fresh("e", "loaded-e", &[]);
    session.restored("d", "hash-d", &[("e", "recorded-e")]);
    assert_eq!(
        record_of(session.build("m", &["d", "e"])),
        pairs(&[("d", "hash-d"), ("e", "loaded-e")])
    );
}

#[test]
fn a_cycle_back_to_the_module_is_not_a_member() {
    let session = Session::new();
    session.fresh("m", "hash-m", &["d"]);
    session.fresh("d", "hash-d", &["m"]);
    session.restored("r", "hash-r", &[("m", "hash-m")]);
    assert_eq!(
        record_of(session.build("m", &["d", "r"])),
        pairs(&[("d", "hash-d"), ("r", "hash-r")])
    );
}

#[test]
fn prelude_the_session_never_loaded_is_dropped() {
    let session = Session::new();
    let outcome = build_dependency_record(
        &session.shared,
        &m("m"),
        ModuleEdges::of_declarations(&m("m"), &[], &[], &[], true),
    );
    assert_eq!(outcome, RecordOutcome::Settled(DependencyRecord::default()));
}

#[test]
fn loaded_prelude_is_recorded_with_its_own_edges() {
    let session = Session::new();
    session.fresh("text", "hash-text", &[]);
    session.fresh("prelude", "hash-prelude", &["text"]);
    let outcome = build_dependency_record(
        &session.shared,
        &m("m"),
        ModuleEdges::of_declarations(&m("m"), &[], &[], &[], true),
    );
    assert_eq!(
        record_of(outcome),
        pairs(&[("prelude", "hash-prelude"), ("text", "hash-text")])
    );
}

#[test]
fn a_fresh_member_with_the_fallback_bit_reaches_the_prelude() {
    let session = Session::new();
    session.fresh("prelude", "hash-prelude", &[]);
    session.fresh("d", "hash-d", &[]);
    session.shared.prelude_fallback.insert(m("d"), true);
    assert_eq!(
        record_of(session.build("m", &["d"])),
        pairs(&[("d", "hash-d"), ("prelude", "hash-prelude")])
    );
}

/// The manifest entry `module` would restore under in the next session.
fn persisted_record(session: &Session, module: &str) -> Option<Vec<(String, String)>> {
    session.shared.cache.flush_manifest();
    let dir = session.shared.cache.cache_dir().unwrap();
    let manifest = cranelisp_backend::cache::manifest::read_manifest(&dir)?;
    let entry = manifest.get_module(&m(module))?;
    let record = DependencyRecord::from_manifest(&entry.dependency_hashes);
    Some(
        record
            .members()
            .map(|(member, hash)| (member.to_string(), hash.to_string()))
            .collect(),
    )
}

// A declared child that imports its parent typechecks while the parent still
// waits on it (ancestors are exempt from the signature barrier), so the
// child's write sees an unsettled parent. Its entry lands once the parent has
// settled, before the manifest flush.
#[test]
fn a_child_written_before_its_parent_settles_is_recorded_once_it_has() {
    let session = Session::new();
    session.install_table("p", &[]);
    session.shared.scheduler.register_module(
        m("p"),
        Arc::from(Vec::<cranelisp_types::Sexp>::new()),
        true,
    );
    session
        .shared
        .cache
        .record_source_hash(&m("p"), "hash-p".to_string());
    let child_edges =
        ModuleEdges::of_declarations(&m("p.test"), &[named_import("p")], &[], &[], false);

    record_manifest_entry(
        &session.shared,
        &m("p.test"),
        "hash-t".to_string(),
        child_edges,
    );
    assert_eq!(persisted_record(&session, "p.test"), None);

    session.shared.scheduler.notify_typecheck_done(&m("p"));
    record_deferred_entries(&session.shared);
    assert_eq!(
        persisted_record(&session, "p.test"),
        Some(pairs(&[("p", "hash-p")]))
    );
}

// Each unsettled case yields no record — never an empty or partial one. A
// restored member without a stored record is unrepresentable:
// `LoadedSource::Restored` carries its record.

#[test]
fn unsettled_when_a_member_is_not_loaded() {
    let session = Session::new();
    session.fresh("d", "hash-d", &["e"]);
    assert_eq!(
        session.build("m", &["d"]),
        RecordOutcome::Unsettled { member: m("e") }
    );
}

#[test]
fn unsettled_when_a_member_has_not_finished_typechecking() {
    let session = Session::new();
    session.install_table("d", &[]);
    session.shared.scheduler.register_module(
        m("d"),
        Arc::from(Vec::<cranelisp_types::Sexp>::new()),
        true,
    );
    session
        .shared
        .cache
        .record_source_hash(&m("d"), "hash-d".to_string());
    assert_eq!(
        session.build("m", &["d"]),
        RecordOutcome::Unsettled { member: m("d") }
    );
}

#[test]
fn unsettled_when_a_typechecked_member_has_no_stashed_hash() {
    let session = Session::new();
    session.install_table("d", &[]);
    drop(
        session
            .shared
            .scheduler
            .register_module_cached(m("d"), HashSet::new()),
    );
    assert_eq!(
        session.build("m", &["d"]),
        RecordOutcome::Unsettled { member: m("d") }
    );
}

// ---------------------------------------------------------------------------
// Callee-module edges (`design/int/int.md` §7.6.1)
// ---------------------------------------------------------------------------

mod callee_modules {
    use std::collections::HashMap as StdHashMap;

    use cranelisp_types::{
        CallableArmDraft, CallableOrigin, CodeStore, DefnVariant, Expr, FQSymbol, MacroClauseDraft,
        MonoDefnVariant, MonoExpr, Realization, Scheme, Sexp, Symbol, SymbolTable, TemplateBody,
        TemplateKind, Type,
    };

    use super::*;

    fn callees(modules: &[&str]) -> Vec<FQSymbol> {
        modules
            .iter()
            .map(|module| FQSymbol {
                module: m(module),
                symbol: Symbol::from("f"),
            })
            .collect()
    }

    fn scheme(ty: Type) -> Scheme {
        Scheme {
            type_vars: cranelisp_types::free_vars(&ty).into_iter().collect(),
            constraints: StdHashMap::new(),
            ty,
        }
    }

    fn concrete_ty(arity: usize) -> Type {
        Type::Fn(vec![Type::Int; arity], Box::new(Type::Int))
    }

    fn template_ty() -> Type {
        Type::Fn(vec![Type::Var(0)], Box::new(Type::Int))
    }

    fn body(name: &str) -> (DefnVariant, MonoDefnVariant) {
        let ast = DefnVariant {
            params: Vec::new(),
            body: Expr::IntLit {
                value: 0,
                span: Span::SYNTHETIC,
                inferred_type: Some(Box::new(Type::Int)),
            },
            span: Span::SYNTHETIC,
        };
        let view = MonoDefnVariant {
            name: Symbol::from(name),
            params: Vec::new(),
            body: MonoExpr::lenient_from_expr(
                &ast.body,
                &Default::default(),
                &Default::default(),
                &Default::default(),
            ),
            span: Span::SYNTHETIC,
            mode_summary: None,
        };
        (ast, view)
    }

    pub(super) fn concrete<C: CodeStore>(
        table: &mut SymbolTable<C, ()>,
        name: &str,
        modules: &[&str],
    ) {
        let (ast, view) = body(name);
        table
            .install_concrete(
                Symbol::from(name),
                scheme(concrete_ty(0)),
                Vec::new(),
                None,
                0,
                CallableOrigin::Plain,
                Realization::Body { view, code: None },
                Some(ast),
                callees(modules),
                Visibility::Public,
            )
            .unwrap();
    }

    fn template<C: CodeStore>(table: &mut SymbolTable<C, ()>, name: &str, modules: &[&str]) {
        let (ast, _) = body(name);
        table
            .install_template(
                Symbol::from(name),
                scheme(template_ty()),
                Vec::new(),
                None,
                0,
                CallableOrigin::Plain,
                TemplateBody::Ast(ast),
                TemplateKind::Parametric,
                callees(modules),
                Visibility::Public,
            )
            .unwrap();
    }

    fn concrete_arm(name: &str, arity: usize, modules: &[&str]) -> CallableArmDraft {
        let (ast, view) = body(name);
        CallableArmDraft::concrete_body(
            scheme(concrete_ty(arity)),
            Vec::new(),
            ast,
            view,
            callees(modules),
        )
    }

    fn template_arm(name: &str, modules: &[&str]) -> CallableArmDraft {
        let (ast, _) = body(name);
        CallableArmDraft::template(
            scheme(template_ty()),
            Vec::new(),
            TemplateBody::Ast(ast),
            TemplateKind::Parametric,
            callees(modules),
        )
    }

    /// One binding of every callable kind, each calling a distinct module:
    /// concrete and template callables, an overload with a template and a
    /// concrete arm, and a macro clause.
    fn every_callable_kind<C: CodeStore>(table: &mut SymbolTable<C, ()>) {
        concrete(table, "plain", &["c-concrete"]);
        template(table, "generic", &["c-template"]);
        table
            .install_overloaded(
                Symbol::from("multi"),
                None,
                0,
                vec![
                    template_arm("multi-generic", &["c-arm-template"]),
                    concrete_arm("multi-binary", 2, &["c-arm-concrete"]),
                ],
                Visibility::Public,
            )
            .unwrap();
        let clause = MacroClauseDraft::new(Vec::new(), None, concrete_arm("mac", 0, &["c-macro"]));
        table
            .install_macro(
                Symbol::from("mac"),
                None,
                0,
                Sexp::List(Vec::new(), Span::SYNTHETIC),
                vec![clause],
                Visibility::Public,
            )
            .unwrap();
    }

    const EVERY_KIND: [&str; 5] = [
        "c-arm-concrete",
        "c-arm-template",
        "c-concrete",
        "c-macro",
        "c-template",
    ];

    fn table_edges(table: &SessionSymbolTable) -> Vec<String> {
        let ModuleEdges(edges) = ModuleEdges::of_table(&m("m"), table, false);
        edges.into_iter().map(|edge| edge.to_string()).collect()
    }

    #[test]
    fn every_callable_kind_contributes_its_callee_modules() {
        let mut table = SessionSymbolTable::new_with_params(m("m"));
        every_callable_kind(&mut table);
        assert_eq!(table_edges(&table), EVERY_KIND);
    }

    // The restore walk reads a decoded table before installing it.
    #[test]
    fn a_decoded_table_yields_the_same_callee_modules() {
        let mut table = SymbolTable::<(), ()>::new_with_params(m("m"));
        every_callable_kind(&mut table);
        let modules: Vec<String> = callee_modules(&m("m"), &table)
            .into_iter()
            .map(|module| module.to_string())
            .collect();
        assert_eq!(modules, EVERY_KIND);
    }

    #[test]
    fn own_module_and_compiler_owned_callees_are_not_edges() {
        let mut table = SessionSymbolTable::new_with_params(m("m"));
        concrete(
            &mut table,
            "plain",
            &["m", "primitives", "macros", "platform.io"],
        );
        assert!(table_edges(&table).is_empty(), "{:?}", table_edges(&table));
    }

    #[test]
    fn a_table_without_callees_yields_exactly_its_declared_edges() {
        let mut table = SessionSymbolTable::new_with_params(m("m"));
        concrete(&mut table, "plain", &[]);
        template(&mut table, "generic", &[]);
        table.imports = vec![named_import("d"), import("n", None, ImportNames::None)];
        table.exports = vec![reexport("e")];
        table.submodules = vec![child("kid")];
        assert_eq!(
            ModuleEdges::of_table(&m("m"), &table, true),
            ModuleEdges::of_declarations(
                &m("m"),
                &table.imports,
                &table.exports,
                &table.submodules,
                true,
            )
        );
    }

    #[test]
    fn a_fresh_member_linked_only_by_a_callee_is_in_the_closure() {
        let session = Session::new();
        session.fresh("e", "hash-e", &[]);
        session.fresh("d", "hash-d", &[]);
        concrete(
            &mut session.shared.symbol_tables.get_mut(&m("d")).unwrap(),
            "g",
            &["e"],
        );
        assert_eq!(
            record_of(session.build("m", &["d"])),
            pairs(&[("d", "hash-d"), ("e", "hash-e")])
        );
    }

    #[test]
    fn unsettled_when_a_callee_module_has_no_loaded_source() {
        let session = Session::new();
        session.fresh("d", "hash-d", &[]);
        concrete(
            &mut session.shared.symbol_tables.get_mut(&m("d")).unwrap(),
            "g",
            &["e"],
        );
        assert_eq!(
            session.build("m", &["d"]),
            RecordOutcome::Unsettled { member: m("e") }
        );
    }
}

// ---------------------------------------------------------------------------
// Lookup dependencies (`design/int/int.md` §7.6.2)
// ---------------------------------------------------------------------------

mod lookup_dependencies {
    use cranelisp_types::{CodeStore, SymbolTable};

    use super::*;

    /// Callee edges to `c-callee` and `shared`, lookup dependencies on
    /// `l-lookup` and `shared`, plus records the union must filter out.
    fn record_both<C: CodeStore>(table: &mut SymbolTable<C, ()>) {
        callee_modules::concrete(table, "g", &["c-callee", "shared", "primitives"]);
        for module in ["l-lookup", "shared", "macros", "platform.io", "m"] {
            table.record_lookup_dependency(m(module));
        }
    }

    const UNION: [&str; 3] = ["c-callee", "l-lookup", "shared"];

    #[test]
    fn recorded_edges_are_the_union_of_callee_modules_and_lookup_dependencies() {
        let mut table = SessionSymbolTable::new_with_params(m("m"));
        record_both(&mut table);
        let ModuleEdges(edges) = ModuleEdges::of_table(&m("m"), &table, false);
        let edges: Vec<String> = edges.iter().map(ToString::to_string).collect();
        assert_eq!(edges, UNION);
    }

    #[test]
    fn a_decoded_table_yields_the_same_recorded_edges() {
        let mut table = SymbolTable::<(), ()>::new_with_params(m("m"));
        record_both(&mut table);
        let edges: Vec<String> = recorded_edges(&m("m"), &table)
            .iter()
            .map(ToString::to_string)
            .collect();
        assert_eq!(edges, UNION);
    }

    #[test]
    fn a_fresh_member_linked_only_by_a_lookup_dependency_is_in_the_closure() {
        let session = Session::new();
        session.fresh("f", "hash-f", &[]);
        session.fresh("e", "hash-e", &["f"]);
        session.fresh("d", "hash-d", &[]);
        session
            .shared
            .symbol_tables
            .get_mut(&m("d"))
            .unwrap()
            .record_lookup_dependency(m("e"));
        assert_eq!(
            record_of(session.build("m", &["d"])),
            pairs(&[("d", "hash-d"), ("e", "hash-e"), ("f", "hash-f")])
        );
    }

    #[test]
    fn unsettled_when_a_lookup_dependency_has_no_loaded_source() {
        let session = Session::new();
        session.fresh("d", "hash-d", &[]);
        session
            .shared
            .symbol_tables
            .get_mut(&m("d"))
            .unwrap()
            .record_lookup_dependency(m("e"));
        assert_eq!(
            session.build("m", &["d"]),
            RecordOutcome::Unsettled { member: m("e") }
        );
    }

    // Restore loads no lookup dependency, so a restored member's table may
    // name one this session never loaded; its validated record stands in.
    #[test]
    fn a_restored_member_settles_without_its_lookup_dependencies_loaded() {
        let session = Session::new();
        session.restored("d", "hash-d", &[("e", "hash-e")]);
        session
            .shared
            .symbol_tables
            .get_mut(&m("d"))
            .unwrap()
            .record_lookup_dependency(m("e"));
        assert_eq!(
            record_of(session.build("m", &["d"])),
            pairs(&[("d", "hash-d"), ("e", "hash-e")])
        );
    }
}
