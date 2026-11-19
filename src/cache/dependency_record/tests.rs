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
    import(
        target,
        None,
        ImportNames::Specific(vec![crate::imports::plain_entry("f")]),
    )
}

fn reexport(target: &str) -> ExportSpec {
    ExportSpec {
        module_path: m(target),
        alias: None,
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

// spec: spec/08-modules.md §8.11.2 item 1 — a bare import or re-export target
// names the declared child `m.q`, never the root `q`; undeclared, it names `q`.
#[test]
fn bare_target_is_an_edge_to_the_declared_child_only() {
    let declared = edges_of(&[named_import("q")], &[reexport("q")], &[child("q")], false);
    assert_eq!(declared, ["m.q"], "declared `(mod q)`");
    let undeclared = edges_of(&[named_import("q")], &[reexport("q")], &[], false);
    assert_eq!(undeclared, ["q"], "no `(mod q)`");
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
            recorded_sources: dashmap::DashMap::new(),
            symbol_tables: dashmap::DashMap::new(),
            next_type_id: AtomicU32::new(0),
            typecheck_products: dashmap::DashMap::new(),
            kept_dlls: Mutex::new(Vec::new()),
            introspection: None,
            importable_indices: crate::session_v4::ImportableIndices::default(),
            retained_code: Mutex::new(Vec::new()),
            fresh_jit_drop_glues: dashmap::DashMap::new(),
            run_mode: crate::session_v4::RunMode::Run,
            entry_module: cranelisp_types::ModuleFullPath::from("user"),
            definition_origins: dashmap::DashMap::new(),
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
                .register_module_cached(m(module), HashSet::new(), Vec::new()),
        );
        self.shared.scheduler.end_restore(&m(module), &Ok(()));
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
                .register_module_cached(m(module), HashSet::new(), Vec::new()),
        );
        self.shared.scheduler.end_restore(&m(module), &Ok(()));
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

/// The derivation key of a walked member whose live table assigns no slot.
fn key(source_hash: &str) -> String {
    AuthoredSlotLayout(BTreeMap::new()).derivation_key(source_hash)
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
        pairs(&[("d", &key("hash-d")), ("e", &key("hash-e"))])
    );
}

#[test]
fn restored_member_contributes_its_stored_record_without_walking_its_table() {
    let session = Session::new();
    session.restored("d", "hash-d", &[("e", "hash-e")]);
    assert_eq!(
        record_of(session.build("m", &["d"])),
        pairs(&[("d", &key("hash-d")), ("e", "hash-e")])
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
        pairs(&[("d", &key("hash-d")), ("e", &key("loaded-e"))])
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
        pairs(&[("d", &key("hash-d")), ("r", &key("hash-r"))])
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
        pairs(&[
            ("prelude", &key("hash-prelude")),
            ("text", &key("hash-text"))
        ])
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
        pairs(&[("d", &key("hash-d")), ("prelude", &key("hash-prelude"))])
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
        Some(pairs(&[("p", &key("hash-p"))]))
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
            .register_module_cached(m("d"), HashSet::new(), Vec::new()),
    );
    session.shared.scheduler.end_restore(&m("d"), &Ok(()));
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
        MonoDefnVariant, Realization, Scheme, Sexp, Symbol, SymbolTable, TemplateBody,
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
            body: cranelisp_types::test_support::lenient_from_expr(
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
        let d_key = AuthoredSlotLayout::of(&session.shared.symbol_tables.get(&m("d")).unwrap())
            .derivation_key("hash-d");
        assert_ne!(d_key, key("hash-d"), "`g`'s slot is part of `d`'s layout");
        assert_eq!(
            record_of(session.build("m", &["d"])),
            pairs(&[("d", &d_key), ("e", &key("hash-e"))])
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
            pairs(&[
                ("d", &key("hash-d")),
                ("e", &key("hash-e")),
                ("f", &key("hash-f"))
            ])
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
            pairs(&[("d", &key("hash-d")), ("e", "hash-e")])
        );
    }
}

// ---------------------------------------------------------------------------
// Reload edges (design/int/repl-lifecycle.md §1.2; design/int/int.md §6.12)
// ---------------------------------------------------------------------------

fn reload_edges_of(imports: Vec<ImportSpec>, fallback: bool) -> Vec<String> {
    let mut table = SessionSymbolTable::new_with_params(m("x"));
    table.imports = imports;
    reload_edges(&m("x"), &table, fallback)
        .iter()
        .map(ToString::to_string)
        .collect()
}

// spec: design/int/int.md §6.12 — the bit alone gives the prelude edge,
// whatever else the module depends on or whatever reaches it.
#[test]
fn reload_edges_follow_the_prelude_fallback_bit() {
    assert_eq!(reload_edges_of(Vec::new(), true), ["prelude"]);
    assert!(reload_edges_of(Vec::new(), false).is_empty());
}

// spec: spec/08-modules.md §8.3.7; design/int/int.md §6.12 — a null import,
// plain or aliased, loads nothing and is no reload edge; a named import of
// the prelude is one.
#[test]
fn a_null_import_is_no_reload_edge_and_a_named_prelude_import_is_one() {
    assert!(reload_edges_of(vec![import("prelude", None, ImportNames::None)], false).is_empty());
    assert!(reload_edges_of(vec![import("y", Some("w"), ImportNames::None)], false).is_empty());
    assert_eq!(
        reload_edges_of(vec![named_import("prelude")], false),
        ["prelude"]
    );
}

// spec: design/int/int.md §7.6 — the cache-validity edge set keeps a null
// import, which the reload predicate drops.
#[test]
fn the_cache_validity_edges_keep_a_null_import() {
    assert_eq!(
        edges_of(
            &[import("prelude", None, ImportNames::None)],
            &[],
            &[],
            false
        ),
        ["prelude"]
    );
}

// ---------------------------------------------------------------------------
// Slot-layout identity (`design/int/int.md` §7.6.3, ACT-1052)
// ---------------------------------------------------------------------------

mod slot_layout {
    use cranelisp_types::{
        CallableOrigin, CallableTarget, ConcreteType, DefnVariant, Expr, FQSymbol, InstanceLink,
        MonoDefnVariant, Realization, Scheme, Symbol, Type,
    };

    use super::callee_modules::concrete;
    use super::*;

    const SOURCE: &str = "(defn f [] 1)";

    /// A project holding `dep.cl`, whose current key `ModuleSources` reads
    /// against `tables` and the cache directory.
    pub(super) struct Project {
        root: tempfile::TempDir,
        pub(super) cache_dir: tempfile::TempDir,
        tables: dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
    }

    impl Project {
        pub(super) fn new() -> Self {
            let project = Project {
                root: tempfile::tempdir().unwrap(),
                cache_dir: tempfile::tempdir().unwrap(),
                tables: dashmap::DashMap::new(),
            };
            std::fs::write(project.root.path().join("dep.cl"), SOURCE).unwrap();
            project
        }

        fn current_key(&self) -> Option<String> {
            let cache = ObjectCache::new(Some(self.cache_dir.path().to_path_buf()), None);
            ModuleSources::new(self.root.path(), &[], &self.tables, &cache).current_key(&m("dep"))
        }
    }

    fn hash() -> String {
        cranelisp_backend::cache::manifest::hash_source(SOURCE)
    }

    /// `dep`'s table defining `f`; after `moves` language-type changes with no
    /// caller, `f`'s earlier slots are retired and it holds a fresh one.
    pub(super) fn table_with_f_after(moves: usize) -> SessionSymbolTable {
        let mut table = SessionSymbolTable::new_with_params(m("dep"));
        concrete(&mut table, "f", &[]);
        for _ in 0..moves {
            table.retire_abi_changing(&Symbol::from("f")).unwrap();
            concrete(&mut table, "f", &[]);
        }
        table
    }

    /// Install a minted `(id Int)` instance and the synthetic `__expr`.
    fn add_restaged_slots(table: &mut SessionSymbolTable) {
        concrete(table, crate::worker::SYNTHETIC_EXPR_WRAPPER, &[]);
        let template = FQSymbol {
            module: m("dep"),
            symbol: Symbol::from("id"),
        };
        let template_scheme = Scheme {
            type_vars: vec![0],
            constraints: Default::default(),
            ty: Type::Fn(vec![Type::Var(0)], Box::new(Type::Int)),
        };
        let link = InstanceLink::from_type_args(
            CallableTarget::Binding(template),
            vec![ConcreteType::Int],
        );
        let name = link.instance_key(&template_scheme).unwrap();
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
            name,
            params: Vec::new(),
            body: cranelisp_types::test_support::lenient_from_expr(
                &ast.body,
                &Default::default(),
                &Default::default(),
                &Default::default(),
            ),
            span: Span::SYNTHETIC,
            mode_summary: None,
        };
        table
            .install_instance(
                link,
                Scheme {
                    type_vars: Vec::new(),
                    constraints: Default::default(),
                    ty: Type::Fn(vec![Type::Int], Box::new(Type::Int)),
                },
                Vec::new(),
                None,
                0,
                CallableOrigin::Plain,
                Realization::Body { view, code: None },
                Some(ast),
                Vec::new(),
                Visibility::Public,
            )
            .unwrap();
    }

    // spec: design/int/int.md §7.6.3 — the current key of an unchanged source
    // and layout matches the recorded key; a moved authored slot with the
    // same source does not, so an importer compiled against the old slot
    // misses (ACT-1052).
    #[test]
    fn a_moved_authored_slot_changes_the_key_and_an_unchanged_one_does_not() {
        let recorded = AuthoredSlotLayout::of(&table_with_f_after(0)).derivation_key(&hash());
        let project = Project::new();
        project.tables.insert(m("dep"), table_with_f_after(0));
        assert_eq!(project.current_key(), Some(recorded.clone()));

        project.tables.insert(m("dep"), table_with_f_after(2));
        assert_ne!(project.current_key(), Some(recorded));
    }

    // spec: design/int/int.md §7.6.3 — the stored-layout memo ends with the
    // `.meta` it decoded: a session overwrite of a member it holds no table
    // for, as the index worker writes one, is what the next validation reads.
    #[test]
    fn a_stored_meta_overwrite_is_read_by_the_next_validation() {
        let project = Project::new();
        let cache = ObjectCache::new(Some(project.cache_dir.path().to_path_buf()), None);
        let (meta, _) =
            cranelisp_backend::cache::module_cache_path(project.cache_dir.path(), &m("dep"));
        std::fs::create_dir_all(meta.parent().unwrap()).unwrap();
        let sources = ModuleSources::new(project.root.path(), &[], &project.tables, &cache);
        for moves in [0, 2] {
            let table = table_with_f_after(moves);
            cache.write_meta(&m("dep"), &table).unwrap();
            assert_eq!(
                sources.current_key(&m("dep")),
                Some(AuthoredSlotLayout::of(&table).derivation_key(&hash())),
                "after {moves} moves"
            );
        }
    }

    /// A cache holding `dep`'s stored `.meta` written from `table`, and the
    /// path of that file.
    pub(super) fn cache_storing(
        project: &Project,
        table: &SessionSymbolTable,
    ) -> (ObjectCache, PathBuf) {
        let cache = ObjectCache::new(Some(project.cache_dir.path().to_path_buf()), None);
        let (meta, _) =
            cranelisp_backend::cache::module_cache_path(project.cache_dir.path(), &m("dep"));
        std::fs::create_dir_all(meta.parent().unwrap()).unwrap();
        cache.write_meta(&m("dep"), table).unwrap();
        (cache, meta)
    }

    fn stored_layout_of(
        module: Option<cranelisp_backend::cache::CachedModule>,
    ) -> AuthoredSlotLayout {
        AuthoredSlotLayout::of(&module.expect("a stored module").symbol_table)
    }

    // spec: design/int/int.md §7.6.3 — validation's read of a member's stored
    // layout and the member's restore share one decode: once validation has
    // read it, the restore takes that value without reading the file, and
    // the value is taken, not kept.
    #[test]
    fn a_validated_member_restores_from_the_decode_validation_made() {
        let project = Project::new();
        let (cache, meta) = cache_storing(&project, &table_with_f_after(1));
        let sources = ModuleSources::new(project.root.path(), &[], &project.tables, &cache);
        assert!(sources.current_key(&m("dep")).is_some());

        std::fs::remove_file(&meta).unwrap();
        assert_eq!(
            stored_layout_of(cache.stored_module(&m("dep"))),
            AuthoredSlotLayout::of(&table_with_f_after(1))
        );
        assert!(cache.stored_module(&m("dep")).is_none());
    }

    // spec: design/int/int.md §7.6.3 — a rewrite of the `.meta` between
    // validation and restore ends the held decode; the restore reads the new
    // file.
    #[test]
    fn a_meta_rewritten_after_validation_is_what_the_restore_reads() {
        let project = Project::new();
        let (cache, _) = cache_storing(&project, &table_with_f_after(0));
        assert!(cache.stored_layout(&m("dep")).is_some());

        cache.write_meta(&m("dep"), &table_with_f_after(2)).unwrap();
        assert_eq!(
            stored_layout_of(cache.stored_module(&m("dep"))),
            AuthoredSlotLayout::of(&table_with_f_after(2))
        );
    }

    // spec: design/int/int.md §7.6.3 — a member loaded fresh after validation
    // holds no decoded value: its fresh registration ends the hold.
    #[test]
    fn a_member_loaded_fresh_after_validation_holds_no_decode() {
        let project = Project::new();
        let (cache, meta) = cache_storing(&project, &table_with_f_after(0));
        assert!(cache.stored_layout(&m("dep")).is_some());

        cache.record_source_hash(&m("dep"), hash());
        std::fs::remove_file(&meta).unwrap();
        assert!(cache.stored_module(&m("dep")).is_none());
    }

    // spec: design/int/int.md §7.6.3 — minted instances and `__expr` are
    // restaged by every recompile, so their slots are not part of the layout.
    #[test]
    fn minted_instances_and_the_expression_wrapper_are_not_layout() {
        let plain = table_with_f_after(0);
        let mut restaged = table_with_f_after(0);
        add_restaged_slots(&mut restaged);
        assert!(restaged.all_symbols().count() > plain.all_symbols().count());
        assert_eq!(
            AuthoredSlotLayout::of(&restaged),
            AuthoredSlotLayout::of(&plain)
        );
    }

    // spec: design/int/int.md §7.6.3 — a member being built fresh holds an
    // empty live table, which matches no recorded layout; a member with no
    // live table and no stored `.meta` has no key.
    #[test]
    fn a_fresh_build_and_an_absent_member_are_misses() {
        let recorded = AuthoredSlotLayout::of(&table_with_f_after(0)).derivation_key(&hash());
        let project = Project::new();
        assert_eq!(project.current_key(), None, "no live table, no .meta");

        project
            .tables
            .insert(m("dep"), SessionSymbolTable::new_with_params(m("dep")));
        assert_ne!(project.current_key(), Some(recorded));
    }

    // spec: design/int/int.md §7.6.3 — a key never equals a bare source hash,
    // so a record written before keys carried the layout is a miss.
    #[test]
    fn a_key_is_never_a_bare_source_hash() {
        let project = Project::new();
        project.tables.insert(m("dep"), table_with_f_after(0));
        assert_ne!(project.current_key(), Some(hash()));
    }
}

// ---------------------------------------------------------------------------
// One generation beside an entry (`design/int/int.md` §7.7, ACT-1083)
// ---------------------------------------------------------------------------

mod one_generation {
    use super::slot_layout::{Project, cache_storing, table_with_f_after};
    use super::*;
    use crate::cache::StoredObject;

    fn object_path(project: &Project) -> PathBuf {
        cranelisp_backend::cache::module_cache_path(project.cache_dir.path(), &m("dep")).1
    }

    fn restored_object(cache: &ObjectCache) -> StoredObject {
        StoredObject::of(&cache.stored_module(&m("dep")).expect("a stored module"))
    }

    // spec: design/int/int.md §7.7 — every `.meta` write retires the module's
    // object first, so a new `.meta` never stands beside an older `.o`.
    #[test]
    fn a_meta_write_retires_the_modules_object() {
        let project = Project::new();
        let (cache, _) = cache_storing(&project, &table_with_f_after(0));
        std::fs::write(object_path(&project), "the earlier generation's object").unwrap();
        assert_eq!(restored_object(&cache), StoredObject::Load);

        cache.write_meta(&m("dep"), &table_with_f_after(0)).unwrap();
        assert!(!object_path(&project).exists());
    }

    // spec: design/int/int.md §7.7 — when the object pass writes no `.o` after
    // its `.meta` (its codegen or `.o` write failed), the `.meta` has codegen
    // targets and no object, which the restore's object gate misses whatever
    // entry keys it.
    #[test]
    fn a_meta_left_without_its_object_is_a_miss_at_restore() {
        let project = Project::new();
        let (cache, _) = cache_storing(&project, &table_with_f_after(0));
        std::fs::write(object_path(&project), "the earlier generation's object").unwrap();

        cache.write_meta(&m("dep"), &table_with_f_after(2)).unwrap();
        assert_eq!(restored_object(&cache), StoredObject::Missing);
    }

    // spec: design/int/int.md §7.7 — an object that cannot be removed stops
    // the write: the earlier `.meta` and `.o` stand as one generation.
    #[test]
    fn an_object_that_cannot_be_removed_stops_the_meta_write() {
        let project = Project::new();
        let (cache, meta) = cache_storing(&project, &table_with_f_after(0));
        std::fs::create_dir(object_path(&project)).unwrap();

        assert!(cache.write_meta(&m("dep"), &table_with_f_after(2)).is_err());
        assert_eq!(
            AuthoredSlotLayout::of(&cranelisp_backend::cache::serialize::load_meta(&meta).unwrap()),
            AuthoredSlotLayout::of(&table_with_f_after(0)),
            "the earlier `.meta` stands"
        );
    }
}

// ---------------------------------------------------------------------------
// Reference edges (`design/int/int.md` §7.6.4, row B10 step 1)
// ---------------------------------------------------------------------------

mod reference_edges {
    use super::callee_modules::concrete;
    use super::*;

    fn edges(table: &SessionSymbolTable, prelude: PreludeEdge) -> Vec<String> {
        reference_edges(&m("m"), table, prelude)
            .iter()
            .map(ToString::to_string)
            .collect()
    }

    fn tables_with(modules: &[&str]) -> dashmap::DashMap<ModuleFullPath, SessionSymbolTable> {
        let tables = dashmap::DashMap::new();
        for module in modules {
            tables.insert(m(module), SessionSymbolTable::new_with_params(m(module)));
        }
        tables
    }

    // spec: spec/08-modules.md §8.3.7 — a null import loads nothing; a use
    // through it makes its target a callee module.
    #[test]
    fn a_null_import_is_an_edge_only_through_a_use() {
        let mut table = SessionSymbolTable::new_with_params(m("m"));
        table.imports = vec![
            import("n", None, ImportNames::None),
            import("a", Some("aa"), ImportNames::None),
        ];
        assert!(
            edges(&table, PreludeEdge::Absent).is_empty(),
            "no use: {:?}",
            edges(&table, PreludeEdge::Absent)
        );
        concrete(&mut table, "g", &["n"]);
        assert_eq!(edges(&table, PreludeEdge::Absent), ["n"], "qualified use");
    }

    // spec: spec/08-modules.md §8.11.2 item 1 — an import named through a
    // declared child is an edge to the child; the declaration alone is none.
    #[test]
    fn an_import_named_through_a_declared_child_is_an_edge_to_the_child() {
        let mut table = SessionSymbolTable::new_with_params(m("m"));
        table.submodules = vec![child("q"), child("unused")];
        table.imports = vec![named_import("q")];
        table.exports = vec![reexport("r")];
        assert_eq!(edges(&table, PreludeEdge::Absent), ["m.q", "r"]);
    }

    // spec: design/int/int.md §7.6 *Prelude edge* — the fallback bit and a
    // session prelude table together, and neither alone.
    #[test]
    fn the_prelude_is_an_edge_with_the_fallback_bit_and_a_prelude_table() {
        let table = SessionSymbolTable::new_with_params(m("m"));
        let with_prelude = tables_with(&["prelude"]);
        let without_prelude = tables_with(&["m"]);
        let cases = [
            (
                "bit and table",
                PreludeEdge::of(true, &with_prelude),
                vec!["prelude"],
            ),
            (
                "table, no bit",
                PreludeEdge::of(false, &with_prelude),
                vec![],
            ),
            (
                "bit, no table",
                PreludeEdge::of(true, &without_prelude),
                vec![],
            ),
        ];
        for (case, prelude, expected) in cases {
            assert_eq!(edges(&table, prelude), expected, "{case}");
        }
    }

    // spec: design/arch/tracing.md §5.1 — a platform module the module calls
    // is a reference edge, though the record excludes it; the module is not.
    #[test]
    fn a_platform_callee_module_is_an_edge_and_the_module_itself_is_not() {
        let mut table = SessionSymbolTable::new_with_params(m("m"));
        concrete(&mut table, "g", &["platform.stdio", "m"]);
        table.imports = vec![named_import("m")];
        assert_eq!(edges(&table, PreludeEdge::Absent), ["platform.stdio"]);
    }
}

// ---------------------------------------------------------------------------
// The covered set (`design/int/int.md` §7.6.4, row B10 step 2)
// ---------------------------------------------------------------------------

mod covered_set {
    use super::callee_modules::concrete;
    use super::*;

    fn table(module: &str) -> SessionSymbolTable {
        SessionSymbolTable::new_with_params(m(module))
    }

    /// `e` imports `u` and calls into `macros`; `u` calls `x`; `e` declares a
    /// child `c` it never imports, which has a table of its own.
    fn chain() -> dashmap::DashMap<ModuleFullPath, SessionSymbolTable> {
        let tables = dashmap::DashMap::new();
        let mut e = table("e");
        e.imports = vec![named_import("u")];
        e.submodules = vec![child("c")];
        concrete(&mut e, "run", &["macros"]);
        let mut u = table("u");
        concrete(&mut u, "f", &["x"]);
        for (module, table) in [
            ("e", e),
            ("u", u),
            ("x", table("x")),
            ("e.c", table("e.c")),
            ("primitives", table("primitives")),
            ("macros", table("macros")),
        ] {
            tables.insert(m(module), table);
        }
        tables
    }

    const PLANNING: UnpublishedPrelude = UnpublishedPrelude::ReadAsItStands;
    const OBJECT_PASS: UnpublishedPrelude = UnpublishedPrelude::Answer;

    fn covered(modules: &[&str]) -> CoveredSet {
        CoveredSet::Covered(modules.iter().map(|module| m(module)).collect())
    }

    // spec: design/arch/tracing.md §5.1 — the closure from the form's module,
    // plus `primitives`, less the module itself, `macros` and a declared child
    // the module does not import.
    #[test]
    fn the_covered_set_is_the_closure_plus_primitives() {
        let set = covered_set(&m("e"), &chain(), &Default::default(), PLANNING, |_| true);
        assert_eq!(set, covered(&["primitives", "u", "x"]));
    }

    // spec: design/int/int.md §7.6.4 *Settled members* — the first member that
    // has not published is answered, and one with no table is unpublished.
    #[test]
    fn an_unpublished_or_absent_member_is_answered() {
        let tables = chain();
        let unpublished = covered_set(&m("e"), &tables, &Default::default(), PLANNING, |module| {
            module.as_ref() != "x"
        });
        assert_eq!(unpublished, CoveredSet::Unpublished(m("x")));
        tables.remove(&m("x"));
        let absent = covered_set(&m("e"), &tables, &Default::default(), PLANNING, |_| true);
        assert_eq!(absent, CoveredSet::Unpublished(m("x")));
    }

    // spec: design/int/int.md §7.6.4 *Settled members* item 2 — an unpublished
    // prelude is covered as it stands and its edges are not followed; a
    // published one is walked like any member.
    #[test]
    fn an_unpublished_prelude_is_read_as_it_stands() {
        let tables = chain();
        let mut prelude = table("prelude");
        prelude.imports = vec![named_import("p")];
        tables.insert(m("prelude"), prelude);
        tables.insert(m("p"), table("p"));
        let fallback = cranelisp_typecheck::PreludeFallback::default();
        fallback.insert(m("e"), true);
        let unpublished = covered_set(&m("e"), &tables, &fallback, PLANNING, |module| {
            !matches!(module.as_ref(), "prelude" | "p")
        });
        assert_eq!(unpublished, covered(&["prelude", "primitives", "u", "x"]));
        let published = covered_set(&m("e"), &tables, &fallback, PLANNING, |_| true);
        assert_eq!(
            published,
            covered(&["p", "prelude", "primitives", "u", "x"])
        );
    }

    // spec: design/int/int.md §7.6.4 *The object pass waits* — the walk the
    // object pass asks for answers an unpublished prelude like any member, and
    // reads a published one as commit planning does.
    #[test]
    fn the_object_pass_walk_answers_an_unpublished_prelude() {
        let tables = chain();
        let mut prelude = table("prelude");
        prelude.imports = vec![named_import("p")];
        tables.insert(m("prelude"), prelude);
        tables.insert(m("p"), table("p"));
        let fallback = cranelisp_typecheck::PreludeFallback::default();
        fallback.insert(m("e"), true);
        let unpublished = covered_set(&m("e"), &tables, &fallback, OBJECT_PASS, |module| {
            module.as_ref() != "prelude"
        });
        assert_eq!(unpublished, CoveredSet::Unpublished(m("prelude")));
        let published = covered_set(&m("e"), &tables, &fallback, OBJECT_PASS, |_| true);
        assert_eq!(
            published,
            covered(&["p", "prelude", "primitives", "u", "x"])
        );
    }
}
