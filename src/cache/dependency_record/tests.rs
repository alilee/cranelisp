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
        self.shared
            .scheduler
            .register_module_cached(m(module), HashSet::new());
        self.shared
            .cache
            .record_source_hash(&m(module), hash.to_string());
    }

    /// A cache restore that validated under `record`; its table's imports
    /// are deliberately unloaded, so walking them would be unsettled.
    fn restored(&self, module: &str, hash: &str, record: &[(&str, &str)]) {
        self.install_table(module, &["never-loaded"]);
        self.shared
            .scheduler
            .register_module_cached(m(module), HashSet::new());
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
    session
        .shared
        .scheduler
        .register_module_cached(m("d"), HashSet::new());
    assert_eq!(
        session.build("m", &["d"]),
        RecordOutcome::Unsettled { member: m("d") }
    );
}
