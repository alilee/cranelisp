//! The module cache's dependency record and the current-hash source that
//! validates it (`design/int/int.md` §7.6).
//!
//! A module's manifest entry records the source hash of every module in its
//! transitive dependency closure, as compiled against. Under-recording is the
//! silent failure — a stale artefact restores — so a record is written only
//! from fully settled session state, and never as an empty or partial
//! stand-in.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::path::{Path, PathBuf};

use cranelisp_types::{
    CodeStore, ExportSpec, ImportSpec, LinkerStore, ModDecl, ModuleFullPath, SymbolTable,
};

use crate::callee_edges::binding_callees;
use crate::code::SessionSymbolTable;
use crate::session_v4::SharedState;

const PRELUDE: &str = "prelude";

/// Source hash of every module in one module's transitive dependency closure,
/// keyed by module path. The module itself is never a member.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct DependencyRecord(BTreeMap<ModuleFullPath, String>);

impl DependencyRecord {
    /// The record a manifest entry stores (`CachedModuleRef::dependency_hashes`).
    pub(crate) fn from_manifest(stored: &HashMap<String, String>) -> Self {
        DependencyRecord(
            stored
                .iter()
                .map(|(module, hash)| (ModuleFullPath::from(module.as_str()), hash.clone()))
                .collect(),
        )
    }

    pub(crate) fn into_manifest(self) -> HashMap<String, String> {
        self.0
            .into_iter()
            .map(|(module, hash)| (module.to_string(), hash))
            .collect()
    }

    pub(crate) fn members(&self) -> impl Iterator<Item = (&ModuleFullPath, &str)> {
        self.0.iter().map(|(module, hash)| (module, hash.as_str()))
    }
}

/// A module's direct dependency edges: every import (including alias-only and
/// null imports), every re-export target, every declared child, the prelude
/// when the module's prelude-fallback bit is set, and every callee module.
/// Compiler-owned modules are excluded — the build identity keys `primitives`
/// and `macros`, and platform modules are §7.6 *Known gaps* 5.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ModuleEdges(BTreeSet<ModuleFullPath>);

impl ModuleEdges {
    /// The declared edges alone, for a writer whose table does not carry the
    /// structural declarations.
    pub(crate) fn of_declarations(
        module: &ModuleFullPath,
        imports: &[ImportSpec],
        exports: &[ExportSpec],
        children: &[ModDecl],
        prelude_fallback: bool,
    ) -> Self {
        let targets = imports
            .iter()
            .map(|spec| spec.module_path.clone())
            .chain(exports.iter().map(|spec| spec.module_path.clone()))
            .chain(
                children
                    .iter()
                    .map(|decl| ModuleFullPath::from(format!("{module}.{}", decl.name))),
            )
            .chain(prelude_fallback.then(|| ModuleFullPath::from(PRELUDE)));
        ModuleEdges(targets.filter(|target| is_edge(module, target)).collect())
    }

    pub(crate) fn of_table(
        module: &ModuleFullPath,
        table: &SessionSymbolTable,
        prelude_fallback: bool,
    ) -> Self {
        Self::of_declarations(
            module,
            &table.imports,
            &table.exports,
            &table.submodules,
            prelude_fallback,
        )
        .with_callee_modules(module, table)
    }

    pub(crate) fn with_callee_modules(
        mut self,
        module: &ModuleFullPath,
        table: &SessionSymbolTable,
    ) -> Self {
        self.0.extend(callee_modules(module, table));
        self
    }
}

/// The module of every callee recorded on `table`'s callables, overload arms
/// and macro clauses (§7.6.1), other than `module` itself and compiler-owned
/// modules. Generic over the code store so a decoded table can be read before
/// it is installed.
pub(crate) fn callee_modules<C: CodeStore, L: LinkerStore>(
    module: &ModuleFullPath,
    table: &SymbolTable<C, L>,
) -> BTreeSet<ModuleFullPath> {
    table
        .all_symbols()
        .flat_map(|(_, binding)| binding_callees(binding))
        .map(|callee| &callee.module)
        .filter(|target| is_edge(module, target))
        .cloned()
        .collect()
}

fn is_edge(module: &ModuleFullPath, target: &ModuleFullPath) -> bool {
    target != module && !is_compiler_owned(target)
}

pub(crate) fn is_compiler_owned(module: &ModuleFullPath) -> bool {
    let path: &str = module.as_ref();
    path == "primitives" || path == "macros" || path.starts_with("platform.")
}

/// Whether a record could be built from settled session state.
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum RecordOutcome {
    Settled(DependencyRecord),
    /// `member` is not loaded, not yet typechecked, or has no stashed hash.
    /// No entry is written until the record settles.
    Unsettled {
        member: ModuleFullPath,
    },
}

/// Build `module`'s record from the versions this session loaded (Principle
/// 26): a restored member contributes itself and its own validated record
/// without its table being walked; a fresh member contributes its stashed hash
/// and the edges of its typechecked table.
///
/// A prelude edge whose table the session never loaded is dropped: no prelude
/// file resolved, so the fallback had no table to consult.
pub(crate) fn build_dependency_record(
    shared: &SharedState,
    module: &ModuleFullPath,
    edges: ModuleEdges,
) -> RecordOutcome {
    let prelude = ModuleFullPath::from(PRELUDE);
    let mut walked: BTreeMap<ModuleFullPath, String> = BTreeMap::new();
    let mut inherited: BTreeMap<ModuleFullPath, String> = BTreeMap::new();
    let mut pending: Vec<ModuleFullPath> = edges.0.into_iter().collect();

    while let Some(member) = pending.pop() {
        if member == *module || walked.contains_key(&member) {
            continue;
        }
        if member == prelude && !shared.symbol_tables.contains_key(&prelude) {
            continue;
        }
        match shared.cache.loaded_source(&member) {
            Some(LoadedSource::Restored {
                source_hash,
                record,
            }) => {
                for (inner, hash) in record.0 {
                    inherited.entry(inner).or_insert(hash);
                }
                walked.insert(member, source_hash);
            }
            Some(LoadedSource::Fresh { source_hash }) => {
                let typechecked = shared
                    .scheduler
                    .module_pool(&member)
                    .is_some_and(|pool| pool.is_terminal_typecheck());
                let Some(table) = shared.symbol_tables.get(&member).filter(|_| typechecked) else {
                    return RecordOutcome::Unsettled { member };
                };
                let fallback = shared.prelude_fallback.get(&member).is_some_and(|bit| *bit);
                pending.extend(ModuleEdges::of_table(&member, &table, fallback).0);
                walked.insert(member, source_hash);
            }
            None => return RecordOutcome::Unsettled { member },
        }
    }

    // A member reached through a walked edge keeps the hash this session
    // loaded; a restored member's record fills in the rest.
    inherited.remove(module);
    inherited.extend(walked);
    RecordOutcome::Settled(DependencyRecord(inherited))
}

/// A manifest entry whose record was unsettled when its module was written.
#[derive(Debug, Clone)]
pub(crate) struct DeferredEntry {
    pub(crate) module: ModuleFullPath,
    pub(crate) source_hash: String,
    pub(crate) edges: ModuleEdges,
}

/// Write `module`'s manifest entry if its record settles. Otherwise defer it
/// to [`record_deferred_entries`]; an entry still unsettled when the session
/// ends is never written, so the next session rebuilds `module`. Every cache
/// writer goes through here.
pub(crate) fn record_manifest_entry(
    shared: &SharedState,
    module: &ModuleFullPath,
    source_hash: String,
    edges: ModuleEdges,
) {
    match build_dependency_record(shared, module, edges.clone()) {
        RecordOutcome::Settled(record) => shared.cache.record_compiled(module, source_hash, record),
        RecordOutcome::Unsettled { member } => {
            if std::env::var("CRANELISP_MODULE_TRACE").is_ok() {
                eprintln!("module-trace: manifest entry for {module} deferred: {member} unsettled");
            }
            shared.cache.defer_entry(DeferredEntry {
                module: module.clone(),
                source_hash,
                edges,
            });
        }
    }
}

/// Retry the entries deferred because a member was still settling — a declared
/// child that imports its parent is written while the parent still waits on
/// it. Runs before the manifest flush, once object codegen has drained.
pub(crate) fn record_deferred_entries(shared: &SharedState) {
    for entry in shared.cache.take_deferred_entries() {
        record_manifest_entry(shared, &entry.module, entry.source_hash, entry.edges);
    }
}

/// How the session holds a loaded module's source, for the record builder.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum LoadedSource {
    Fresh {
        source_hash: String,
    },
    /// Restored from the cache under `record`, which validated against the
    /// current sources when it was restored.
    Restored {
        source_hash: String,
        record: DependencyRecord,
    },
}

impl LoadedSource {
    pub(crate) fn source_hash(&self) -> &str {
        match self {
            LoadedSource::Fresh { source_hash } | LoadedSource::Restored { source_hash, .. } => {
                source_hash
            }
        }
    }
}

/// The source each recorded member would load from now, resolved exactly as
/// the loading handlers resolve it.
pub(crate) struct ModuleSources<'a> {
    project_root: &'a Path,
    lib_dirs: &'a [PathBuf],
}

impl<'a> ModuleSources<'a> {
    pub(crate) fn new(project_root: &'a Path, lib_dirs: &'a [PathBuf]) -> Self {
        ModuleSources {
            project_root,
            lib_dirs,
        }
    }

    /// `None` when the member cannot be resolved or read, which is a miss.
    pub(crate) fn current_hash(&self, module: &ModuleFullPath) -> Option<String> {
        let file = if module.as_ref() == PRELUDE {
            crate::session_setup::resolve_prelude(self.project_root, self.lib_dirs)
        } else {
            crate::pipeline::resolve_module_file(module, self.project_root, self.lib_dirs)
        }?;
        let source = std::fs::read_to_string(file).ok()?;
        Some(cranelisp_backend::cache::manifest::hash_source(&source))
    }
}

#[cfg(test)]
mod tests;
