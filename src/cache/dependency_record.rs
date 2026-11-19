//! The module cache's dependency record and the current-hash source that
//! validates it (`design/int/int.md` §7.6).
//!
//! A module's manifest entry records the source hash of every module in its
//! transitive dependency closure, as compiled against. Under-recording is the
//! silent failure — a stale artefact restores — so a record is written only
//! from fully settled session state, and never as an empty or partial
//! stand-in.

use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};
use std::path::{Path, PathBuf};

use cranelisp_types::{
    CallableTarget, CodeStore, ExportSpec, ImportSpec, Life, LinkerStore, ModDecl, ModuleFullPath,
    SymbolTable,
};

use crate::callee_edges::binding_callees;
use crate::code::SessionSymbolTable;
use crate::imports::{DeclaredChildren, declared_child_path, names_load};
use crate::session_v4::SharedState;

const PRELUDE: &str = "prelude";
const PRIMITIVES: &str = "primitives";
const MACROS: &str = "macros";

/// The derivation key of every module in one module's transitive dependency
/// closure, keyed by module path (`design/int/int.md` §7.6.3). The module
/// itself is never a member.
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

/// The slot assignments another module's object can embed: each codegen
/// target of a table and its GOT slot, excluding minted instances and the
/// synthetic `__expr` — the slots the entry preload releases because the
/// from-source recompile restages them (`design/int/int.md` §7.6.3). Retired
/// slots are not part of it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct AuthoredSlotLayout(BTreeMap<String, usize>);

impl AuthoredSlotLayout {
    pub(crate) fn of<C: CodeStore, L: LinkerStore>(table: &SymbolTable<C, L>) -> Self {
        let synthetic = crate::worker::SYNTHETIC_EXPR_WRAPPER;
        let mut ordinals: BTreeMap<String, usize> = BTreeMap::new();
        let mut layout = BTreeMap::new();
        for (target, arm) in table.codegen_targets() {
            let (owner, kind) = match &target {
                CallableTarget::Binding(owner) => (owner, "fn"),
                CallableTarget::OverloadArm { owner, .. } => (owner, "arm"),
                CallableTarget::MacroClause { owner, .. } => (owner, "clause"),
                _ => continue,
            };
            if owner.symbol.as_ref() == synthetic {
                continue;
            }
            let Life::Concrete {
                slot, minted_from, ..
            } = &arm.life
            else {
                continue;
            };
            if minted_from.is_some() {
                continue;
            }
            // Arm and clause ids are generation-local; their order within
            // the declaration is what a rebuild of the same text reproduces.
            let owner_key = format!("{kind} {owner}");
            let ordinal = ordinals.entry(owner_key.clone()).or_default();
            layout.insert(format!("{owner_key} #{ordinal}"), slot.index());
            *ordinal += 1;
        }
        AuthoredSlotLayout(layout)
    }

    /// The member's derivation key under this layout. Its form is private and
    /// never equals a bare source hash, so a record written before keys
    /// carried the layout is a miss.
    pub(crate) fn derivation_key(&self, source_hash: &str) -> String {
        let rendered = self
            .0
            .iter()
            .map(|(target, slot)| format!("{target}={slot}\n"))
            .collect::<String>();
        format!(
            "{source_hash}+slots:{}",
            cranelisp_backend::cache::manifest::hash_source(&rendered)
        )
    }
}

/// A module's direct dependency edges: every import (including alias-only and
/// null imports), every re-export target, every declared child, the prelude
/// when the module's prelude-fallback bit is set, every callee module and
/// every lookup dependency. Compiler-owned modules are excluded — the build
/// identity keys `primitives` and `macros`, and platform modules are §7.6
/// *Known gaps* 5.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ModuleEdges(BTreeSet<ModuleFullPath>);

impl ModuleEdges {
    /// The declared edges alone. Import and re-export targets resolve against
    /// `children` (`design/int/int.md` §6.9).
    fn of_declarations(
        module: &ModuleFullPath,
        imports: &[ImportSpec],
        exports: &[ExportSpec],
        children: &[ModDecl],
        prelude_fallback: bool,
    ) -> Self {
        let declared = DeclaredChildren::of(module, children);
        let targets = imports
            .iter()
            .map(|spec| declared.resolve(&spec.module_path))
            .chain(
                exports
                    .iter()
                    .map(|spec| declared.resolve(&spec.module_path)),
            )
            .chain(
                children
                    .iter()
                    .map(|decl| declared_child_path(module, decl.name.as_ref())),
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
        .with_recorded_edges(module, table)
    }

    fn with_recorded_edges(mut self, module: &ModuleFullPath, table: &SessionSymbolTable) -> Self {
        self.0.extend(recorded_edges(module, table));
        self
    }
}

/// The edges `table` records from its compile: callee modules and lookup
/// dependencies (§7.6.1, §7.6.2), filtered like every other edge. Generic
/// over the code store so a decoded table can be read before it is installed.
pub(crate) fn recorded_edges<C: CodeStore, L: LinkerStore>(
    module: &ModuleFullPath,
    table: &SymbolTable<C, L>,
) -> BTreeSet<ModuleFullPath> {
    let mut edges = callee_modules(module, table);
    edges.extend(
        table
            .lookup_dependencies()
            .filter(|target| is_edge(module, target))
            .cloned(),
    );
    edges
}

/// The module each `import` and `export` of `table` loads, resolved through its
/// declared children (`design/int/int.md` §6.9). A name-less spec loads nothing
/// (spec §8.3.7, §8.4.0); `names_load` is that rule's one source.
fn loading_spec_targets<C: CodeStore, L: LinkerStore>(
    module: &ModuleFullPath,
    table: &SymbolTable<C, L>,
) -> impl Iterator<Item = ModuleFullPath> {
    let declared = DeclaredChildren::of(module, &table.submodules);
    let imports = table
        .imports
        .iter()
        .filter(|spec| names_load(&spec.names))
        .map(|spec| &spec.module_path);
    let exports = table
        .exports
        .iter()
        .filter(|spec| names_load(&spec.names))
        .map(|spec| &spec.module_path);
    imports
        .chain(exports)
        .map(move |spelling| declared.resolve(spelling))
}

/// Whether a module's prelude edge exists: its fallback bit is on and the
/// session holds a prelude table, the record's prelude rule (§7.6, *Prelude
/// edge*).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PreludeEdge {
    Present,
    Absent,
}

impl PreludeEdge {
    pub(crate) fn of(
        prelude_fallback: bool,
        tables: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
    ) -> Self {
        if prelude_fallback && tables.contains_key(&ModuleFullPath::from(PRELUDE)) {
            PreludeEdge::Present
        } else {
            PreludeEdge::Absent
        }
    }
}

/// A module's reference edges: the modules its image makes a load
/// (`design/int/int.md` §7.6.4). They are each `import` and `export` that
/// loads, resolved through its declared children; every callee module,
/// compiler-owned and platform modules included; and the prelude when
/// `prelude` is present. Never the module itself; a `mod` declaration alone
/// adds no edge. Generic over the code store so a decoded table and a session
/// table answer alike.
pub(crate) fn reference_edges<C: CodeStore, L: LinkerStore>(
    module: &ModuleFullPath,
    table: &SymbolTable<C, L>,
    prelude: PreludeEdge,
) -> BTreeSet<ModuleFullPath> {
    let mut edges: BTreeSet<ModuleFullPath> = loading_spec_targets(module, table).collect();
    edges.extend(every_callee_module(table).cloned());
    if prelude == PreludeEdge::Present {
        edges.insert(ModuleFullPath::from(PRELUDE));
    }
    edges.remove(module);
    edges
}

/// A covered-set derivation's result (`design/int/int.md` §7.6.4), or the
/// member that keeps it from being settled.
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum Covered<T> {
    Covered(T),
    /// The first member, in walk order, that has not yet published a
    /// generation. A set read through it would depend on scheduling.
    Unpublished(ModuleFullPath),
}

/// The modules a trace form in a root module covers besides the root.
pub(crate) type CoveredSet = Covered<BTreeSet<ModuleFullPath>>;

/// A codegen batch's targets, each paired with the covered set of its module
/// of origin (`design/int/int.md` §7.6.4, *The form's home*).
///
/// A target's module of origin is its arm's template module, and the batch's
/// module for an authored arm. One set is held per module of origin, the
/// batch's module always among them, and each set lists its own module of
/// origin, because the backend adds none (row B10-C2).
#[derive(Debug)]
pub(crate) struct CoveredBatch {
    targets: Vec<CallableTarget>,
    /// Parallel to `targets`; every entry is a key of `sets`.
    origins: Vec<ModuleFullPath>,
    sets: BTreeMap<ModuleFullPath, BTreeSet<ModuleFullPath>>,
}

impl CoveredBatch {
    /// Derive one covered set per module of origin among `targets` from
    /// `tables`, each by [`covered_set`] with the same prelude rule and
    /// published predicate. `root`'s table answers each target's origin.
    pub(crate) fn derive(
        root: &ModuleFullPath,
        targets: Vec<CallableTarget>,
        tables: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
        prelude_fallback: &cranelisp_typecheck::PreludeFallback,
        unpublished_prelude: UnpublishedPrelude,
        published: impl Fn(&ModuleFullPath) -> bool,
    ) -> Covered<Self> {
        let origins: Vec<ModuleFullPath> = {
            let table = tables.get(root);
            targets
                .iter()
                .map(|target| {
                    table
                        .as_deref()
                        .and_then(|table| table.callable_target(target))
                        .and_then(|arm| arm.template_module())
                        .unwrap_or(root)
                        .clone()
                })
                .collect()
        };
        let mut sets = BTreeMap::new();
        for origin in std::iter::once(root).chain(&origins) {
            if sets.contains_key(origin) {
                continue;
            }
            let mut set = match covered_set(
                origin,
                tables,
                prelude_fallback,
                unpublished_prelude,
                &published,
            ) {
                Covered::Covered(set) => set,
                Covered::Unpublished(member) => return Covered::Unpublished(member),
            };
            set.insert(origin.clone());
            sets.insert(origin.clone(), set);
        }
        Covered::Covered(CoveredBatch {
            targets,
            origins,
            sets,
        })
    }

    pub(crate) fn targets(&self) -> &[CallableTarget] {
        &self.targets
    }

    /// Each target paired with the covered set of its module of origin.
    pub(crate) fn codegen_targets(&self) -> Vec<cranelisp_backend::CodegenTarget<'_>> {
        self.pairs()
            .map(|(target, set)| cranelisp_backend::CodegenTarget::new(target, set))
            .collect()
    }

    fn pairs(&self) -> impl Iterator<Item = (&CallableTarget, &BTreeSet<ModuleFullPath>)> {
        self.targets
            .iter()
            .zip(&self.origins)
            .map(|(target, origin)| {
                let Some(set) = self.sets.get(origin) else {
                    unreachable!("invariant: every module of origin has a derived covered set")
                };
                (target, set)
            })
    }

    /// The pairs [`Self::codegen_targets`] builds.
    #[cfg(test)]
    pub(crate) fn paired(&self) -> Vec<(&CallableTarget, &BTreeSet<ModuleFullPath>)> {
        self.pairs().collect()
    }

    /// The covered set derived for `origin`, if it is a module of origin.
    #[cfg(test)]
    pub(crate) fn set_of(&self, origin: &ModuleFullPath) -> Option<&BTreeSet<ModuleFullPath>> {
        self.sets.get(origin)
    }

    /// The modules of origin with a derived set.
    #[cfg(test)]
    pub(crate) fn origins(&self) -> impl Iterator<Item = &ModuleFullPath> {
        self.sets.keys()
    }

    #[cfg(test)]
    pub(crate) fn set_of_mut(
        &mut self,
        origin: &ModuleFullPath,
    ) -> Option<&mut BTreeSet<ModuleFullPath>> {
        self.sets.get_mut(origin)
    }
}

/// How a covered-set walk treats a prelude that has not published
/// (`design/int/int.md` §7.6.4, *The object pass waits*).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum UnpublishedPrelude {
    /// Covered as it stands, its edges not followed. Commit planning cannot
    /// wait on the prelude: `prelude → parent → child → prelude` would
    /// deadlock.
    ReadAsItStands,
    /// Answered like any other unpublished member. The object pass is off
    /// every publication path, so it can wait.
    Answer,
}

/// The covered set of `root` in `tables`: the transitive closure of reference
/// edges from `root`, each member's edges read from its own table, plus
/// `primitives`, less `root` and `macros` (`design/int/int.md` §7.6.4).
///
/// A member is unpublished when it has no table or `published` denies it; the
/// walk answers the first such member. A compiler-owned module, which no load
/// publishes, is never answered; the caller chooses, by `unpublished_prelude`,
/// whether an unpublished prelude is.
pub(crate) fn covered_set(
    root: &ModuleFullPath,
    tables: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
    prelude_fallback: &cranelisp_typecheck::PreludeFallback,
    unpublished_prelude: UnpublishedPrelude,
    published: impl Fn(&ModuleFullPath) -> bool,
) -> CoveredSet {
    let prelude = ModuleFullPath::from(PRELUDE);
    let answers = |member: &ModuleFullPath| {
        !is_compiler_owned(member)
            && (*member != prelude || unpublished_prelude == UnpublishedPrelude::Answer)
    };
    let prelude_table = tables.contains_key(&prelude);
    let mut covered = BTreeSet::new();
    let mut seen = BTreeSet::from([root.clone(), ModuleFullPath::from(MACROS)]);
    let mut walk = VecDeque::from([root.clone()]);
    while let Some(member) = walk.pop_front() {
        if member != *root {
            let settled = tables.contains_key(&member) && published(&member);
            if !settled && answers(&member) {
                return CoveredSet::Unpublished(member);
            }
            covered.insert(member.clone());
            if !settled && member == prelude {
                continue;
            }
        }
        let fallback = prelude_fallback.get(&member).is_some_and(|bit| *bit);
        let prelude_edge = if fallback && prelude_table {
            PreludeEdge::Present
        } else {
            PreludeEdge::Absent
        };
        let Some(edges) = tables
            .get(&member)
            .map(|table| reference_edges(&member, &table, prelude_edge))
        else {
            continue;
        };
        for edge in edges {
            if seen.insert(edge.clone()) {
                walk.push_back(edge);
            }
        }
    }
    covered.insert(ModuleFullPath::from(PRIMITIVES));
    CoveredSet::Covered(covered)
}

/// A module's reload edges as `table` records them: each `import` and `export`
/// that loads, resolved through its declared children; `prelude` when
/// `prelude_fallback` holds; and its callee modules and lookup dependencies. A
/// name-less import or export loads nothing (spec §8.3.7, §8.4.0) and is no
/// edge; a use through it is recorded as a callee or lookup dependency. Declared
/// children are not reload edges: a `mod` declaration compiles no reference
/// into the child. Reload selection and order and the publication cycle check
/// read this one predicate, each supplying the fallback bit of the generation
/// it reads (`design/int/repl-lifecycle.md` §1.2, `design/int/int.md` §6.12).
pub(crate) fn reload_edges(
    module: &ModuleFullPath,
    table: &SessionSymbolTable,
    prelude_fallback: bool,
) -> BTreeSet<ModuleFullPath> {
    let mut edges: BTreeSet<ModuleFullPath> = loading_spec_targets(module, table).collect();
    if prelude_fallback {
        edges.insert(ModuleFullPath::from(PRELUDE));
    }
    edges.extend(recorded_edges(module, table));
    edges.remove(module);
    edges
}

/// The module of every callee recorded on `table`'s callables, overload arms
/// and macro clauses (§7.6.1), other than `module` itself and compiler-owned
/// modules. Generic over the code store so a decoded table can be read before
/// it is installed.
pub(crate) fn callee_modules<C: CodeStore, L: LinkerStore>(
    module: &ModuleFullPath,
    table: &SymbolTable<C, L>,
) -> BTreeSet<ModuleFullPath> {
    every_callee_module(table)
        .filter(|target| is_edge(module, target))
        .cloned()
        .collect()
}

fn every_callee_module<C: CodeStore, L: LinkerStore>(
    table: &SymbolTable<C, L>,
) -> impl Iterator<Item = &ModuleFullPath> {
    table
        .all_symbols()
        .flat_map(|(_, binding)| binding_callees(binding))
        .map(|callee| &callee.module)
}

fn is_edge(module: &ModuleFullPath, target: &ModuleFullPath) -> bool {
    target != module && !is_compiler_owned(target)
}

pub(crate) fn is_compiler_owned(module: &ModuleFullPath) -> bool {
    let path: &str = module.as_ref();
    path == PRIMITIVES || path == MACROS || path.starts_with("platform.")
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
/// without its table's edges being walked; a fresh member contributes the
/// edges of its typechecked table. Each walked member is keyed by its stashed
/// source hash and the authored slot layout of its live table now; an
/// inherited member keeps the key its restored record holds.
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
                let Some(table) = shared.symbol_tables.get(&member) else {
                    return RecordOutcome::Unsettled { member };
                };
                let key = AuthoredSlotLayout::of(&table).derivation_key(&source_hash);
                drop(table);
                for (inner, hash) in record.0 {
                    inherited.entry(inner).or_insert(hash);
                }
                walked.insert(member, key);
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
                let key = AuthoredSlotLayout::of(&table).derivation_key(&source_hash);
                drop(table);
                walked.insert(member, key);
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

/// The current derivation key of each recorded member: the source it would
/// load from now, resolved exactly as the loading handlers resolve it, and
/// the authored slot layout of the version the session would link an
/// importer against (`design/int/int.md` §7.6.3). Every validity query reads
/// it; no caller compares layouts itself.
pub(crate) struct ModuleSources<'a> {
    project_root: &'a Path,
    lib_dirs: &'a [PathBuf],
    tables: &'a dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
    cache: &'a crate::cache::ObjectCache,
}

impl<'a> ModuleSources<'a> {
    /// `tables` is read one member at a time under a read guard; the caller
    /// must hold no mutable guard on it.
    pub(crate) fn new(
        project_root: &'a Path,
        lib_dirs: &'a [PathBuf],
        tables: &'a dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
        cache: &'a crate::cache::ObjectCache,
    ) -> Self {
        ModuleSources {
            project_root,
            lib_dirs,
            tables,
            cache,
        }
    }

    /// `None` when the member cannot be resolved or read, or has neither a
    /// live table nor a stored `.meta`, which is a miss.
    pub(crate) fn current_key(&self, module: &ModuleFullPath) -> Option<String> {
        let file = if module.as_ref() == PRELUDE {
            crate::session_setup::resolve_prelude(self.project_root, self.lib_dirs)
        } else {
            crate::pipeline::resolve_module_file(module, self.project_root, self.lib_dirs)
        }?;
        let source = std::fs::read_to_string(file).ok()?;
        let source_hash = cranelisp_backend::cache::manifest::hash_source(&source);
        Some(self.layout(module)?.derivation_key(&source_hash))
    }

    /// The layout of the member's live table when the session holds one (a
    /// terminal, restored or preloaded table, or a fresh build's incomplete
    /// one, which matches nothing); otherwise that of its stored `.meta`.
    fn layout(&self, module: &ModuleFullPath) -> Option<AuthoredSlotLayout> {
        if let Some(table) = self.tables.get(module) {
            return Some(AuthoredSlotLayout::of(&table));
        }
        self.cache.stored_layout(module)
    }
}

#[cfg(test)]
mod tests;
