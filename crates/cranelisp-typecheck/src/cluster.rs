//! `ClusterContext<'a, C, L>` — the cluster-vs-committed dispatch choke point
//! for the two-pass per-form typecheck surface.
//!
//! Per Decision 44 (amended FIXME 0167 — Approach B + `ClusterContext`),
//! `ClusterContext` is the single point where staging-vs-live access is
//! decided. The two pass functions (`check_form_signatures` and
//! `check_form_body`) accept `&mut ClusterContext` and route every read /
//! write through the accessors `current_symbol_table()` (read) and
//! `current_symbol_table_mut()` (write).
//!
//! Variants:
//! - `Live { modules }` — committed mode. Used outside cluster processing
//!   (REPL introspection, fine-grained drivers, code paths that read live
//!   state directly).
//! - `Cluster { modules, staging, current_module }` — used by
//!   `int::process_cluster` for the duration of one cluster's processing.
//!   Writes redirect to the orchestrator-handed staging table; reads union
//!   staging-first with live.
//!
//! See `design/typecheck/wave-3a-check-form.md` §3 for the full design and
//! `design/arch/facades/typecheck.md` §"Per-form-pass scaffolding" for the
//! authorised public surface.

use dashmap::DashMap;

use cranelisp_types::{
    CodeStore, LinkerStore, ModuleFullPath, SymbolTable, View,
};

/// The cluster-vs-committed dispatch choke point. See module docs.
#[non_exhaustive]
pub enum ClusterContext<'a, C: CodeStore = (), L: LinkerStore = ()> {
    /// Committed mode — used outside cluster processing.
    Live {
        modules: &'a DashMap<ModuleFullPath, SymbolTable<C, L>>,
        current_module: ModuleFullPath,
    },
    /// Cluster mode — used by `int::process_cluster`.
    Cluster {
        modules: &'a DashMap<ModuleFullPath, SymbolTable<C, L>>,
        staging: &'a mut SymbolTable<C, L>,
        current_module: ModuleFullPath,
    },
}

impl<'a, C: CodeStore, L: LinkerStore> ClusterContext<'a, C, L> {
    /// Construct a `Live` mode ClusterContext. Lookups dispatch directly to
    /// the per-module live table; writes go to the per-module live table
    /// (caller takes `&mut self`, but the actual write surface is the
    /// DashMap shard lock — see `current_symbol_table_mut`).
    pub fn live(
        modules: &'a DashMap<ModuleFullPath, SymbolTable<C, L>>,
        current_module: ModuleFullPath,
    ) -> Self {
        ClusterContext::Live { modules, current_module }
    }

    /// Construct a `Cluster` mode ClusterContext. The orchestrator owns the
    /// staging table and holds it across the cluster's processing; this
    /// reference is the single write surface for the cluster.
    pub fn cluster(
        modules: &'a DashMap<ModuleFullPath, SymbolTable<C, L>>,
        staging: &'a mut SymbolTable<C, L>,
        current_module: ModuleFullPath,
    ) -> Self {
        ClusterContext::Cluster { modules, staging, current_module }
    }

    /// Currently scoped module path.
    pub fn current_module(&self) -> &ModuleFullPath {
        match self {
            ClusterContext::Live { current_module, .. }
            | ClusterContext::Cluster { current_module, .. } => current_module,
        }
    }

    /// Read accessor: returns a `View` over the current module's symbol
    /// table.
    ///
    /// - In `Cluster` mode: `View::union(staging, live)` — staging-first.
    ///   If the current module has no live table yet, the live side is an
    ///   empty placeholder (panic) — Wave 3a-α's registration discipline
    ///   ensures the current module's live table exists before
    ///   `process_cluster` constructs a `Cluster` variant.
    /// - In `Live` mode: `View::single(live)` — single-source over live.
    ///
    /// Returns a `View` that borrows the underlying tables; the borrow ends
    /// when the returned `View` is dropped.
    ///
    /// Note on lifetime: in `Cluster` mode the live side is read by holding
    /// a `dashmap::mapref::one::Ref` guard for the duration of the borrow —
    /// callers should NOT hold a `View` across calls that would re-enter
    /// the DashMap (deadlock risk). Use the `with_view` helper for scoped
    /// access.
    pub fn current_symbol_table(&self) -> ClusterRead<'_, C, L> {
        match self {
            ClusterContext::Live { modules, current_module } => {
                let guard = modules
                    .get(current_module)
                    .unwrap_or_else(|| panic!(
                        "ClusterContext::current_symbol_table: current module '{}' not present in live modules",
                        current_module
                    ));
                ClusterRead::Live(guard)
            }
            ClusterContext::Cluster { modules, staging, current_module } => {
                let guard = modules
                    .get(current_module)
                    .unwrap_or_else(|| panic!(
                        "ClusterContext::current_symbol_table: current module '{}' not present in live modules (cluster precondition)",
                        current_module
                    ));
                ClusterRead::Cluster { staging, live: guard }
            }
        }
    }

    /// Write accessor. In `Cluster` mode returns `&mut staging`; in `Live`
    /// mode returns a `RefMut` guard to the per-module live table.
    ///
    /// The returned wrapper transparently derefs to `&mut SymbolTable<C, L>`
    /// so the 91 register-call sites in `program.rs` continue to write
    /// uniformly.
    pub fn current_symbol_table_mut(&mut self) -> ClusterWrite<'_, C, L> {
        match self {
            ClusterContext::Live { modules, current_module } => {
                let guard = modules
                    .get_mut(current_module)
                    .unwrap_or_else(|| panic!(
                        "ClusterContext::current_symbol_table_mut: current module '{}' not present in live modules",
                        current_module
                    ));
                ClusterWrite::Live(guard)
            }
            ClusterContext::Cluster { staging, .. } => ClusterWrite::Cluster(staging),
        }
    }
}

/// Read-side wrapper produced by `ClusterContext::current_symbol_table`.
///
/// In `Live` mode it owns a `DashMap` read guard; in `Cluster` mode it
/// owns the live read guard plus the staging reference. The wrapper
/// exposes a `view()` method that constructs the `View<'_, C, L>` over
/// the held references.
pub enum ClusterRead<'a, C: CodeStore, L: LinkerStore> {
    /// Live mode: read guard over the per-module live table.
    Live(dashmap::mapref::one::Ref<'a, ModuleFullPath, SymbolTable<C, L>>),
    /// Cluster mode: staging reference + live read guard.
    Cluster {
        staging: &'a SymbolTable<C, L>,
        live: dashmap::mapref::one::Ref<'a, ModuleFullPath, SymbolTable<C, L>>,
    },
}

impl<'a, C: CodeStore, L: LinkerStore> ClusterRead<'a, C, L> {
    /// Construct a `View` over the held references.
    pub fn view(&self) -> View<'_, C, L> {
        match self {
            ClusterRead::Live(guard) => View::single(guard.value()),
            ClusterRead::Cluster { staging, live } => View::union(staging, live.value()),
        }
    }
}

/// Write-side wrapper produced by `ClusterContext::current_symbol_table_mut`.
///
/// Derefs transparently to `&mut SymbolTable<C, L>` so call sites that
/// already write through `current_symbol_table_mut()` need no source
/// changes.
pub enum ClusterWrite<'a, C: CodeStore, L: LinkerStore> {
    /// Live mode: write guard from the DashMap.
    Live(dashmap::mapref::one::RefMut<'a, ModuleFullPath, SymbolTable<C, L>>),
    /// Cluster mode: direct `&mut` to the orchestrator-handed staging
    /// table.
    Cluster(&'a mut SymbolTable<C, L>),
}

impl<'a, C: CodeStore, L: LinkerStore> std::ops::Deref for ClusterWrite<'a, C, L> {
    type Target = SymbolTable<C, L>;
    fn deref(&self) -> &Self::Target {
        match self {
            ClusterWrite::Live(g) => g.value(),
            ClusterWrite::Cluster(s) => s,
        }
    }
}

impl<'a, C: CodeStore, L: LinkerStore> std::ops::DerefMut for ClusterWrite<'a, C, L> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        match self {
            ClusterWrite::Live(g) => g.value_mut(),
            ClusterWrite::Cluster(s) => s,
        }
    }
}

#[cfg(test)]
mod tests {
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
        }
    }

    #[test]
    fn live_mode_routes_to_live_table() {
        let modules = empty_modules();
        let mut ctx: ClusterContext<'_, (), ()> = ClusterContext::live(&modules, module_path());
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
            let mut ctx: ClusterContext<'_, (), ()> =
                ClusterContext::cluster(&modules, &mut staging, module_path());
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

        let ctx: ClusterContext<'_, (), ()> =
            ClusterContext::cluster(&modules, &mut staging, module_path());
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
            },
        );

        let ctx: ClusterContext<'_, (), ()> =
            ClusterContext::cluster(&modules, &mut staging, module_path());
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
        let ctx: ClusterContext<'_, (), ()> = ClusterContext::live(&modules, module_path());
        assert_eq!(ctx.current_module(), &module_path());
    }
}
