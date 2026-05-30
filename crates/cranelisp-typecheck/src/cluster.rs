//! `ClusterContext<'a, C, L>` — the cluster-vs-committed dispatch choke point
//! for the per-cluster typecheck surface.
//!
//! Per Decision 44 (amended FIXME 0167 — Approach B + `ClusterContext`),
//! `ClusterContext` is the single point where staging-vs-live access is
//! decided. The cluster entry function (`check_forms`) accepts
//! `&mut ClusterContext` and routes every read / write through the accessors
//! `current_symbol_table()` (read) and `current_symbol_table_mut()` (write).
//!
//! Variants:
//! - `Live { modules }` — committed mode. Used outside cluster processing
//!   (REPL introspection, fine-grained drivers, code paths that read live
//!   state directly).
//! - `Cluster { modules, staging, current_module }` — used by
//!   `int::process_cluster` for the duration of one cluster's processing.
//!   Writes redirect to the orchestrator-handed staging table; reads union
//!   staging-first with live. Staging is wrapped in a `RefCell` so the
//!   accessor pair can hand out runtime-checked borrow guards (the same
//!   `SymbolTableRead` / `SymbolTableMut` types that the interior
//!   `TypeCheckEnv` accessor pair returns — single-pair invariant).
//!
//! See `design/typecheck/wave-3a-check-form.md` §3 for the design context and
//! `design/arch/facades/typecheck.md` §"Single-pair invariant" for the
//! authoritative configuration that constrains this module's shape.

use std::cell::RefCell;

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
    ///
    /// `staging` is wrapped in a `RefCell` so the read + write accessors can
    /// each hand out a runtime-checked borrow guard. The orchestrator's
    /// `&'a mut SymbolTable` is consumed by the `cluster()` constructor; the
    /// `RefCell` is owned by the `ClusterContext` value.
    Cluster {
        modules: &'a DashMap<ModuleFullPath, SymbolTable<C, L>>,
        staging: RefCell<&'a mut SymbolTable<C, L>>,
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
    /// staging table and lends it to the cluster's processing via `&mut`; the
    /// constructor wraps that reference in a `RefCell` so the read + write
    /// accessors can hand out borrow guards.
    pub fn cluster(
        modules: &'a DashMap<ModuleFullPath, SymbolTable<C, L>>,
        staging: &'a mut SymbolTable<C, L>,
        current_module: ModuleFullPath,
    ) -> Self {
        ClusterContext::Cluster {
            modules,
            staging: RefCell::new(staging),
            current_module,
        }
    }

    /// Currently scoped module path.
    pub fn current_module(&self) -> &ModuleFullPath {
        match self {
            ClusterContext::Live { current_module, .. }
            | ClusterContext::Cluster { current_module, .. } => current_module,
        }
    }

    /// Read accessor: returns a `SymbolTableRead` borrow guard over the
    /// current module's symbol table. Call `.view()` on the returned guard to
    /// obtain the `View<'_, C, L>` used by lookup code.
    ///
    /// - In `Cluster` mode: `SymbolTableRead::Cluster { staging, live }` —
    ///   `.view()` returns `View::union(staging, live)` (staging-first). The
    ///   guard holds both a `RefCell` runtime borrow on staging and a DashMap
    ///   per-shard read guard on live; drop it before acquiring another guard
    ///   to avoid deadlocks or `RefCell` borrow-check panics.
    /// - In `Live` mode: `SymbolTableRead::Live(...)` — `.view()` returns
    ///   `View::single(live)`. Guard holds a DashMap per-shard read guard.
    pub fn current_symbol_table<'b>(&'b self) -> SymbolTableRead<'b, 'a, C, L> {
        match self {
            ClusterContext::Live { modules, current_module } => {
                let guard = modules
                    .get(current_module)
                    .unwrap_or_else(|| panic!(
                        "ClusterContext::current_symbol_table: current module '{}' not present in live modules",
                        current_module
                    ));
                SymbolTableRead::Live(guard)
            }
            ClusterContext::Cluster { modules, staging, current_module } => {
                let guard = modules
                    .get(current_module)
                    .unwrap_or_else(|| panic!(
                        "ClusterContext::current_symbol_table: current module '{}' not present in live modules (cluster precondition)",
                        current_module
                    ));
                SymbolTableRead::Cluster { staging: staging.borrow(), live: guard }
            }
        }
    }

    /// Write accessor: returns a `SymbolTableMut` borrow guard that
    /// transparently derefs to `&mut SymbolTable<C, L>` via `Deref`/`DerefMut`.
    ///
    /// - In `Cluster` mode: `SymbolTableMut::Staging(...)` — wraps the
    ///   `RefCell::borrow_mut()` guard pointing at the orchestrator-handed
    ///   staging table.
    /// - In `Live` mode: `SymbolTableMut::Live(...)` — wraps the DashMap
    ///   per-module write guard for the per-module live table.
    pub fn current_symbol_table_mut<'b>(&'b mut self) -> SymbolTableMut<'b, 'a, C, L> {
        match self {
            ClusterContext::Live { modules, current_module } => {
                let guard = modules
                    .get_mut(current_module)
                    .unwrap_or_else(|| panic!(
                        "ClusterContext::current_symbol_table_mut: current module '{}' not present in live modules",
                        current_module
                    ));
                SymbolTableMut::Live(guard)
            }
            ClusterContext::Cluster { staging, .. } => {
                SymbolTableMut::Staging(staging.borrow_mut())
            }
        }
    }

}

/// Read-side borrow guard returned by both `ClusterContext::current_symbol_table()`
/// and `TypeCheckEnv::current_symbol_table()` — the single-pair invariant
/// (per `facades/typecheck.md` §"Single-pair invariant") mandates one pair of
/// read+write wrappers across the typecheck surface.
///
/// - `Live`: a DashMap per-shard read guard over the live per-module table.
///   `.view()` returns `View::single(live)`.
/// - `Cluster`: a `RefCell` borrow on staging plus a DashMap read guard on
///   live. `.view()` returns `View::union(staging, live)` — staging-first.
///
/// The two lifetimes name the borrow's source: `'a` is the read borrow itself
/// (the guard); `'b` is the lifetime of the orchestrator's underlying
/// `&'b mut SymbolTable<C, L>` reference held inside the staging `RefCell`.
/// In `Live` mode `'b` is unused on the variant payload.
pub enum SymbolTableRead<'a, 'b, C: CodeStore, L: LinkerStore> {
    /// Live mode: read guard over the per-module live table.
    Live(dashmap::mapref::one::Ref<'a, ModuleFullPath, SymbolTable<C, L>>),
    /// Cluster mode: staging `RefCell::borrow()` guard + live read guard.
    Cluster {
        staging: std::cell::Ref<'a, &'b mut SymbolTable<C, L>>,
        live: dashmap::mapref::one::Ref<'a, ModuleFullPath, SymbolTable<C, L>>,
    },
}

impl<'a, 'b, C: CodeStore, L: LinkerStore> SymbolTableRead<'a, 'b, C, L> {
    /// Construct a `View<'_, C, L>` over the held references.
    ///
    /// - `Live` → `View::single(live)`.
    /// - `Cluster` → `View::union(staging, live)` — lookups dispatch
    ///   staging-first, then live.
    pub fn view(&self) -> View<'_, C, L> {
        match self {
            SymbolTableRead::Live(guard) => View::single(guard.value()),
            SymbolTableRead::Cluster { staging, live } => {
                // `staging` is `Ref<'_, &'b mut SymbolTable>`; auto-deref
                // collapses both layers to `&SymbolTable<C, L>`.
                let staging_ref: &SymbolTable<C, L> = staging;
                View::union(staging_ref, live.value())
            }
        }
    }
}

/// Write-side borrow guard returned by both
/// `ClusterContext::current_symbol_table_mut()` and
/// `TypeCheckEnv::current_symbol_table_mut()` — the single-pair invariant
/// counterpart to `SymbolTableRead`.
///
/// - `Live`: a DashMap per-module write guard.
/// - `Staging`: a `RefCell::borrow_mut()` guard over the orchestrator-handed
///   staging table.
///
/// Derefs (`Deref` + `DerefMut`) to `&[mut] SymbolTable<C, L>` so the
/// register-call sites in `program.rs`, `traits.rs`, etc. write through
/// uniformly without per-site changes.
///
/// Lifetimes: `'a` is the guard borrow; `'b` is the lifetime of the
/// underlying `&'b mut SymbolTable<C, L>` reference held inside the staging
/// `RefCell` (unused in `Live`).
pub enum SymbolTableMut<'a, 'b, C: CodeStore, L: LinkerStore> {
    /// Live mode: write guard from the DashMap.
    Live(dashmap::mapref::one::RefMut<'a, ModuleFullPath, SymbolTable<C, L>>),
    /// Staging mode: `RefCell::borrow_mut()` guard over the orchestrator-handed
    /// staging table.
    Staging(std::cell::RefMut<'a, &'b mut SymbolTable<C, L>>),
}

impl<'a, 'b, C: CodeStore, L: LinkerStore> std::ops::Deref for SymbolTableMut<'a, 'b, C, L> {
    type Target = SymbolTable<C, L>;
    fn deref(&self) -> &Self::Target {
        match self {
            SymbolTableMut::Live(g) => g.value(),
            // `g` is `RefMut<'_, &'b mut SymbolTable>`; auto-deref walks both
            // layers to `&SymbolTable`.
            SymbolTableMut::Staging(g) => g,
        }
    }
}

impl<'a, 'b, C: CodeStore, L: LinkerStore> std::ops::DerefMut for SymbolTableMut<'a, 'b, C, L> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        match self {
            SymbolTableMut::Live(g) => g.value_mut(),
            SymbolTableMut::Staging(g) => g,
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
            visibility: cranelisp_types::Visibility::Private,
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
                visibility: cranelisp_types::Visibility::Private,
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
