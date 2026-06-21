//! `SymbolTableAccess<'a, C, L>` — the cluster-vs-committed dispatch choke point
//! for the per-cluster typecheck surface.
//!
//! Per Decision 44 (amended FIXME 0167 — Approach B + `SymbolTableAccess`),
//! `SymbolTableAccess` is the single point where staging-vs-live access is
//! decided. The cluster entry function (`check_forms`) accepts
//! `&mut SymbolTableAccess` and routes every read / write through the accessors
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
pub enum SymbolTableAccess<'a, C: CodeStore = (), L: LinkerStore = ()> {
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
    /// `RefCell` is owned by the `SymbolTableAccess` value.
    Cluster {
        modules: &'a DashMap<ModuleFullPath, SymbolTable<C, L>>,
        staging: RefCell<&'a mut SymbolTable<C, L>>,
        current_module: ModuleFullPath,
    },
}

impl<'a, C: CodeStore, L: LinkerStore> SymbolTableAccess<'a, C, L> {
    /// Construct a `Live` mode SymbolTableAccess. Lookups dispatch directly to
    /// the per-module live table; writes go to the per-module live table
    /// (caller takes `&mut self`, but the actual write surface is the
    /// DashMap shard lock — see `current_symbol_table_mut`).
    pub fn live(
        modules: &'a DashMap<ModuleFullPath, SymbolTable<C, L>>,
        current_module: ModuleFullPath,
    ) -> Self {
        SymbolTableAccess::Live { modules, current_module }
    }

    /// Construct a `Cluster` mode SymbolTableAccess. The orchestrator owns the
    /// staging table and lends it to the cluster's processing via `&mut`; the
    /// constructor wraps that reference in a `RefCell` so the read + write
    /// accessors can hand out borrow guards.
    pub fn cluster(
        modules: &'a DashMap<ModuleFullPath, SymbolTable<C, L>>,
        staging: &'a mut SymbolTable<C, L>,
        current_module: ModuleFullPath,
    ) -> Self {
        SymbolTableAccess::Cluster {
            modules,
            staging: RefCell::new(staging),
            current_module,
        }
    }

    /// Currently scoped module path.
    pub fn current_module(&self) -> &ModuleFullPath {
        match self {
            SymbolTableAccess::Live { current_module, .. }
            | SymbolTableAccess::Cluster { current_module, .. } => current_module,
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
            SymbolTableAccess::Live { modules, current_module } => {
                let guard = modules
                    .get(current_module)
                    .unwrap_or_else(|| unreachable!(
                        "SymbolTableAccess::current_symbol_table: current module '{}' not present in live modules",
                        current_module
                    ));
                SymbolTableRead::Live(guard)
            }
            SymbolTableAccess::Cluster { modules, staging, current_module } => {
                let guard = modules
                    .get(current_module)
                    .unwrap_or_else(|| unreachable!(
                        "SymbolTableAccess::current_symbol_table: current module '{}' not present in live modules (cluster precondition)",
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
            SymbolTableAccess::Live { modules, current_module } => {
                let guard = modules
                    .get_mut(current_module)
                    .unwrap_or_else(|| unreachable!(
                        "SymbolTableAccess::current_symbol_table_mut: current module '{}' not present in live modules",
                        current_module
                    ));
                SymbolTableMut::Live(guard)
            }
            SymbolTableAccess::Cluster { staging, .. } => {
                SymbolTableMut::Staging(staging.borrow_mut())
            }
        }
    }

}

/// Read-side borrow guard returned by both `SymbolTableAccess::current_symbol_table()`
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
/// `SymbolTableAccess::current_symbol_table_mut()` and
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
mod tests;
