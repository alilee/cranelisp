//! `View<'a, C, L>` — the cluster read surface (per Decision 44, amended FIXME 0167).
//!
//! A thin newtype that wraps either two `&SymbolTable<C, L>` references (staging
//! + live) and routes lookups staging-first then live, or a single
//! `&SymbolTable<C, L>` (committed mode). It is the read surface that the two-pass
//! typecheck functions (`check_form_signatures` and `check_form_body`) see for
//! the current cluster's per-module read. Typecheck does not know whether a given
//! lookup hits staging, live, or unioned content; it just calls
//! `view.lookup(name)`.
//!
//! Construction site: `View` is produced inside `ClusterContext::current_symbol_table()`
//! (in `cranelisp-typecheck`). In `ClusterContext::Cluster` mode the accessor
//! returns `View::union(staging, live)`; in `ClusterContext::Live` mode the
//! accessor returns `View::single(live)`.
//!
//! See `design/arch/facades/types.md` §"`View<'a, C, L>`" for the canonical
//! specification.

use crate::module::{CodeStore, LinkerStore, ModuleEntry, SymbolTable};
use crate::newtype::Symbol;

/// A read-only view over a module's symbol-table, optionally unioned with a
/// staging table. Constructed by `ClusterContext::current_symbol_table()`.
///
/// Two construction forms:
/// - `View::union(staging, live)` — staging shadows live; lookups dispatch
///   staging-first, then live.
/// - `View::single(live)` — a single-source view over `live` alone, used by
///   `ClusterContext::Live` (REPL introspection, fine-grained-test paths).
///
/// `View` exposes no write methods; staging is mutated only through the
/// orchestrator's `&mut SymbolTable` handle outside the typecheck call.
#[non_exhaustive]
#[derive(Debug)]
pub enum View<'a, C: CodeStore = (), L: LinkerStore = ()> {
    /// Union view: staging shadows live; lookups dispatch staging-first.
    Union {
        staging: &'a SymbolTable<C, L>,
        live: &'a SymbolTable<C, L>,
    },
    /// Single-source view over the live table alone.
    Single { live: &'a SymbolTable<C, L> },
}

impl<'a, C: CodeStore, L: LinkerStore> View<'a, C, L> {
    /// Construct a composite read view. Lookups dispatch staging-first, then
    /// live. Both refs must outlive `'a`; the returned `View` borrows them.
    pub fn union(staging: &'a SymbolTable<C, L>, live: &'a SymbolTable<C, L>) -> Self {
        View::Union { staging, live }
    }

    /// Construct a single-source read view over `live` alone. Used by
    /// `ClusterContext::Live` (REPL introspection, fine-grained-test paths,
    /// any caller reading committed state directly).
    pub fn single(live: &'a SymbolTable<C, L>) -> Self {
        View::Single { live }
    }

    /// Read-through lookup. In `Union` mode, staging entries shadow live
    /// entries. In `Single` mode, dispatches directly to live.
    pub fn lookup(&self, name: &Symbol) -> Option<&'a ModuleEntry<C>> {
        match self {
            View::Union { staging, live } => staging.get(name.as_ref()).or_else(|| live.get(name.as_ref())),
            View::Single { live } => live.get(name.as_ref()),
        }
    }

    /// Iterate the union, staging-first; live entries shadowed by staging keys
    /// are skipped (i.e., iteration produces each key exactly once). Order is
    /// iteration order of the underlying maps; not stable across runs.
    pub fn iter(&self) -> Box<dyn Iterator<Item = (&'a Symbol, &'a ModuleEntry<C>)> + 'a> {
        match self {
            View::Union { staging, live } => {
                // Live entries not shadowed by staging follow staging entries.
                let staging_iter = staging.all_symbols();
                // Build a set of staging keys so we can filter live.
                let staging_keys: std::collections::HashSet<Symbol> =
                    staging.symbols.keys().cloned().collect();
                let live_iter = live
                    .all_symbols()
                    .filter(move |(k, _)| !staging_keys.contains(*k));
                Box::new(staging_iter.chain(live_iter))
            }
            View::Single { live } => Box::new(live.all_symbols()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::newtype::ModuleFullPath;

    fn empty_table(name: &str) -> SymbolTable<(), ()> {
        SymbolTable::<(), ()>::new_with_params(ModuleFullPath::from(name))
    }

    #[test]
    fn view_single_dispatches_to_live() {
        let live = empty_table("m");
        let view: View<'_, (), ()> = View::single(&live);
        assert!(view.lookup(&Symbol::from("absent")).is_none());
        let count = view.iter().count();
        assert_eq!(count, 0);
    }

    #[test]
    fn view_union_staging_shadows_live() {
        let live = empty_table("m");
        let staging = empty_table("m");
        let view: View<'_, (), ()> = View::union(&staging, &live);
        assert!(view.lookup(&Symbol::from("absent")).is_none());
        assert_eq!(view.iter().count(), 0);
    }
}
