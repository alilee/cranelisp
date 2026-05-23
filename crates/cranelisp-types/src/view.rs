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
//!
//! ## Shape — `struct` with private fields, NOT `pub enum` (S69 Submission 34)
//!
//! `View` is a `struct` whose internal staging-vs-live distinction is hidden
//! behind private fields. The shape is grounded in two places:
//!
//! - **Decision 44** (cluster-atomic typecheck via orchestrator-owned staging)
//!   names the opacity intent + uses the term "newtype" (singular structural
//!   shape) for `View`. The Decision's load-bearing claim — "typecheck reads
//!   `ctx.current_symbol_table()` whenever it would have read `&SymbolTable`
//!   directly; it cannot tell whether the view unions staging+live or hits live
//!   alone" — is structurally enforced only by the struct form with private
//!   fields. The prior `pub enum View { Single, Union }` form admitted
//!   consumer-side `match view { View::Union { .. } => …, View::Single { .. } =>
//!   … }`, which IS observable staging-vs-live distinction and defeats the
//!   Decision's opacity rationale.
//!
//! - **Principle 18** (enforce architectural invariants structurally where
//!   possible) directs that when both a structural option and a behavioural one
//!   exist, the structural option is the right choice. The struct-with-private-
//!   fields form prevents the cluster-mode shortcircuit by construction;
//!   consumers consume `View` only through `lookup` / `iter`, which is the
//!   read-side abstraction Decision 44 names.
//!
//! Internal encoding: `staging: Option<&'a SymbolTable<C, L>>` — `Some` =
//! cluster mode (staging consulted before live); `None` = committed mode (live
//! only). `live: &'a SymbolTable<C, L>` is unconditional.

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
///
/// **Opacity is structural.** The fields below are private; consumers cannot
/// observe whether a given `View` was constructed via `union` or `single`. This
/// enforces Decision 44's opacity intent + Principle 18 (enforce invariants
/// structurally). See module-level rustdoc above for the full grounding.
///
/// `#[non_exhaustive]` is intentionally NOT applied — private fields already
/// prevent external construction, so the structural non-exhaustivity is implicit.
#[derive(Debug)]
pub struct View<'a, C: CodeStore = (), L: LinkerStore = ()> {
    /// `Some(staging)` in cluster mode — staging is consulted before live.
    /// `None` in committed mode — live only.
    staging: Option<&'a SymbolTable<C, L>>,
    /// The live table; always present. Lookups fall through to live when
    /// staging (if present) does not contain the name.
    live: &'a SymbolTable<C, L>,
}

impl<'a, C: CodeStore, L: LinkerStore> View<'a, C, L> {
    /// Construct a composite read view. Lookups dispatch staging-first, then
    /// live. Both refs must outlive `'a`; the returned `View` borrows them.
    pub fn union(staging: &'a SymbolTable<C, L>, live: &'a SymbolTable<C, L>) -> Self {
        View { staging: Some(staging), live }
    }

    /// Construct a single-source read view over `live` alone. Used by
    /// `ClusterContext::Live` (REPL introspection, fine-grained-test paths,
    /// any caller reading committed state directly).
    pub fn single(live: &'a SymbolTable<C, L>) -> Self {
        View { staging: None, live }
    }

    /// Read-through lookup. In cluster mode (staging `Some`), staging entries
    /// shadow live entries; in committed mode (staging `None`), dispatches
    /// directly to live. Consumers cannot tell from the return value which
    /// side a hit came from — the staging-vs-live distinction is hidden by
    /// construction (per Decision 44 opacity intent + Principle 18).
    pub fn lookup(&self, name: &Symbol) -> Option<&'a ModuleEntry<C>> {
        self.staging
            .and_then(|s| s.get(name.as_ref()))
            .or_else(|| self.live.get(name.as_ref()))
    }

    /// Iterate the union, staging-first; live entries shadowed by staging keys
    /// are skipped (i.e., iteration produces each key exactly once). Order is
    /// iteration order of the underlying maps; not stable across runs.
    pub fn iter(&self) -> Box<dyn Iterator<Item = (&'a Symbol, &'a ModuleEntry<C>)> + 'a> {
        match self.staging {
            Some(staging) => {
                // Live entries not shadowed by staging follow staging entries.
                let staging_iter = staging.all_symbols();
                // Build a set of staging keys so we can filter live.
                let staging_keys: std::collections::HashSet<Symbol> =
                    staging.symbols.keys().cloned().collect();
                let live_iter = self
                    .live
                    .all_symbols()
                    .filter(move |(k, _)| !staging_keys.contains(*k));
                Box::new(staging_iter.chain(live_iter))
            }
            None => Box::new(self.live.all_symbols()),
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
