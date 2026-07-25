//! CS-3/CS-4 — publication + observability
//! (`design/typecheck/ownership-inference.md` §13.2 CS-4, §13.6(b)).
//!
//! Post-convergence, writes the pass output through `current_symbol_table_mut`
//! (staging-aware, cluster-atomic — the `write_callees_to_module_entries` write
//! path, Decision 44):
//!
//! - **summaries** onto the callable entry (`set_mode_summary`) and its stored
//!   `codegen_view` (`MonoDefnVariant.mode_summary` — the compile-in-hand
//!   carrier the backend reads);
//! - **value-use marks** (`set_value_use`) for callables referenced in value
//!   position (§8.3);
//! - (CS-4) **site facts + provenance** onto the stored `codegen_view` body in
//!   one post-convergence walk (§13.6(b)) + the H5 `CRANELISP_OWNERSHIP_TRACE`
//!   dump.

use cranelisp_types::ModuleEntry;

use crate::checker::{CheckState, TypeCheckEnv};

use super::fixpoint::ClusterOwnership;

/// Publish the cluster's ownership analysis onto the symbol table.
pub(crate) fn publish<C, L>(
    env: &TypeCheckEnv<C, L>,
    state: &CheckState,
    cluster: &ClusterOwnership,
) where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    let mut guard = env.current_symbol_table_mut(state);
    for (key, summary) in &cluster.summaries {
        let Some(entry) = guard.symbols.get_mut(key) else {
            continue;
        };
        // Persisted twin on the callable DefKind variant (⇒ `.meta.json`).
        entry.set_mode_summary(Some(summary.clone()));
        // Compile-in-hand carrier + the one-shot post-convergence site-fact
        // annotation walk (§13.6(b)) onto the stored codegen_view body.
        if let ModuleEntry::Def {
            codegen_view: Some(cv),
            ..
        } = entry
        {
            cv.mode_summary = Some(summary.clone());
            if let Some(facts) = cluster.facts.get(key) {
                super::sites::annotate(&mut cv.body, facts);
            }
        }
    }
    // Value-use marks (§8.3): any callable referenced in value position.
    for key in &cluster.value_used {
        if let Some(entry) = guard.symbols.get_mut(key) {
            entry.set_value_use(true);
        }
    }
    drop(guard);

    // H5 observability (§11) — silent unless CRANELISP_OWNERSHIP_TRACE is set.
    super::trace::emit(state, cluster);
}

#[cfg(test)]
mod tests;
