//! CS-3/CS-4 — publication + observability
//! (`design/typecheck/ownership-inference.md` §13.2 CS-4, §13.6(b)).
//!
//! Post-convergence, writes the pass output through `current_symbol_table_mut`
//! (staging-aware and cluster-atomic, Decision 44):
//!
//! - **summaries** onto the callable entry (`set_mode_summary`) and its stored
//!   `codegen_view` (`MonoDefnVariant.mode_summary` — the compile-in-hand
//!   carrier the backend reads);
//! - **value-use marks** (`set_value_use`) for callables referenced in value
//!   position (§8.3);
//! - (CS-4) **site facts + provenance** onto the stored `codegen_view` body in
//!   one post-convergence walk (§13.6(b)) + the H5 `CRANELISP_OWNERSHIP_TRACE`
//!   dump.

use cranelisp_types::{CallableTarget, FQSymbol, Life, Realization};

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
    // §19.5 — a refused cluster publishes NOTHING: no summary, no site fact, no
    // value-use mark. The refusal already leaves the maps empty at the producer;
    // the funnel refuses too, so a future producer that hands one over cannot
    // publish it by accident. The refused module then compiles on exactly the
    // `CRANELISP_NO_OWNERSHIP` shape. The trace still runs — the refusal is what
    // it exists to report.
    if cluster.refusal.is_some() {
        super::trace::emit(state, cluster);
        return;
    }
    let mut guard = env.current_symbol_table_mut(state);
    for (key, summary) in &cluster.summaries {
        let Some(mut view) = guard.get(key.as_ref()).and_then(|entry| {
            let callable = entry.callable()?;
            let Life::Concrete {
                realization: Realization::Body { view, .. },
                ..
            } = &callable.arm.life
            else {
                return None;
            };
            Some(view.clone())
        }) else {
            continue;
        };
        if let Some(facts) = cluster.facts.get(key) {
            super::sites::annotate(&mut view.body, facts);
        }
        guard
            .publish_body_ownership(
                &CallableTarget::Binding(FQSymbol {
                    module: state.current_module.clone(),
                    symbol: key.clone(),
                }),
                summary.clone(),
                view,
            )
            .expect("ownership universe contains publishable concrete bodies");
    }
    // Value-use marks (§8.3): any callable referenced in value position.
    for key in &cluster.value_used {
        // The ownership walk also sees foreign/global and local-lambda names.
        // Publication is module-local: retain the pre-facade behaviour and
        // mark only a callable actually owned by this table.
        if guard
            .get(key.as_ref())
            .and_then(|binding| binding.callable())
            .is_some_and(|callable| matches!(callable.arm.life, Life::Concrete { .. }))
        {
            guard
                .set_value_use(key, true)
                .expect("concrete callable accepts its value-use mark");
        }
    }
    drop(guard);

    // H5 observability (§11) — silent unless CRANELISP_OWNERSHIP_TRACE is set.
    super::trace::emit(state, cluster);
}

#[cfg(test)]
mod tests;
