//! CS-4 — the H5 `CRANELISP_OWNERSHIP_TRACE` debug dump
//! (`design/typecheck/ownership-inference.md` §11 Observability, §13.2 CS-4).
//!
//! A sibling of `CRANELISP_CODEGEN_TRACE`: when the env var is set, dumps each
//! cluster's per-callable summaries + per-site verdicts to stderr. This is an
//! **in-increment deliverable** — I-G3 and the L-D3f ledger guard are
//! unmeasurable without it. Silent (zero output, zero cost beyond the env read)
//! when unset.

use std::sync::OnceLock;

use crate::checker::CheckState;

use super::fixpoint::ClusterOwnership;

fn trace_on() -> bool {
    static E: OnceLock<bool> = OnceLock::new();
    *E.get_or_init(|| std::env::var_os("CRANELISP_OWNERSHIP_TRACE").is_some())
}

/// Dump the cluster's ownership analysis to stderr when the env var is set.
pub(crate) fn emit(state: &CheckState, cluster: &ClusterOwnership) {
    if !trace_on() {
        return;
    }
    let module = &state.current_module;
    eprintln!("=== OWNERSHIP {module} ===");
    // Deterministic order (sorted by callable key) for reproducible dumps.
    let mut keys: Vec<&cranelisp_types::Symbol> = cluster.summaries.keys().collect();
    keys.sort();
    for key in keys {
        let s = &cluster.summaries[key];
        let value_use = if cluster.value_used.contains(key) { " value-use" } else { "" };
        eprintln!(
            "  {key}: modes={:?} result={:?} flow={:?} spark_ops={:?}{value_use}",
            s.param_modes, s.result, s.param_flow, s.spark_ops
        );
        if let Some(f) = cluster.facts.get(key) {
            let mut esc: Vec<_> = f.escapes.iter().filter(|(_, v)| **v).map(|(k, _)| *k).collect();
            esc.sort_by_key(|s| (s.start, s.end));
            if !esc.is_empty() {
                eprintln!("    escapes@ {esc:?}");
            }
            let mut cross: Vec<_> =
                f.confined.iter().filter(|(_, v)| !**v).map(|(k, _)| *k).collect();
            cross.sort_by_key(|s| (s.start, s.end));
            if !cross.is_empty() {
                eprintln!("    crossing@ {cross:?}");
            }
            if !f.provenance.is_empty() {
                let mut prov: Vec<_> = f.provenance.iter().collect();
                prov.sort_by_key(|(s, _)| (s.start, s.end));
                eprintln!("    provenance {prov:?}");
            }
        }
    }
}
