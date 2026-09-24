---
number: 0694
target: /qa
filed_by: /review
filed_at: 2026-07-20
sprint_filed: 114
refers_to: tests/nullary_return_dispatch_method_only_import.rs;
  tests/macro_expansion_interior_alias_double_free.rs;
  tests/multi_sig_module_locality.rs;
  tests/agent.rs;
  tests/repl_persist.rs;
  tests/cache.rs;
  tests/plan/s122-evidence-delta.md
status: open
---

# Run-dependent guards: attribute each member; never count one as "flaky"

The standing counting convention this filing produced — an exact stable
failing set plus a separately named run-dependent set — is canonical in
[QA traceability](../../../tests/plan/PLAN.md#traceability-and-authoring).
This filing carries the unattributed members.

Every e2e test spawns a multi-threaded `cranelisp` subprocess (index worker,
rayon sparks, IO reactor); host CPU load changes intra-subprocess interleaving.
That shared condition does not make the members one defect.

## Members and state

| Member | Observed signature | State |
|---|---|---|
| `nullary_return_dispatch_method_only_import::…_no_codegen_leak` (Class II, publication ordering) | clean compile diagnostic `codegen error at 14..15: undefined function: z` | S121 D1: 53/200 failures under twelve non-Cranelisp CPU workers, one Cranelisp subprocess, one signature. Host contention alone suffices; shared cache/tmpdir/`CRANELISP_LIB`/`user.cl` state is not required. Mechanism not yet demonstrated. |
| `multi_sig_module_locality::imported_multi_sig_base_direct_call_repl` (Class II candidate) | one RED under load, output not captured | same seam family as the nullary member; unattributed |
| `macro_expansion_interior_alias_double_free::macro_clause_interior_alias_double_free_run` (Class I, heap invariant) | glibc `free(): chunks in smallbin corrupted`, killed by signal | memory-safety event, not a flap; one S115 capture; not re-characterised since |
| `agent::y_short_flag_errors_on_non_agent_build`, `repl_persist::imported_trait_impl_survives_restart` (Class III) | one RED each under load, output not captured | unclassified |
| `cache::cache_restores_sibling_written_trait_impls_for_dispatch` (inverse polarity) | an intended-RED guard passed once in an interleaved multi-binary run | intended REDs are verified per binary; unattributed |

## Remaining obligation

- **Class II.** Demonstrate or falsify the publication-ordering mechanism at
  the existing Binary/int publication boundary, under D1's load shape:
  - D2 — an env-gated, experiment-only event pair records `zlib/z` batch
    publication and the REPL eval read. The attribution holds only if a
    failing trace orders the read before publication and a passing trace
    orders it after. Current `CRANELISP_MODULE_TRACE` emits only on a
    terminal-closure breach, so setting it alone is vacuous.
  - D3 — an env-gated delay before live publication makes the unloaded
    nullary row fail 5/5 with the exact text while the unarmed twin returns
    42 5/5.
  - Remove the experiment-only events and delay before the change-set closes.
    The S122 allocation asks `qa` to reconcile this against the current Q1/Q7
    publication evidence: identify a surviving exact condition or seek an
    explicit residual disposition, not another speculative detector.
- **Class I** owes its own characterisation under the armed diagnostic modes
  and a single-threaded run at identical load. Absence under a perturbing
  tool is not a fix.
- **Class III and the inverse-polarity member** owe isolation-versus-load
  characterisation with captured in-suite output.
- Tee every characterisation run; the D1 capture and binary hash are in Git
  history of this file.

## Closure

Each member has a demonstrated mechanism and a fix that fails on revert, or an
explicit user-approved residual disposition. A later green suite does not
reconstruct missing attribution.
