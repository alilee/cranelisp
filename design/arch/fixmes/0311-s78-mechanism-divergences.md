---
number: 0311
target: /design
filed_by: /dev
filed_at: 2026-06-10
sprint_filed: 78
refers_to: design/int/s78-implementation.md §1.1, §1.2, §3, §4
status: open
---

# S78 implementation — three mechanism divergences from the companion (source-forced)

## Issue

Implementing the S78 restructure (Wave 2, src/) surfaced three places where the
source-forced realization diverges from the `s78-implementation.md` companion's
*mechanism* detail. Per the companion's own rule ("where they disagree on a
mechanism detail, the source-verified detail wins") and the root `CLAUDE.md`
"source moves toward facade by default" calibration, these were resolved in
source. Recording them so `/design` can reconcile the companion's prose to the
as-built shape (none change intent, scope, or soundness).

1. **Packet approach = 1b, not the recommended 1a (§1.1).** The companion
   recommended (1a) "queue carries the packet" and noted 1b as the permitted
   fallback "if 1a's `Eq`/queue-type churn proves disproportionate." It is
   disproportionate: the requeue path (`try_unblock_locked`) reconstructs the
   packet from `ModuleState`, so the sexps must live on `ModuleState` REGARDLESS
   of 1a vs 1b — 1a would store them BOTH on the queue and on `ModuleState`
   (redundant) while churning ~10 queue-mutation sites (`push`/`pop`/`retain`)
   and forcing a manual `PartialEq`/`Eq` on `PriorityWork` anyway. Chosen: queues
   stay `VecDeque<ModuleFullPath>`; `ModuleState.sexps: Option<Arc<[Sexp]>>` holds
   the packet; `dispatch_typecheck_locked` reads it on pop to build
   `PriorityWork::Typecheck { module, sexps }`. `PriorityWork` carries a manual
   `PartialEq`/`Eq` (module identity only, sexps ignored). `SharedState.module_sexps`
   still deletes — the goal (no shared in-progress parking map) is met.

2. **Per-symbol staging commit stays inside `check_program_compat`, NOT moved to
   `insert_cluster` (§1.2, §4 Step 1).** The companion says "the commit-site
   moves from inside `process_cluster_with_staging` to `insert_cluster` (route
   the drained entries through `ProcessedCluster.entries`)". Moving the commit
   to `insert_cluster` breaks the worker codegen ordering: `derive_codegen_batch`
   + `inline_jit_codegen_for_module` read the committed entries from the LIVE
   `symbol_tables` to compile them, and the worker handler runs codegen BEFORE
   `insert_cluster` (per the companion's own "claim → process_cluster → codegen →
   insert_cluster → notify" order). If the commit lived in `insert_cluster`,
   codegen would run against an empty live table. Chosen: `process_cluster_once`
   keeps the staging commit in `commit_staging_to_live` (on Ok, as today);
   `ProcessedCluster::empty()` is returned for the worker path; `insert_cluster`
   drains only the cluster-level introspection metadata. `ProcessedCluster` is
   unchanged (no shape change). The expanded `program` for codegen rides the
   `ClusterOnce::Done { program }` / `ClusterOutcome::Done { program }` outcome,
   not `ProcessedCluster`.

3. **Orchestration core stays in `worker.rs`, not moved into `cluster.rs`
   (§1.2, §4 Step 1).** The companion says "move the staging core
   (`process_cluster_with_staging` + `commit_staging_to_live`) from `worker.rs`
   into `cluster.rs`" and frame `process_cluster_once` as living in `cluster.rs`.
   The Pass-0/1/2 core depends on ~30 `worker.rs`-private helpers
   (`classify_form`, `handle_import`/`handle_export`/`handle_mod`,
   `separate_macros`, `pass1_register`, `process_regular_form`,
   `top_level_to_parsed_entries`, `check_error_to_cranelisp_error`, …). Moving
   the core to `cluster.rs` mid-RED-span would force ~30 helpers `pub(crate)` and
   a 1200-LOC cross-file relocation for a doc-placement preference (Principle 6
   budget, Principle 8 no-interim-churn). Chosen: `worker::process_cluster_once`
   (the shared core) + `worker::drive_module_dep` (register-edge) stay in
   `worker.rs` where the helpers live; `cluster::process_cluster` (the worker
   wrapper) + `cluster::insert_cluster` are the `cluster.rs` facade entries that
   delegate. `process_cluster_with_staging` / `commit_staging_to_live` stay in
   `worker.rs`. The functional target (single live orchestration, packet-carries-
   sexps, no parking maps, in-call-stack retry-from-top, kernel unchanged) is
   fully met regardless of file placement.

## Proposed resolution

`/design` reconciles `s78-implementation.md` §1.1 / §1.2 / §3 / §4 prose to the
as-built shape above (packet = 1b on `ModuleState`; commit stays in
`check_program_compat`; core stays in `worker.rs` with the `cluster.rs` facade
entries delegating). No intent/scope/soundness change — these are mechanism
detail. If `/design` prefers the companion's placement (core in `cluster.rs`,
commit in `insert_cluster`), that is a follow-on refactor with its own codegen-
ordering rework, not an S78 blocker.

## Operational implication / Context

All S78 gate tests are green with the as-built shape (field-count == 14;
cluster-atomicity; Defect-B; 2-node + 3-node cycle-rejection; FQ-autoload/dep-
chain suite; H5-replay gate green under 50-iter stress both WITH and AFTER the
`eval_in_flight` guard deletion). The divergences are documentation-currency
items, not correctness items.
