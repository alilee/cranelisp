# Sprint 78: int restructure — cluster-atomic orchestration + in-call-stack dependency threading

**Status**: PHASE 5 LANGUAGE (ACTIVE) — Wave 2 (D/D/R on src/)

**Goal**: Transform `int` to its target-state flow per `design/int/s77-int-restructure.md` and get the suite largely green — `cluster::process_cluster` as the single Pass-0/1/2 orchestration with in-call-stack dependency threading, deleting the cross-thread `module_sexps`/`suspend_states` parking maps that are the S60–S62 heisenbug substrate. Land it complete to the target shape: no substantial interim change persists past the sprint (Principle 8 — no interim implementations carried forward).

## Scope

**Centerpiece (the whole sprint).** Realize the restructure designed in `design/int/s77-int-restructure.md` — the indivisible rebuild of the dependency block→resume cycle on the most dangerous surface in the codebase:

- **Lift Pass-0/1/2 into `cluster::process_cluster`** (retire `worker::process_module_forms`, ~1200 LOC). The staging-construct + `check_forms` + commit/discard core (already live since `a2dcebd`) moves into `src/cluster.rs`, wrapped with the Pass-1 expand loop, Pass-0 structural peel, and the in-call-stack gap-drive.
- **In-call-stack dependency threading** — a worker that hits a dependency gap drives the dep to readiness *within its own call frame* and retries its cluster from the top against now-larger live state, instead of parking half-finished state into shared maps for another thread to resume. `module_sexps` + `suspend_states` delete from `SharedState` (16 → 14 fields).
- **Workaround removal** — `eval_in_flight` guard + `register_dep_for_eval` republish dance delete with the maps (the H5 fix's reason-for-being evaporates), gated on a retained H5-replay regression test.
- **Scheduler cleanup** — `resume_from_form` machinery + dead `PriorityEntry`/`BlockingJitCodegen` removal.
- **Test regrounding** — relocate `shared_state_field_count` out of `tests/facade_pif_rows.rs` (it pins int-*internal* shape, not a boundary — FIXME 0298) into an int-internal target tracker; it regrounds to passing at 14. Behaviour tests (Defect-B resume, H5/heisenbug suite, cluster-atomicity) stay green by construction.

**Per FIXME 0310:** "Step 0" (sexps-onto-packet) is **not** cleanly separable — it folds into the indivisible Steps 1+2 span. The restructure is one red→green change; `/arch` corrects the design doc §5/§2.3 in the Phase-2/3 design pass before `/dev` begins.

**Soundness obligation (the central deliverable, not a side-effect):** the in-call-stack model must be *validated under `CRANELISP_SCHEDULER_TRACE` stress*, not asserted. The argument — in-progress cluster state is stack-local (no sharing → no race); cross-thread signalling is monotonic-terminal-only (publish-once → no resume race) — folds in the deferred S62 concurrency audit.

### Out of scope (deferred to S79+, Stage 2 component drawdown)

- Platform-interface round-trip (FIXME 0289 + 0229–0235 residuals + 0238) — independent surface; defer.
- Stdlib in-language test runner (0273); legacy test harvest (0116–0149); the ~40 deferred-live FIXMEs + W0 follow-ups (0303/0306/0308/0304/0309).
- Performance baseline (Stage 3); Phase-6 user-facing docs/demos/exemplar showcase (Stage 4).
- `/spec` items 0307 (EOF-error §5.13.2), 0141 (TCO MUST), 0278 (Self capitalization).

**Sprint shape (user-directed, Phase 1 gate 2026-06-10):** *"Transform int and get to largely green based on the target design. We don't want substantial change to persist."* Dedicated single-deliverable sprint: the restructure lands **complete to the target shape and largely green within S78** — not a multi-sprint half-build. Design §7's arc holds: Steps 1+2 are an indivisible, very-high-risk, build-red span re-confronting the H5 bug class (we remove their fix and argue it is no longer needed); rebuild → workaround-removal-gated-on-new-regression-test → deletion → reground, with stress-validation between each.

## Settled decisions (Phase 1 user sign-off, 2026-06-10)

Per `feedback_explicit_decision_review` — concurrency-sensitive architecture confirmed at the scope gate before `/arch`/`/dev` fire. The design doc (§3.3, §3.5) recommended each; user confirmed.

- **OQ-1 — (b) block on scheduler [CONFIRMED].** On a dependency gap the worker drops its staging frame, registers the dep, and blocks on the scheduler (cycle-check fires first); the pool processes the dep; the worker retries its cluster from the top against now-larger live state. Option (a) recurse-in-frame **rejected** — two modules' staging on one stack re-creates the entanglement the restructure removes and defeats cycle detection.
- **OQ-3 — delete, gated on H5 test [CONFIRMED].** `eval_in_flight` guard + `register_dep_for_eval` republish dance + `republish_module_sexps_from_symbol_table` delete with the maps, gated on a retained H5-replay regression test green under `CRANELISP_SCHEDULER_TRACE` stress. The repro joins the suite as an eternal regression guard.
- **OQ-2 / OQ-4 (validation obligations, not choices).** Cycle-rejection (Decision 30) still fires before any wait; Defect-B "resume restarts Pass-2 from 0" semantics preserved-by-construction (retry-from-top has no saved index). Confirmed by retained tests; no user decision needed.

## FIXME debt

| FIXME | Target skill | Status | Notes |
|---|---|---|---|
| 0176 | /arch (carrier) | open | Cluster-orchestrator scope; `module_sexps`/`suspend_states` removal is its residual scope. Residual-scope note updated (Phase 2). Closes when the restructure lands. |
| 0310 | /arch | **RESOLVED + deleted** | Step-0-not-separable correction actioned into design §2.3/§5/§7 (Phase 2). File deleted. |
| 0298 | /arch | open | int-facade reframe + W-Retire doc-reorg. **Phase 2 ruling: W-Retire runs AFTER the restructure, NOT in S78** — restructure has no facade edit this sprint; W-Retire records the 14-field SharedState target when it runs. |
| 0239 | /arch | open | **Phase 2 ruling: DEFER (independent)** — typecheck/primitives seeding surface; disjoint from the restructure. Out of S78. |

## Architecture review (Phase 2)

**Verdict: PASS — no scope revisions** (`/arch`, 2026-06-10).

- **Coherence + Principle-8 interim-risk: PASS.** Steps 1+2 build the target shape directly (`drive_gap_to_readiness` + packet-carries-`Arc<[Sexp]>` are target structures, not scaffolding); Steps 3–6 are pure deletion/cleanup; no step introduces a structure a later step tears down. The only residual is a documentation tombstone (stale facade SharedState rows until W-Retire) — not an interim *implementation*; the int-internal `shared_state_field_count` tracker guards the real shape.
- **FIXME 0310 actioned + deleted.** Design doc §2.3 gained the publisher-vs-reader-side subsection (proves entry-module sexps are read on the resume path → not independently relocatable); §5 folded "Step 0" into the indivisible Steps 1+2; §7 superseded the "land Step 0 in S77" sub-recommendation.
- **Target sequence diagram reconciled.** `concurrency/dependency-protocol-target.mmd` + `.svg` redrawn to the in-call-stack option-(b) shape; `concurrency/README.md` updated.
- **Canonical cascade confirmed (design §8).** Verified int-interior by source: `PriorityWork`/`ModuleSuspendState` are int-internal (not `cranelisp-types`); `Sexp` rides the packet unchanged; `SymbolTableAccess`/`View`/`check_forms`/`ProcessedCluster` untouched. **No `cranelisp-types` change, no cross-crate type, no new boundary type.** Only canonical touch: `bounded-contexts.md §6.2` sharpening sentence (landed).
- **W-Retire (0298): sequenced AFTER the restructure, NOT in S78.** Editing facade SharedState rows in place now only to retire the facade later is throwaway churn; the restructure has **no facade edit this sprint** — W-Retire records the 14-field target shape when it runs. S78 stays the single-deliverable restructure sprint.
- **FIXME 0239: DEFER (independent).** Touches typecheck/primitives seeding surface; names no `SharedState`/`process_cluster`/scheduler/worker/block→resume. Disjoint from the restructure.

**Gate: cleared for Phase 3.**

## Skill plans (Phase 3)

### /design (src/) — DONE (Phase 3)

- **Task**: Refined the `/arch` proposal into an implementation-ready design. Output: new `design/int/s78-implementation.md` (cross-referenced from `s77-int-restructure.md`).
- **Crate**: src/ (int binary)
- **Key outputs**:
  - **Packet type = `Arc<[Sexp]>`** on `PriorityWork::Typecheck { module, sexps }`; recommended the sexps live on `ModuleState` so the requeue path reconstructs the packet (eliminates the keyed map outright).
  - **Signatures pinned**: `cluster::process_cluster(shared, forms: Arc<[Sexp]>, scope) -> Result<ProcessedCluster, CranelispError>` + shared `process_cluster_once` core (`Ok | Gap(ResolutionGap) | Err`) + `drive_gap_to_readiness(shared, scope, &gap)` (register-edge only). `ProcessedCluster` unchanged.
  - **Mechanism correction (load-bearing)**: the proposal's §3.3 "W parks in `wait_for_typecheck`" is wrong — **there is no park API**. The real kernel is *requeue-on-pool*: the worker returns to the pool (freed, not parked); the scheduler requeues the work via `try_unblock_locked` on dep-done. "In-call-stack" describes the **state** (stack-local staging, dropped-and-rebuilt-from-packet), NOT thread-blocking. Kernel preserved verbatim. Resolved int-interior (no boundary/Decision change → no /arch FIXME; FIXME 0298 confirms SharedState/scheduler/worker are int-internal).
  - **Deletion surface verified larger than the doc**: **30 non-test code sites across 5 files** (worker, session_v4, scheduler, observability), not ~26. Surprises: `PriorityEntry`/`BlockingJitCodegen` are **already deleted** (Step 5 reduces to `resume_from_form`-only); `reload_module` + `re_register_module` also publish to `module_sexps` (proposal §5 omitted them). Field count 16→14 exact.
- **Acceptance**: Implementation-ready — nothing blocks Phase 5. `src/CLAUDE.md` stale-paragraph correction recorded as a Phase-5 `/dev` action item (exact wording in the design doc; not edited by /design — it is /dev-owned).

### /qa — DONE (Phase 3)

- **Task**: Authored the Phase-3 test plan. Output: new `tests/plan/sprint78-restructure.md` (regression guards + soundness evidence; no new spec coverage — behaviour-preserving re-plumbing).
- **Key outputs**:
  - **H5-replay gate test** (`repl_persist_race.rs::h5_replay_gate_deterministic_under_scheduler_stress`): two-input `(import helper)` + dep-load under `CRANELISP_SCHEDULER_TRACE`. **Stress-green = 50 iterations, fresh tmpdir each, zero failures** — no N-of-M tolerance, no retry ("flaky" is a banned disposition). **GATES Step 3 guard-deletion**: green with guard present, must stay green after deletion.
  - **OQ-2 cycle-rejection** (`spec_08_modules.rs::mutual_import_cycle_rejected_before_wait_neg`): tightest 2-node `m↔n` (existing `module_cycle_detection_neg` is a looser 3-node); asserts `!success` + a `.timeout()` liveness bound (prompt rejection = "fires before any wait" evidence).
  - **`shared_state_field_count` relocates** out of `tests/facade_pif_rows.rs` into `tests/regression.rs`; tightens `<= 14` → `== 14`; stays failing-not-ignored at 16 until Step 2 lands.
  - **Behaviour-preservation set (real names verified)** stays green: `defn_before_import_resumes_correctly_after_dep_load` (Defect-B/OQ-4), `cache_repl_loads_heisenbug_parallel_stress`, `heisenbug_race_reduced_concurrent_import_pairs`, `module_cycle_detection_neg`, the FQ-autoload/dep-chain suite, `process_form_dispatch.rs` cluster-atomicity (verified observable-only).
  - **3 tests MUST reground off internals** (all `repl_persist_race.rs`): `h5_gate_typechecking_user_fires_only_on_repl_thread`, `h5_normal_completion_does_not_starve_repl_eval_thread`, `repl_dep_load_no_race_with_persistent_workers` — reground from probing `eval_in_flight`/`EvalInFlightGuard`/the `"no parsed sexps"` string to observable outcomes (strictly stronger).
- **Acceptance**: Plan gives /dev + /qa enough to author failing tests in Phase 5 Stage 1. Two non-blocking calibration caveats (iteration-count floor; relocation landing file).

### /spec — NOT INVOKED

No language-semantics change. Confirmed Phase 2 + Phase 3 (int-interior re-plumbing).

### /arch — interface work COMPLETE (Phase 2)

No new boundary types, no `cranelisp-types` change. The /design "requeue-not-park" correction is int-interior prose-mechanism, not a Decision/boundary — no cascade owed. (Doc-currency note: master `s77-int-restructure.md` §3.3 mechanism prose is now superseded by `s78-implementation.md`; /arch reconciles §3.3 opportunistically or folds into W-Retire — non-blocking.)

## Waves (Phase 4)

Single crate (src/), single indivisible centerpiece → waves are sequential gates, not parallel fan-out. The restructure's internal Steps 1–6 are the `/dev` implementation sequence (per `s78-implementation.md`), each gated by the `/qa` test map (`tests/plan/sprint78-restructure.md §5`).

### Wave 1 (Phase 5 Stage 1) — QA-first: author the failing tests + guards

| Skill | Crate | Task | Status |
|---|---|---|---|
| /qa | tests/ | Author H5-replay gate test (50-iter stress) + 2-node cycle-rejection test as failing/guard; relocate `shared_state_field_count` → `tests/regression.rs` (`== 14`, failing at 16); **reground the 3 internal-probing tests to observable outcomes NOW** (decouple from `eval_in_flight`/`module_sexps` so /dev's Step-3 deletions don't break the build). Behaviour-preservation set stays green. | **DONE** |

**Wave 1 outcome:** `repl_persist_race.rs::h5_replay_gate_deterministic_under_scheduler_stress` (50 iters, **3.0s isolated**, green-with-guard = the OQ-3 gate); `spec_08_modules.rs::mutual_import_cycle_rejected_before_wait_neg` (green); `regression.rs::shared_state_field_count_at_target_14` (relocated out of `facade_pif_rows.rs`, **RED at 16** — the durable green-flip tripwire for Steps 1+2; `== 14`). 3 internal-probing tests regrounded to observable outcomes — **grep confirms `tests/` has zero code references to `eval_in_flight`/`EvalInFlightGuard`/`module_sexps`/`suspend_states`/`ProcessResult::Blocked`/`resume_from_form`** (only comments + the field-count source-text scan remain), so /dev's deletions will NOT break the test build. Suite subset 58 passed / 1 red-by-design / 8.22s. **/dev coordination notes:** (1) `"no parsed sexps for module 'user'"` is a user-facing error string asserted by 5 `s60_run_tests_reduction_*` tests — coordinate wording if Steps 1+2 change that path; (2) pre-existing dead-code `repl_std` (`spec_05_definitions.rs:34`) is NOT /qa's and NOT this restructure's — leave it.

### Wave 2 (Phase 5 Stage 2) — D/D/R on src/: land the restructure

| Skill | Crate | Task | Status |
|---|---|---|---|
| /dev | src/ | Implement the restructure per `s78-implementation.md`: **Steps 1+2** (indivisible red span — lift Pass-0/1/2 into `cluster::process_cluster`, packet-carries-sexps, in-call-stack requeue-on-pool gap-drive, delete `module_sexps`/`suspend_states`) → **Step 3** (delete `eval_in_flight` guard + republish, **gated on H5 test green under stress**) → **Step 4** (retire `process_module_forms`, thin the worker loop) → **Step 5** (scheduler cleanup — `resume_from_form` only) → **Step 6** (reground the 3 internal-probing tests + correct `src/CLAUDE.md`). Regenerate baselines only at the 1+2 span close. | pending |
| /review | src/ | **ARCHITECTURAL AUDIT (user-reframed): parallel codepaths / escape hatches / facade drift.** | **DONE** |

**/review verdict: restructure substantially holds the facade.** CLEAN: single-orchestration core (`process_cluster_once` is the ONLY module-form path; `process_module_forms`/`ProcessResult::Blocked`/`BlockAction`-park/`ModuleSuspendState`/`pass2_resume_index`/`resume_from_form`/`eval_in_flight`/`EvalInFlightGuard`/`republish_*` all GONE → Step 3 DID complete); only 2 sanctioned thread-spawn sites (priority pool + nice pool); all live-table writes via `commit_staging_to_live` staging discipline; `register_dep_for_eval` now a pure scoped wait. **Findings:**
- **B1 (Blocker) — `user`-module dual-orchestration; FALSE invariant comment.** `scheduler.rs:94-97` claims `user` is "never requeued onto the pool" — but it IS: REPL registers `user` with `sexps=Some(init)`; on a dep gap `block_for_typecheck(user,dep)` → `TypecheckBlocked` → `try_unblock_locked(user)` requeues it → a pool worker runs `process_cluster(user, STALE init sexps)` **concurrently with the eval thread's retry of the same `user` live table.** Benign-by-luck only because fresh-REPL init source is `String::new()` (worker re-typechecks empty = no-op); **NOT benign when `user.ModuleState.sexps` is non-empty** (`--run`-then-REPL / non-empty entry) → two actors on one module = the in-progress-sharing class the restructure aimed to remove, **relocated from `module_sexps` to `ModuleState.sexps`.** Fix = single-orchestrator ownership of the eval-owned caller (don't give it a pool-claimable `ModuleState`, or skip it in `block/try_unblock`). Needs `/design`(int)→`/dev`(+`/qa` repro: `--run`-then-REPL-then-import-gap). False comment must not ship regardless.
- **I1 (Important)** — `BlockAction` retained as Pass-0 peel signal vs design said "fold"; NOT a parallel path (converts to `Gap` immediately) — as-built/as-design reconciliation (`/design`/`/dev`).
- **I2 (Important)** — `ProcessedCluster.entries`/`from_parts`/`insert_cluster` drain loop is DEAD scaffold (commit happens in `check_program_compat`, not `insert_cluster`); land-or-document-and-trim.
- **S1/S2 (Suggestion)** — stale doc tombstones (`worker.rs:4033` actively wrong) + `ProcessResult` header comment / `ClusterOnce`↔`ClusterOutcome` naming drift. Hygiene.

**Wave gates** (per `tests/plan/sprint78-restructure.md §5`): Steps 1+2 → cluster-atomicity + Defect-B + H5-with-guard green; **Step 3 → H5 test green under 50-iter stress (the OQ-3 gate)**; Step 4 → Defect-B preserved-by-construction; Step 5 → full behaviour set; Step 6 → relocation + reground commits land.

**Wave 2 RESULT: restructure LANDED + verified sound** (builds clean; all gate tests green incl. H5 both with+after `eval_in_flight` deletion, field-count==14, cycle-rejection 2+3-node, FQ-autoload, cluster-atomicity — per FIXME 0311; 173/173 broad at `-j2`). The "deadlock" was macOS dyld cold-start on debug test binaries, not a cranelisp bug. /review (architectural audit) PASS-with-B1.

### De-special-casing waves (user-directed 2026-06-11 — all in S78, broken into waves)

Target design: `design/int/s78-entry-module.md` (§1 entry-module, §2 prelude-as-outer-scope, §3 B1). No `cranelisp-types` change. Per-crate D/D/R, QA-first per wave.

### Wave 3 — Entry-module (§1) + B1 single-orchestration (§3) — src/ int-internal

| Skill | Crate | Task | Status |
|---|---|---|---|
| /qa | tests/ | B1 repro (`--run`-then-REPL-import-gap → no parallel re-typecheck of entry module); entry-module-is-not-`user` tests (program with no `user` module compiles+runs; `/mod` no-arg → entry module; entry named non-`user`). | pending |
| /design | src/ | Refine §1+§3 (entry-module concept; B1 ownership-as-data not-pool-enqueued). | pending |
| /dev | src/ | §3: entry module not pool-claimable (ownership-as-data), fix false `scheduler.rs:94` invariant. §1: delete vestigial `"user"` seed (`session_v4.rs:1005`); `handle_mod`/`current_repl_module`/FQ-parse defaults → entry module. | pending |
| /review | src/ | Change-set review. | pending |

### Wave 4 — Prelude-as-outer-scope (§2) — cranelisp-typecheck + src/ + spec

| Skill | Crate | Task | Status |
|---|---|---|---|
| /spec | spec/ | Editorial align §8.6.4/§8.8: implicit prelude = outer scope consulted on a miss, not materialised; "injection" = activating the fallback. | pending |
| /qa | tests/ | explicit/local silently shadows prelude; explicit-vs-explicit still ambiguous (§8.6.5); `(import [prelude []])` refusal → no fallback; primitives-via-prelude resolve; `/imports` shows "Prelude (implicit)" group. | pending |
| /design | cranelisp-typecheck, src/ | Refine the outer-scope fallback per crate. | pending |
| /dev | cranelisp-typecheck | The 2 resolution chokepoints (`probe_module_entry_owned` checker.rs:979; `current_symbol_table→View` checker.rs:416 two-hop). | pending |
| /dev | src/ | Installer: `inject_prelude_if_needed` sets fallback bit (session-side `SharedState`) instead of flattening; delete `is_seeded`. Introspection: `/imports` group + `describe_symbol` prelude hop. | pending |
| /review | cranelisp-typecheck, src/ | Per-crate change-set review. | pending |

### Wave 5 — Expunge + cleanup

| Skill | Crate | Task | Status |
|---|---|---|---|
| /dev | src/ | Expunge stale/false comments (the `scheduler.rs:94` invariant lands in W3; `session_v4.rs:1007` stale special-forms comment; `is_seeded` doc); reconcile FIXME 0311 (I1 `BlockAction` doc, I2 `ProcessedCluster` dead-scaffold) + /review S1/S2 tombstones. | pending |
| /arch | design/ | Expunge canonical-set references (`bounded-contexts.md §6`, `facades/int.md`, `src/CLAUDE.md`); author Principle 19 ("No module is privileged by name") if user-approved. | pending |

**Wave gate (each de-special wave):** scan `design/arch/fixmes/` for open `target: /dev`/`/qa`/`/typecheck`/`/spec`; tests green at sane `-j` (dyld — use `-j 2` or `--release` for stress, NOT high-concurrency debug).

## Notes

- **PIVOT (user-directed 2026-06-10) — entry-module de-special-casing.** The /review B1 (`user`-module dual-orchestration) is a symptom; the disease is that the **entry module** (the `main`-bearing / REPL-target module; `"user"` is ONLY the default CLI name — most programs have no `user` module) has accreted **special-casing it should not have**, violating the principle "no module special treatment except synthetic (`primitives`/`platforms`/`macros`) + `prelude` (implied import)". Sites: (1) hardcoded `"user"` init-seed `session_v4.rs:1005` with a **STALE comment** — claims `register_builtins` "registers special forms on it" but special forms mount at **root `""`** (`bootstrap.rs:295`, test `mounts_special_forms_at_root`); the real entry registration is the **root compile call `s.register_module(entry_module_name)` in `main.rs:172`** (correct, name-agnostic). (2) `imports.rs:311` `m == "user" || "primitives"` seeded-import ambiguity-skip — name-based hack from **S76 W2 `d62db12`** ("seeded builtins take priority"); wrong — only `prelude` is implied, primitives reach user code via prelude (D0048 uniformity). (3) `handle_mod` no-arg → `"user"` (`2682`) should → entry module. (4) `current_repl_module` default = `"user"` (`1154`) should = entry module. (5) the dual-orchestration (B1). **All to retract + expunge from docs.** Recorded in memory `project_entry_module_concept`. **Audit-first `/arch`+`/spec` pass fired to define the target (entry-module concept + import model + single-orchestration + expunge list) BEFORE any /dev.**

**SETTLED through user-led design discussion (2026-06-11):**
- **§2 import model = PRELUDE-AS-OUTER-SCOPE (decided IN SCOPE).** Through a deep back-and-forth the provenance-marker proposal was rejected (provenance is error-message richness, not correctness — ambiguity is binary over the table's actual entries) and the root cause identified: the impl **flattens** the implicit prelude into every module table, then needs `is_seeded`/a marker to re-distinguish what flattening erased. Spec §8.6.4 says explicit shadows the implicit prelude *"just as inner `let` shadows outer"* — i.e. **scope layering**, not a flattened table. **Target: prelude becomes an OUTER SCOPE resolved by symbol-lookup FALLBACK, not materialised into the module table.** Then explicit/local-shadows-prelude is automatic, explicit-vs-explicit ambiguity is unaffected, and `is_seeded` + the `"user"`/`"primitives"` name-keys + the `cranelisp-types` marker ALL delete. One per-module bit (prelude-fallback enabled), OFF when the module refuses/references prelude (`(import [prelude []])` / selective) — same gate as implicit injection today. Recorded: memory `project_prelude_outer_scope`. **Blast radius:** module table stops holding prelude symbols → typecheck name resolution + REPL introspection (`/imports`/`/list`) + the import installer all fall back to prelude on a miss.
- §1 entry-module (kill hardcoded `"user"`, vestigial seed) + §3 B1 single-orchestration remain in scope (clean, int-internal).
- /arch revising `s78-entry-module.md §2` to the outer-scope model + assessing blast radius → then S78-fold-vs-S79 disposition.
- **Wave 2 /dev stopped mid-flight (2026-06-10) — load-triggered deadlock found.** The agent landed the full structural restructure (builds clean: `cargo check --bin cranelisp` green; ~1650 LOC deleted; `module_sexps`/`suspend_states`/`process_module_forms` gone; renamed `process_cluster_once` core + `worker::drive_module_dep` register-edge driver; `src/CLAUDE.md` rewritten). But its `cargo nextest run` deadlocked → agent blocked waiting on hung test processes → stopped via TaskStop. **Diagnosis (/sprint, source-grounded):** restructure is correct in isolation (single program / single import / REPL+prelude / `spec_06` 21/21 / `repl_persist_race` 5/5 all pass alone) but **deadlocks under concurrent suite load (CPU oversubscription)** — the new **REPL eval-path dep-load** (`process_single_form` gap → `wait_module_inmem_complete_blocking`) hits a **lost-wakeup** vs the worker's `notify_*` (hung processes observed at 0% CPU = blocked, not spinning). This is the §3 (3a) eval-path wrapper the design flagged as the central risk. Structurally sound (worker requeue model correct); a wakeup bug in one wait, not a wrong shape. **Gate gap:** the H5 gate test passes in isolation (5.9s) and only hangs under cross-process contention — it does not currently catch this. **Disposition: trace-pinned /dev fix (user-directed 2026-06-10).** Keep the in-tree restructure; fire /dev scoped to pin + fix the eval-path lost-wakeup, verify, then /qa gate.

**Wave 2b RESULT — /sprint's "lost-wakeup deadlock" diagnosis was WRONG (investigate-first overturned it).** /dev audited every wait/notify pair in `scheduler.rs` and found the **guarded-condvar discipline already correct** (predicate re-checked under held lock; state-set-under-lock + `notify_all`; no TOCTOU, no missing-notify). **No source edits made.** The dramatic "hang"/0%-CPU/19-min-nextest was substantially a **macOS dyld cold-start stall on large debug TEST binaries** (independently confirmed: `spec_05_definitions --list` — zero cranelisp code — took **31.03s first launch / 0.00s warm**; the real `cranelisp` binary launches instantly). NOT a cranelisp deadlock. The restructure builds clean and largely passes (broad filter once **95/95 green in 107s**; REPL suites 90 tests **7.6s green ×3**). **BUT a REAL residual surfaced (the actual remaining work):** an intermittent **data-plane race in the REPL `user` module's dual-orchestration** — `user` is BOTH scheduler-registered (workers can claim it) AND eval-thread-driven (`process_single_form`); `try_unblock_locked(user)` requeues it to the worker pool, so a worker AND the eval thread can both process `user` (trace-confirmed: `ModuleStateTypechecking module=user` fires on a worker thread). This is the H5/H6/H7 heisenbug class — **structural, the exact substrate the restructure was meant to remove, still present for the REPL path.** Guarded by `heisenbug_race_reduced_concurrent_import_pairs` + `cache_repl_loads_heisenbug_parallel_stress` (saw 3 fail in one run). Needs a **/design decision on single-orchestrator ownership of the REPL module**, not a condvar patch. **+ test-infra item: /qa should run the stress suite via `--release` (small dyld closures) or cap `--list`/test-thread concurrency + per-test timeout >40s so dyld stalls aren't misread as cranelisp hangs.**

**Investigation CONCLUDED (user-directed investigate-first, 2026-06-10) — restructure is SOUND; the residual is benign + the scare was dyld.** Evidence:
- **Real `cranelisp` binary, import-race scenario ×80 → 80/80 correct** (no wrong output / hang / crash). The real binary launches in ~0s (no dyld stall).
- **Heisenbug guard tests warm ×13 → 13/13 green** (`heisenbug_race_reduced_concurrent_import_pairs` + `cache_repl_loads_heisenbug_parallel_stress` + H5 gate), ~7s each.
- **Broad set (173 tests, 7 binaries) at `-j 2` (low dyld concurrency) → 173/173 passed, 0 skipped (181s)** — incl. `regression::shared_state_field_count_at_target_14` GREEN (SharedState now at **14** — the S77 deliberate-failure tripwire flipped, the restructure's structural proof).
- dyld confirmed independently: `spec_05_definitions --list` (zero cranelisp code) = **31.03s cold / 0.00s warm**. The broad suite at HIGH `-j` is dyld-thrash-bound (can't keep 7 large debug binaries warm) → the "3 failed"/"hang" were dyld cold-start timeouts, NOT the data-plane race.
- **Conclusion:** the `user`-module dual-orchestration is structurally present but produces **no observable correctness failure** under heavy stress. NOT a sprint-blocking defect. Optional follow-up: tidy REPL-module single-orchestrator ownership for soundness-completeness (file as a non-urgent structural item).
- **Methodology note:** /sprint's "lost-wakeup deadlock" framing was wrong; investigate-first (the /dev audit + this repro pass) overturned it — consistent with the S77 investigate-first lesson. The first restructure /dev agent was stopped during its *dyld-stalled verification*, misread as a deadlock; its edits (the restructure) were complete and are sound.

**Status: restructure landed + verified sound. Remaining: /review (Wave 2), full-suite green confirmation (at sane `-j`), /qa dyld test-infra mitigation, optional dual-orchestration tidy. Disposition: ready to proceed to /review + close-prep on user go.**
- Sprint 77 closed at 1152 passed / 1 failed / 8 skipped. The 1 failure is `shared_state_field_count` — deliberately left to reground with this restructure (not papered, per ratified FIXME 0298).
- Design doc `design/int/s77-int-restructure.md` is the `/arch` proposal returning for user review; this sprint's Phase 1 gate is its review point (per FIXME 0310 §"Operational implication").

## Outcome (Phase 7)

{Pending.}
