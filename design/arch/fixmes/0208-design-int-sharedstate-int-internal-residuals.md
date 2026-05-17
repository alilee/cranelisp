---
number: 0208
target: /design (int)
filed_by: /dev (int)
filed_at: 2026-05-17
sprint_filed: 67
refers_to: design/arch/facades/int.md §"SharedState facade alignment plan", design/arch/facades/int.md §"SharedState" (lines 151-228), src/session_v4.rs:637-806
status: open
---

# Refresh `facades/int.md` for int-internal SharedState residuals after Sprint 67 Cluster B

## Issue

Sprint 67 Cluster B (`/dev (int)` SharedState reconciliation) lands the
edge-aligned subset of the W1 PIF table: `cached_modules` deletes (now
scheduler-only via accessor), `cache_dir` + `cache_state` +
`compiled_o_paths` fold into `ObjectCache`, `current_module` relocates to
`CompilerSession.current_repl_module`. The fields below are confirmed
LIVE by W3 implementation inspection and stay on `SharedState` past S67
close — but their as-built rustdoc no longer matches the facade-plan
disposition, and the facade itself either omits them entirely or carries
a stale narrowing direction.

Fields needing facade-text refresh (all stay on `SharedState` post-S67;
narrowing is S68+ scope):

1. **`next_type_id: AtomicU32`** — Facade `SharedState` block omits it.
   Plan row says `PFR — facade widens`. Confirmed live (TypeCheckEnv
   borrows it on every cluster).

2. **`test_runner_state: Box<TestRunnerState>`** — Facade `SharedState`
   block omits it. Plan row says `PFR — facade widens`. Confirmed live
   (session-stable Box for thread-local intrinsic indirection).

3. **`suspend_states: Mutex<HashMap<ModuleFullPath, ModuleSuspendState>>`**
   — Plan row says `PIF — relocate or eliminate` gated on FIXME 0179.
   Confirmed live in S67 (pre-cluster-atomic resume-on-dep-arrival path
   still uses it). Facade should document the deferred-deletion plan
   with the gate explicit.

4. **`promote_nice_workers: AtomicBool`** — Facade `SharedState` block
   omits it. Plan row says `PFR — facade widens`. Confirmed live
   (per-iteration read by `spawn_nice_workers`; write by
   `wait_object_complete` hot-flush boost).

5. **`repl_check_state: Mutex<Option<CheckState>>`** — Plan row says
   `PIF — relocate to CompilerSession`. Confirmed live in S67 (two REPL
   eval paths + `tc_snapshot`/`tc_restore`). Relocation needs cluster-
   atomic completion first; deferred to S68.

6. **`codegen_behaviour: CodegenBehaviour`** — Added in S67 W4 per
   FIXME 0205; facade has the cross-reference but not the field row.
   Currently independent of `SessionSettings`; consider folding under
   the §"Settings and config" subsection per FIXME 0205 proposal.

7. **`file_to_module: Mutex<HashMap<PathBuf, ModuleFullPath>>`** — Plan
   row says `PFR — facade widens`; facade omits it. Confirmed live (file
   watcher cascade in `try_pop_changes`).

8. **`module_sexps: Mutex<HashMap<ModuleFullPath, Vec<Sexp>>>`** — Plan
   row says `PIF — relocate` (process_cluster local). Currently load-
   bearing across the cluster-atomic transition; see FIXME 0179 +
   cluster-mode read-union completion.

## Proposed resolution

Edit `design/arch/facades/int.md`:

1. §"SharedState" block (lines 151-209) — add the seven missing rows
   (`next_type_id`, `test_runner_state`, `suspend_states`,
   `promote_nice_workers`, `codegen_behaviour`, `file_to_module`, and
   the `repl_check_state` deletion direction). Each row carries its
   facade-plan disposition (PIF/PFR/cross-field).

2. §"Initiator vs worker reach" table (lines 213-226) — add rows for
   the seven fields, plus update the existing `current_repl_module`
   row to reflect the S67 W3 relocation (now on `CompilerSession`,
   not `SharedState`) — that change ships in S67 sub-fire 2.

3. §"SharedState facade alignment plan" (lines 232-265) — refresh the
   "S67 W1 reconciliation" net-direction sentence to reflect what
   actually landed in S67 vs what carries forward to S68. Today says
   "/dev Wave 3 picks one" for the `ObjectCache` row — that decision
   is taken (PIF-author, see sub-fire 3 commit). The narrowing of
   `repl_check_state`, `suspend_states`, `module_sexps` is deferred.

4. §"Int-owned JIT intrinsics" — already covered by FIXME 0205 for the
   12-fn trace edifice and `codegen_behaviour` thread; this FIXME does
   not duplicate that scope.

## Operational implication / Context

**Sequencing**: Lands after S67 Cluster B close (sub-fires 1–3 in this
fire). `/dev (int)` does not edit `facades/int.md` (file-ownership
boundary).

**Cascade with FIXME 0205**: 0205 covers the trace-edifice surface +
`build_program_compat` validator wiring. This FIXME (0208) covers the
broader SharedState residuals. Together they close the S67 facade-text
debt; the next /design (int) fire can resolve both in one pass.

**Public-API impact**: `int` is a binary crate — no public-api shift.
The facade refresh is documentation-only.

**Unit-of-work**: medium (~60 lines of facade text across two §-blocks
and one table).
