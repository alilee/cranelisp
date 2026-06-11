# S78 int restructure — implementation-ready companion

**Status:** PHASE 3 DESIGN — implementation companion to `design/int/s77-int-restructure.md`.
**Owner:** `/design` (int). **Author:** Phase 3 design pass (2026-06-10).
**Purpose:** Refine the `/arch` proposal (`s77-int-restructure.md`) from a *proposal* into an *implementation-ready* design, verified against current `src/` source, so `/dev` (Phase 5) implements without re-deriving structure. The proposal owns the *why* (soundness argument §3, scope §7); this doc owns the *what exactly* (pinned signatures, verified deletion-site list, build-state-per-step, source-forced decisions).

This companion is subordinate to the proposal (per `/design` "feature design subordinate to crate design"): it does not re-argue scope or soundness — it pins the source-grounded shape and resolves the open items the proposal abstracts over. Where this doc and the proposal disagree on a *mechanism detail*, this doc (source-verified line numbers) is the implementation reference; where they disagree on *intent*, the proposal governs.

> **Source-line caveat.** Every line number below is verified against the working tree at this Phase-3 pass (2026-06-10). The proposal's inline line numbers were partly stale; this doc supersedes them for `/dev`. Re-confirm with `grep` before editing — the restructure itself moves everything.

---

## 0. The single most load-bearing correction vs the proposal

**The proposal's §3.3 says option-(b) is "register + block: W parks in `wait_for_typecheck`." There is no `wait_for_typecheck` park API on the worker path.** Source verification of the *actual* current block→resume mechanism (the model the restructure must preserve the liveness of):

The current model is **requeue-on-pool**, not **park-the-thread**, for the *worker* path:

1. A worker hits a gap → `process_module_forms` returns `ProcessResult::Blocked { form_index, dep_module, dep_sexps }` (`worker.rs:1283-1320`, `:4369`).
2. `handle_typecheck_work_shared` (`worker.rs:4279`) saves `suspend_states[module] = state`, publishes `module_sexps[dep] = dep_sexps`, calls `set_resume_from_form(module, form_index)`, and **returns to the pool loop** — the worker thread is freed, it does NOT block. The dep-registration + `block_for_typecheck(module, dep, sym)` happened earlier, inside the form handler (`handle_import` → `register_dep` + `scheduler.register_module(dep, true)` + `block_for_typecheck`, `worker.rs:1958`).
3. `block_for_typecheck` (`scheduler.rs:612`) runs `detect_cycle_locked` FIRST (`:631`), then `add_waiter_locked` — it records the edge + waiter; **it does not park anything**.
4. When the dep completes, `notify_typecheck_done(dep)` (`scheduler.rs:661`) sweeps the waiter, clears `blocked_on`, and `try_unblock_locked` (`scheduler.rs:1333`) **re-enqueues** the blocked module's bare `ModuleFullPath` into `typecheck_first`/`typecheck_next` for *any* worker to re-claim.
5. The re-claiming worker re-enters `handle_typecheck_work_shared`, reads `module_resume_from_form` + `suspend_states[module]` + `module_sexps[module]`, and resumes `process_module_forms` from the saved index.

For the **REPL eval** path the shape is different and *already* close to target:

- `process_single_form` (`session_v4.rs:2532`) has a `for retry in 0..MAX_DEP_RETRIES` loop that re-runs `process_module_forms` over `&single_sexp` with a **fresh** `ModuleSuspendState` each retry (`:2567-2571`) — it does NOT use saved suspend state; it re-derives from the same sexp. On `Blocked` it calls `register_dep_for_eval` (`:2614`) which **does block** the eval thread on `wait_module_inmem_complete_blocking(dep)` (`session_v4.rs:2302`) until the pool brings the dep to inmem, then loops to retry. This is the retry-from-top model the target generalizes — but the *caller* (entry/REPL) module's sexps are kept alive across the eval-thread's wait by the H5 `republish_module_sexps_from_symbol_table` (`session_v4.rs:2233`), because the *worker* path may also claim the caller and read `module_sexps[caller]`.

**Implication for the target shape.** "In-call-stack drive, retry from top" must be realized as **two coordinated edits, not one park**:

- **Worker path:** the requeue-based resume is *retained* (the pool, `block_for_typecheck`, `notify_typecheck_done`, `try_unblock_locked` requeue are unchanged kernel) — what changes is that the requeued work item must **carry the cluster sexps on the packet** (so the re-claiming worker reads them off the packet, not `module_sexps`), and the worker re-runs `process_cluster` **from the top with no saved suspend state** (so `suspend_states` + `resume_from_form` delete). The worker frame's "in-call-stack" property is: in-progress staging is a stack local that is *dropped* on a gap (atomic discard) and *rebuilt from the packet's sexps* on resume — it never lands in a shared map. The thread is still freed to the pool between block and resume (liveness preserved); "in-call-stack" describes the *state*, not literal thread-blocking.
- **Eval path:** the `process_single_form` retry loop *already* re-derives from the sexp with no saved state — it stays, but its dependency on `register_dep_for_eval`'s `module_sexps[caller]` republish + the `eval_in_flight` guard deletes, because once the worker path reads caller sexps off the packet there is no `module_sexps[caller]` for a racing worker to find empty.

This is consistent with the proposal's soundness claim (§3.5: "share only monotonic-terminal facts; keep all in-progress state on the owning stack frame") and with the target `.mmd` (`dependency-protocol-target.mmd` step 28: "requeue M's packet (sexps_M ride the packet)"). The `.mmd`'s "park in wait_for_typecheck (W1 yields, pool slot not held busy)" (step 21) is the *abstraction* of "worker returns to pool, scheduler requeues on dep-done" — `/dev` should read it that way, NOT as a literal new park API. **No new scheduler park primitive is introduced; the kernel's block/notify/requeue stays verbatim (OQ-2 cycle path included).**

This is an int-interior mechanism clarification, not a boundary/Decision question — resolved here, no `/arch` FIXME owed (see §6).

---

## 1. Pinned target signatures

### 1.1 The packet type — what rides `PriorityWork::Typecheck`

**Decision: `Arc<[Sexp]>`.**

- `Sexp` is `Clone` and lives in `cranelisp-types` (rides the packet unchanged — confirmed by the Phase-2 cascade, SPRINT.md Architecture review). The current map value is `Vec<Sexp>` (`session_v4.rs:670`). The packet wants cheap clone on requeue (the work item is `#[derive(Clone)]` — `scheduler.rs:175`) and shared ownership across the dispatch→claim→possibly-requeue path, so `Arc<[Sexp]>` over `Arc<Vec<Sexp>>` (one indirection, immutable slice — the sexps are never mutated after parse).
- `PriorityWork::Typecheck(ModuleFullPath)` → `PriorityWork::Typecheck { module: ModuleFullPath, sexps: Arc<[Sexp]> }`. The variant stays `#[derive(Debug, Clone, PartialEq, Eq)]` — `Arc<[Sexp]>` is `Clone`; `Sexp` must remain `PartialEq + Eq` (it is today — the derive on `PriorityWork` compiles, so `Sexp: Eq`). Verify the derive still holds after the change; if `Eq` on `Arc<[Sexp]>` is awkward in a test assertion, the test asserts on `.module` not the whole variant.
- **Where the sexps enter the packet.** The scheduler's `register_module(module, delays_other)` (`scheduler.rs:304`) currently enqueues a bare `ModuleFullPath` into `typecheck_first`/`typecheck_next` (`VecDeque<ModuleFullPath>`). To carry sexps, the enqueue must carry them. Two source-faithful options for `/dev` (resolve during Step 1 — both are target-shaped, neither is interim):
  - **(1a) Queue carries the packet.** Change `typecheck_first`/`typecheck_next` from `VecDeque<ModuleFullPath>` to `VecDeque<(ModuleFullPath, Arc<[Sexp]>)>` (or `VecDeque<PriorityWork>`), and `register_module` gains a `sexps: Arc<[Sexp]>` parameter. `take_priority_work` (`scheduler.rs:458`/`:480`) pops the pair and returns `PriorityWork::Typecheck { module, sexps }`. The requeue path (`try_unblock_locked`, `scheduler.rs:1347-1355`) must re-push the *same* packet — so `ModuleState` must retain the `Arc<[Sexp]>` (store it on `ModuleState`, `scheduler.rs:~85`, alongside `resume_from_form` which is being deleted) to reconstruct the packet on requeue. **This is the cleaner target shape** — the scheduler owns the work item fully; there is no side map.
  - **(1b) Sexps on `ModuleState` only.** Keep the queues `VecDeque<ModuleFullPath>`; store `Arc<[Sexp]>` on `ModuleState` at register time; `take_priority_work` reads it from `ModuleState` when constructing the returned `PriorityWork::Typecheck`. Requeue is unchanged (bare path); the sexps are found on `ModuleState`. **This is a smaller diff** but keeps a module→sexps association inside the scheduler (functionally `module_sexps` relocated one layer down).
  - **Design recommendation: (1a).** It removes the keyed association entirely (the sexps *are* the work item), matching the proposal's "sexps travel with the work item, owned by it, dropped when the work completes" (§2.3 payload #1). (1b) re-creates a thinner `module_sexps` on `ModuleState` — admissible but less aligned with the target. `/dev` may fall back to (1b) if (1a)'s `Eq`/queue-type churn proves disproportionate; flag the choice in the `/dev` close note. Either way `SharedState.module_sexps` deletes.

### 1.2 `cluster::process_cluster` — the single orchestration entry

Current (zero live caller, `cluster.rs:177`):
```rust
pub fn process_cluster(
    shared: &SharedState,
    forms: Vec<cranelisp_types::Sexp>,
    scope: &ModuleFullPath,
) -> Result<ProcessedCluster, CranelispError>
```

**Target signature — keep it, with one change to `forms`:**
```rust
pub fn process_cluster(
    shared: &SharedState,
    forms: Arc<[cranelisp_types::Sexp]>,   // was Vec<Sexp>; now the packet's payload, by value-cheap-clone
    scope: &ModuleFullPath,
) -> Result<ProcessedCluster, CranelispError>
```
- Error type is `CranelispError` (NOT a typecheck `CheckError` — the boundary already converts via `check_error_to_cranelisp_error`, `worker.rs:374`; `process_cluster_with_staging` returns `Result<Option<ResolutionGap>, CranelispError>` and the int boundary owns the gap→scheduler translation per `facades/int.md` invariant 5). `process_cluster` returns `CranelispError` on hard failure; recoverable gaps are driven *internally* (the gap never escapes `process_cluster` as an error — it becomes a `drive_gap_to_readiness` call + retry, §1.4).
- `forms` as `Arc<[Sexp]>` lets the worker pass the packet's payload without a clone, and lets the internal retry loop re-borrow the same slice on each `continue` (the proposal's "retry from the top against larger live state", §2.2). Take `Arc<[Sexp]>` by value (cheap Arc clone) so the caller's packet stays intact for a scheduler requeue if `process_cluster` itself returns and the worker re-dispatches.
- `ProcessedCluster` is **unchanged** (`cluster.rs:67-154`) — it already carries `entries`, `warnings`, `resolved_imports`, `introspection_records`, and `from_parts`/`empty`/`is_empty`/`into_iter` accessors. The new body populates it from the committed staging (today the live path commits inside `process_cluster_with_staging` and returns `empty()`; the target moves the commit into `insert_cluster` and routes the drained entries through `ProcessedCluster.entries` — see §4 Step 1 note on commit-site).

### 1.3 `drive_gap_to_readiness` — the in-call-stack gap driver

**New free function in `cluster.rs`** (the proposal names it; pin the signature):
```rust
fn drive_gap_to_readiness(
    shared: &SharedState,
    scope: &ModuleFullPath,         // the cluster that hit the gap (the blocking module M)
    gap: &cranelisp_types::ResolutionGap,
) -> Result<(), CranelispError>
```
- Body = the union of today's two block-paths, collapsed:
  1. Map `gap` → the needed module (`gap_module(&gap)`, `worker.rs:~2115` `ResolutionGap::{SymbolTypechecked,MacroInMem,Type}` → `fq.module`). A gap that names no module (or a module already in `symbol_tables`) is a hard error / immediate-retry respectively (preserve `handle_fq_autoload_gap`'s "already loaded → hard error" arm, `worker.rs:1460`).
  2. `ensure_registered(needed)` — resolve the module file (`pipeline::resolve_module_file`, same rules as `import`, `worker.rs:2477`), parse to `Arc<[Sexp]>`, `scheduler.register_module(needed, sexps, /*delays_other=*/true)`, recording source-hash + `file_to_module` + `/source` text (the current `register_dep` prologue, `worker.rs:2169` — retained, but its `publish_dep_sexps` step is replaced by handing sexps to `register_module`).
  3. `scheduler.block_for_typecheck(scope, needed, sym)` — **unchanged kernel** (cycle-check fires first, OQ-2; `scheduler.rs:612`). For an already-`TypecheckDone` dep (cache-hit / already-imported) keep the immediate `unblock_module(scope)` re-queue (`scheduler.rs:602`), since no future `notify_typecheck_done(needed)` sweep will fire.
  4. Return `Ok(())`. The **caller** (the `process_cluster` retry loop OR the eval-thread retry loop) is responsible for the wait+retry: on the worker path the worker returns to the pool and the requeue brings it back (§0); on the eval path the eval thread calls `wait_module_inmem_complete_blocking(needed)` then loops. `drive_gap_to_readiness` does NOT itself block — it registers + records the edge, mirroring the current split where the form-handler registers and the *caller* (`handle_typecheck_work_shared` returns to pool / `register_dep_for_eval` waits) drives the wait.

> **Why `drive_gap_to_readiness` does not block internally.** Keeping the wait in the caller preserves the worker-pool liveness property verbatim (a blocked worker is freed, not held). If `drive_gap_to_readiness` blocked, it would have to block *the worker thread*, re-introducing the exact "a thread is busy waiting" cost the requeue model avoids. The proposal's "block on scheduler" (OQ-1 b) is realized as register-edge + return-to-pool + requeue, NOT thread-park (§0). This is the single most important shape decision for `/dev` to get right.

### 1.4 The `process_cluster` retry envelope (target body)

```rust
pub fn process_cluster(shared, forms: Arc<[Sexp]>, scope) -> Result<ProcessedCluster, CranelispError> {
    loop {
        // Pass 1: expand each form in-call-stack (already int's — expand_sexp_recursive).
        // Pass 0: peel import/export/mod/platform; install_imports/install_exports/mod-alias;
        //         a structural dep that is unloaded surfaces here as a gap too.
        // Build: build_form over the non-structural forms -> Vec<TopLevel>.
        // Stage:  fresh staging SymbolTable; SymbolTableAccess::cluster(...); check_forms.
        match staged_check(shared, &forms, scope)? {
            ClusterStep::Ok(processed)      => return Ok(processed),     // commit happens in insert_cluster
            ClusterStep::Gap(gap)           => { drive_gap_to_readiness(shared, scope, &gap)?;
                                                  // worker: return to pool here (the pool requeues);
                                                  // eval:   wait_module_inmem_complete then continue.
                                                  continue; }
            // hard errors are returned as Err(CranelispError) by `?` above.
        }
    }
}
```
- The proposal's pseudocode (§2.2) is the intent; the source-faithful realization folds today's `process_module_forms` Pass-0 loop (`worker.rs:1272-1330`), `separate_macros` (`:1332`), `pass1_register`/`register_macro_in_module`/`register_default_methods` (`:1341-1349`), `pass2_check_bodies_with_expansion` (`:1359`), and `finalize_module`'s `check_program_compat` (`:1454`) into the single `staged_check` step. The staging machinery (`process_cluster_with_staging` + `commit_staging_to_live`, `worker.rs:273`/`:317`) **moves into `cluster.rs`** and becomes the `staged_check` core.
- **`continue`-on-gap is the retry-from-top.** No `pass2_resume_index`, no saved `expanded_program`, no `ModuleSuspendState`. Each iteration re-expands + re-stages from `forms` against now-larger live (`facades/int.md:1224` monotonic-progress termination). Cost (re-expansion) is the proposal's accepted trade (§2.3).

---

## 2. Verified deletion-site inventory

Every `module_sexps` + `suspend_states` read/write site in `src/`, with verified line numbers and per-site disposition. **Count: 30 code sites + 6 test-only sites + 4 doc-comment-only sites = 40 textual hits across 5 files** (the proposal's "~26" undercounted; the surplus is mostly the H5/H4 republish-and-guard cluster in `session_v4.rs` + the dead-code path in `register_transitive_cached_imports`, not new surface). Test-only and doc-comment hits are tagged separately because they delete *as a consequence*, not as orchestration edits.

### worker.rs

| Line | Site | Disposition |
|---|---|---|
| 2128–2146 | `publish_dep_sexps` fn (writes `module_sexps[dep]`) | **delete** — sexps go to `register_module` packet (§1.1), not the map. |
| 2157, 2206–2211, 2218–2227 | `register_dep` prologue: publish step + debug-assert | **relocate-to-packet** — `register_dep` survives as the "parse + record source-hash + /source text + file_to_module" prologue, but its publish + assert delete; it returns `Arc<[Sexp]>` to hand to `register_module`. |
| 2446, 2508 | `register_transitive_cached_imports` comment + `let _ = dep_sexps` | **relocate-to-packet** — pass the returned sexps to `scheduler.register_module(dep, sexps, true)`. |
| 4172 | module-level comment "`module_sexps`/`suspend_states` now live on SharedState" | **delete** (stale doc). |
| 4289–4297 | `handle_typecheck_work_shared` reads `module_sexps[module]` | **delete** — sexps arrive on the packet (`PriorityWork::Typecheck { sexps }`). |
| 4301–4308 | `handle_typecheck_work_shared` takes/creates `suspend_states[module]` | **delete** — no saved state; `process_cluster` rebuilds from packet. |
| 4363–4366 | Complete arm: `module_sexps.remove(module)` cleanup | **delete** — packet drops when work completes (no map entry). |
| 4377–4387 | Blocked arm: write `module_sexps[dep]` + `suspend_states[module]` | **delete** — the whole `ProcessResult::Blocked` arm goes; `drive_gap_to_readiness` replaces it. |
| 4392–4395 | Err arm: `module_sexps.remove(module)` | **delete**. |

`handle_typecheck_work_shared` (`worker.rs:4279`) collapses to the thin body the proposal §2.2 describes: claim packet → `process_cluster(shared, sexps, module)` → `inline_jit_codegen_for_module` → `insert_cluster` → `notify_typecheck_done`. `ModuleSuspendState` (`worker.rs:4140`), `ProcessResult` (`worker.rs:985`, both variants), `BlockAction` (`worker.rs:1178`), `pass2_resume_index` (`worker.rs:1226`), `process_module_forms` (`worker.rs:1230`), `finalize_module` (`worker.rs:1423`), `pass2_check_bodies_with_expansion` (`worker.rs:1615`), and the `BlockAction::Block` returns in `handle_import`/`handle_export`/`handle_mod`/`inject_prelude_if_needed` (`worker.rs:1958, 2587, 2751, 3237`) all delete or fold into `process_cluster` + `drive_gap_to_readiness`.

### session_v4.rs

| Line | Site | Disposition |
|---|---|---|
| 670 | `pub module_sexps: Mutex<HashMap<…, Vec<Sexp>>>` field | **delete from SharedState** (16→15). |
| 682 | `pub suspend_states: Mutex<HashMap<…, ModuleSuspendState>>` field | **delete from SharedState** (15→14). |
| 776 | comment "`module_sexps`/`suspend_states`, which remain worker-shared" | **delete** (stale). |
| 1136–1137 | ctor inits in `SharedState::new` | **delete**. |
| 1872–1892 | `republish_module_sexps_from_symbol_table` write half | **delete** (whole fn, §3.5 / OQ-3). |
| 1894–1939 | `republish_module_sexps_from_symbol_table` fn body | **delete**. |
| 1977–1980 | `reload_module`: `suspend_states.remove` | **delete** — no suspend state to clear. |
| 1994–1997 | `reload_module`: `module_sexps.insert` | **relocate-to-packet** — `reload_module` parses sexps then calls `re_register_module`; the sexps must ride the re-register packet (extend `re_register_module` to carry `Arc<[Sexp]>`, parallel to `register_module` §1.1). |
| 2055, 2080–2083 | `register_module_with_source`: `module_sexps.insert` before register | **relocate-to-packet** — parse → `scheduler.register_module(module, sexps, false)`. |
| 2104–2110 | `register_dep_for_eval` doc (publish/republish references) | **delete/rewrite** — the fn's republish body goes; the fn either deletes or shrinks to "register dep packet + wait_module_inmem_complete" (§3). |
| 2148–2152 | `EvalInFlightGuard` construction | **delete** (OQ-3). |
| 2165–2196 | `register_dep_for_eval` defensive publish pair | **delete**. |
| 2209–2234 | the H5 `republish_module_sexps_from_symbol_table(&caller)` call + rationale | **delete** (OQ-3 — caller sexps ride the packet, no map to republish). |
| 2249–2273 | publish-before-register debug-assert | **delete**. |
| 2178–2183 | `already_published` / `skip_defensive_pair` computation | **delete**. |

### session_v4.rs — test-only (delete as consequence)

| Line | Site | Disposition |
|---|---|---|
| 5467–5524 | `register_dep_for_eval_publish_then_register_is_observable_to_downstream` + helpers reading `module_sexps` | **delete or reground** — these probe the publish-before-register *mechanism* that is being removed. `/dev` deletes them (the behaviour they guarded — dep loads correctly — is covered e2e by the retained H5-replay test `/qa` authors). Flag for `/qa` if any asserts a still-live behaviour. |
| 5557+ | `register_dep_for_eval_uses_delays_other_true` | **reground** — `delays_other=true` survives on the new `register_module(needed, …, true)` call in `drive_gap_to_readiness`; the test reasserts that against the new site, or deletes if it only probes the deleted fn. |

### scheduler.rs

| Line | Site | Disposition |
|---|---|---|
| 91, 125, 145, 428 | `ModuleState.resume_from_form` field + inits | **delete** — no saved resume index (retry-from-top). |
| 1054 | doc comment referencing `module_sexps.contains_key(dep)` | **delete** (stale). |
| 1133–1140 | `module_resume_from_form` accessor | **delete**. |
| 1185–1195 | `set_resume_from_form` accessor | **delete**. |
| 1771–1772 | test ctor inits `module_sexps`/`suspend_states` | **delete** (these are inside a `#[cfg(test)]` SharedState builder). |
| 111, 127, 147, 430, 1325–1356, 1369–1385, 1430–1446 | `eval_in_flight` field + `try_unblock_locked` H5 push-gate + `set_eval_in_flight`/`eval_in_flight_for_test` | **delete** (OQ-3). `try_unblock_locked` simplifies to the unconditional push branch (the `if !eval_in_flight` wrapper goes; the push body stays — the requeue is the worker-path resume, §0). |
| 2003–2162 | `try_unblock_locked_*` eval-in-flight unit tests | **delete** (probe the deleted gate). |

### observability.rs

| Line | Site | Disposition |
|---|---|---|
| 143 | doc "`register_dep` published dep_sexps to `shared.module_sexps`" | **delete/rewrite** (stale doc). |
| 187, 190 | doc referencing `suspend_states` + `republish_module_sexps_from_symbol_table` | **delete/rewrite** (stale doc). |

**Surprises vs the proposal's "~26":**
1. The count is **40 textual hits / 30 non-test code sites** — higher because the H5/H4 republish-and-guard machinery in `register_dep_for_eval` (`session_v4.rs:2104-2273`) is ~10 coupled sites, not one, and `try_unblock_locked`'s `eval_in_flight` gate spans field + gate + setters + 3 unit tests.
2. **`resume_from_form` is a `ModuleState` field, not a `SharedState` field** — its deletion is a scheduler-internal cleanup (Step 5), confirming the proposal's Step-5 framing but pinning the exact sites (`scheduler.rs:91/125/145/428/1133/1185`).
3. **`PriorityEntry`/`BlockingJitCodegen` are ALREADY deleted** (confirmed: `PriorityWork` has only `Typecheck`/`JitCodegen`, `scheduler.rs:175-181`; the priority-codegen queue comment at `:170-174` and `:194-196` confirms removal in S76 W3). The proposal's Step 5 "possibly remove the already-dead `PriorityEntry`/`BlockingJitCodegen`" is a **no-op** — there is nothing left to remove there; Step 5 reduces to deleting `resume_from_form`. `/dev` should NOT hunt for `PriorityEntry`.
4. **`reload_module` and `re_register_module` need the packet change too** — the proposal's §5 Step 1 names `register_module_with_source` + `register_module` + dispatch sites but not `reload_module`/`re_register_module`. The file-watcher reload path (`session_v4.rs:1946`) also publishes to `module_sexps` (`:1994`) and must relocate sexps onto the re-register packet. This is in-scope for Step 1 (the packet-shape change is not complete until every dispatch site carries sexps).

---

## 3. The eval path's fate (source-forced; resolved here)

The proposal abstracts "the REPL eval re-drives a cluster on resume" but does not pin how `register_dep_for_eval` reshapes. Source-forced resolution:

`process_single_form` (`session_v4.rs:2532`) is already a retry-from-top loop that re-derives from the sexp. In the target it calls `cluster::process_cluster(shared, Arc::from([sexp]), &module)` instead of `process_module_forms` + `ProcessResult::Blocked`. But `process_cluster`'s gap branch calls `drive_gap_to_readiness` which (§1.3) does NOT block — so the **eval thread still needs to wait** for the dep before retrying. Two shapes:

- **(3a) `process_cluster` is worker-only; eval keeps its own loop.** `process_single_form` keeps its `for retry` loop, calls a thinner `process_cluster_once(shared, &forms, scope) -> Result<ClusterOutcome, _>` that returns `Gap(needed)` instead of looping, and on `Gap` the eval thread does `ensure_registered(needed)` + `wait_module_inmem_complete_blocking(needed)` + `continue`. The worker path's `process_cluster` wraps `process_cluster_once` in the `loop { … }` with return-to-pool-on-gap.
- **(3b) `process_cluster` takes a "wait strategy".** One `process_cluster` with the gap-wait behaviour parameterised (worker: return-to-pool-and-requeue; eval: block-on-wait). Heavier; risks a mode flag on the hot path (Principle 11 tension).

**Design recommendation: (3a).** Keep the loop owner explicit per caller. The shared core is `process_cluster_once` (expand + Pass-0 peel + stage + check → `Ok(ProcessedCluster)` | `Gap(ResolutionGap)` | `Err`); the worker wraps it in return-to-pool-requeue, the eval thread wraps it in wait-then-retry. This matches today's *de facto* split (worker loop vs `process_single_form` loop) and avoids a mode parameter. `drive_gap_to_readiness` (the register-edge half) is shared by both wrappers; only the *wait* half differs (return-to-pool vs `wait_module_inmem_complete_blocking`). The proposal's single-`process_cluster` framing (§2.2) is the conceptual target; (3a) realizes it as one shared core + two thin wrappers, which is the honest source shape. **Record `process_cluster` (worker wrapper) and `process_cluster_once` (shared core) as the two public/crate functions; `insert_cluster` stays the commit step both call.**

> Once the `eval_in_flight` guard + `module_sexps[caller]` republish delete, the eval path's `wait_module_inmem_complete_blocking(needed)` is race-free by the proposal's argument (§3.5): the caller's sexps are not in any shared map, so no worker can read them empty mid-wait. The retained H5-replay test (Step 3 gate) is the evidence.

---

## 4. Step landing order + build-state per step

Confirms/refines proposal §5. **Steps 1+2 are one indivisible build-red span** (per `feedback_facade_first_migration` + `feedback_facade_walk_no_interior` — touch the structures, accept red, regenerate baselines only at span close).

| Step | Files touched | Build state | What makes it safe to proceed |
|---|---|---|---|
| **1+2 (indivisible)** | `cluster.rs` (new `process_cluster_once`/`process_cluster`/`drive_gap_to_readiness`; move staging core in), `worker.rs` (delete `process_module_forms` + `ProcessResult` + `BlockAction` + `ModuleSuspendState` + `handle_typecheck_work_shared` map-juggle + `publish_dep_sexps` + `register_dep` publish; thin the worker loop), `scheduler.rs` (`PriorityWork::Typecheck { module, sexps }`; queue/`register_module`/`take_priority_work`/`try_unblock_locked` requeue carry the packet; `register_module` + `re_register_module` gain `Arc<[Sexp]>`), `session_v4.rs` (`SharedState` loses both fields + ctor; `register_module_with_source`/`reload_module` parse→packet; `process_single_form` calls the new core; `register_dep_for_eval` republish+guard deleted) | **RED throughout** — expected. The packet-shape change, the orchestration lift, and the map deletion cannot be cleanly separated (FIXME 0310 / proposal §2.3 publisher-vs-reader-side). | Span closes when: `cargo check` green; the dep-load e2e (`spec_08`, FQ-autoload suite), the cluster-atomicity tests, and the H5-replay test all green under one run. **Do NOT regenerate `public-api.txt` baselines until the span closes** (it is the binary crate — no `public-api.txt`; but `facade_pif_rows` field-count regrounds here, see §5). |
| **3 — delete `eval_in_flight` guard** | `scheduler.rs` (`eval_in_flight` field + `try_unblock_locked` gate + setters + accessor + 3 unit tests), `session_v4.rs` (`EvalInFlightGuard` + its construction). | **GREEN after** (deletion-only once 1+2 landed). | **Gated on a retained H5-replay e2e test green** (`/qa` authors; the two-input `(import helper)` + dep-load sequence, green under `CRANELISP_SCHEDULER_TRACE` stress). Per OQ-3 / SPRINT.md settled decision. Do not land Step 3 before that test exists and is green. |
| **4 — retire residual `process_module_forms` artefacts** | `worker.rs` (anything `process_module_forms`-specific that survived 1+2: `finalize_module`, `pass2_check_bodies_with_expansion`, `pass2_resume_index`, `separate_macros` if not reused by `process_cluster_once`). | **GREEN** (deletion once the new core subsumes them). | Mostly subsumed by Step 1+2; Step 4 is the sweep for anything 1+2 left dangling. Confirm `spec_08::defn_before_import_resumes_correctly_after_dep_load` (Defect-B) stays green — retry-from-top has no saved index, so forms-before-import always re-process (OQ-4, preserved by construction). |
| **5 — scheduler cleanup** | `scheduler.rs` (`ModuleState.resume_from_form` field + inits + `set_resume_from_form` + `module_resume_from_form`). | **GREEN** (dead-code removal). | `resume_from_form` has no readers once Step 1+2 deletes the resume path. **`PriorityEntry`/`BlockingJitCodegen` are already gone — Step 5 is `resume_from_form`-only.** |
| **6 — reground tests + field-count** | `tests/` (`/qa`-owned, see §5) + `observability.rs` stale doc comments (`/dev`). | **GREEN.** | Field count is 14 after Step 1+2; the `<= 14` assertion already passes at target. §5. |

**Landing rule for `/dev`:** `(1+2 together)` → `3` (gated) → `4` → `5` → `6`. Regenerate nothing mid-span. One `cargo nextest run` at the close of 1+2 (the wave's risk gate), then per-step runs for 3/4/5/6.

---

## 5. Test regrounding (ownership-correct)

- **`shared_state_field_count_matches_facade_after_pif`** (`tests/facade_pif_rows.rs:590`) asserts `field_count <= 14` by parsing `session_v4.rs` text. After Step 1+2 the count is exactly **14** (verified: current 16 pub fields = scheduler, project_root, lib_dirs, platform_dirs, module_sexps, suspend_states, cache, promote_nice_workers, file_to_module, symbol_tables, next_type_id, module_aliases, typecheck_products, kept_dlls, introspection, test_runner_state; minus module_sexps + suspend_states = 14). The `<= 14` assertion **passes at target** — it is the S77 single deliberate failure (SPRINT.md Notes) that regrounds to green here.
  - **Relocation is `/qa`'s, not `/dev`'s.** Per `tests/CLAUDE.md` (tests are e2e or unit, no middle tier; `tests/` is `/qa`-owned) the relocation of this internal-shape check out of the boundary-conformance file (FIXME 0298) is a `/qa` action. `/design` flags it; `/dev` does not edit `tests/`. **Design note for `/sprint`:** file the relocation as a `/qa` task in Phase 5 (the check moves to an int-internal target tracker — or, since `tests/` has no internal tier, becomes a standing e2e-adjacent structural guard `/qa` owns). It can stay in place and green at 14 for S78; the *relocation* is a follow-on hygiene item, not a blocker.
- **Behaviour tests that stay green by construction:** `spec_08` Defect-B resume; the FQ-autoload suite; cluster-atomicity (staging commit/discard) — the staging core moves file (worker.rs → cluster.rs) but its contract is identical.
- **New tests owed (`/qa` + `/dev`):** the retained H5-replay e2e (Step 3 gate); a mutual-import cycle-rejection e2e (OQ-2 — cycle path fires before any wait, unchanged kernel). Both are `/qa` e2e authoring per the test strategy.

---

## 6. Source-forced decisions — resolved here; no `/arch` FIXME owed

All four items the proposal left open are int-interior mechanism, resolved in this doc:

1. **Packet type = `Arc<[Sexp]>`; enqueue carries the packet (1a recommended).** §1.1. Int-internal (`PriorityWork`/scheduler queues are int-internal per the Phase-2 cascade; `Sexp` rides unchanged). No boundary change.
2. **"Block on scheduler" = register-edge + return-to-pool + requeue, NOT a new park API.** §0 / §1.3. The kernel (block/notify/requeue/cycle-check) is unchanged. No boundary change.
3. **Eval path = shared `process_cluster_once` core + per-caller wait wrapper (3a recommended).** §3. Int-internal orchestration shape.
4. **Pass-0 structural peel moves into `process_cluster_once` before `staged_check`** (`install_imports`/`install_exports`/mod-alias run in-frame; a structural dep surfaces as a gap driven in-frame). §1.4. `ProcessedCluster` already carries the fields the new body needs (`entries`/`warnings`/`resolved_imports`/`introspection_records`); the commit-site moves from inside `process_cluster_with_staging` to `insert_cluster` (route drained staging through `ProcessedCluster.entries`). Int-internal.

**No `/arch` FIXME is filed.** Each item is `SharedState`/`process_cluster`/scheduler/worker interior (FIXME 0298: int-internal, not a boundary). The Phase-2 cascade (SPRINT.md Architecture review) already confirmed no `cranelisp-types` change, no cross-crate type, no new boundary type. The one genuine *clarification* surfaced — that there is no `wait_for_typecheck` park API and "block on scheduler" is requeue-based (§0) — is a correction to the proposal's *prose mechanism*, not to a Decision or boundary; it is recorded here (int-owned design) rather than filed up.

> Re-checked against `bounded-contexts.md §6` (int boundary): the restructure stays inside int — it consumes typecheck's `check_forms`/`SymbolTableAccess::cluster`/`ResolutionGap` unchanged (the int→typecheck call surface is identical), and it touches no frontend/backend/types signature. The §6.2 "submit work and wait on terminal signal" handoff pattern is *realized* by the in-call-stack model (the Phase-2 sharpening sentence already landed). No bounded-context invariant moves.

---

## 7. `src/CLAUDE.md` correction — Phase-5 `/dev` action item (note only)

`src/CLAUDE.md` is `/dev`-owned; `/design` does not edit it. Record for `/dev` to action during implementation (proposal §9):

The `src/CLAUDE.md` §"Cluster-Atomic Orchestration" paragraph "**Status (Sprint 66 Wave 3b-2c.2).** … staging machinery … wired and tested by inspection but **not yet activated on the hot path** — `check_program_compat` continues to use `ClusterContext::Live` pending FIXME 0179 …" is **STALE**. Commit `a2dcebd` landed the read-union and flipped `check_program_compat` to delegate **unconditionally** to `process_cluster_with_staging` (verified: `worker.rs:218-234` delegates unconditionally; `:273-309` is the staging path with `SymbolTableAccess::cluster` + commit-on-Ok / discard-on-Err). Cluster-mode staging is the **live hot path today**; FIXME 0179 is closed.

Corrected wording for `/dev` to write (also update the §"Still on the wall (FIXME 0176/0179)" and §"Macro expansion … The walk" notes that call `cluster::process_cluster` a "zero-caller facade-conformance scaffold" — after S78 it is **the live orchestration**):

> *"Cluster-mode staging is the live typecheck path (`process_cluster_with_staging`, `a2dcebd`). The remaining cluster-atomic work (S78) retired the `process_module_forms` outer per-form loop and lifted Pass-0/1/2 + in-call-stack dep-drive into `cluster::process_cluster` (+ `process_cluster_once` core + `drive_gap_to_readiness`), deleting the cross-thread `module_sexps`/`suspend_states` parking maps and the `eval_in_flight` guard. `cluster::process_cluster` is now the single live orchestration; the `process_module_forms` worker loop is gone."*

Also retire, in the same pass, the stale `src/CLAUDE.md` lines that describe the block→resume via `ProcessResult::Blocked` / `suspend_states` / `module_sexps` republish (the "FQ auto-loading" §"Load + retry" paragraph references `ProcessResult::Blocked { form_index, … }` and "`handle_typecheck_work_shared` and the REPL retry loop already drive block→resume" — both describe the deleted mechanism).

---

## 8. Implementation-readiness verdict

**Implementation-ready for `/dev`.** Pinned: the packet type (`Arc<[Sexp]>`), `process_cluster` / `process_cluster_once` / `drive_gap_to_readiness` signatures, the verified 30-code-site deletion inventory, the build-state-per-step landing order, and the four source-forced decisions resolved int-interior. No `/arch` boundary question blocks Phase 5. The one residual `/qa` coordination item (relocate the field-count check per FIXME 0298) is a non-blocking hygiene follow-on; the check passes green at 14 in place.

The single risk `/dev` must hold (per SPRINT.md soundness obligation): the §0 clarification — "block on scheduler" is **requeue-based**, the worker thread is freed not parked, and the in-call-stack property is about *state* (stack-local staging, dropped-and-rebuilt-from-packet) not literal thread-blocking. Getting `drive_gap_to_readiness` to register-the-edge-and-return (not block internally) is the load-bearing shape; the soundness argument (§3.5 of the proposal) and the H5-replay stress test are the evidence that the substrate is gone.

---

## Change history

- 2026-06-10 (`/design`, Phase 3): authored. Verified all `module_sexps`/`suspend_states`/`resume_from_form`/`eval_in_flight` sites against the working tree; pinned signatures; corrected the proposal's "wait_for_typecheck park" prose to the actual requeue-based model; resolved the four open items int-interior; confirmed `PriorityEntry` already deleted (Step 5 is `resume_from_form`-only); flagged the field-count relocation as `/qa`-owned.
