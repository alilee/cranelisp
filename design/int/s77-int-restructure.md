> **HISTORICAL — superseded slice / working doc (triaged S110, FIXME 0607).** A
> point-in-time implementation-slice narrative, retained for the audit trail only; NOT
> current design intent. The durable design is `int.md` (master) plus the subsystem docs
> indexed in `design/int/CLAUDE.md` §"Document index". Where this doc disagrees with the
> current source or the master, the source and master win.

# S77 int restructure — target cluster-atomic orchestration + in-call-stack dependency threading

**Status:** DESIGN PROPOSAL — S78 centerpiece. Concurrency-sensitive. No code changes yet. **Phase-2 actioned 2026-06-10** (`/arch`): FIXME 0310 folded in — §2.3 + §5 + §7 corrected to record that the sexps-onto-packet move is NOT a separable "Step 0" (it is entangled with the resume kernel and folds into the indivisible Steps 1+2). OQ-1 settled to (b) block-on-scheduler; OQ-3 settled to delete-the-guard-gated-on-H5-test (Phase-1 user sign-off, both reflected in §3.3 / §3.5).
**Author:** `/arch` (2026-06-10), grounding the user's 2026-06-10 directive to "spend a wave to properly restructure `int` toward its target state, realizing the flow the new facade affords, then reground the tests."
**Manifestation:** this is per-crate (int-interior) design — `design/int/` is the right home (per FIXME 0298: `SharedState`/`process_cluster`/scheduler/worker are int-internal, NOT a cross-crate boundary). Cross-crate facets (none expected) would cascade to `bounded-contexts.md §6` / `facades/int.md`; §"Cascade to canonical set" below records the (small) expected touch.

---

## 1. Overview (solution-first)

Three int-internal structures are still shaped for a pipeline that no longer exists:

1. **The legacy per-form outer loop** — `worker::process_module_forms` (`src/worker.rs:1230`, ~1200 LOC of orchestration with Pass-0/Pass-1/Pass-2 inline, dep-load-retry, and block-point bookkeeping). It predates the cluster-atomic typecheck flip.
2. **Two cross-thread shared-mutable parking maps** — `SharedState.module_sexps` and `SharedState.suspend_states` (`session_v4.rs:670/682`). They exist *only* to let a block→resume cycle hop worker threads: a worker that blocks on a dependency saves its half-finished state into `suspend_states[module]`, publishes the dep's sexps into `module_sexps[dep]`, returns to the pool, and *any* worker later resumes by reading both maps back.
3. **A split dependency-publication protocol** — the same "discover dep → publish sexps → register → block → resume" logic implemented twice (worker-side `handle_import`/`register_dep`; session-side `register_dep_for_eval`), which the existing concurrency audit (`concurrency-architecture.md §3.5`) already flags as "the most important concurrency design smell… one logical protocol exists in more than one place… known observed failure already sits on this surface."

**What already landed** (correcting the stale `src/CLAUDE.md` understanding — see §9): the cluster-atomic *typecheck* flip is **live**. Commit `a2dcebd` ("Wave 3b-2c.3 — read-union via View; activate Cluster mode") closed FIXME 0179: `check_program_compat` delegates **unconditionally** to `process_cluster_with_staging`, which builds `SymbolTableAccess::Cluster { staging, … }`, runs `check_forms`, and atomically commits staging→live on `Ok` / drops staging on `Err`. The read-union (`View::union(staging, live)`) is in typecheck. So the *typecheck atomicity* half of Decision 44 is done. What remains is the *orchestration* half: the per-form outer loop that wraps `check_program_compat` still owns Pass-0/1/2 sequencing, the block→resume cross-thread dance, and the two parking maps.

**Target.** `cluster::process_cluster` becomes the single live orchestration. The block→resume cycle becomes an **in-call-stack recursion**: a worker that hits a dependency gap does NOT park-and-return — it drives the dependency to readiness *synchronously, within its own call frame* (the dep is registered, the worker recursively/iteratively processes the dep cluster or waits on the scheduler for another worker to, then retries its own cluster against now-larger live state). `module_sexps` and `suspend_states` become locals inside that frame and delete from `SharedState`. The split protocol collapses to one function.

**Why this is sound by construction (the central obligation).** The S60–S62 heisenbugs all lived on the cross-thread republish/resume surface: state for an in-flight cluster was externalized into shared maps and re-read by a *different* thread after an unblock, with the publish/register/block/unblock ordering racing against `notify_typecheck_done`→`try_unblock_locked` (the H5 race, the `eval_in_flight` guard, the `republish_module_sexps_from_symbol_table` re-publish — `session_v4.rs:2110+`, `heisenbug-race-closure.md`). The target removes the surface entirely: a cluster's in-progress state never leaves the stack frame of the worker processing it, so no other thread can observe or mutate it. The only cross-thread coordination that survives is the scheduler's *terminal-readiness* signalling (module reached `TypecheckDone` / `InmemDone`) — a monotonic, publish-once, observe-many edge that is already race-free (it never carries in-progress state, only "this module is now complete"). **The design's safety argument is: in-progress cluster state is stack-local (no sharing → no race); cross-thread signalling is monotonic-terminal-only (publish-once → no resume race).**

> **Implementation companion (Phase 3).** `design/int/s78-implementation.md` (`/design`, 2026-06-10) refines this proposal into an implementation-ready design verified against the working-tree source: pinned signatures (`process_cluster`/`process_cluster_once`/`drive_gap_to_readiness`, packet = `Arc<[Sexp]>`), the verified 30-code-site deletion inventory (vs this doc's "~26"), build-state-per-step, and the four open items resolved int-interior. **It corrects one prose-mechanism error in §3.3 below:** there is no `wait_for_typecheck` worker-park API — "block on scheduler" (OQ-1 b) is realized as *register-edge + return-to-pool + requeue* (the worker thread is freed, not parked; in-call-stack describes the *state*, stack-local staging dropped-and-rebuilt-from-packet, not literal thread-blocking). Read §3.3 / the `.mmd`'s "park in wait_for_typecheck" as that requeue model. `/dev` works from the companion for the exact shape; this doc governs intent/scope/soundness.

### Doc map

- §2 — target architecture (the three areas)
- §2.1 — the single main-loop entry (`run()`) — confirm/specify
- §2.2 — `process_cluster` as the single Pass-0/1/2 home (retire `process_module_forms`)
- §2.3 — in-call-stack dependency threading (delete `module_sexps`/`suspend_states` from `SharedState`)
- §3 — concurrency model (precise: ownership, the block→resume cycle, worker interaction, soundness)
- §4 — sequence of the new block→resume cycle (prose + the participants)
- §5 — blast radius + migration plan (the ~26 sites, grouped into steps, risk-flagged)
- §6 — test-regrounding implications + `shared_state_field_count` disposition
- §7 — scope recommendation (S77 wave vs S78 centerpiece)
- §8 — cascade to the canonical set
- §9 — note for /dev: stale `src/CLAUDE.md` correction

### Open questions (surface up-front; flagged for /dev + user)

- **OQ-1 (the deepest).** When a worker drives a dependency synchronously in-call-stack, does it (a) *process the dep cluster itself* (recursion into `process_cluster(dep)`), or (b) *register the dep + block on the scheduler* so the pool processes it, while the blocking worker waits in `wait_for_typecheck`? §3.3 recommends **(b)** (block-on-scheduler) as the soundness-preserving choice and explains why (a) risks a thread processing two modules' staging simultaneously. This is the single most load-bearing decision and wants explicit user/`/dev` sign-off.
- **OQ-2.** Mutual-import deadlock (Decision 30) is a *known accepted constraint*. The in-call-stack shape must preserve the scheduler's existing cycle detection (`detect_cycle_locked`, `scheduler.rs:631`). Confirm the cycle-rejection path still fires before any wait — §3.4.
- **OQ-3.** The `eval_in_flight` guard + `register_dep_for_eval`'s H5 closure exist *because* of the cross-thread republish. If in-progress state is stack-local, is the guard still needed? §3.5 argues it **deletes** — but this is exactly the kind of "remove the workaround when you remove the cause" claim that wants a careful /dev confirmation (and a regression test that the H5 scenario stays green).
- **OQ-4.** `process_module_forms` carries Pass-0 (`import`/`export`/`mod`/`platform` structural handling) inline with a "resume restarts Pass 2 from 0" subtlety (`pass2_resume_index`, worker.rs:1226, Defect-B guard). The cluster shape must preserve that semantics — but in the in-call-stack model "resume" is just "retry the cluster from the top against larger live state," which makes the subtlety *disappear* (there is no saved Pass-2 index to honour). Confirm no behaviour the Defect-B test pins is lost — §5 step 3.

---

## 2. Target architecture

### 2.1 The single main-loop entry — `run()` (confirm/specify)

**Already realized.** `src/main.rs::run(action, project_root, entry_module_name, settings)` (`main.rs:157`) is the unified entry for all three modes. The shape is:

```
let mut s = CompilerSession::new(settings, project_root);   // spawns + parks worker pool
s.register_module(entry_module_name)?;                       // Phase 0 + dispatch
match action {
    Run  => { wait_inmem_complete; trampoline; wait_object_complete; shutdown; exit }
    Link => { wait_object_complete; link_by_name }
    Repl => { wait_inmem_complete; init_watcher; <turn loop: read → eval → display> }
}
```

This conforms to Principle 11 (single pipeline, mode parameters) and pipeline-v4: there is one `register_module` path, one worker pool, one cluster-processing entry; modes differ only in the *tail* (what is awaited and how results surface). **No restructure is owed here** — area 1 is "confirm," and it is confirmed. The one consequence the restructure has on `run()`: REPL `eval` and batch `register_module` both funnel into `process_cluster` (§2.2), so the entry's mode-tail divergence is the *only* place modes differ, which is exactly the target.

The facade's `process_cluster`/`insert_cluster` free functions (`src/cluster.rs`, taking `&SharedState`) are the shared cluster-processing entry both the worker loop and `eval` call. That free-fn shape is the durable shape (per the S67 W1 PFR note in `facades/int.md:54-67`) and the restructure builds on it.

### 2.2 `process_cluster` as the single Pass-0/1/2 home (retire `process_module_forms`)

**Today.** `cluster::process_cluster` is a zero-caller facade-conformance scaffold (`src/cluster.rs:177`); the live orchestration is `worker::process_module_forms` (`worker.rs:1230`), driven by `handle_typecheck_work_shared` (`worker.rs:4279`). `process_module_forms` owns:

- **Pass 0** — `import`/`export`/`mod`/`platform` structural-form handling, with `BlockAction::Block { dep_module, dep_sexps }` returns when a dep must load (worker.rs:1272–1320).
- **Pass 1 / Pass 2** — register-then-check, delegating the actual typecheck to `check_program_compat` → `process_cluster_with_staging` (the cluster-atomic call that already landed).
- **Resume bookkeeping** — `start_form_index` + `ModuleSuspendState { accumulator, expanded_program, pass1_done }` + the `pass2_resume_index` Defect-B subtlety.
- **Block-point publication** — returning `ProcessResult::Blocked` to `handle_typecheck_work_shared`, which then writes `module_sexps[dep]` + `suspend_states[module]` and returns to the pool.

**Target.** `process_cluster(shared, forms, scope)` is the single orchestration. It absorbs Pass-0/1/2 + dep-load-retry into one call frame:

```
process_cluster(shared, forms, scope):
  loop:                                            # whole-cluster retry envelope
    parsed = []
    for form in forms:
       expanded = expand_loop(shared, form, scope) # Pass 1 (macro expand, in-call-stack — §2.2.1)
       parsed += build_form(expanded)
    # Pass 0 structural forms are peeled here (import/export/mod/platform) and
    # any dep they name is driven to readiness IN THIS FRAME (§2.3 / §3.3),
    # not parked. install_imports / install_exports / mod-alias install run here.
    staging = SymbolTable::new(scope)
    ctx = SymbolTableAccess::cluster(&shared.symbol_tables, &mut staging, scope)
    match check_forms(parsed, &mut ctx, &shared.symbol_tables, &shared.module_aliases):
        Ok(())              => return Ok(ProcessedCluster::from(staging, …))
        Err(Gap(gap))       => drive_gap_to_readiness(shared, gap)?; continue   # in-call-stack retry
        Err(other)          => return Err(other)
```

The `process_cluster_with_staging` body (worker.rs:273) is *already* the staging-construct + `check_forms` + commit/discard core. The restructure **moves that core into `cluster::process_cluster`** and wraps it with: (a) the Pass-1 expand loop (already int's per S76 W-Macro — `expand_sexp_recursive` is the live driver), (b) the Pass-0 structural peeling currently inline in `process_module_forms`, and (c) the in-call-stack gap-drive that replaces the park-and-return. `process_module_forms`, `ModuleSuspendState`, `ProcessResult::Blocked`, `pass2_resume_index`, and `handle_typecheck_work_shared`'s map-juggling all **delete**.

The worker loop (`priority_worker_loop_shared`, worker.rs:4185) becomes thin: `take_priority_work_blocking() → process_cluster(shared, sexps, module) → inline_jit_codegen + notify_typecheck_done`. The sexps it needs come from the work packet, not from a shared map (§2.3).

#### 2.2.1 Pass-1 expand is already in-call-stack

S76 W-Macro already made macro expansion an in-call-stack loop (`expand_sexp_recursive`, the three-pass model — `macro-availability-model.md §0`). Recognition is the `cranelisp-types` primitive (`resolve_macro_head`), execution is int's `JitMacroExpander`, and a dependency-module macro a clause needs is loaded just-in-time *within the expand loop* (the FQ-autoload path, FIXME 0268, `src/CLAUDE.md` §"FQ auto-loading"). This is the *pattern the whole restructure generalizes*: Pass 1 already drives deps synchronously in-frame; the restructure makes Pass 0 and Pass 2 do the same, and removes the *other* (worker-park) path that still coexists with it. The current duplication — Pass-1 deps drive in-frame, Pass-0/Pass-2 deps park-and-resume — is the residual inconsistency.

### 2.3 In-call-stack dependency threading (delete `module_sexps` / `suspend_states`)

**`module_sexps` today** carries two distinct payloads conflated into one `Mutex<HashMap<ModuleFullPath, Vec<Sexp>>>`:

1. *The entry/REPL module's sexps* — published by `register_module_with_source` (session_v4.rs:2080) before registering, so a waking worker finds them. **Target:** carried *on the work packet*. The scheduler's `PriorityWork::Typecheck(module)` becomes `PriorityWork::Typecheck { module, sexps: Arc<Vec<Sexp>> }` (or the sexps are parsed in `register_module` and handed to the dispatched packet). Either way the sexps travel *with the work item*, owned by it, dropped when the work completes — no shared map.
2. *A discovered dep's sexps* — published by the worker when it blocks (worker.rs:4380) so the *resumer* finds them. **Target:** deleted. In the in-call-stack model the worker that discovers the dep parses it and either processes it in-frame or hands it to the scheduler *as a fresh work packet carrying its own sexps* (§3.3). No worker ever reads back another worker's parked sexps.

**Why payload #1 is NOT independently relocatable (publisher-side vs reader-side — FIXME 0310 correction).** It is tempting to read payload #1 as a clean, standalone first move: "just carry the entry-module sexps on the packet, leave the dep half on the map for later." That reading holds on the *publisher* side but breaks on the *reader/resume* side, and the source disproves the separability:

- **One read site, not two.** All modules — entry, dep, and *resumed* — flow through the single `handle_typecheck_work_shared` read site (`worker.rs:4289`). The work item it claims is a bare `ModuleFullPath` with no sexps attached; it reads `module_sexps[module]` to obtain them. The resume requeue path (`try_unblock_locked`, `scheduler.rs:1351`) likewise carries no sexps — it just re-enqueues the `ModuleFullPath`.
- **Payload #1 is read on the resume path, not only at first processing.** The entry/REPL module's sexps are deliberately kept alive across a block→resume by the H5 fix's unconditional `republish_module_sexps_from_symbol_table(&caller)` (`session_v4.rs:2233`). The resumer re-reads `module_sexps[caller]` *after* the dep arrives — so removing payload #1 from the map removes the data the H5 fix republishes.
- **Therefore removing payload #1 forces editing the block→resume kernel.** Carrying the entry-module sexps on the packet means the resumer must obtain them from the packet, not the map — which means the requeue (`try_unblock_locked`) must carry the packet (sexps included), and the `eval_in_flight`/republish dance that exists *only* to keep the map entry alive across the resume becomes dead. That edit IS Steps 1+2 (the in-call-stack drop-and-retry-from-top model that owns the packet across the resume). The packet-carries-sexps change cannot land *as a separable, build-green precursor* — it is entangled with the very kernel rewrite it was imagined to precede.

The consequence for the plan: there is no safe "Step 0" that relocates payload #1 ahead of the kernel rewrite. Payload #1's relocation is *part of* Steps 1+2 (§5). The publisher-side framing above (payload #1 = packet; payload #2 = deleted) is the correct *target* picture; it is not a separable *migration order*.

**`suspend_states` today** holds `ModuleSuspendState { accumulator, expanded_program, pass1_done }` — the half-finished cluster state saved across a thread-hopping resume. **Target:** deleted entirely. In-progress cluster state (`parsed`, `staging`, the expand-loop position) lives in `process_cluster`'s stack frame. On a gap, the frame drives the dep to readiness then **retries the whole cluster from the top** against now-larger live state (the `loop { … continue }` envelope, §2.2). There is no "resume at form N with saved Pass-1 state" — there is "run the cluster again; it gets further this time because the dep is now in live." This is the same monotonic-progress termination argument the facade's `process_cluster` pseudocode already states (`facades/int.md:1224`): each gap-drive advances dependency state strictly; retries see strictly more; the loop terminates on full success, non-gap error, or scheduler cycle-rejection.

Cost of "retry from the top": re-running the expand loop + Pass-1 register for forms already processed. This is the explicit trade the cluster-atomic model accepts (`facades/int.md` §"Cluster orchestration result", Decision 44) — atomicity over incremental-resume efficiency. Clusters are small (one REPL form, one `(begin …)`, or one file); re-expansion is cheap relative to the heisenbug-class of bugs incremental-resume cost us. (Pass-1 macro *execution* results are pure functions of input + committed tables, so re-running is safe and deterministic.)

After both deletions `SharedState` drops from 16 → 14 pub fields (the `shared_state_field_count` test target — §6).

---

## 3. Concurrency model (precise — the central design obligation)

### 3.1 Ownership partition

| State | Owner | Sharing | Mutability |
|---|---|---|---|
| In-progress cluster (`parsed`, `staging`, expand position) | the `process_cluster` stack frame on one worker | **none** — never leaves the frame | exclusive (stack-local `&mut staging`) |
| Cluster sexps | the work packet (`PriorityWork`) | moved into the worker that claims it | owned by the packet |
| `symbol_tables` (live) | `SharedState`, `DashMap` | all workers | per-entry inner-DashMap locks; staging→live commit is per-symbol under write guard |
| `module_aliases`, `next_type_id`, `cache`, `introspection`, `scheduler` | `SharedState` | all workers | interior-mutable (DashMap / Atomic / internal locks) |
| Scheduler readiness (pool state, waiters, blocked_on edges) | `CompileScheduler` | all workers | one `Mutex<SchedulerState>` (the concurrency kernel) |

The key change: **the first two rows move OUT of `SharedState`**. Today they are `SharedState.suspend_states` (row 1) and `SharedState.module_sexps` (row 2), shared-mutable across threads. Target: row 1 is stack-local, row 2 is packet-local. Everything still on `SharedState` is *terminal/authoritative* state (the committed symbol tables, the scheduler kernel, config) — none of it carries *in-progress* cluster state.

### 3.2 What stays cross-thread (and why it's safe)

The scheduler kernel stays. Its job is **terminal-readiness signalling**: a module transitions `Registered → TypecheckWorking → TypecheckDone → InmemDone`, monotonically, and workers/initiator `wait_for_*` on those terminal edges. This is sound because:

- **Monotonic.** A module never un-completes. `notify_typecheck_done(module)` (scheduler.rs:661) is publish-once; it sweeps waiters and unblocks them. There is no "resume with state" — the waiter, once unblocked, *retries its own cluster from the top* (§2.3) reading the now-`TypecheckDone` module's *committed live* entries.
- **No in-progress payload crosses.** The unblock carries no sexps, no half-finished accumulator — just "the module you waited on is done; look at live." The data the resumer reads (live `symbol_tables[dep]`) was committed atomically by the dep's own `process_cluster` (staging→live drain). The resumer reads *committed* state only.
- **Commit is atomic per cluster.** `commit_staging_to_live` (worker.rs:317, moves into cluster.rs) drains staging under the live module's `DashMap::get_mut` write guard. Other workers see either the pre-cluster live table or the fully-committed one — never a partial cluster. (This invariant already holds post-`a2dcebd`; the restructure preserves it.)

### 3.3 The block→resume cycle without cross-thread parking (OQ-1 — recommend (b))

When `process_cluster` on worker W, processing module M, hits `Err(Gap(needed_module))`:

**Option (a) — recurse in-frame:** W calls `process_cluster(shared, dep_sexps, needed_module)` directly, then retries M. **Rejected for soundness:** W would hold M's `staging` frame *and* construct needed_module's `staging` frame on the same stack. Two staging tables for two modules alive simultaneously on one thread is exactly the kind of state-entanglement the restructure removes. It also breaks the scheduler's per-module pool accounting (M is `TypecheckWorking` while W is secretly also doing needed_module's work) and defeats cycle detection (the scheduler never sees the M→needed_module edge).

**Option (b) — register + block on scheduler (RECOMMENDED):** W
1. drops M's `staging` frame (atomic discard — live unchanged; M's in-progress state was only ever on W's stack, so nothing to clean up elsewhere),
2. ensures needed_module is registered (`ensure_registered` — parse its source into a fresh work packet, `scheduler.register_module(needed_module)`, which wakes the pool),
3. records the M→needed_module edge and **blocks**: `scheduler.block_for_typecheck(M, needed_module, needed_symbol)` (scheduler.rs:612) → this runs `detect_cycle_locked` FIRST (rejecting mutual imports per Decision 30 before any wait), then adds W as a waiter and W parks in `wait_for_typecheck`,
4. **some worker** (possibly W itself after being woken, possibly another pool thread) processes needed_module's packet to `TypecheckDone`, committing its entries to live,
5. `notify_typecheck_done(needed_module)` sweeps W's waiter and unblocks it,
6. W resumes — **at the top of M's `process_cluster` retry loop** (it re-claims M's work or, in the REPL eval case, the eval thread re-drives) — and re-runs M's cluster against live state that now contains needed_module. The gap does not recur for this dep; M gets further.

The difference from today: in step 1, W's in-progress state is *dropped*, not *saved to `suspend_states`*. In step 6, W *re-derives* M's state from M's sexps (still owned by M's work packet / re-parsed), not *re-read from `module_sexps` + `suspend_states`*. The thread that resumes M re-does M's expand+Pass-1 from scratch against larger live — cheap, deterministic, and crucially **stateless across the block**.

This is precisely the existing facade `handle_gap` shape (`facades/int.md:1177`): `ensure_registered` + `scheduler.wait_for_typecheck_symbol`. The restructure makes it the *only* path (today it coexists with the worker-park path for Pass-0 blocks). The Pass-1 expand loop *already* works this way for FQ-macro deps (FIXME 0268).

### 3.4 Persistent priority workers interaction

`handle_typecheck_work_shared` (worker.rs:4279) — the per-module work handler — collapses into the thin loop body of §2.2: claim packet → `process_cluster` → codegen → notify. The persistent worker pool (`priority_worker_loop_shared`) is *unchanged in shape*: park on condvar → claim work → handle → repeat. What changes is what "handle" does internally (in-call-stack drive instead of park-and-return). The pool's existing panic→`notify_module_failed` robustness (worker.rs:4199, FIXME 0285 defect 2) is preserved — a panic inside `process_cluster` still converts to a module failure so waiters don't hang.

Crucially, **a blocked worker is not lost to the pool.** When W blocks in step 3 (§3.3), it parks in the scheduler's `wait_for_typecheck`; it is not occupying a pool slot doing nothing forever — the scheduler's condvar wakes it when its dep completes. Other pool workers continue claiming and processing packets (including, possibly, needed_module's). This is the same liveness property the current code has; the restructure does not change worker-count math.

Cycle safety (OQ-2): `block_for_typecheck` runs `detect_cycle_locked` *before* adding the waiter (scheduler.rs:631). A mutual import M↔N: W blocks M on N; a worker blocks N on M; the second `block_for_typecheck` detects the M→N→M cycle and returns `Err(circular dependency)`, failing the module cleanly rather than deadlocking. **Preserved verbatim** — the restructure does not touch the scheduler kernel's cycle logic.

### 3.5 Why the S60–S62 heisenbugs cannot recur (OQ-3)

The heisenbugs (catalogued in `heisenbug-race-closure.md`, ~160KB) all reduced to: **in-progress state externalized to a shared map, re-read by a different thread after an unblock, with publish/register/block/unblock ordering racing `notify_typecheck_done`→`try_unblock_locked`.** Concretely:

- The **H5 race** (`session_v4.rs:2110+`): t1 (eval thread) discovers dep `helper`, but before t1 sets `eval_in_flight`, t2 (worker) has already typechecked `helper`, called `notify_typecheck_done(helper)` → `try_unblock_locked(user)`, and begun typechecking `user` — re-reading `module_sexps[user]` which t1 may not have re-published yet. The fix was the `eval_in_flight` guard + `republish_module_sexps_from_symbol_table`.
- The fix *only existed because `user`'s sexps lived in a shared map that got removed (`handle_typecheck_work_shared` cleans up `module_sexps[caller]`) and had to be re-published*.

**In the target, there is no `module_sexps[user]` to remove or re-publish.** `user`'s sexps live on its work packet; the eval thread owns the cluster frame; resume = re-run the cluster from the packet's sexps against committed live. There is no shared in-progress payload, so:
- no thread re-reads another thread's in-progress state → no read-after-removal race;
- no publish/re-publish ordering → no publish-vs-unblock race;
- the `eval_in_flight` guard's entire reason-for-being (linearize the set/read against `try_unblock_locked` to protect the re-publish) **evaporates**.

**Recommendation:** `eval_in_flight` + `EvalInFlightGuard` + `register_dep_for_eval`'s republish dance + `republish_module_sexps_from_symbol_table` all **delete** with the maps. This is the "remove the workaround when you remove the cause" claim and it wants a /dev confirmation backed by a *retained regression test* replaying the H5 scenario (the two-input `(import helper)` + dep-load sequence) staying green under stress (`CRANELISP_SCHEDULER_TRACE`). Per the project's repros-join-the-suite discipline, that test stays.

The soundness argument restated as a one-liner: **share only monotonic-terminal facts; keep all in-progress state on the owning stack frame.** Shared-mutable-in-progress is the heisenbug substrate; the restructure removes the substrate.

---

## 4. Sequence of the new block→resume cycle

Participants: `Eval`/`Initiator` (REPL turn or `register_module`), `W1`/`W2` (pool workers), `Sched` (scheduler kernel), `Live` (`symbol_tables` DashMap).

**Batch / fresh-module path (no dep):**
1. `Initiator.register_module(M)` — Phase 0 (parse M's source → sexps, write structural decls to Live[M]). Dispatch `PriorityWork{M, sexps}` → `Sched`, wake pool.
2. `W1` claims `{M, sexps}`. `process_cluster(shared, sexps, M)`: expand loop (Pass 1) → `build_form` → Pass-0 peel → `check_forms` over fresh `staging` → `Ok` → commit `staging`→`Live[M]` (atomic) → codegen → `Sched.notify_typecheck_done(M)` / `notify_inmem(M)`.
3. `Initiator.wait_inmem_complete` returns. Done. (No map touched.)

**Dep path (M imports N, N not loaded):**
1–2 as above until `W1`'s `check_forms` (or its Pass-0 peel of `(import N)`) surfaces `Err(Gap(N))` / a structural dep on N.
3. `W1` drops M's `staging` (atomic discard; Live[M] unchanged). `ensure_registered(N)`: parse N → `PriorityWork{N, sexps_N}` → `Sched.register_module(N)`, wake pool.
4. `W1.block_for_typecheck(M, N, sym)` → `Sched` runs cycle check (M→N edge; no cycle) → `W1` parks in `wait_for_typecheck`.
5. `W2` claims `{N, sexps_N}`. `process_cluster(shared, sexps_N, N)` → `Ok` → commit `staging_N`→`Live[N]` → `Sched.notify_typecheck_done(N)`.
6. `notify_typecheck_done(N)` sweeps `W1`'s waiter, clears M's `blocked_on`, requeues M. `W1` (or any worker) re-claims M.
7. M's `process_cluster` runs again from M's sexps: expand+Pass-1 re-run, Pass-0 peel of `(import N)` now resolves (N in Live), `check_forms` `Ok` → commit → codegen → notify. Done.

The only shared touch in step 6 is the scheduler's monotonic unblock; the only data M's resume reads is committed `Live[N]`. **No `module_sexps`/`suspend_states`.** Contrast with today: step 3 would write `suspend_states[M]` + `module_sexps[N]`, step 7 would read both back on possibly a different thread — the race surface.

> A sequence diagram (`.mmd`) renders this cycle: `design/int/concurrency/dependency-protocol-target.mmd` (+ rendered `.svg`) was reconciled to the in-call-stack option-(b) shape in the Phase-2 design pass (2026-06-10, `/arch`) — drop-staging → ensure_registered → block_for_typecheck (cycle-check first) → pool processes dep → notify_typecheck_done → retry-cluster-from-top. It supersedes the prior generic "Dependency service / publication store" sketch.

---

## 5. Blast radius + migration plan

The ~26 `module_sexps`/`suspend_states` sites cluster into 4 files: `worker.rs` (~14), `session_v4.rs` (~9: register_module_with_source, register_dep_for_eval, republish_*, reload_module, the struct field + ctor), `scheduler.rs` (resume_from_form machinery), `observability.rs` (1 trace ref). Grouped into implementable steps, ordered to keep the build green between steps where possible (the central ones cannot — see Principle "facade-walk leaves build broken"; the user accepted a wave for exactly this).

> **Note — no separable "Step 0" (FIXME 0310 correction).** An earlier draft of this plan opened with a "Step 0 — sexps onto the work packet" classified LOW-risk / build-green / separable, on the premise that the entry-module sexps (payload #1, §2.3) could move onto the packet ahead of the kernel rewrite "while the maps still exist for the dep half." A source-grounded separability check (S77, zero edits) disproved that premise: payload #1 is read on the **resume** path through the single `handle_typecheck_work_shared` site, kept alive by the H5 fix's `republish_module_sexps_from_symbol_table`. Carrying it on the packet forces the resumer to obtain it from the packet, which forces editing `try_unblock_locked` (requeue carries the packet) and retires the `eval_in_flight`/republish dance — i.e. it IS Steps 1+2, not a precursor to them. **The packet-carries-sexps change therefore folds into Steps 1+2 below; there is no standalone de-risking move ahead of the kernel rewrite.** §2.3's publisher-side framing (payload #1 = packet, payload #2 = deleted) is the correct *target* picture, not a separable *migration order*. The restructure is one indivisible red→green span, consistent with §7's risk note.

**Step 1 — lift Pass-0/1/2 into `cluster::process_cluster`; carry sexps on the packet (structural, build-red expected).** Move `process_cluster_with_staging`'s core + `commit_staging_to_live` into `cluster.rs`. Move the Pass-0 structural peel (import/export/mod/platform handling, `install_imports`/`install_exports`/mod-alias) from `process_module_forms` into `process_cluster`. Make `process_cluster` the live body. Change `PriorityWork::Typecheck(module)` → carry the cluster sexps (e.g. `Arc<[Sexp]>`) so the worker loop reads them off the packet, not `module_sexps`; update `register_module_with_source`, `register_module`, the dispatch sites, and `take_priority_work*`; remove the `module_sexps.insert(M, …)` publish at register time and the `module_sexps.get(M)` read in `handle_typecheck_work_shared`. **Risk: HIGH** (the largest single move; ~1200 LOC of `process_module_forms` redistributes; the packet-shape change touches the dispatch + requeue surface). *Hotspot: the Pass-0 `BlockAction::Block` returns become in-call-stack gap-drives (step 2 wires them); the requeue (`try_unblock_locked`) must now carry the packet so the resumer reads sexps from it, not the map (§2.3 / FIXME 0310).*

**Step 2 — in-call-stack gap-drive; delete the maps (the core, build-red).** Replace `ProcessResult::Blocked` + `handle_typecheck_work_shared`'s map-juggling + `register_dep_for_eval`'s republish with the single `drive_gap_to_readiness(shared, gap)` (= `ensure_registered` + `block_for_typecheck` + `wait_for_typecheck`, then `continue` the cluster retry loop). Delete `module_sexps` (both payloads — entry-module sexps now ride the packet per step 1; dep sexps ride fresh packets per §3.3), `suspend_states`, `ModuleSuspendState`, `ProcessResult::Blocked`, `pass2_resume_index`, `republish_module_sexps_from_symbol_table`, `register_dep_for_eval`'s republish body. **Risk: VERY HIGH** (this is the concurrency-critical change). *Hotspot: the entire block→resume cycle; the H5 surface; OQ-1's option-(b) discipline.*

> Steps 1 and 2 are **one indivisible build-red span** — the packet-shape change (formerly "Step 0"), the orchestration lift, and the map deletion cannot be cleanly separated for the reasons above. `/dev` lands them as a single red→green unit; the build is not expected to be green between them.

**Step 3 — delete the `eval_in_flight` guard (workaround removal, OQ-3).** Remove `EvalInFlightGuard`, the `eval_in_flight` scheduler flag, and the linearization comments — *after* a retained H5-replay regression test is green. **Risk: MEDIUM** (correctness claim; gated on the test). *Hotspot: confirm no remaining reader of in-progress shared state justifies the guard.*

**Step 4 — retire `process_module_forms` + thin the worker loop.** Delete `process_module_forms`, `ModuleCompiler`'s resume-specific fields if any, and collapse `handle_typecheck_work_shared` into the thin claim→process_cluster→codegen→notify body. **Risk: MEDIUM** (mostly deletion once steps 1–2 land). *Hotspot: ensure the Defect-B "resume restarts Pass 2 from 0" semantics is preserved-by-construction — in the retry-from-top model there is no saved index, so the forms-before-import are always re-processed; confirm the spec_08 Defect-B test stays green.*

**Step 5 — scheduler cleanup.** Remove `resume_from_form`/`set_resume_from_form`/`module_resume_from_form` (no longer any saved resume index). Possibly remove the already-dead `PriorityEntry`/`BlockingJitCodegen` subsystem (`src/CLAUDE.md` notes it is dead post-W-Macro). **Risk: LOW** (dead-code removal). *Hotspot: none.*

**Step 6 — reground tests + `shared_state_field_count`.** §6.

**Sequencing note (Plan cascade discipline):** steps 1–2 are one indivisible red→green span (the build is broken between them — expected, per the facade-walk-leaves-build-broken memory) and they subsume the formerly-separate "Step 0" packet-shape change (FIXME 0310 — not independently landable). `/dev` should land (1+2 together) → 3 → 4 → 5 → 6, regenerating the baseline only at the end. Steps 1+2 are the wave's center of gravity and its entire risk.

---

## 6. Test-regrounding implications

**`shared_state_field_count_matches_facade_after_pif` (the relic).** Per FIXME 0298: this test introspects an *internal* struct, so it does not belong in a *boundary*-conformance file (`tests/facade_pif_rows.rs`). Two coupled actions:
1. **Relocate it** out of the boundary-conformance file into an int-internal design-target tracker (it is a structural target check, not a public-API check — int is a binary with no `public-api.txt`). It stays **failing-not-ignored** at the current 16 until step 2 lands, at which point it passes at 14 (its `<= 14` assertion is already correct for the target). After the restructure it becomes a standing guard that `module_sexps`/`suspend_states` do not creep back.
2. The `<= 14` threshold is the *post-this-restructure* target (16 − 2). Confirm the count after step 2; if `register_dep_for_eval`/republish removal sheds no field (they are methods, not fields) the count is exactly 14. Tighten to `== 14` once landed if no slack is wanted.

**Facade-era relic tests generally.** Any `tests/facade_pif_rows.rs` row that pins a `SharedState` *internal* shape (not a cross-crate boundary) is mis-homed per FIXME 0298 and should move to the int-internal tracker. The user's directive ("instead of maintaining facade-era relic tests… reground the tests") targets exactly these.

**Tests that reground (behaviour preserved, mechanism changed):**
- **Dep-load / resume tests** (`spec_08::defn_before_import_resumes_correctly_after_dep_load` — the Defect-B guard; the FQ-autoload e2e suite). These pin *behaviour* (a defn before an import survives a dep-load) that the target preserves by construction (retry-from-top). They should stay green unchanged; if any asserts on the *mechanism* (saved resume index, `ProcessResult::Blocked`), that assertion regrounds to the behaviour.
- **The H5 / heisenbug regression suite.** Retain and keep green under stress — this is the soundness evidence for OQ-3. If any test directly probes `module_sexps`/`suspend_states`/`eval_in_flight` internals, it regrounds to probing the observable outcome (the two-input import sequence produces the right result deterministically).
- **Cluster-atomicity tests** (staging commit/discard). Unchanged — the staging core moves files (worker.rs → cluster.rs) but its contract is identical.

**New tests owed (/qa + /dev):**
- A retained H5-scenario replay (gated for step 3).
- A mutual-import cycle-rejection test (OQ-2 — confirm the cycle path fires before any wait in the in-call-stack shape).
- The relocated `shared_state_field_count` guard.

---

## 7. Scope recommendation

**This is S78-centerpiece-sized, NOT one more S77 wave. Recommend: carry the whole restructure (Steps 1–6) as the S78 centerpiece — one indivisible deliverable.**

> **Superseded sub-recommendation (FIXME 0310).** An earlier version of this section proposed landing a low-risk "Step 0" (sexps-onto-packet) in S77 ahead of the centerpiece, to de-risk it. The S77 separability check disproved that the packet-shape change is separable (§5 note + §2.3): it is entangled with the resume kernel and folds into Steps 1+2. There is no safe precursor wave to peel off. The recommendation collapses to: the restructure is a single S78 deliverable, landed complete to target shape.

Rationale (honest about concurrency risk):

- **Steps 1+2 are an indivisible, very-high-risk, build-red span** touching the single most dangerous surface in the codebase (the dependency-publication protocol the existing audit rates "Very High" risk with "known observed failure already on this surface"). This is not a wave-tail polish item; it is a from-scratch rebuild of the block→resume cycle. ~1200 LOC of `process_module_forms` redistributes; the H5 class of bugs is in scope to *re-confront* (we are removing their fix and arguing the fix is no longer needed).
- **The soundness argument is strong but unproven-in-source.** §3 argues correctness-by-construction (stack-local in-progress state; monotonic-terminal signalling). That argument must be *validated by /dev under `CRANELISP_SCHEDULER_TRACE` stress*, not asserted. The S60–S62 history is that this surface punishes "looks correct" — the project's own memory (`feedback_cross_skill_minimal_repro`, the heisenbug docs) is that reductions here cost hours.
- **OQ-1 (option a vs b) and OQ-3 (delete the guard) want explicit user sign-off before implementation.** Per `feedback_explicit_decision_review` (concurrency-sensitive architecture), these return for review — which this doc does.
- **A full sprint is the right unit** because the wave is: rebuild (1+2) → workaround removal gated on a new regression test (3) → deletion (4–5) → reground (6), with stress-validation between each. That is a sprint's arc, not a wave's.

**Counter-position considered:** could 1+2 land as one S77 wave if the wave is the *whole* sprint's remaining capacity? Only if S77 is otherwise empty and the user accepts a single-deliverable sprint. Given the risk, a dedicated S78 with explicit stress-validation gates is the safer call — which is the path taken (S78 is exactly this single-deliverable sprint).

---

## 8. Cascade to the canonical set (when actioned — not in this proposal pass)

This restructure is int-interior (FIXME 0298: `SharedState`/`process_cluster`/scheduler/worker are internal, not a boundary). Expected canonical-set touches are therefore **small**, and the Phase-2 cascade (2026-06-10, `/arch`) confirmed them:

- **`facades/int.md`** — the §"SharedState" field table loses `module_sexps` + `suspend_states` rows; the §"SharedState facade alignment plan" PIF rows for those two move from "deferred/PIF — delete via redesign" to "done"; the `process_cluster` pseudocode re-syncs to the three-pass + in-call-stack-gap shape (it is currently flagged "retained verbatim as gap-orchestration reference"). **Sequencing decision (Phase 2 — W-Retire vs restructure):** `facades/int.md` is slated to **retire wholesale** into `design/int/` + `src/` rustdoc as W-Retire (FIXME 0298, a pure doc-reorg not gated on this restructure). Editing the SharedState rows in place *now*, only to delete the whole facade in W-Retire, is throwaway churn. **Recommendation: W-Retire runs AFTER the restructure lands, and absorbs the SharedState-row change rather than the restructure editing the facade in place.** The restructure's facade-side consequence is therefore *not* a facade edit in this sprint — it is a fact W-Retire records when it migrates the SharedState section into `design/int/` + source rustdoc (the section migrates already at its 14-field target shape). Until W-Retire runs, the facade's `module_sexps`/`suspend_states` rows are stale-but-harmless (the facade is being retired anyway, and per FIXME 0298 the SharedState shape is int-internal — not boundary — so its staleness gates nothing). If `/sprint` schedules W-Retire in a later sprint, the int-internal `shared_state_field_count` tracker (§6) is the durable guard that the rows reached target; the facade rows are a tombstone until retirement. **W-Retire is NOT pulled into S78** (S78 is the single-deliverable restructure sprint per §7); it is a follow-on doc-reorg.
- **`bounded-contexts.md §6`** — §6.2 "Inter-cadence handoffs" described the target ("REPL submits work and waits; compilation signals when ready") in handoff-pattern terms that the in-call-stack model *realizes*. A sharpening sentence was added in the Phase-2 cascade tying the dependency-gap case to the same submit-and-wait-on-terminal-signal pattern (drop stack-local state, register, block on the monotonic signal, retry from top). No invariant changes.
- **`design/int/concurrency*`** — this doc + the existing `concurrency-architecture.md §3.5`/§6.2 (which already recommend collapsing the split protocol + reducing SharedState) reconcile; `concurrency/dependency-protocol-target.mmd` was **re-drawn to the in-call-stack option-(b) shape** in the Phase-2 pass (`.svg` regenerated; `/arch`-owned).
- **`src/CLAUDE.md`** — the stale "Cluster-Atomic Orchestration" §"wired but not activated / pending FIXME 0179" paragraph is /dev-owned; flagged for correction in §9.
- **No `cranelisp-types` change, no cross-crate type change, no new boundary type.** `SymbolTableAccess`, `View`, `check_forms`, `ProcessedCluster` are all unchanged. `PriorityWork` (the packet whose shape gains `Arc<[Sexp]>`) and `ModuleSuspendState` are both int-internal (`src/worker.rs`/`src/scheduler.rs`), not `cranelisp-types`. `Sexp` rides the packet unchanged — its shape is not touched. This is pure int-interior re-plumbing; confirmed by the Phase-2 cascade.

---

## 9. Note for /dev — stale `src/CLAUDE.md` to correct

`src/CLAUDE.md` §"Cluster-Atomic Orchestration" and §"Macro expansion … Still on the wall (FIXME 0176/0179)" both say the staging machinery is **"wired but NOT activated on the hot path; `check_program_compat` still uses `ClusterContext::Live`; activating cluster mode without the read-union flip regresses ~12 tests."** This is **STALE**. Commit `a2dcebd` (2026-05-14, "Wave 3b-2c.3 — read-union via View; activate Cluster mode") landed the read-union *and* flipped `check_program_compat` to delegate **unconditionally** to `process_cluster_with_staging` (`worker.rs:218-233`, 273-309). Cluster mode is the **active hot path today**; FIXME 0179 is **closed**.

The correct current statement (for /dev to write into `src/CLAUDE.md` when implementing): *"Cluster-mode staging is the live typecheck path (`process_cluster_with_staging`, a2dcebd). The remaining cluster-atomic work is not the typecheck flip — it is retiring the `process_module_forms` outer per-form loop and lifting Pass-0/1/2 + in-call-stack dep-drive into `cluster::process_cluster`, deleting the cross-thread `module_sexps`/`suspend_states` parking maps (this doc)."* FIXME 0176's residual scope is exactly this restructure, not the read-union.

`/arch` does not edit `src/CLAUDE.md` (it is /dev-owned). This note records the correction for the implementing /dev wave.
