> **HISTORICAL — superseded / completed working doc (triaged S110, FIXME 0607).** A
> point-in-time record retained for the audit trail only; NOT current design intent. The
> durable design is `int.md` (master) plus the subsystem docs indexed in
> `design/int/CLAUDE.md` §"Document index". Where this doc disagrees with the current source
> or the master, the source and master win.

# Dual-Path Persistence Collapse (Workstream A, Sprint 59)

> Status: DESIGN (Phase 3, Sprint 59 Workstream A)
> Owner: `/int` (lead); reviewed by `/arch` (Decision 37 alignment) and `/backend` (cache-read surface).
> Prerequisite: Sprint 58 Wave 2 `try_cache_hit_load` (scheduler-side deletion; Decision 37 enacted there) and Wave 6 Defect 1 publish-before-register reordering at 5 sites.

This doc commissions the Sprint 59 Workstream A collapse: deleting the REPL-session-side dual-path persistence shape (a scheduler-side `register_module` flow running in parallel with a `compile_dep_inline` + per-form-handler fallback flow) in favour of the single `register_module` recursion path specified by Decision 37. This is the *same* structural collapse Sprint 58 Wave 2 applied at the scheduler-side surface (`try_cache_hit_load`), now applied at the REPL-session-side surfaces named by Sprint 58 /review I-3.

## 1. Problem Statement

Today, a module can be made resident in a `CompilerSession` by two independent, partially divergent code paths:

1. **Scheduler-side path** — `CompilerSession::register_module` → `register_module_with_source` → the persistent priority worker loop (`src/worker.rs::priority_worker_loop_shared`). This is the path main.rs uses for the entry module, and the path `handle_import` / `handle_export` / `handle_mod` / `inject_prelude_if_needed` use for transitive deps discovered during typecheck (via `ctx.scheduler.register_module(dep, true)` after `publish_dep_sexps`).
2. **Session-side path** — `CompilerSession::compile_dep_inline` (used when a REPL eval discovers it needs an unloaded dep) runs its own copy of the priority worker loop on the calling thread with a local `module_sexps` map, while *also* registering with the scheduler and publishing to the shared map so persistent workers do not emit "no parsed sexps for module '…'".

The two paths coexist because persistent priority workers (Sprint 57 Wave 4 G9) and the REPL eval thread both need to be able to make progress on a dep discovered mid-eval, and neither is guaranteed to get there first. The session-side path is not a cache — it is a second, independent compile orchestrator that races the scheduler. Sprint 58 Wave 6 Defect 1 fixed the racy publish-before-register ordering at 5 sites (`compile_dep_inline` + 4 form-handlers), but the fix was *localised to the race window* and did not remove the duality of the paths themselves.

The failures this duality produces:

| Test | File | Symptom |
|---|---|---|
| `cache_repl_loads_on_startup` | `tests/sprint23.rs:1132` | Second REPL run reports `undefined variable: +` after the prelude was supposedly loaded from cache. Cache-hit path does not restore prelude bindings into the new session. |
| `persist_import_survives_restart` | `tests/sprint23.rs:1313` | Second REPL session does not see a helper module imported in session 1 and persisted via `user.cl` regeneration — the persisted `user.cl` is not re-read on session-2 startup. |
| `v4_cache_hit_dependency` (residual) | `tests/v4_pipeline.rs:609` | Cross-module cache-restore residual carried from Sprint 58 Wave 2 partial close. |

The heisenbug shape is load-bearing: `persist_import_survives_restart` passes ~1755/1754 times under heavy nextest parallelism and fails some runs (Sprint 58 §Findings). Under mixed-parallelism scheduling the session-side inline loop sometimes wins the race to install a dep's symbol table before the scheduler-side persistent worker does; sometimes the scheduler wins; sometimes the two interleave and one writes the table the other is mid-reading. That is a structural symptom — two orchestrators working on the same module at once — not a localised memory-ordering bug.

Decision 37 names this exact structural shape at the scheduler-side surface: *cache-hit decision + load is a branch INSIDE `register_module`'s recursive flow, not a parallel code path*. Sprint 58 Wave 2 enacted it at `try_cache_hit_load` (inside the scheduler-side `register_module` recursion). This workstream enacts the same discipline at the session-side surface — collapse `compile_dep_inline` and the per-form-handler dep-registration prologues into the single `register_module` recursion path.

## 2. Decision-37 alignment (Condition 1a)

Decision 37 defines `register_module(M)` as the SINGLE recursive flow that (a) installs M's symbol table (from cache or fresh typecheck), (b) walks `symbol_tables[M].imports` and recursively calls `register_module(each transitive dep)`, with cache-hit-or-fresh as a per-call branch INSIDE the same function. No parallel orchestrator; no `try_cache_hit_load` clone.

Sprint 58 Wave 2 applied this at the scheduler side: `try_cache_hit_load` lives INSIDE the recursive flow rather than being a parallel pipeline, and its cache-hit-or-not-cache-hit decision resolves per-call. The same decision framework, at the *session* side, says: the REPL eval thread that discovers an unloaded dep MUST NOT open an independent `priority_worker_loop` on that dep. It must drive the dep's registration through the SAME `register_module` recursion (synchronously waiting on `wait_inmem_complete_blocking` for the dep's completion), exactly as `main.rs`'s entry-module path does.

**Sprint 58 Wave 2 is the precedent.** Wave 2 deleted a scheduler-side dual (the `try_cache_hit_load` parallel path alongside fresh-build typecheck). Sprint 59 Workstream A deletes the session-side dual (the `compile_dep_inline` parallel worker loop alongside the persistent worker loop, and the handler-site "register *and* block *and* carry local state" pattern). In both cases the structural shape is identical: *two orchestrators converge to one `register_module` recursion*. If the Phase 3 design treated cache-hit integration (Wave 2) and persistence-dual collapse (S59 W/A) as independent problems, the convergence would re-diverge — Sprint 58 /review I-3 flagged exactly this risk. The collapse here is the second half of the same structural move, not a new concept.

The Decision-37 canonical flow (`design/arch/CLAUDE.md` Decision 37, reproduced for pseudocode clarity):

```
register_module(M):
  if <cache_dir>/M.meta.json exists and schema_version matches:
    deserialise → install SymbolTable for M → mark typecheck-complete
  else:
    parse → typecheck → install SymbolTable for M
  for each import in SymbolTable[M].imports:
    register_module(import.module)   # recursive, blocking on transitive deps
# codegen phase runs AFTER typecheck phase completes for all reachable modules;
# per-module order in codegen phase is independent (Decision 37 §3.2).
```

Under the collapsed shape, both the entry-module call (from `main.rs`) and the REPL-discovered-dep call (from eval) reduce to the same function call: `session.register_module(dep)`, which internally routes through the scheduler + persistent worker loop, uses `publish_dep_sexps` BEFORE scheduler notify (the Sprint 58 Wave 6 fix, preserved here), and blocks on `wait_inmem_complete_blocking` for completion. The session-side inline worker loop is deleted.

## 3. Target shape

A single `register_module` recursion, used by every persistence entry point in the session. Pseudocode (illustrative — exact signatures pinned in Phase 4 implementation):

```
// src/session_v4.rs
impl CompilerSession {
    /// THE single recursion entry. Called by main.rs (entry module),
    /// REPL eval (discovered dep), and every form handler in worker.rs
    /// via ctx.scheduler.register_module (which routes here).
    pub fn register_module(&mut self, module: &ModuleFullPath) -> Result<(), CranelispError> {
        if self.shared.symbol_tables.contains_key(module) {
            return Ok(());   // already installed — idempotent
        }

        // Decision 37 / Sprint 58 Wave 2 — cache-hit branch INSIDE the
        // recursion. Cache-hit installs the SymbolTable and returns; the
        // codegen worker later links the .o. Cache-miss parses, publishes
        // sexps, registers with the scheduler, and blocks.
        if self.try_cache_hit_install(module)? {
            // Transitive imports recursed into by try_cache_hit_install.
            return Ok(());
        }

        // Cache miss — resolve source, parse, publish sexps BEFORE
        // scheduler notify (Sprint 58 Wave 6 Defect 1).
        let (source, sexps) = self.read_and_parse_module_source(module)?;
        publish_sexps(&self.shared, module, &sexps);
        self.shared.scheduler.register_module(module.clone(), false);

        // Block until the persistent worker reaches inmem_done for this
        // module (and, transitively, every dep discovered during form
        // processing). The form handlers themselves call back into
        // self.register_module for each discovered dep, not into an
        // independent inline loop.
        self.shared.scheduler.wait_inmem_complete_blocking()?;
        Ok(())
    }
}

// src/worker.rs (unchanged in shape, but form handlers route dep
// registration through self.register_module via a new trait rather
// than through a second, session-side inline compile loop).
fn handle_import(ctx, module, specs) -> BlockAction {
    for spec in specs {
        if ctx.symbol_tables.contains_key(dep) { ... continue; }
        // Collapsed: one entry point, not "register-with-scheduler +
        // publish-sexps + block + hope persistent-workers-win-the-race".
        ctx.register_dep(dep, dep_file)?;   // delegates to session's
                                            // register_module path
        continue;
    }
    Ok(BlockAction::Continue)
}
```

Concretely, the collapse means:

- `compile_dep_inline` is deleted. REPL eval's dep-discovery routes through `self.register_module(dep)` directly, which uses the persistent worker loop exclusively.
- The per-form-handler `ctx.scheduler.register_module(dep, true)` + `block_for_typecheck` + `BlockAction::Block` return sequence remains the scheduler's correct shape, but the code path that runs it is `register_module`'s recursion — not a second orchestrator running on the eval thread.
- `wait_inmem_complete_blocking()` remains the single synchronisation primitive. No parallel drain on the eval thread.

The key behavioural difference: under the collapsed shape, the *single* persistent-worker pool drives all dep typechecking; the REPL eval thread waits on the scheduler's completion condvar. There is no race because there is no second worker — there is one worker pool and one waiter, the normal producer-consumer pattern.

Decision 37 §3.2's "order-independent codegen phase" property (slot indices pinned at typecheck time; slot contents filled by codegen workers in any order) is unchanged — the collapse affects the *typecheck phase* shape, not the codegen phase.

## 4. Prelude loading under the collapsed path (Condition 1b)

The Sprint 49 regression surface was a prelude-load code path that bypassed the macro expansion pipeline. The collapsed path MUST preserve the property that prelude enters the system through `register_module` as an ordinary module — no REPL-specific-bootstrap branch.

The current shape:

- `inject_prelude_if_needed` (src/worker.rs:2243) runs inside the priority worker loop's form classification. If a non-prelude module's first form is reached and the prelude is not yet installed, it resolves the prelude file, tries cache-hit, and on miss parses + publishes sexps + calls `ctx.scheduler.register_module(prelude_path, true)` + `block_for_typecheck`, returning `BlockAction::Block`. The worker then resumes when prelude typecheck completes. This already enters through `register_module` (via the scheduler) — good.
- `CompilerSession::new` seeds the `user` module symbol table and registers built-ins, but *does not* load the prelude. Prelude load is deferred until a module actually needs it (the first eval in a REPL session, or the first non-prelude module registered by `main.rs`). The Sprint 58 Wave 5 `new_with_prelude` test helper (referenced in /arch Condition 1b) drives this by calling `register_entry_module("user")` after construction; the worker loop discovers the implicit `(import [prelude [*]])` during form classification and routes prelude load through `inject_prelude_if_needed` → `register_module` — exactly the same path a user-authored `(import [prelude [*]])` would take.

Under the collapsed shape, `inject_prelude_if_needed` remains — it is already a branch INSIDE the recursion (the call-site is the priority worker loop processing a user-module form). The only change is that the `ctx.scheduler.register_module(prelude_path, true)` + `block_for_typecheck` it emits lands on the same `register_module` recursion everyone else uses; there is no REPL-special-case that bypasses it.

**Property statement (Condition 1b)**: under the collapsed path, every prelude-load invocation — from `main.rs` via `register_entry_module("user")`, from REPL-startup via `new_with_prelude`-style initialisation, or from a user-authored `(import [prelude [*]])` — enters through the same `inject_prelude_if_needed` call on the persistent priority worker, which calls `ctx.scheduler.register_module(prelude_path, true)` + `block_for_typecheck`. There is no REPL-session code path that loads the prelude by parsing + typechecking it directly without going through the scheduler. The "user" module is the only entry point that triggers implicit prelude injection, and it reaches that injection through the same form-classification path as every other module.

This property CAN be stated without qualification; Sprint 58 Wave 5 `new_with_prelude` already operates this way, and the collapse does not introduce any new prelude path. The collapse specifically does not introduce a REPL startup "pre-load prelude" shortcut — the risk pattern is precisely the one Sprint 49 hit.

If Phase 4 implementation discovers that deleting `compile_dep_inline` forces the eval thread to re-enter a synchronous block that can't be satisfied by the persistent worker (e.g., because the eval thread holds a lock the worker needs), that is a redesign signal and the design returns to `/arch` for review BEFORE landing. This is the Condition 1b qualification trigger.

## 5. Carry-forward invariant preservation (Condition 1c)

Decision 31 Scenario 2's per-redefinition JIT reclaim correctness rests on the upsert at `crates/cranelisp-typecheck/src/program.rs:2184-2232`: `register_defn_signature` reads the existing `ModuleEntry::Def.code: Option<C>` and clones it forward into the rebuilt entry so the carrier `Arc<Jit>` survives across the typecheck attempt; on success, codegen overwrites with the new `Code::Jit`; on failure, the carried-forward `code` remains and the GOT slot stays valid.

The collapsed path touches the *orchestration* of `register_module` but NOT the upsert site itself. The upsert lives downstream of `register_module` — inside `pass1_register` → `check_form` → `register_defn_signature` in the typecheck crate, called from the persistent worker loop. Under the collapsed path, *every* `defn` registration flows through exactly this code (because there is only one worker loop now, not two), so the carry-forward fires uniformly.

**Property statement (Condition 1c)**: the carry-forward upsert at `program.rs:2184-2232` is preserved verbatim. The collapsed path removes the session-side inline worker loop (which was a second caller of the *same* typecheck crate code, *not* a different code path for the upsert) — the upsert itself is unchanged. `register_module`'s recursion terminates at the typecheck crate boundary; the carry-forward is downstream of that boundary and its behavioural contract is orthogonal to the collapse.

Verification: `tests/v4_jit_reclaim.rs::decision31_scenario2_per_redefinition_jit_pages_reclaimed` (the direct Sc.2 test) MUST remain green across the collapse. If it regresses, the carry-forward site has been disturbed and the collapse has violated Condition 1c. The test is part of the Phase 5 baseline and is in the collapse's acceptance surface.

## 6. Sites being collapsed

Sprint 58 Wave 6 Defect 1 identified 5 sites that needed publish-before-register. Those sites are exactly the REPL-session-side persistence surfaces Workstream A collapses:

| # | File:line | Function | Role | Collapse action |
|---|---|---|---|---|
| 1 | `src/session_v4.rs:1938` | `compile_dep_inline` | REPL eval's inline dep compile (session-side second orchestrator) | **Delete.** Replace every call with `self.register_module(dep)`. |
| 2 | `src/worker.rs:1286` | `handle_import` publish-before-register | Persistent-worker form handler for `(import …)` | Keep the `publish_dep_sexps` + `scheduler.register_module` + `block_for_typecheck` sequence — but ensure it is the *only* orchestrator for this dep. No session-side `compile_dep_inline` mirror. |
| 3 | `src/worker.rs:1703` | `handle_export` publish-before-register | Persistent-worker form handler for `(export …)` | Same as #2. |
| 4 | `src/worker.rs:1803` | `handle_mod` publish-before-register | Persistent-worker form handler for `(mod …)` | Same as #2. |
| 5 | `src/worker.rs:2315` | `inject_prelude_if_needed` publish-before-register | Persistent-worker implicit prelude injection | Same as #2. (This is the Condition 1b prelude-load path — unchanged.) |

Additional surfaces to audit during Phase 4 (enumerated explicitly to prevent "collapse surfaces another dual we didn't know about"):

- `CompilerSession::register_module_with_source` (src/session_v4.rs:1240) — used by tests and by `register_entry_module`. This is the public entry shape; its body becomes the canonical `register_module` body. Confirm no call site bypasses it by constructing its internals directly.
- `CompilerSession::register_entry_module` (src/session_v4.rs:2985) — calls `register_module_with_source`. Unchanged; entry point.
- `CompilerSession::register_module` (src/session_v4.rs:1224) — today this delegates to `register_entry_module`. Confirm it keeps that shape and is the public name external callers (including REPL eval's dep-discovery) use.

If Phase 4 discovers a sixth site (e.g., a `handle_*` variant whose dep-registration bypasses both paths), that surface is added to the collapse list before implementation begins. The enumerated list is the commissioned scope, and a new surface resets the list.

## 7. Migration plan

The collapse lands in a single ordered sequence with cargo-check checkpoints — `/int`'s standard pattern. Each step keeps the build green.

1. **Thread a `register_dep(&mut ModuleCompiler, &ModuleFullPath, &Path) -> Result<(), CranelispError>` shim.** The shim runs the form-handler's per-dep prologue (source read, parse, source-hash record, publish_dep_sexps, `file_to_module` update) but does NOT call the scheduler — it returns a descriptor that the caller enqueues. Introduces no behaviour change; just refactors the prologue into one place. Cargo check: green.
2. **Route all 4 form-handler sites (#2–#5) through the shim.** `handle_import`, `handle_export`, `handle_mod`, `inject_prelude_if_needed` all emit the same publish-before-register prologue; replace each with `register_dep(ctx, dep, &dep_file)?; ctx.scheduler.register_module(dep.clone(), true); ctx.scheduler.block_for_typecheck(...)`. No behaviour change (the prologue is identical to before). Cargo check: green. Cargo nextest `tests::sprint23` subset (including the still-failing `cache_repl_loads_on_startup` and `persist_import_survives_restart`): still fails *in the same way* as baseline — the shim preserves behaviour, it does not yet collapse.
3. **Introduce `CompilerSession::register_dep_for_eval(&mut self, dep: &ModuleFullPath) -> Result<(), CranelispError>` as the replacement for `compile_dep_inline`.** Body: `self.register_module(dep)`. Does NOT delete `compile_dep_inline` yet. Cargo check: green.
4. **Rewire every `compile_dep_inline` call site to `register_dep_for_eval`.** Two expected call sites in `session_v4.rs` (the REPL eval's dep-discovery logic). Cargo check: green. Cargo nextest `tests::sprint23 cache_repl_loads_on_startup` + `persist_import_survives_restart` + `tests::v4_pipeline v4_cache_hit_dependency`: expected to FLIP GREEN at this step (the session-side dual orchestrator is no longer engaged). If they don't, halt and diagnose.
5. **Delete `compile_dep_inline`.** Cargo check: unused-function warning on the deleted function resolves when the last caller is gone. Cargo nextest: full suite green (modulo the 4 `/backend` and `/port` failures tracked by Workstreams B/C, which are orthogonal).
6. **Delete dead supporting helpers.** `SharedState.repl_check_state` usage patterns that only `compile_dep_inline` read; the local `module_sexps: HashMap` construction in the deleted function; any `ModuleCompiler` field that was only populated by the session-side inline loop. Cargo check: clean (no warnings per `/int` release gate #1).
7. **Run the heisenbug repro.** `cargo nextest run -p cranelisp tests::sprint23::persist_import_survives_restart --test-threads 8 --no-capture` in a loop 50 times — MUST be 50/50 green under the collapsed path (heisenbug source eliminated). If it flakes, the collapse missed a surface. Halt and diagnose.

Checkpoint commits: one per step. Each step is independently revertible. Step 4 is the headline test-flipping commit; step 5 is the dead-code deletion; step 6 is the release-gate cleanup; step 7 is the heisenbug verification (no code change — just the loop-repro).

## 8. Test strategy

**Existing failing tests expected to clear**:

| Test | File:line | Expected clear at step |
|---|---|---|
| `sprint23::cache_repl_loads_on_startup` | `tests/sprint23.rs:1132` | Step 4 |
| `sprint23::persist_import_survives_restart` | `tests/sprint23.rs:1313` | Step 4 |
| `v4_cache_hit_dependency` (residual) | `tests/v4_pipeline.rs:609` | Step 4 (the cross-module cache-restore residual is a session-side dep-discovery race shape at its root) |

**Heisenbug repro** (per Sprint 58 §Findings): `persist_import_survives_restart` has flaked at ~1755/1754 under `--max-fail=15` nextest parallelism. The collapse's step 7 verifies this specifically: 50 loop runs, high parallelism (`--test-threads 8`), one assertion — no failures. This is a *new* acceptance criterion introduced by Workstream A; it does not live in the existing test file (the test itself is sufficient), but the loop-repro IS the verification that the heisenbug shape is gone.

**Regression guard** (Condition 1c): `tests/v4_jit_reclaim.rs::decision31_scenario2_per_redefinition_jit_pages_reclaimed` MUST remain green. This test directly observes the carry-forward invariant and will catch any accidental disturbance.

**Regression guard** (Condition 1b): A new or existing test that exercises the REPL prelude-load path — `tests/e2e.rs` prelude-load tests + `tests/sprint23::persist_user_cl_created` — MUST remain green. These cover the "user" module injection and the persisted-user.cl backing file, which are the two prelude-related surfaces the collapse touches.

No new `tests/` authored by `/int` — `/qa` derives the test cases from this design doc per Sprint 59 Wave 3 sequencing (the existing failing tests plus the heisenbug repro ARE the test plan; `/qa` validates).

## 9. Risk and fallback

**Risk 1 — Sixth surface discovered**. If Phase 4 finds that some test or code path drives dep registration through a path other than the enumerated 5, the collapse list is incomplete. Mitigation: Step 2 thread-in of `register_dep` forces a cargo-wide re-read of every dep-registration call; the shim's type signature is narrow enough that any uncollapsed callsite is a compile error. If the new surface is discovered, it joins the collapse list before implementation.

**Risk 2 — Persistent worker pool cannot satisfy REPL eval's dep-discovery synchronously**. If deleting `compile_dep_inline` makes REPL eval wait forever on `wait_inmem_complete_blocking` because a worker is blocked on a lock the eval thread holds, the collapse has exposed a lock inversion. Mitigation: Condition 1b qualification trigger — return to `/arch` for review before landing. Likely root cause would be `self.shared.repl_check_state` contention, which is why step 6 explicitly names it for cleanup.

**Risk 3 — Cache-hit recursion under the collapsed path surfaces a transitive dep shape not yet tested**. `register_transitive_cached_imports` (worker.rs:1555) already recurses on cache-hit transitive imports per Sprint 58 Wave 2c. The collapse should not change its shape — but it now routes through the same `register_module` as fresh-build. Mitigation: Step 4's nextest run includes `v4_cache_hit_dependency` — if it does not flip green, the transitive-import recursion has a dual shape not yet seen.

**Fallback / re-scope trigger**. If step 4 does not flip all three failing tests green, the collapse is incomplete. `/sprint` re-scopes: either (a) split the collapse into two sprints (Sprint 59 lands the shim + form-handler reroute, Sprint 60 lands the `compile_dep_inline` deletion once a sixth surface is known), or (b) re-engage `/arch` on the dual-path root-cause assumption. Either route preserves the baseline (`git stash` + `git stash pop` discipline per `/int`'s git rules) — the collapse is not partially landed.

## 10. Sketch comparison

The sketch's pipeline is a single-threaded synchronous orchestrator: `compile_module_graph` does a topological sort, then iterates modules in order, calling per-module typecheck + codegen on the main thread. There is no scheduler, no persistent worker pool, no `compile_dep_inline`. The sketch has no session-side vs scheduler-side dual because the sketch has no scheduler — the whole pipeline is session-side.

The sketch is therefore SILENT on this problem. That silence IS the answer: the dual-path persistence shape is an artefact of introducing concurrent typechecking (Sprint 57 Wave 4 G9 persistent workers, Pipeline v4) without simultaneously retiring the synchronous driver that the pre-v4 codebase used for REPL dep-discovery. `compile_dep_inline` is a v3-era holdover ported forward, not a v4 design.

Under the collapsed shape, the v4 pipeline reaches the sketch's shape in the relevant sense: *one orchestrator per module*. The v4 difference is that the orchestrator is a persistent worker pool driven by a scheduler, not a main-thread loop — but the *number* of orchestrators per module is one in both designs. This is consistent with the broader v4 pipeline-convergence story: the sketch's correctness property (single orchestrator) carried forward; the sketch's *mechanism* (synchronous main-thread loop) did not.

No sketch-side divergence is being introduced; if anything, this workstream converges v4 toward the sketch's single-orchestrator property that got lost during the v3→v4 concurrency migration.

## 8. Sprint 60 Workstream E follow-ons

Sprint 59 Wave 1 /review (`design/review/sprint-59-wave-1.md`) raised three Importants against the Workstream A landing. All three are structural-completeness items: the §7 collapse is load-bearingly correct, but its "every dep registration routes through publish-first, statically" invariant has one unguarded site and one silent pool-assignment divergence, and the unit guard that pinned the invariant was deleted before both were closed. Sprint 60 Workstream E closes the three of them together.

The fixes are small and strictly additive to the §7 collapse — no collapse-era assumptions change. Framing them here (rather than in a new design doc) keeps the collapse's invariant statement in one place: future readers looking for "where is every dep registration consolidated?" find §6 (the 5-site enumeration), §7 (the shim), and §8 (the 6th site + the unit guard re-site).

### 8.1 E-1 — `register_transitive_cached_imports` is the 6th prologue site

**Location**: `src/worker.rs::register_transitive_cached_imports`, cache-miss branch at lines 1637–1684 (the SPRINT.md label "`recurse_into_transitive_deps` at ~1637" names this function colloquially; the actual name is `register_transitive_cached_imports`, introduced in Sprint 58 Wave 2c for transitive cache-hit recursion).

**Why it was missed in S59.** §6 enumerated the 5 sites from Sprint 58 Wave 6 Defect 1 (which pinned the publish-before-register race). Those 5 are the *form-handler* prologues. `register_transitive_cached_imports` is NOT a form handler — it is called from `try_cache_hit_load` (`worker.rs:1581`) when a cache-hit install needs to eagerly register a cache-miss transitive import for fresh build before the outer cache-hit can return. It was introduced in a later sprint (58 Wave 2c) for a different motivation (transitive cache-hit recursion) and was not in the Sprint 58 Wave 6 "5 publish-before-register sites" enumeration that §6 inherited. §9 Risk 1 predicted *exactly* this class ("a `handle_*` variant whose dep-registration bypasses both paths"); the prediction held.

**Call-path context.** A cache-hit load of module A discovers A's import B in A's serialised symbol table. If B is also cached → recurse (cache-hit). If B is NOT cached → register B for fresh build so a later worker processes it. The outer module A is mid-install (mid cache-hit recursion) and is NOT waiting on B synchronously — it has already installed A's own SymbolTable and returned to its caller. B's registration is therefore "fire-and-forget from A's perspective": no outer waiter.

**Does it need `delays_other=true` or `false`?** The current code passes `true` (line 1684). This is the right value, but the rationale is different from the form-handler sites: in the form-handler case the outer module IS blocked on B (`block_for_typecheck`) and must be prioritised; here, the outer module has already finished. The reason `true` is still correct is that any OTHER module that imports B will block on B's typecheck (via normal form-handler import-blocking), so prioritising B's typecheck is the right default regardless of whether the originating caller is waiting. `true` is the correct value for all dep-registration sites in the worker; see §8.2 below for the reconciliation.

**Migration approach.** Route the cache-miss branch (lines 1647–1684) through the existing `register_dep` shim (`worker.rs:1327`). The shim already performs steps 1–6 of the prologue (source read, parse, source-hash record, source-text stash, file_to_module update, publish_dep_sexps). The cache-miss branch currently inlines steps 1, 2, 3, 5 (no source-text stash; no file_to_module update above the inline). After migration:

```rust
// Replace lines 1647–1684 with:
let dep_sexps = match register_dep(ctx, transitive_dep, &dep_file, |e| CranelispError::ModuleError {
    message: format!("failed to read transitive dep '{}': {}", transitive_dep, e),
    file: Some(dep_file.clone()),
    span: Span::SYNTHETIC,
}) {
    Ok(s) => s,
    Err(_) => continue,   // preserve current silent-continue behaviour
                          // (cache-hit recursion is best-effort; regular
                          // import resolution will re-surface a hard error).
};
let _ = dep_sexps;        // ignore returned sexps — `register_dep` has
                          // published them into shared.module_sexps.
ctx.scheduler.register_module(transitive_dep.clone(), true);
```

This is a structural refactor: net-zero behaviour change in the success case (the shim does the same steps, in the same order, with the same publish-before-register discipline). The surface-observable effect is that source-text stash and file_to_module update now happen in this site too — both are strictly additive (no call site reads them in a way that `register_transitive_cached_imports` would regress). The `continue`-on-error pattern preserves the current "best-effort eager registration" stance of the function.

**LOC impact**: −38, +10 (worker.rs only).

**Side-property gained**: after E-1 lands, *every* publish-then-register sequence in the codebase routes through either `register_dep` (worker-side) or `register_dep_for_eval` (session-side, which in turn delegates to the same scheduler surface). The static invariant E-3 re-asserts becomes defensible.

### 8.2 E-2 — `register_dep_for_eval` passes `delays_other=false`, diverging from every other worker-side site

**Location**: `src/session_v4.rs:1311`.

**What `delays_other` controls.** `scheduler.register_module(module, delays_other: bool)` at `src/scheduler.rs:296` routes the newly-registered module into `ModulePool::TypecheckFirst` if `true`, `ModulePool::TypecheckNext` if `false`. TypecheckFirst is the prioritised queue (`scheduler.rs:487-498`): workers pull from it before TypecheckNext. The semantic distinction is "is some other module currently blocked on this module's typecheck completing?" — if yes, prioritise.

**Worker-side sites.** All five worker-side call sites (`worker.rs:1268`, `1684`, `1755`, `1838`, `2326`) pass `true`. In four of the five the outer module is in `TypecheckBlocked` state on this dep (via `block_for_typecheck`) and `true` is structurally correct. In the fifth (`1684` — the E-1 site) the outer module has already finished, but `true` is still correct (see §8.1 rationale: other modules transitively importing this dep will block). The worker-side consensus is `true` always.

**Session-side `register_module_with_source` (line 1268) and `reload_module` (line 1199)** pass `false`. In both cases the module being registered IS the entry module — the eval thread is the single caller and is itself blocked on `wait_inmem_complete_blocking()`. `false` is correct at the entry-module surface because there is no *other* module currently waiting: the eval thread owns the whole-world wait.

**`register_dep_for_eval` (line 1311)** passes `false`. This is the divergence. The function is called from eval's retry loop (`session_v4.rs:1639`), *after* a `ProcessResult::Blocked` return from the form handler. The form handler that produced `Blocked` has already called `scheduler.register_module(dep, true)` — so the dep IS in TypecheckFirst already, and the `register_dep_for_eval` call is an idempotent no-op by the scheduler's `contains_key` guard (`scheduler.rs:304`). **Today, `false` has no observable effect.**

**Why it matters anyway.** The docstring on `register_dep_for_eval` says it defensively serves call sites "without a prior form-handler registration (tests, alternative eval paths)". Along that speculative path — which the `/review` Suggestion 1 correctly flags as speculative — the dep lands in TypecheckNext, not TypecheckFirst. That is a silent pool-assignment divergence from the worker-side consensus (`true` everywhere a dep is registered on behalf of someone blocked on it). The caller (`eval` retry loop) IS blocked on this dep via `wait_module_inmem_complete_blocking` (line 1328) — so by the `delays_other` contract, the right value is `true`.

**Reconciliation.** Change `false` → `true` at line 1311. Low-risk:
- Hot path: form handler already registered with `true`; the change is no-op under the idempotency guard.
- Speculative path: silently upgrades the dep to TypecheckFirst, matching worker-side consensus.
- No test is known to observe the `false` value — /review characterised it as "silent".

**ONE value is correct for ALL worker-side and session-side dep-registration sites: `true`.** The entry-module sites (`register_module_with_source:1268`, `reload_module:1199`) are genuinely different: they are the single caller on the whole-world wait, and `false` reflects "no other module is waiting on this." Those two sites stay `false`. The `register_dep_for_eval` site is NOT an entry-module site — it is a dep-registration site — and therefore should match worker-side dep-registration sites.

**LOC impact**: 1 line.

**Follow-on tidying (bundle-scale, per SPRINT.md §FIXME Debt "bundled into E")**: the FIXME comment at `tests/sprint23.rs:1126-1131` (Sprint 59 Wave 1 misattribution finding) — remove / rewrite per /review wave 1's note. Read the FIXME text before rewriting to preserve any load-bearing signal.

### 8.3 E-3 — Re-site the deleted unit guard `compile_dep_inline_publishes_sexps_before_register`

**What the deleted test guarded.** The original test lived in `session_v4.rs::persistent_worker_tests` (referenced at `worker.rs:1293` in the `publish_dep_sexps` docstring). It pinned the *within-`compile_dep_inline`-ordering* invariant: that `compile_dep_inline` published dep_sexps to `shared.module_sexps` BEFORE calling `scheduler.register_module(dep, true)`. The concrete failure it caught was a codegen-regression that swapped the two operations, exposing the Sprint 58 Wave 6 Defect 1 race.

After §7 Step 5 deleted `compile_dep_inline`, the function no longer exists; the unit test was deleted with its subject. The /review argument for its deletion was "invariant is now structurally preserved" — which is true *in aggregate* across all dep-registration sites, but /review I-3 correctly observed the structural argument is only sound once E-1 lands (otherwise `register_transitive_cached_imports` is a counterexample to the "every dep registration routes through the shim" structural claim).

**Post-E-1 structural invariant (to be guarded).** Every dep registration reaches `scheduler.register_module(dep, _)` via a call path that, immediately upstream, called `publish_dep_sexps` (directly or via `register_dep`'s body). The causal order is:

```
publish_dep_sexps(..., dep, sexps)   //  happens-before
    ↓
scheduler.register_module(dep, _)
```

under *every* execution — not just the paths /review happened to re-read.

**How to re-express under the shim.** Two complementary test shapes, both in `session_v4.rs::persistent_worker_tests` (beside where the deleted test lived):

**Test A — `register_dep_shim_publishes_before_caller_registers` (unit, direct)**. Call `register_dep` on a minimal `ModuleCompiler` fixture, observe that on return: (a) `shared.module_sexps` contains an entry for the dep, (b) the entry value equals the parsed sexps of the input source. The caller of `register_dep` (form handler) then calls `scheduler.register_module` — so the shim's contract is "publish THEN return; caller registers AFTER." The test asserts the publication precondition is established at return-time.

```rust
// Pseudocode / Rust signature shape:
#[test]
fn register_dep_shim_publishes_before_caller_registers() {
    // Fixture: minimal ModuleCompiler wrapping a fresh SharedState with empty
    // module_sexps + a test scheduler. Write a 1-form dep source to a tempfile.
    let shared = test_shared_state_empty();
    let dep = ModuleFullPath::from("test_dep");
    let dep_file = write_tempfile("(defn x [] 1)");
    let mut ctx = test_module_compiler(&shared, ...);

    // Act: invoke the shim (no caller-level scheduler.register_module yet).
    let _sexps = register_dep(&mut ctx, &dep, &dep_file, |e| panic!("{e}"))
        .expect("register_dep should succeed");

    // Assert: dep_sexps are published BEFORE the caller gets a chance to
    // call scheduler.register_module. If a future refactor moves the publish
    // below the return, this assertion fails.
    assert!(shared.module_sexps.lock().unwrap().contains_key(&dep),
        "register_dep MUST publish dep_sexps into shared.module_sexps before returning");

    // Additionally: scheduler MUST NOT yet know about the dep — the shim
    // is publish-only; caller is responsible for register_module.
    assert!(!shared.scheduler.is_registered(&dep),
        "register_dep MUST NOT call scheduler.register_module — caller does that");
}
```

**Test B — `register_dep_for_eval_publishes_before_registering` (unit, session-side)**. The session-side equivalent for `register_dep_for_eval`: assert that when called with a dep not yet in `shared.module_sexps`, on the scheduler-register call-path (the function's body) the publish precedes the register.

Because `register_dep_for_eval` internally runs `publish` then `scheduler.register_module`, the natural guard is a sequencing test: install a test hook / observable into `scheduler.register_module` that records `shared.module_sexps.contains_key(dep)` at the call-moment; assert it returns `true`. If the test hook infrastructure is heavier than the guard is worth, an alternative is a **grep-style structural test** that scans `register_dep_for_eval`'s source for the order of calls (similar to the "no bare `scheduler.register_module` without prior `publish_dep_sexps`" structural pattern /review Suggestion 1 hinted at):

```rust
#[test]
fn register_dep_for_eval_body_orders_publish_before_register() {
    // Read the session_v4.rs source, locate register_dep_for_eval's body,
    // assert the first occurrence of "module_sexps.lock" precedes the first
    // occurrence of "scheduler.register_module" within the function's span.
    // Coarse but sufficient as a regression guard against accidental reordering.
}
```

`/int` judgement: pick Test A unconditionally (direct, fast, no source-grep fragility); pick Test B only if the `register_dep_for_eval`-specific fixture is trivial to construct. If it isn't, rely on Test A plus a single assertion inside `register_dep_for_eval` (`debug_assert!(self.shared.module_sexps.lock()...contains_key(dep_module))` immediately before the `scheduler.register_module` call) as the release-debug guard. /review's Suggestion 1 already hinted at this debug-assert shape; E-3 adopts it.

**LOC impact**: +25–40 (one unit test, one debug-assert).

### 8.4 Test plan

Existing tests flipped / new regression guards:

| Behaviour | Shape | Location |
|---|---|---|
| `register_dep_shim_publishes_before_caller_registers` | New unit (Test A above) | `src/session_v4.rs::persistent_worker_tests` |
| `register_dep_for_eval_publishes_before_registering` OR `debug_assert!` precondition | Unit OR inline debug-assert | `src/session_v4.rs::register_dep_for_eval` + tests module |
| `register_transitive_cached_imports_routes_through_shim` | New unit — call the function with a cache-miss dep; verify the `register_dep` shim's postconditions (sexps published, source stashed, file_to_module updated) | `src/worker.rs::tests` |
| `register_dep_for_eval_uses_delays_other_true` | New unit — observable via scheduler state after call: pool is TypecheckFirst not TypecheckNext | `src/session_v4.rs::persistent_worker_tests` |

No `tests/*.rs` integration test is authored for E by `/int`; `/qa` derives integration coverage from this section if needed. The unit tests above live beside the code they guard (per user preference `feedback_unit_tests_with_dev.md`).

**Tests expected to FLIP behaviour**: none. E-1 is structural (same behaviour, one call path). E-2's visible behaviour is a no-op on the hot path (form handler already registered with `true`). E-3 is additive tests. No existing failing test flips green or red. That is by design — E is hygiene, not defect repair.

**Regression guards that would catch re-emergence**:
- E-1 regression (a new 7th inlined prologue site): caught by `register_transitive_cached_imports_routes_through_shim` via the missing source-stash / file_to_module-update assertion.
- E-2 regression (someone writes another `register_module(_, false)` for a non-entry-module site): caught by `register_dep_for_eval_uses_delays_other_true` (scheduler-pool observation).
- E-3 regression (the publish-before-register race re-opens inside `register_dep` or `register_dep_for_eval`): caught by Test A's publish-before-return assertion and/or the debug-assert.

### 8.5 Scope estimate

- E-1: ~50 LOC net (−38 inline, +10 shim call, +2 reshuffled imports), one unit test ~30 LOC.
- E-2: 1 LOC change, one unit test ~20 LOC, one docstring update ~5 lines.
- E-3: ~40 LOC unit test + optional debug-assert (~3 LOC). Test A alone is ~30 LOC.

**Combined**: ~170–200 LOC across `src/worker.rs` and `src/session_v4.rs`; **~0.5 day** of implementation. No interface changes. No crate-boundary touches. Isolated to `/int`'s crate. Falls well under the Condition 2 (SPRINT.md §Architecture Review §Condition 2) scope threshold for rescope; no /arch escalation required.

Wave placement: parallel-safe with Workstream A audit (per SPRINT.md §Phase 3b disposition — E is explicitly named as safe to launch in parallel with A).

## 9. Sprint 60 Workstream G — `/sig` docstring format fix

Workstream G (SPRINT.md §Workstreams, row G) is a 1-line format fix in `/int`'s introspection path. It is scoped here rather than a dedicated design doc because (a) it is a single-function edit, (b) the spec reference is unambiguous, (c) the fix shape is mechanically obvious from comparison with an adjacent function that does the right thing.

### 9.1 Current vs. spec-required output

**Spec reference** — `repl/spec.md §1.1 Universal Output Format` (verbatim from line 156–167):

> All REPL output uses a unified format that mirrors Cranelisp type annotation syntax. The primary line is always:
>
> ```
> :Type {value|name} ; {classification} - {docstring first line}
> ```
>
> […]
> - `; {classification} - {docstring}` — optional comment suffix. The classification is the name of the defining special form (`defn`, `deftype`, `deftrait`, `defmacro`, `special form`, `impl`) […]. The docstring is the first line of the symbol's documentation. If the symbol has no docstring, only the classification appears. […]

Spec example (line 185):

```
user> double
:(Fn [primitives/Int] primitives/Int) user/double ; defn - Multiply by 2
```

**Current output** for `/sig add` on `(defn add "Add two ints" [:Int a :Int b] (+ a b))`:

```
:(Fn [Int Int] Int) add ; defn
```

The dash `-` and the docstring first line are omitted. The classification is correct; the trailing `- <doc>` field is missing.

### 9.2 Location

`src/session_v4.rs::format_entry_sig`, line 361 (the single-sig `Def { scheme, kind, docstring, .. }` arm):

```rust
format!(":{} {} ; {}", scheme.ty, name, classification)
```

The bug: `docstring` is destructured from the pattern (line 345) but never used in the format call. The multi-sig branch (`format_overloaded_variants_bare`, line 425–426) correctly calls `append_docstring_comment(base, docstring)`; the single-sig branch does not.

The helper `append_docstring_comment` (line 3547) already implements the spec-compliant " - {first_line}" append with a correct empty-docstring fallthrough. It is the exact helper used by `format_overloaded_variants_bare`; reusing it ensures both paths produce identical formatting.

### 9.3 Proposed fix

2 lines (1-line behavioural + style reformat for readability):

```rust
// Before (line 361):
format!(":{} {} ; {}", scheme.ty, name, classification)

// After:
let base = format!(":{} {} ; {}", scheme.ty, name, classification);
append_docstring_comment(base, docstring.as_deref())
```

`docstring` is typed `Option<String>` in `ModuleEntry::Def`; `append_docstring_comment` takes `Option<&str>`; `.as_deref()` bridges.

No other /sig / introspection paths need change — all already call `append_docstring_comment` or have no docstring field (e.g., `Constructor`, `TypeDef`, `TraitDecl` — those use their own formats that /repl spec distinguishes).

### 9.4 Regression guard

One unit test in `src/session_v4.rs::format_entry_sig_tests` (or similar) asserting the exact spec-expected string shape for:

- (a) a `Def` with a docstring — expect trailing ` - <doc>`.
- (b) a `Def` without a docstring — expect no trailing dash, classification is last token.
- (c) a `Def` with a multi-line docstring — expect only first line appended (delegated to `append_docstring_comment`, but cover the caller's wiring).

Test shape:

```rust
#[test]
fn format_entry_sig_defn_includes_docstring_after_dash() {
    // spec: repl/spec.md §1.1 — universal format mandates "; classification - docstring"
    let entry = make_def_entry(
        "(Fn [Int Int] Int)",
        Some("Add two ints".to_string()),
        DefKind::Defn { ... },
    );
    let out = format_entry_sig(&entry, "add");
    assert_eq!(out, ":(Fn [Int Int] Int) add ; defn - Add two ints");
}

#[test]
fn format_entry_sig_defn_without_docstring_omits_dash() {
    // spec: repl/spec.md §1.1 — "If the symbol has no docstring, only the classification appears."
    let entry = make_def_entry("(Fn [Int] Int)", None, ...);
    assert_eq!(format_entry_sig(&entry, "id"), ":(Fn [Int] Int) id ; defn");
}

#[test]
fn format_entry_sig_defn_docstring_uses_first_line_only() {
    // spec: repl/spec.md §1.1 — "The docstring is the first line of the symbol's documentation."
    let entry = make_def_entry("(Fn [Int] Int)", Some("First line\nSecond line".into()), ...);
    let out = format_entry_sig(&entry, "f");
    assert!(out.contains(" - First line"));
    assert!(!out.contains("Second line"));
}
```

LOC: ~2 source lines + ~40 test lines. Co-located with the existing `format_entry_sig` unit tests, if any; if none, introduce a small `#[cfg(test)] mod format_entry_sig_tests` block. Per /int scope discipline (`src/CLAUDE.md` §Testing), unit tests live beside the code.

### 9.5 `/repl` spec-audit touchpoint

Workstream G's SPRINT.md framing names `/repl` as spec-auditor and `/int` as implementor. `/int`'s reading of `repl/spec.md §1.1` here is sufficient for the fix; no FIXME(/repl) is filed because the spec is unambiguous on format and the example at line 185 is directly actionable. If `/repl` has a concern about the test shape (e.g., wants the test to assert against a canonical fixture rather than a hand-written expected string), that is a review-time adjustment, not a blocking design concern.

### 9.6 Unit-vs-integration coverage layering (resolving `tests/plan/ring4.md §G.20.10` FIXME)

The three §9.4 unit tests and `/qa`'s proposed integration smoke (`sig_slash_command_displays_docstring_after_dash` in `tests/plan/ring4.md §G.20.7`) are **complementary, not redundant**. They guard different layers:

- **Unit layer (`/int`, §9.4)** — `format_entry_sig` invoked directly on hand-constructed `ModuleEntry::Def` values. Guards the formatter: the `" - <first-line>"` append, the empty-docstring fallthrough, the multi-line-first-only policy. Isolated from parsing, typecheck, REPL dispatch, and module-qualification path construction.
- **Integration layer (`/qa`, §G.20.7)** — live REPL session issues `/sig add` and the output string is asserted end-to-end. Guards the REPL dispatch chain: input line → slash-command parser → handler lookup → symbol resolution → `format_entry_sig` call → stdout. A regression in any of those layers (e.g., the slash-command router returns early without calling the formatter, or module-qualification rewrites the Fn type before display) passes the unit tests and fails the integration smoke.

The integration smoke is authored **regardless of** unit coverage: unit-passing + integration-failing is a documented failure shape this pair discriminates, and its value is precisely that it can catch REPL-dispatch regressions the unit tests structurally cannot see.

This confirms `/qa`'s recommendation in `tests/plan/ring4.md §G.20.10`. No change to §9.4; `/qa` proceeds with `sig_slash_command_displays_docstring_after_dash` as planned.

## Cross-references

- `design/arch/CLAUDE.md` Decision 37 — cache-hit integration lives inside `register_module`'s recursive flow (the precedent for this collapse).
- `design/arch/CLAUDE.md` Decision 31 Scenario 2 — carry-forward invariant (Condition 1c).
- `design/arch/CLAUDE.md` Decision 25 — compiled code on `ModuleEntry::Def.code`; cache stores `.meta.json` + `.o`; cache-hit LOADS the `.o`, does not re-codegen. The collapse must preserve this post-5c shape.
- `design/arch/pipeline-v4.md` §9 — v4 target data-model.
- `design/int/cache-hit-loading.md` — the Sprint 58 Wave 2c cache-hit-side of this same structural collapse.
- `design/int/persistent-workers.md` — Sprint 57 Wave 4 G9 persistent priority workers (the concurrency model under which the dual emerged).
- `sprints/archive/sprint-58.md` §Findings — "Dual-path persistence is the next structural debt"; heisenbug narrative.
- `sprints/archive/sprint-58.md` §Wave 6 /review Importants — I-3 commissioning this design doc.
- Sprint 58 Wave 2 — `try_cache_hit_load` deletion (the scheduler-side precedent collapse).
