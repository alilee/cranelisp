use super::*;
use std::sync::atomic::AtomicBool;

fn mod_path(name: &str) -> ModuleFullPath {
    ModuleFullPath::from(name)
}

/// Empty cluster-sexps packet for scheduler unit tests that only exercise
/// pool/queue/waiter coordination (S78 packet model — the sexps payload is
/// not read by these tests).
fn no_sexps() -> std::sync::Arc<[Sexp]> {
    std::sync::Arc::from(Vec::new())
}

#[test]
fn take_object_codegen_returns_none_on_shutdown() {
    let sched = CompileScheduler::new();
    sched.shutdown();
    assert!(sched.take_object_codegen().is_none());
}

#[test]
fn take_object_codegen_object_working_prevents_double_claim() {
    let sched = CompileScheduler::new();
    let m = mod_path("test.mod");
    sched.register_module(m.clone(), no_sexps(), false);
    sched.notify_typecheck_done(&m);

    // First claim should succeed and set object_working.
    let first = sched.take_object_codegen();
    assert_eq!(first, Some(m.clone()));

    // Verify the module is marked as object_working.
    {
        let state = sched.lock();
        let ms = state.modules.get(&m).unwrap();
        assert!(ms.object_working);
        assert!(!ms.object_done);
    }

    // Shutdown so the second take_object_codegen doesn't block.
    sched.shutdown();

    // Second call should return None (module is object_working,
    // and shutdown is set).
    let second = sched.take_object_codegen();
    assert!(second.is_none());
}

#[test]
fn notify_object_codegen_complete_clears_object_working() {
    let sched = CompileScheduler::new();
    let m = mod_path("test.mod");
    sched.register_module(m.clone(), no_sexps(), false);
    sched.notify_typecheck_done(&m);

    // Claim the module.
    let claimed = sched.take_object_codegen();
    assert_eq!(claimed, Some(m.clone()));

    // Complete object codegen.
    sched.notify_object_codegen_complete(&m);

    // Verify object_working is cleared and object_done is set.
    let state = sched.lock();
    let ms = state.modules.get(&m).unwrap();
    assert!(!ms.object_working);
    assert!(ms.object_done);
}

// S95 window-#2 (nice-worker object-codegen lost wakeup) deterministic
// guard. Models the EXACT stranding ordering the SIGUSR1 dump pinned: a
// module reaches `TypecheckDone` with `object_done == false` AND its
// `notify_typecheck_done` `object_work_available.notify_all()` already fired
// (the nice worker was mid check-then-park gap, not yet parked, so the notify
// was lost). A nice worker then calls `park_nice_worker`. With the fix it
// re-checks pending object work UNDER THE LOCK and returns `true` (do not
// park — re-loop and claim). On revert (no re-check) it parks forever on a
// notify that will never fire again — the module strands and
// `wait_object_complete` hangs. The spawned-thread + `recv_timeout` shape
// makes the revert a clean RED (assertion failure after the timeout), not a
// suite hang; `shutdown()` releases the parked thread either way.
#[test]
fn park_nice_worker_does_not_strand_pending_object_codegen() {
    use std::sync::mpsc;
    use std::time::Duration;

    let sched = std::sync::Arc::new(CompileScheduler::new());
    let m = mod_path("user");

    // Drive `m` to TypecheckDone with object_done == false. The
    // `notify_typecheck_done` call ALSO fires the `object_work_available`
    // notify here — modelling the notify that landed in the nice worker's
    // check-then-park gap and was lost (no waiter parked yet).
    sched.register_module(m.clone(), no_sexps(), false);
    let _ = sched.take_priority_work(); // pop -> TypecheckWorking
    sched.notify_typecheck_done(&m); // -> TypecheckDone, object_done=false

    // Sanity: object work IS pending (this is the work the nice worker must
    // not strand).
    {
        let state = sched.lock();
        let ms = state.modules.get(&m).unwrap();
        assert_eq!(ms.pool, ModulePool::TypecheckDone);
        assert!(!ms.object_done && !ms.object_working);
    }

    // A nice worker now parks — AFTER the (lost) notify. With the fix this
    // returns `true` promptly (pending work seen under the lock). Without it,
    // it blocks forever.
    let (tx, rx) = mpsc::channel();
    let sched_clone = std::sync::Arc::clone(&sched);
    let handle = std::thread::spawn(move || {
        let r = sched_clone.park_nice_worker();
        let _ = tx.send(r);
    });

    let outcome = rx.recv_timeout(Duration::from_secs(2));

    // Release the parked thread on the revert path (and join cleanly on the
    // fix path) so no thread leaks regardless of branch.
    sched.shutdown();
    let _ = handle.join();

    match outcome {
        Ok(returned) => assert!(
            returned,
            "park_nice_worker must report work-available (true), not shutdown",
        ),
        Err(_) => panic!(
            "park_nice_worker STRANDED pending object codegen — lost wakeup \
                 (window #2): it parked on an already-fired notify instead of \
                 re-checking pending object work under the lock",
        ),
    }
}

#[test]
fn wait_object_complete_returns_when_all_done() {
    let sched = CompileScheduler::new();
    let m = mod_path("test.mod");
    sched.register_module(m.clone(), no_sexps(), false);
    sched.notify_typecheck_done(&m);

    // Mark object codegen complete (skip the claim step — direct
    // notification is valid for testing the wait condition).
    sched.notify_object_codegen_complete(&m);

    // wait_object_complete should return immediately.
    let result = sched.wait_object_complete();
    assert!(result.is_ok());
}

#[test]
fn wait_object_complete_returns_err_on_failed_module() {
    let sched = CompileScheduler::new();
    let m = mod_path("test.mod");
    sched.register_module(m.clone(), no_sexps(), false);
    sched.notify_module_failed(
        &m,
        CranelispError::ModuleError {
            message: "test error".into(),
            location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
        },
    );

    let result = sched.wait_object_complete();
    assert!(result.is_err());
}

// spec: design/int/session-transaction.md §8 — R18 deterministic persist:
// a completed module marked object-stale re-enters the nice-worker claim
// scan and `wait_object_complete` genuinely waits for the rewrite.
#[test]
fn mark_object_stale_requeues_completed_module_for_object_codegen() {
    let sched = CompileScheduler::new();
    let m = mod_path("user");
    sched.register_module(m.clone(), no_sexps(), false);
    sched.notify_typecheck_done(&m);

    // First object pass completes normally.
    assert_eq!(sched.try_take_object_codegen(), Some(m.clone()));
    sched.notify_object_codegen_complete(&m);
    assert!(
        sched.try_take_object_codegen().is_none(),
        "object-done module must not be re-claimable without a mark"
    );

    // A defining turn marks the table stale — the module is claimable
    // again and wait_object_complete blocks until the rewrite lands.
    sched.mark_object_stale(&m);
    {
        let state = sched.lock();
        let ms = state.modules.get(&m).unwrap();
        assert!(!ms.object_done, "mark must clear object_done");
    }
    assert_eq!(
        sched.try_take_object_codegen(),
        Some(m.clone()),
        "stale module must be re-claimable for the rewrite"
    );
    sched.notify_object_codegen_complete(&m);
    assert!(sched.wait_object_complete().is_ok());
}

// spec: (same anchor) — the lost-update race: a mark that lands WHILE a
// write is in flight must NOT be clobbered by the write's completion
// (the completed write observed an older table).
#[test]
fn mark_object_stale_neg_mid_write_mark_is_not_lost() {
    let sched = CompileScheduler::new();
    let m = mod_path("user");
    sched.register_module(m.clone(), no_sexps(), false);
    sched.notify_typecheck_done(&m);

    // Nice worker claims (write in flight)…
    assert_eq!(sched.try_take_object_codegen(), Some(m.clone()));
    // …a defining turn marks the module stale mid-write…
    sched.mark_object_stale(&m);
    // …and the in-flight write completes: the module must STAY not-done
    // (re-claimable), not be marked complete with the older table.
    sched.notify_object_codegen_complete(&m);
    {
        let state = sched.lock();
        let ms = state.modules.get(&m).unwrap();
        assert!(
            !ms.object_done,
            "a mid-write mark must survive the write's completion"
        );
        assert!(!ms.object_working);
    }
    assert_eq!(
        sched.try_take_object_codegen(),
        Some(m.clone()),
        "the pending rewrite must be claimable after the stale write"
    );
    sched.notify_object_codegen_complete(&m);
    assert!(sched.wait_object_complete().is_ok());
}

// spec: (same anchor) — negative: marking is a no-op for modules the
// scheduler doesn't know or that never reached a terminal typecheck pool
// (nothing coherent to persist yet).
#[test]
fn mark_object_stale_neg_noop_for_unknown_or_mid_typecheck_module() {
    let sched = CompileScheduler::new();
    // Unknown module: no panic, nothing claimable.
    sched.mark_object_stale(&mod_path("ghost"));
    assert!(sched.try_take_object_codegen().is_none());

    // Registered but not yet terminal: still not claimable.
    let m = mod_path("user");
    sched.register_module(m.clone(), no_sexps(), false);
    sched.mark_object_stale(&m);
    assert!(
        sched.try_take_object_codegen().is_none(),
        "a mid-typecheck module must not enter the object queue via a mark"
    );
}

#[test]
fn nice_worker_lifecycle_spawn_and_shutdown() {
    use std::sync::Arc;

    let shared = Arc::new(crate::session_v4::SharedState {
        scheduler: CompileScheduler::new(),
        project_root: std::path::PathBuf::new(),
        lib_dirs: Mutex::new(Vec::new()),
        platform_dirs: Mutex::new(Vec::new()),
        module_aliases: cranelisp_types::ModuleAliases::default(),
        prelude_fallback: cranelisp_typecheck::PreludeFallback::default(),
        declared_exports: crate::imports::DeclaredExports::default(),
        // Sprint 67 Cluster B sub-fire 3: ObjectCache facade. Disabled
        // (None) for this unit test — no .o compilation runs here.
        cache: std::sync::Arc::new(crate::cache::ObjectCache::new(None, None)),
        promote_nice_workers: AtomicBool::new(false),
        // Sprint 67 Cluster B sub-fire 2e: `cached_modules` SharedState
        // duplicate deleted — scheduler set is single source of truth.
        file_to_module: Mutex::new(std::collections::HashMap::new()),
        symbol_tables: dashmap::DashMap::new(),
        next_type_id: std::sync::atomic::AtomicU32::new(0),
        // Sprint 67 Cluster B sub-fire 2d: `current_module` PIF-relocated
        // to `CompilerSession::current_repl_module`.
        // Sprint 77 W-SharedState: `repl_check_state` PIF-relocated to
        // `CompilerSession::repl_check_state` (initiator-only).
        typecheck_products: dashmap::DashMap::new(),
        // Sprint 58 Wave 3b: kept_jits / kept_linkers dissolved per
        // Decision 35.
        kept_dlls: Mutex::new(Vec::new()),
        // D1b: store is REPL-only; `run_mode` is `Repl` below, so `Some`.
        introspection: crate::session_v4::RunMode::Repl
            .populates_introspection()
            .then(dashmap::DashMap::new),
        // S91 Pillar-3: importable-symbol indices (empty/unarmed default —
        // this scheduler unit test does not arm the burn-down).
        importable_indices: crate::session_v4::ImportableIndices::default(),
        // No redefinition transaction runs in this lifecycle test.
        retained_code: Mutex::new(Vec::new()),
        fresh_jit_drop_glues: dashmap::DashMap::new(),
        // D1 ruling §4: run-mode carrier. This scheduler unit test does not
        // exercise the introspection gate or the layout-hash gate; `Repl`
        // is an inert default here.
        run_mode: crate::session_v4::RunMode::Repl,
        // Sprint 66 Wave 3a-γ: TestRunnerState stub for the scheduler
        // unit test. The test exercises the nice-worker lifecycle, not
        // test/trace intrinsics — a default state with empty/null
        // pointers is fine; no JIT codegen runs in this test.
        test_runner_state: Box::new(crate::session_v4::TestRunnerState::stub()),
    });

    let m = mod_path("test.mod");
    shared
        .scheduler
        .register_module(m.clone(), no_sexps(), false);
    shared.scheduler.notify_typecheck_done(&m);

    // Spawn a nice worker, let it process the module, then shut down.
    std::thread::scope(|scope| {
        crate::session_v4::spawn_nice_workers(scope, &shared, 1);

        // The worker calls notify_object_codegen_complete, which
        // sets object_done = true. Wait for it.
        let result = shared.scheduler.wait_object_complete();
        assert!(result.is_ok());

        shared.scheduler.shutdown();
    });

    // After scope exits, worker threads have joined.
    assert!(shared.scheduler.is_shutdown());
}

#[test]
fn drop_without_shutdown_sets_shutdown_flag() {
    // Verify that dropping a CompileScheduler without calling
    // shutdown() still sets the shutdown flag (defensive Drop).
    let sched = CompileScheduler::new();
    let m = mod_path("test.mod");
    sched.register_module(m, no_sexps(), false);
    // Drop without calling shutdown() — the Drop impl should
    // call shutdown() automatically, preventing any parked
    // threads from hanging.
    drop(sched);
    // If we get here without hanging, the Drop impl works.
}

#[test]
fn drop_after_shutdown_is_idempotent() {
    // Verify that dropping after explicit shutdown() is harmless.
    let sched = CompileScheduler::new();
    sched.shutdown();
    assert!(sched.is_shutdown());
    drop(sched);
    // No panic, no double-shutdown issue.
}

#[test]
fn drop_wakes_parked_worker() {
    // Verify that dropping a scheduler wakes a thread parked on
    // take_object_codegen, preventing a hang.
    use std::sync::Arc;

    let sched = Arc::new(CompileScheduler::new());
    let sched_clone = Arc::clone(&sched);

    let handle = std::thread::spawn(move || {
        // This call parks on the object_work_available condvar
        // because no modules are in TypecheckDone.
        sched_clone.take_object_codegen()
    });

    // Drop our Arc reference. The spawned thread still holds one,
    // so the scheduler is not dropped yet. We need to call shutdown
    // explicitly to wake it.
    // (This test validates the pattern: explicit shutdown before
    // joining threads. The Drop impl is a safety net, not a
    // replacement for explicit shutdown when threads are alive.)
    sched.shutdown();
    let result = handle.join().expect("worker thread panicked");
    assert!(result.is_none()); // shutdown returns None
}

// ──────────────────────────────────────────────────────────────────────
// Sprint 58 Wave 2c: split the claim from inmem_done so
// wait_inmem_complete only sees inmem_done after the cache-hit worker
// actually finishes loading the .o.
// ──────────────────────────────────────────────────────────────────────

// spec: design/int/int.md §7.1 — claim guard does not
// pre-set `inmem_done`; only the claim's completion does.
#[test]
fn level4_claim_guard_sets_inmem_claimed_not_inmem_done() {
    let sched = CompileScheduler::new();
    let m = mod_path("cached.dep");
    // Cached module enters TypecheckDone with object_done=true,
    // inmem_done=false, unclaimed.
    drop(sched.register_module_cached(m.clone(), HashSet::new()));
    {
        let state = sched.lock();
        let ms = state.modules.get(&m).unwrap();
        assert!(!ms.inmem_done, "cached module starts with inmem_done=false");
        assert_eq!(
            ms.cached_load_state(),
            CachedLoadState::Claimable,
            "cached module starts unclaimed"
        );
        assert!(ms.object_done, "cached module starts with object_done=true");
    }

    // Take level-4 work — should claim, NOT mark done.
    let Some(PriorityWork::JitCodegen(claim)) = sched.take_priority_work() else {
        panic!("expected a cache-load work item");
    };
    {
        let state = sched.lock();
        let ms = state.modules.get(&m).unwrap();
        assert!(
            !ms.inmem_done,
            "claim guard MUST NOT pre-set inmem_done — that races against \
                 wait_inmem_complete (Sprint 58 Wave 2c regression guard)"
        );
        assert_eq!(
            ms.cached_load_state(),
            CachedLoadState::Claimed,
            "claim guard marks the load claimed so other workers skip this module"
        );
    }

    // Second take must skip this module (claimed).
    let second = sched.take_priority_work();
    assert!(
        second.is_none(),
        "second take_priority_work must skip the claimed module"
    );

    // Worker reports completion → inmem_done set, claim cleared.
    claim.complete_loaded(&[]);
    {
        let state = sched.lock();
        let ms = state.modules.get(&m).unwrap();
        assert!(ms.inmem_done, "completion sets inmem_done");
        assert_eq!(
            ms.cached_object_load,
            CachedObjectLoad::Released,
            "completion releases the claim atomically with setting done"
        );
    }
}

// spec: design/arch/concrete-boundary-type.md §2.5 (Cache-schemes-without-
//       codegen) — a generic-only cached module has NO
//       `.o` to load. It enters inmem_done=true and produces NO Level-4
//       JitCodegen work (nothing to mmap), so wait_inmem_complete passes
//       immediately without a worker ever touching a (non-existent) object.
#[test]
fn register_module_cached_no_object_enters_inmem_done_no_jitcodegen() {
    let sched = CompileScheduler::new();
    let m = mod_path("generic.only");
    sched.register_module_cached_no_object(m.clone(), HashSet::new());
    {
        let state = sched.lock();
        let ms = state.modules.get(&m).unwrap();
        assert!(
            ms.inmem_done,
            "generic-only cached module (no .o) enters inmem_done=true"
        );
        assert!(ms.object_done, "object_done=true (nothing to compile)");
    }
    // No Level-4 JitCodegen work item should be produced — there is no .o.
    let work = sched.take_priority_work();
    assert!(
        work.is_none(),
        "generic-only cached module must NOT produce JitCodegen work (no .o \
             to mmap); got {work:?}"
    );
    // wait_inmem_complete passes immediately.
    assert!(
        sched.wait_inmem_complete().is_ok(),
        "wait_inmem_complete must pass for an already-inmem-done module"
    );
}

// spec: design/int/int.md §7.1 — wait_inmem_complete
// distinguishes "claimed but not done" from "done"; cache-hit worker
// failure must surface as an error before trampoline runs.
#[test]
fn wait_inmem_complete_does_not_pass_on_claimed_but_unfinished_module() {
    let sched = CompileScheduler::new();
    let m = mod_path("cached.dep");
    drop(sched.register_module_cached(m.clone(), HashSet::new()));

    // Take work — claims the module.
    let _work = sched.take_priority_work();

    // wait_inmem_complete (non-blocking) must NOT report success because
    // inmem_done is still false. It returns InmemIncomplete.
    let result = sched.wait_inmem_complete();
    assert!(
        result.is_err(),
        "wait_inmem_complete must fail while module is claimed but not done — \
             pre-fix: claim-guard set inmem_done, hiding the unfinished work"
    );
}

// spec: design/int/int.md §7.1 — multiple cache-hit
// modules can be loaded in parallel without the claim guard letting
// wait_inmem_complete pass prematurely.
#[test]
fn level4_multiple_cached_modules_each_claim_independently() {
    let sched = CompileScheduler::new();
    let m1 = mod_path("dep.one");
    let m2 = mod_path("dep.two");
    drop(sched.register_module_cached(m1.clone(), HashSet::new()));
    drop(sched.register_module_cached(m2.clone(), HashSet::new()));

    // Two takes — each claims one module.
    let Some(PriorityWork::JitCodegen(c1)) = sched.take_priority_work() else {
        panic!("the first take must claim a cache load");
    };
    let Some(PriorityWork::JitCodegen(c2)) = sched.take_priority_work() else {
        panic!("the second take must claim a cache load");
    };
    let w3 = sched.take_priority_work();
    assert!(w3.is_none(), "third take must return None — both claimed");

    // Both modules must be claimed but not done.
    {
        let state = sched.lock();
        for path in [&m1, &m2] {
            let ms = state.modules.get(path).unwrap();
            assert_eq!(ms.cached_load_state(), CachedLoadState::Claimed);
            assert!(!ms.inmem_done);
        }
    }

    // Complete one. wait_inmem_complete must still fail (the other is
    // still claimed-but-not-done).
    c1.complete_loaded(&[]);
    assert!(
        sched.wait_inmem_complete().is_err(),
        "wait_inmem_complete must fail while ANY module is claimed-but-not-done"
    );

    // Complete the other. Now wait succeeds.
    c2.complete_loaded(&[]);
    assert!(
        sched.wait_inmem_complete().is_ok(),
        "wait_inmem_complete passes after every claim is resolved"
    );
}

// ──────────────────────────────────────────────────────────────────────
// S78 Step 3 (OQ-3): the `eval_in_flight` push-gate is deleted. The three
// `try_unblock_locked_*` flag-state unit tests (Sprint 61 H5 closure) that
// probed it retire with it — the in-call-stack model keeps each cluster's
// in-progress state on its owning stack frame, so `try_unblock_locked`
// unconditionally requeues the unblocked module and the worker re-runs from
// the top. The observable H5 parity is guarded by
// `tests/repl_persist_race.rs::h5_replay_gate_deterministic_under_scheduler_stress`
// (green under 50-iteration stress AFTER this deletion).
// ──────────────────────────────────────────────────────────────────────

// ══════════════════════════════════════════════════════════════════════
// Harvest from tests/legacy/scheduler.rs (FIXME 0116, S81 W-E /dev int).
//
// The legacy file's 18 `CompileScheduler` lifecycle assertions are ported
// here, adjacent to the code under test, against the CURRENT scheduler API
// (the legacy `register_module(module, bool)` / `PriorityWork::Typecheck(m)`
// / `wait_inmem_complete` surface drifted: register now takes the S78 sexps
// packet; `Typecheck` is a struct variant; `block_for_typecheck` returns
// `Result`). Three legacy tests (`block_for_macro_codegen_adds_priority_entry`,
// `priority_codegen_complete_unblocks`, `priority_queue_deduplicates_symbols`)
// are DROPPED — they probed the `block_for_macro_codegen` + `BlockingJitCodegen`
// priority-codegen subsystem that was DELETED (src/CLAUDE.md §"Macro expansion"
// / scheduler header — the locked macro model forbids same-module non-macro
// clause callees, so there is no empty-slot pre-compile case).
// ══════════════════════════════════════════════════════════════════════

fn dummy_error(msg: &str) -> CranelispError {
    CranelispError::ModuleError {
        message: msg.to_string(),
        location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
    }
}

// spec: design/arch/concurrent-pipeline.md §2 — register default pool
#[test]
fn harvest_register_module_starts_in_typecheck_next() {
    let sched = CompileScheduler::new();
    let m = mod_path("test_module");
    sched.register_module(m.clone(), no_sexps(), false);
    match sched.take_priority_work() {
        Some(PriorityWork::Typecheck { module, .. }) => assert_eq!(module, m),
        other => panic!("expected Typecheck(test_module), got {other:?}"),
    }
}

// spec: design/arch/concurrent-pipeline.md §2.1 — delays_other => TypecheckFirst
#[test]
fn harvest_register_module_with_delays_starts_in_typecheck_first() {
    let sched = CompileScheduler::new();
    let m = mod_path("dep_module");
    sched.register_module(m.clone(), no_sexps(), true);
    match sched.take_priority_work() {
        Some(PriorityWork::Typecheck { module, .. }) => assert_eq!(module, m),
        other => panic!("expected Typecheck(dep_module), got {other:?}"),
    }
}

// spec: design/arch/concurrent-pipeline.md §2.1 — first drained before next
#[test]
fn harvest_typecheck_first_before_typecheck_next() {
    let sched = CompileScheduler::new();
    let first = mod_path("first_mod");
    let next = mod_path("next_mod");
    sched.register_module(next.clone(), no_sexps(), false);
    sched.register_module(first.clone(), no_sexps(), true);
    match sched.take_priority_work() {
        Some(PriorityWork::Typecheck { module, .. }) => {
            assert_eq!(module, first, "TypecheckFirst drains before TypecheckNext")
        }
        other => panic!("expected Typecheck(first_mod), got {other:?}"),
    }
    match sched.take_priority_work() {
        Some(PriorityWork::Typecheck { module, .. }) => assert_eq!(module, next),
        other => panic!("expected Typecheck(next_mod), got {other:?}"),
    }
}

// spec: design/arch/concurrent-pipeline.md §8.1 — cached enters TypecheckDone
#[test]
fn harvest_register_module_cached_does_not_appear_as_typecheck_work() {
    let sched = CompileScheduler::new();
    let m = mod_path("cached_mod");
    let symbols = [Symbol::from("foo"), Symbol::from("bar")]
        .into_iter()
        .collect();
    drop(sched.register_module_cached(m.clone(), symbols));
    if let Some(PriorityWork::Typecheck { module, .. }) = sched.take_priority_work() {
        panic!("cached module must NOT appear as Typecheck work, got {module:?}");
    }
}

// spec: design/arch/concurrent-pipeline.md §2 — typecheck+inmem => complete
#[test]
fn harvest_notify_typecheck_done_then_inmem_completes() {
    let sched = CompileScheduler::new();
    let m = mod_path("mod_a");
    sched.register_module(m.clone(), no_sexps(), false);
    assert!(matches!(
        sched.take_priority_work(),
        Some(PriorityWork::Typecheck { .. })
    ));
    sched.notify_typecheck_done(&m);
    sched.notify_inmem_codegen_complete(&m, &Symbol::from("main"), true);
    assert!(sched.wait_inmem_complete().is_ok());
}

// spec: design/arch/concurrent-pipeline.md §6.2 — block_for_typecheck
#[test]
fn harvest_block_for_typecheck_blocks_module() {
    let sched = CompileScheduler::new();
    let a = mod_path("mod_a");
    let b = mod_path("mod_b");
    sched.register_module(a.clone(), no_sexps(), false);
    sched.register_module(b.clone(), no_sexps(), false);
    assert!(matches!(
        sched.take_priority_work(),
        Some(PriorityWork::Typecheck { .. })
    ));
    sched
        .block_for_typecheck(&a, &b, &Symbol::from("foo"), Span::SYNTHETIC)
        .unwrap();
    match sched.take_priority_work() {
        Some(PriorityWork::Typecheck { module, .. }) => {
            assert_eq!(module, b, "blocked module a is skipped; b is returned")
        }
        other => panic!("expected Typecheck(mod_b), got {other:?}"),
    }
}

// spec: design/arch/concurrent-pipeline.md §6.2 — `notify_typecheck_done`'s
// whole-module sweep unblocks a `"*"` waiter (the live readiness path after
// the S93 `notify_symbol_typechecked` retirement — every live waiter is `"*"`).
#[test]
fn harvest_notify_typecheck_done_unblocks_glob_waiter() {
    let sched = CompileScheduler::new();
    let a = mod_path("mod_a");
    let b = mod_path("mod_b");
    sched.register_module(a.clone(), no_sexps(), false);
    sched.register_module(b.clone(), no_sexps(), false);
    let _ = sched.take_priority_work();
    sched
        .block_for_typecheck(&a, &b, &Symbol::from("*"), Span::SYNTHETIC)
        .unwrap();
    let _ = sched.take_priority_work();
    sched.notify_typecheck_done(&b);
    match sched.take_priority_work() {
        Some(PriorityWork::Typecheck { module, .. }) => {
            assert_eq!(module, a, "a unblocks after b's whole-module typecheck")
        }
        other => panic!("expected Typecheck(mod_a) after unblock, got {other:?}"),
    }
}

// spec: design/int/signature-body-prepass.md §7 step 4 — S93 Invariant PP
// lost-wakeup guard for the per-import FQ-dependency discovery path.
//
// Drive `dep` to TypecheckDone (terminal) FIRST, THEN call
// `block_for_typecheck(module, dep, "*")`. This reproduces the two-lock
// window in `dependency.rs` (`register_module(dep)` enqueues + notifies; a
// priority worker pops `dep`, typechecks it, runs `notify_typecheck_done(dep)`
// — whose waiter-sweep finds no waiter for `module` yet — all BEFORE
// `block_for_typecheck` runs). The pre-fix code unconditionally registered
// `module` as a waiter on the now-terminal `dep`; since no future
// `notify_typecheck_done(dep)` would ever fire, `module` was stranded in
// `TypecheckBlocked` forever (the intermittent 30 s hang). The fix's atomic
// check-and-act requeues `module` instead. Assert `module` is NOT left in
// `TypecheckBlocked` — it is requeued (TypecheckFirst/Next), ready to be
// re-driven. RED on the pre-fix code (module stranded `TypecheckBlocked`),
// GREEN with the fix.
#[test]
fn block_for_typecheck_on_already_terminal_dep_requeues_not_strands() {
    let sched = CompileScheduler::new();
    let module = mod_path("importer");
    let dep = mod_path("dependency");
    sched.register_module(module.clone(), no_sexps(), false);
    sched.register_module(dep.clone(), no_sexps(), false);

    // Model the worker flow: both modules are claimed off the queue
    // (TypecheckWorking), so neither is a stale deque entry. `module` is the
    // one a worker is mid-pass on when it discovers + drives `dep`.
    let _ = sched.take_priority_work();
    let _ = sched.take_priority_work();

    // Drive `dep` to TypecheckDone FIRST — its waiter-sweep runs now, before
    // `module` ever registers as a waiter. This is the two-lock window in
    // `dependency.rs`: between `register_module(dep)` (which enqueues + wakes a
    // priority worker that can pop, typecheck, and `notify_typecheck_done`
    // `dep`) and `block_for_typecheck`, `dep` has already gone terminal.
    sched.notify_typecheck_done(&dep);

    // Now the discovery path records the edge — on an already-terminal dep.
    sched
        .block_for_typecheck(&module, &dep, &Symbol::from("*"), Span::SYNTHETIC)
        .unwrap();

    // `module` MUST NOT be stranded in TypecheckBlocked: with `dep` already
    // terminal, no future `notify_typecheck_done(dep)` will ever fire to
    // release it, so the only correct outcome is an immediate requeue.
    // (Pre-fix: `block_for_typecheck` unconditionally registered the dead
    // waiter and left `module` in TypecheckBlocked → permanent hang → RED.)
    {
        let state = sched.lock();
        let pool = state.modules.get(&module).unwrap().pool;
        assert_ne!(
            pool,
            ModulePool::TypecheckBlocked,
            "module stranded in TypecheckBlocked on an already-terminal dep \
                 (lost-wakeup regression — S93 Invariant PP)"
        );
        assert!(
            matches!(pool, ModulePool::TypecheckFirst | ModulePool::TypecheckNext),
            "module must be requeued for typecheck, got {pool:?}"
        );
    }

    // And it is re-drivable: the requeued module surfaces as priority work.
    match sched.take_priority_work() {
        Some(PriorityWork::Typecheck { module: m, .. }) => {
            assert_eq!(m, module, "requeued module is available as typecheck work")
        }
        other => panic!("expected requeued Typecheck(importer), got {other:?}"),
    }
}

// spec: design/arch/concurrent-pipeline.md §2.3 — failure cascades to waiters
#[test]
fn harvest_module_failed_cascades_to_waiters() {
    let sched = CompileScheduler::new();
    let a = mod_path("mod_a");
    let b = mod_path("mod_b");
    sched.register_module(a.clone(), no_sexps(), false);
    sched.register_module(b.clone(), no_sexps(), false);
    let _ = sched.take_priority_work();
    sched
        .block_for_typecheck(&a, &b, &Symbol::from("bar"), Span::SYNTHETIC)
        .unwrap();
    let _ = sched.take_priority_work();
    sched.notify_module_failed(&b, dummy_error("type error in mod_b"));
    assert!(
        sched.wait_inmem_complete().is_err(),
        "cascade failure surfaces as Err"
    );
}

// spec: design/arch/concurrent-pipeline.md §6.5 — wait returns Err on failure
#[test]
fn harvest_wait_inmem_complete_returns_err_on_failure() {
    let sched = CompileScheduler::new();
    let m = mod_path("failing_mod");
    sched.register_module(m.clone(), no_sexps(), false);
    let _ = sched.take_priority_work();
    sched.notify_module_failed(&m, dummy_error("parse error"));
    assert!(sched.wait_inmem_complete().is_err());
}

// spec: design/arch/concurrent-pipeline.md §2.2 — inmem codegen completes module
#[test]
fn harvest_inmem_codegen_complete_moves_to_complete() {
    let sched = CompileScheduler::new();
    let m = mod_path("mod_x");
    sched.register_module(m.clone(), no_sexps(), false);
    let _ = sched.take_priority_work();
    sched.notify_typecheck_done(&m);
    sched.notify_inmem_codegen_complete(&m, &Symbol::from("main"), true);
    assert!(sched.wait_inmem_complete().is_ok());
}

// spec: design/arch/concurrent-pipeline.md §6.5 — full lifecycle, two modules
#[test]
fn harvest_wait_inmem_complete_ok_when_all_complete() {
    let sched = CompileScheduler::new();
    let a = mod_path("mod_a");
    let b = mod_path("mod_b");
    sched.register_module(a.clone(), no_sexps(), false);
    sched.register_module(b.clone(), no_sexps(), false);
    let _ = sched.take_priority_work();
    sched.notify_typecheck_done(&a);
    let _ = sched.take_priority_work();
    sched.notify_typecheck_done(&b);
    sched.notify_inmem_codegen_complete(&a, &Symbol::from("fn_a"), true);
    sched.notify_inmem_codegen_complete(&b, &Symbol::from("fn_b"), true);
    assert!(sched.wait_inmem_complete().is_ok());
}

// spec: design/arch/concurrent-pipeline.md §10.3 — empty scheduler returns None
#[test]
fn harvest_take_priority_work_returns_none_when_empty() {
    let sched = CompileScheduler::new();
    assert!(sched.take_priority_work().is_none());
}

// spec: design/arch/concurrent-pipeline.md §6.5 — shutdown gates work
#[test]
fn harvest_shutdown_gates_priority_work() {
    let sched = CompileScheduler::new();
    let m = mod_path("mod_s");
    sched.register_module(m.clone(), no_sexps(), false);
    sched.shutdown();
    assert!(sched.take_priority_work().is_none());
}

// spec: design/arch/concurrent-pipeline.md §6.5 — vacuously complete
#[test]
fn harvest_wait_inmem_complete_ok_when_no_modules() {
    let sched = CompileScheduler::new();
    assert!(sched.wait_inmem_complete().is_ok());
}

// spec: design/arch/concurrent-pipeline.md §2.1 — TypecheckFirst FIFO
#[test]
fn harvest_typecheck_first_fifo_ordering() {
    let sched = CompileScheduler::new();
    let a = mod_path("first_a");
    let b = mod_path("first_b");
    sched.register_module(a.clone(), no_sexps(), true);
    sched.register_module(b.clone(), no_sexps(), true);
    match sched.take_priority_work() {
        Some(PriorityWork::Typecheck { module, .. }) => assert_eq!(module, a, "FIFO first"),
        other => panic!("expected Typecheck(first_a), got {other:?}"),
    }
    match sched.take_priority_work() {
        Some(PriorityWork::Typecheck { module, .. }) => assert_eq!(module, b, "FIFO second"),
        other => panic!("expected Typecheck(first_b), got {other:?}"),
    }
}

// ══════════════════════════════════════════════════════════════════════
// S93 signature/body pre-pass — Step 1: static dependency closure +
// cycle error (`design/int/signature-body-prepass.md` §7 step 1).
// ══════════════════════════════════════════════════════════════════════

/// Build an adjacency entry `(m, [deps…])`.
fn edge(m: &str, deps: &[&str]) -> (ModuleFullPath, Vec<ModuleFullPath>) {
    (mod_path(m), deps.iter().map(|d| mod_path(d)).collect())
}

// spec: design/int/signature-body-prepass.md §3.1 / §7 step 1 — an acyclic
// import graph yields a topological order with imports BEFORE importers
// (leaves first, root last).
#[test]
fn dependency_closure_acyclic_orders_leaves_first() {
    // root imports mid; mid imports leaf. Order must be leaf, mid, root.
    let decls = vec![
        edge("root", &["mid"]),
        edge("mid", &["leaf"]),
        edge("leaf", &[]),
    ];
    let closure = dependency_closure(&mod_path("root"), &decls)
        .expect("acyclic graph has a topological order");
    let order = &closure.order;
    let pos = |n: &str| order.iter().position(|m| m.as_ref() == n).unwrap();
    assert!(pos("leaf") < pos("mid"), "leaf before mid: {order:?}");
    assert!(pos("mid") < pos("root"), "mid before root: {order:?}");
    assert_eq!(order.last().unwrap(), &mod_path("root"), "root is last");
    assert_eq!(order.len(), 3, "all three modules in closure: {order:?}");
}

// spec: §3.1 — a diamond (root → {a, b} → leaf) is acyclic; `leaf` precedes
// both `a` and `b`, which precede `root`, and `leaf` appears once.
#[test]
fn dependency_closure_diamond_is_acyclic_single_leaf() {
    let decls = vec![
        edge("root", &["a", "b"]),
        edge("a", &["leaf"]),
        edge("b", &["leaf"]),
        edge("leaf", &[]),
    ];
    let closure = dependency_closure(&mod_path("root"), &decls).expect("diamond is acyclic");
    let order = &closure.order;
    let pos = |n: &str| order.iter().position(|m| m.as_ref() == n).unwrap();
    assert!(pos("leaf") < pos("a"));
    assert!(pos("leaf") < pos("b"));
    assert!(pos("a") < pos("root"));
    assert!(pos("b") < pos("root"));
    assert_eq!(
        order.iter().filter(|m| m.as_ref() == "leaf").count(),
        1,
        "shared leaf emitted exactly once: {order:?}"
    );
}

// spec: design/int/signature-body-prepass.md §4 — a 2-cycle (a imports b,
// b imports a) has NO topological order; `dependency_closure` returns
// `CycleError`. This is the D0030 mutual-import disposition (cycle-error,
// not compiled). Underlies tests/spec_08_modules::
// mutual_import_pair_diagnoses_cycle_not_hang.
#[test]
fn dependency_closure_two_cycle_is_cycle_error() {
    let decls = vec![edge("a", &["b"]), edge("b", &["a"])];
    let err = dependency_closure(&mod_path("a"), &decls).expect_err("mutual import is a cycle");
    assert!(
        err.cycle.contains(&mod_path("a")) && err.cycle.contains(&mod_path("b")),
        "cycle names both modules: {:?}",
        err.cycle
    );
    // render() produces an `a -> … -> a` diagnostic string.
    let rendered = err.render();
    assert!(
        rendered.contains("->"),
        "rendered cycle has edges: {rendered}"
    );
}

// spec: §4 — a longer cycle (a → b → c → a) is detected too.
#[test]
fn dependency_closure_three_cycle_is_cycle_error() {
    let decls = vec![edge("a", &["b"]), edge("b", &["c"]), edge("c", &["a"])];
    let err = dependency_closure(&mod_path("a"), &decls).expect_err("3-cycle is a cycle");
    for m in ["a", "b", "c"] {
        assert!(
            err.cycle.contains(&mod_path(m)),
            "cycle names {m}: {:?}",
            err.cycle
        );
    }
}

// spec: §3.1 — modules reachable but absent from the decls (already-loaded
// or compiler-seeded leaves) are treated as edge-free leaves, never a cycle.
#[test]
fn dependency_closure_unlisted_dep_is_leaf() {
    // root imports `seeded`, which is not in the decls list at all.
    let decls = vec![edge("root", &["seeded"])];
    let closure =
        dependency_closure(&mod_path("root"), &decls).expect("unlisted dep is a leaf, not a cycle");
    let order = &closure.order;
    let pos = |n: &str| order.iter().position(|m| m.as_ref() == n).unwrap();
    assert!(
        pos("seeded") < pos("root"),
        "seeded leaf before root: {order:?}"
    );
}

// ══════════════════════════════════════════════════════════════════════
// S93 signature/body pre-pass — Step 2: Phase-A signature publication +
// barrier (`signature-body-prepass.md` §7 step 2). The terminal pool
// transition (`notify_typecheck_done`) IS the publication edge — there is no
// separate `signatures_ready` bit (FIXME 0452 / /arch option i). The barrier
// (`await_signature_barrier`) reads pool-terminal state directly.
// ══════════════════════════════════════════════════════════════════════

fn closure_of(mods: &[&str]) -> ClosureOrder {
    ClosureOrder {
        order: mods.iter().map(|m| mod_path(m)).collect(),
    }
}

// spec: §3.1 — `notify_typecheck_done` publishes the module's signatures
// (the terminal pool transition IS the publication edge): a pool worker's
// atomic barrier probe blocks on the member while it is in-flight, and the
// barrier opens once it is terminal.
#[test]
fn notify_typecheck_done_publishes_signatures() {
    let sched = CompileScheduler::new();
    let helper = mod_path("helper");
    let reader = mod_path("reader");
    sched.register_module(helper.clone(), no_sexps(), false);
    sched.register_module(reader.clone(), no_sexps(), false);
    sched.force_typecheck_working_for_test(&helper);
    let closure = closure_of(&["helper"]);

    // In-flight (TypecheckWorking, not terminal) → unpublished. The pool
    // worker's atomic probe blocks `reader` on `helper`.
    assert_eq!(
        sched
            .block_on_first_unready_closure_member(&reader, &closure)
            .unwrap(),
        Some(helper.clone()),
        "before notify_typecheck_done, helper is unpublished"
    );

    // The terminal pool transition publishes helper's signatures, so a fresh
    // barrier probe opens.
    sched.notify_typecheck_done(&helper);
    assert!(
        sched.await_signature_barrier(&closure).is_ok(),
        "after notify_typecheck_done, the barrier opens (signatures published)"
    );
}

// spec: §3.1 — the barrier opens immediately when every closure module is
// already ready; a compiler-seeded (unregistered) module is implicitly ready.
#[test]
fn await_signature_barrier_opens_when_all_ready() {
    let sched = CompileScheduler::new();
    let helper = mod_path("helper");
    sched.register_module(helper.clone(), no_sexps(), false);
    sched.notify_typecheck_done(&helper);
    // `seeded` is never registered → implicitly ready.
    let closure = closure_of(&["helper", "seeded"]);
    assert!(sched.await_signature_barrier(&closure).is_ok());
}

// spec: §3.1 — the barrier BLOCKS until the LAST closure module's signatures
// publish, then opens. Models N=2 closure with a background publisher.
#[test]
fn await_signature_barrier_blocks_until_last_registration() {
    use std::sync::Arc;
    let sched = Arc::new(CompileScheduler::new());
    let a = mod_path("dep_a");
    let b = mod_path("dep_b");
    sched.register_module(a.clone(), no_sexps(), false);
    sched.register_module(b.clone(), no_sexps(), false);
    sched.force_typecheck_working_for_test(&a);
    sched.force_typecheck_working_for_test(&b);

    let closure = closure_of(&["dep_a", "dep_b"]);
    let opened = Arc::new(AtomicBool::new(false));

    std::thread::scope(|scope| {
        let sched_w = Arc::clone(&sched);
        let opened_w = Arc::clone(&opened);
        let closure_w = closure.clone();
        scope.spawn(move || {
            sched_w.await_signature_barrier(&closure_w).unwrap();
            opened_w.store(true, std::sync::atomic::Ordering::SeqCst);
        });

        // Publish only `a`; the barrier must NOT open (b still pending).
        sched.notify_typecheck_done(&a);
        std::thread::sleep(std::time::Duration::from_millis(30));
        assert!(
            !opened.load(std::sync::atomic::Ordering::SeqCst),
            "barrier must stay closed while dep_b is unpublished"
        );

        // Publish `b` — the LAST module. The barrier now opens.
        sched.notify_typecheck_done(&b);
        // Give the waiter a moment to wake and store.
        for _ in 0..200 {
            if opened.load(std::sync::atomic::Ordering::SeqCst) {
                break;
            }
            std::thread::sleep(std::time::Duration::from_millis(5));
        }
        assert!(
            opened.load(std::sync::atomic::Ordering::SeqCst),
            "barrier must open after the last module's signatures register"
        );
    });
}

// spec: §3.1 — `await_signature_barrier` fails fast if a closure module
// failed, rather than parking forever on a dep that will never become ready.
#[test]
fn await_signature_barrier_errors_on_failed_closure_module() {
    let sched = CompileScheduler::new();
    let m = mod_path("dep_bad");
    sched.register_module(m.clone(), no_sexps(), false);
    sched.notify_module_failed(&m, dummy_error("boom"));
    let closure = closure_of(&["dep_bad"]);
    assert!(
        sched.await_signature_barrier(&closure).is_err(),
        "barrier must surface a failed closure module as Err"
    );
}

// spec: §8.5.4 — I1 (0571.2). `reset_all_failed_modules` RETURNS the list of
// reset modules so the session (which owns `symbol_tables`) can purge their
// stale live tables; each returned module is also removed from the scheduler.
#[test]
fn reset_all_failed_modules_returns_reset_list_and_unregisters() {
    let sched = CompileScheduler::new();
    let good = mod_path("ok");
    let bad = mod_path("bad");
    sched.register_module(good.clone(), no_sexps(), false);
    sched.register_module(bad.clone(), no_sexps(), false);
    sched.notify_module_failed(&bad, dummy_error("boom"));

    let reset = sched.reset_all_failed_modules();
    assert_eq!(
        reset,
        vec![ResetModule {
            module: bad.clone(),
            failure_dependencies: BTreeSet::new(),
        }],
        "only the Failed module is reset"
    );
    assert!(
        !sched.is_registered(&bad),
        "the reset module is unregistered"
    );
    assert!(
        sched.is_registered(&good),
        "a non-failed module is untouched"
    );
}

// spec: §8.5.4 — 0571.3 (a). A module that REACHED terminal typecheck and is
// LATER marked Failed (a cascade victim awaiting a broken dep) keeps its
// was-terminal history across `reset_all_failed_modules` — the history is
// MONOTONE. `reset_failed_modules` reads this to SPARE its live table (a
// was-good module's valid definitions are not destroyed).
#[test]
fn was_ever_terminal_survives_terminal_then_failed_then_reset() {
    let sched = CompileScheduler::new();
    let victim = mod_path("was_good");
    sched.register_module(victim.clone(), no_sexps(), false);
    sched.notify_typecheck_done(&victim);
    assert!(
        sched.was_ever_terminal(&victim),
        "a module reaching TypecheckDone is ever-terminal"
    );
    // Cascade failure marks it Failed; the autoload reset removes it.
    sched.notify_module_failed(&victim, dummy_error("cascade: awaited broken dep"));
    let reset = sched.reset_all_failed_modules();
    assert_eq!(
        reset,
        vec![ResetModule {
            module: victim.clone(),
            failure_dependencies: BTreeSet::new(),
        }]
    );
    assert!(
        !sched.is_registered(&victim),
        "reset dropped the live state"
    );
    assert!(
        sched.was_ever_terminal(&victim),
        "the was-terminal history is monotone — it survives reset so the purge \
             SPARES the cascade victim's table (0571.3 a)"
    );
}

// spec: §8.5.4 — 0571.3 (b). A dep that FAILS before ever reaching terminal
// typecheck is NOT ever-terminal — so `fq_module_is_loaded`'s untracked arm
// reads it not-loaded (the retry re-drives it, no false "no member"), and
// `reset_failed_modules` purges its import-seeded stale table.
#[test]
fn was_ever_terminal_false_for_never_completed_failed_dep() {
    let sched = CompileScheduler::new();
    let broken = mod_path("broken");
    sched.register_module(broken.clone(), no_sexps(), false);
    sched.notify_module_failed(&broken, dummy_error("undefined variable: nope"));
    let _ = sched.reset_all_failed_modules();
    assert!(
        !sched.was_ever_terminal(&broken),
        "a dep that never completed must NOT read ever-terminal (0571.3 b)"
    );
}

// ══════════════════════════════════════════════════════════════════════
// S93 §6 — THE DETERMINISTIC P_publish / P_read INTERLEAVING PIN.
//
// Models `helper ← user`. A test cell `published` stands for
// `symbol_tables[helper]` containing `helper-val`. Two orchestrators:
//   - t2 (publisher/worker): populates the cell, THEN registers signatures.
//   - t1 (reader/eval body): `await_signature_barrier`, THEN reads the cell.
//
// POST-FIX (this test, GREEN in EVERY schedule): under the barrier, the
// reader's P_read point is Phase B — unreachable until
// `await_signature_barrier` opens, which the publisher opens ONLY after the
// publication. So the read finds `helper-val` published in every interleaving.
//
// The publication release edge is `notify_typecheck_done` (the terminal pool
// transition), which runs post-`finalize_cluster` — AFTER the table is
// populated. There is no separate `signatures_ready` bit (FIXME 0452): the
// barrier reads pool-terminal state directly, and the ordering invariant that
// makes that safe is exactly the one this test pins.
// ══════════════════════════════════════════════════════════════════════

// spec: design/int/signature-body-prepass.md §6 tier 1 — the barrier closes
// the publish/read window: when `await_signature_barrier` returns, the
// dependency's publication is, by construction, already visible.
#[test]
fn signature_barrier_closes_publish_read_window() {
    use std::sync::Arc;
    use std::sync::atomic::Ordering;

    let sched = Arc::new(CompileScheduler::new());
    let helper = mod_path("helper");
    sched.register_module(helper.clone(), no_sexps(), false);
    sched.force_typecheck_working_for_test(&helper);

    // The publication cell: `false` = `helper-val` NOT yet in
    // `symbol_tables[helper]`; `true` = published.
    let published = Arc::new(AtomicBool::new(false));
    // Sync so the reader is parked on the barrier BEFORE the publisher runs,
    // exercising the real wait path (P_publish opens after the reader parks).
    let reader_armed = Arc::new(std::sync::Barrier::new(2));
    let closure = closure_of(&["helper"]);

    std::thread::scope(|scope| {
        // --- t2: publisher / worker ---
        let sched_p = Arc::clone(&sched);
        let published_p = Arc::clone(&published);
        let armed_p = Arc::clone(&reader_armed);
        let helper_p = helper.clone();
        scope.spawn(move || {
            armed_p.wait(); // wait until the reader has armed (P_publish)
            // Publish helper-val FIRST (populate symbol_tables[helper])…
            published_p.store(true, Ordering::SeqCst);
            // …THEN drive the terminal pool transition. `notify_typecheck_done`
            // (post-finalize_cluster) is the publication release edge.
            sched_p.notify_typecheck_done(&helper_p);
        });

        // --- t1: reader / dependent body ---
        reader_armed.wait(); // arm: signal the publisher it may proceed
        // Phase-B read is gated by the barrier:
        sched.await_signature_barrier(&closure).unwrap();
        // P_read: by construction the publication happened-before the bit
        // flip, which happened-before this barrier return.
        assert!(
            published.load(Ordering::SeqCst),
            "P_read: under the barrier, helper-val MUST be published when the \
                 barrier opens — every schedule. A miss here is the H6/H7 race."
        );
    });
}

// (RETIRED, FIXME 0452 / /arch option i) `pre_fix_pool_gate_exposes_publish_
// _read_window` is gone. It demonstrated a window in which the terminal pool
// flips Done BEFORE the table is populated — but /arch ruled the terminal pool
// transition IS the publication edge (`notify_typecheck_done` runs
// post-`finalize_cluster`, so `pool → TypecheckDone` happens-after
// publication). The barrier now reads pool-terminal state directly; there is
// no separate `signatures_ready` bit and no "pool-gating is unsafe" premise to
// demonstrate. The artificial interleaving it forced (notify BEFORE store)
// cannot occur in the real pipeline, so the test contradicted the post-ruling
// model and was retired. The POSITIVE pin `signature_barrier_closes_publish_
// _read_window` above stays GREEN and now drives publication via
// `notify_typecheck_done`.

// ══════════════════════════════════════════════════════════════════════
// S93 signature/body pre-pass — Step 3: single-writer exclusive claim
// (`signature-body-prepass.md` §7 step 3 / Invariant SW). A module is
// *claimable* (in a typecheck queue) XOR *owned* (popped → TypecheckWorking).
// The pop is exclusive by construction — under the state lock, exactly one
// caller removes the module from the deque.
// ══════════════════════════════════════════════════════════════════════

// spec: §2 Invariant SW — two claimers race one queued module; exactly one
// obtains the Phase-A drive (the `Typecheck` work item), the other gets
// nothing. There is no second path to suppress, so no flag is needed.
#[test]
fn exclusive_claim_one_winner_for_one_module() {
    use std::sync::Arc;

    let sched = Arc::new(CompileScheduler::new());
    let m = mod_path("contended");
    sched.register_module(m.clone(), no_sexps(), false);

    // Two threads both try to claim. Exactly one gets the work item.
    let results = std::thread::scope(|scope| {
        let s1 = Arc::clone(&sched);
        let s2 = Arc::clone(&sched);
        let h1 = scope.spawn(move || s1.take_priority_work().is_some());
        let h2 = scope.spawn(move || s2.take_priority_work().is_some());
        (h1.join().unwrap(), h2.join().unwrap())
    });

    assert!(
        results.0 ^ results.1,
        "exactly one claimer obtains the module's Phase-A drive (XOR), \
             got ({}, {})",
        results.0,
        results.1
    );
    // The module is now owned (TypecheckWorking) — not in any queue.
    assert_eq!(
        sched.module_pool(&m),
        Some(ModulePool::TypecheckWorking),
        "claimed module is owned (TypecheckWorking), no longer claimable"
    );
}

// spec: §2 Invariant SW — an owned (TypecheckWorking) module is never
// re-pushed onto a queue by the unblock path. `try_unblock_locked`
// early-returns for any non-Blocked module, so a second worker cannot claim
// a module another orchestrator already owns.
#[test]
fn owned_module_is_not_repushed_by_unblock() {
    let sched = CompileScheduler::new();
    let m = mod_path("owned");
    sched.register_module(m.clone(), no_sexps(), false);
    let _ = sched.take_priority_work(); // → TypecheckWorking (owned)
    assert_eq!(sched.module_pool(&m), Some(ModulePool::TypecheckWorking));

    // An unblock attempt on an owned (not-Blocked) module is a no-op — it is
    // not re-pushed, so a second `take_priority_work` finds nothing.
    sched.unblock_module(&m);
    assert_eq!(
        sched.module_pool(&m),
        Some(ModulePool::TypecheckWorking),
        "owned module stays owned — never re-pushed"
    );
    assert!(
        sched.take_priority_work().is_none(),
        "no second claim is possible for an owned module"
    );
}

// ══════════════════════════════════════════════════════════════════════
// S93 signature/body pre-pass — Step 5: retire `eval_owned` via the
// exclusive-claim rule (`signature-body-prepass.md` §7 step 5 / Invariant
// SW; BC §6 ruling B). The eval thread (REPL) is the SOLE orchestrator of
// its entry module BY CONSTRUCTION: on a dependency gap it records a
// cycle-check edge via `register_dep_edge_for_cycle_check` but NEVER moves
// the entry to `TypecheckBlocked`, so the entry never re-enters a typecheck
// queue and no pool worker can re-claim it. These re-express S61's
// `try_unblock_locked_suppressed_*` flag tests structurally (no flag).
// ══════════════════════════════════════════════════════════════════════

// spec: §2 Invariant SW — the eval thread records a `entry → dep`
// dependency edge WITHOUT blocking the entry; a pool worker therefore
// cannot re-claim the entry while the eval thread drives. This is the
// structural successor to the `eval_owned` early-return (the B1 guard).
#[test]
fn eval_entry_dep_edge_keeps_entry_unclaimable_by_pool() {
    let sched = CompileScheduler::new();
    let entry = mod_path("user");
    sched.register_module(entry.clone(), no_sexps(), false);
    // Drive the entry to its terminal pool (startup typecheck done).
    let _ = sched.take_priority_work(); // → TypecheckWorking
    sched.notify_typecheck_done(&entry); // → TypecheckDone
    assert_eq!(sched.module_pool(&entry), Some(ModulePool::TypecheckDone));

    // The eval thread hits a dependency gap and records the cycle-check
    // edge. The entry MUST stay in its terminal pool — NOT TypecheckBlocked.
    let dep = mod_path("helper");
    sched
        .register_dep_edge_for_cycle_check(&entry, &dep, Span::SYNTHETIC)
        .expect("no cycle: helper does not import user");
    assert_eq!(
        sched.module_pool(&entry),
        Some(ModulePool::TypecheckDone),
        "eval-driven dep edge must NOT move the entry to TypecheckBlocked"
    );

    // No pool worker can re-claim the entry for typecheck: it is not in any
    // typecheck queue, and it is not a cache-hit module needing inmem load.
    assert!(
        sched.take_priority_work().is_none(),
        "entry is unclaimable while the eval thread drives — no pool worker \
             can re-typecheck it (the B1 dual-orchestration is closed)"
    );

    // The eval thread clears the edge after its wait — no stale forward edge
    // lingers on the terminal entry.
    sched.clear_dep_edge(&entry);
    assert_eq!(sched.module_pool(&entry), Some(ModulePool::TypecheckDone));
}

// spec: §2 Invariant SW — the cycle-check edge the eval thread records is
// visible to the REVERSE-direction check: if the dependency, while
// compiling on the pool, imports the entry back, `block_for_typecheck`
// detects the cycle against the eval edge and rejects it (so the eval
// thread's wait surfaces a clean circular-dependency error instead of
// hanging). Cycle detection is preserved without blocking the entry.
#[test]
fn eval_entry_dep_edge_is_seen_by_reverse_cycle_check() {
    let sched = CompileScheduler::new();
    let entry = mod_path("user");
    let dep = mod_path("helper");
    sched.register_module(entry.clone(), no_sexps(), false);
    sched.register_module(dep.clone(), no_sexps(), false);

    // Eval thread: entry → helper (no cycle yet — helper imports nothing).
    sched
        .register_dep_edge_for_cycle_check(&entry, &dep, Span::SYNTHETIC)
        .expect("entry → helper alone is acyclic");

    // Pool worker compiling helper hits `(import [user])` → helper → user.
    // The reverse check follows user.blocked_on = helper → CYCLE.
    let err = sched.block_for_typecheck(&dep, &entry, &Symbol::from("*"), Span::SYNTHETIC);
    assert!(
        err.is_err(),
        "the eval edge entry → helper must make helper → entry a detected \
             cycle (preserving REPL cycle diagnosis without blocking the entry)"
    );
}

// spec: §2 Invariant SW — a DIRECT cycle the eval thread itself closes is
// rejected as `Err`, but the entry module is NOT failed (a bad REPL import
// is an eval error, not a session-killer — the entry keeps its pool).
#[test]
fn eval_entry_dep_edge_direct_cycle_errs_without_failing_entry() {
    let sched = CompileScheduler::new();
    let entry = mod_path("user");
    let dep = mod_path("helper");
    sched.register_module(entry.clone(), no_sexps(), false);
    sched.register_module(dep.clone(), no_sexps(), false);
    let entry_pool_before = sched.module_pool(&entry);

    // helper already blocked on user (its worker recorded the edge).
    sched
        .block_for_typecheck(&dep, &entry, &Symbol::from("*"), Span::SYNTHETIC)
        .expect("helper → user alone is acyclic");

    // Eval thread now records user → helper, closing the cycle.
    let err = sched.register_dep_edge_for_cycle_check(&entry, &dep, Span::SYNTHETIC);
    assert!(err.is_err(), "user → helper → user is a detected cycle");
    // The entry was NOT failed — it keeps its pre-edge pool (not Failed).
    assert_eq!(
        sched.module_pool(&entry),
        entry_pool_before,
        "a REPL import cycle is an eval error — the entry module is not failed"
    );
    assert!(!sched.is_failed(&entry), "entry must not be in Failed");
}

// spec: §8.5.4 — I3 fail-fast (0571.2). Blocking on a dependency that has
// ALREADY FAILED must return `Err` IMMEDIATELY rather than register a waiter
// that no future `notify_typecheck_done` will ever sweep (a Failed module
// never reaches a terminal typecheck pool → the blocker would park forever).
#[test]
fn block_for_typecheck_fails_fast_when_dep_already_failed() {
    let sched = CompileScheduler::new();
    let a = mod_path("consumer");
    let b = mod_path("broken_dep");
    sched.register_module(a.clone(), no_sexps(), false);
    sched.register_module(b.clone(), no_sexps(), false);
    let _ = sched.take_priority_work();
    // b fails to typecheck.
    sched.notify_module_failed(&b, dummy_error("undefined variable: nonexistent"));

    let err = sched.block_for_typecheck(&a, &b, &Symbol::from("*"), Span::SYNTHETIC);
    assert!(
        err.is_err(),
        "blocking on an already-Failed dep must fail fast"
    );
    // The dep's own error is surfaced (not a park), and `a` is NOT parked in
    // TypecheckBlocked waiting on a dead dependency.
    assert!(
        err.unwrap_err().to_string().contains("nonexistent"),
        "the failed dependency's recorded error must be surfaced verbatim"
    );
    assert_ne!(
        sched.module_pool(&a),
        Some(ModulePool::TypecheckBlocked),
        "the consumer must not be parked on a dead dependency"
    );
}

// spec: §8.5.4 / AL-3 parity — M2 (0571.2). The circular-dependency error
// must be attributed to the REFERENCE site (the span the caller threads),
// not `Span::SYNTHETIC`, so the diagnostic points at the offending ref.
#[test]
fn cycle_error_carries_reference_span_not_synthetic() {
    let sched = CompileScheduler::new();
    let entry = mod_path("user");
    let dep = mod_path("helper");
    sched.register_module(entry.clone(), no_sexps(), false);
    sched.register_module(dep.clone(), no_sexps(), false);
    let ref_span = Span::new(42, 55);

    // helper → user recorded first (acyclic alone).
    sched
        .block_for_typecheck(&dep, &entry, &Symbol::from("*"), Span::SYNTHETIC)
        .expect("helper → user alone is acyclic");
    // Eval thread closes user → helper → user with a real reference span.
    let err = sched
        .register_dep_edge_for_cycle_check(&entry, &dep, ref_span)
        .expect_err("user → helper → user is a detected cycle");
    assert_eq!(
        err.span(),
        ref_span,
        "the circular-dependency error must carry the reference span, not SYNTHETIC"
    );
}

// ══════════════════════════════════════════════════════════════════════
// S93 signature/body pre-pass — Step 4: the ATOMIC requeue-gate
// (`signature-body-prepass.md` §7 step 4 / Invariant PP; BC §6 ruling B).
// The body is admitted only when EVERY closure member is published (terminal
// pool); a pool worker check-and-blocks NON-BLOCKING and ATOMICALLY
// (`block_on_first_unready_closure_member`) on the first unready member —
// scan + waiter registration under ONE lock, no lost-wakeup gap (the Blocker
// fix) — and frees back to the pool; it never parks.
// ══════════════════════════════════════════════════════════════════════

// spec: §3.1 — the atomic barrier gate blocks the body on the FIRST unready
// closure member (topological order), the scheduler requeues it when that
// member completes, and the gate opens (`Ok(None)`) once every member is
// published — so a worker never parks a pool thread on a signature dependency.
#[test]
fn atomic_barrier_gate_blocks_then_opens_member_by_member() {
    let sched = CompileScheduler::new();
    let helper = mod_path("helper");
    let util = mod_path("util");
    let user = mod_path("user");
    sched.register_module(helper.clone(), no_sexps(), false);
    sched.register_module(util.clone(), no_sexps(), false);
    sched.register_module(user.clone(), no_sexps(), false);
    // Closure ordered leaves-first; the gate covers helper + util (user is
    // the root, excluded by the caller, so it is not listed here).
    let closure = closure_of(&["helper", "util"]);

    // Nothing published → user is blocked on the first member (helper).
    assert_eq!(
        sched
            .block_on_first_unready_closure_member(&user, &closure)
            .unwrap(),
        Some(helper.clone()),
        "the first unready closure member gates the body"
    );
    assert_eq!(sched.module_pool(&user), Some(ModulePool::TypecheckBlocked));

    // helper completes → its waiter-sweep requeues user (no longer blocked).
    sched.notify_typecheck_done(&helper);
    assert_ne!(
        sched.module_pool(&user),
        Some(ModulePool::TypecheckBlocked),
        "user is requeued when the member it blocked on completes"
    );

    // Re-probe: helper now published, util still pending → util gates.
    assert_eq!(
        sched
            .block_on_first_unready_closure_member(&user, &closure)
            .unwrap(),
        Some(util.clone())
    );

    // util completes → requeue, then a final probe finds the barrier open.
    sched.notify_typecheck_done(&util);
    assert_eq!(
        sched
            .block_on_first_unready_closure_member(&user, &closure)
            .unwrap(),
        None,
        "barrier opens only when the LAST closure member is published"
    );
}

// spec: design/int/signature-body-prepass.md §3.6 / FIXME 0452 — THE BLOCKER
// PIN. The worker-path gate must be a SINGLE atomic check-and-block: scan for
// the first unready member AND register the waiter under ONE lock. The former
// two-call shape — `first_unready_closure_member` (lock/scan/release) THEN
// `block_for_typecheck` (re-lock/register) — had a window: if the member
// reached `notify_typecheck_done` BETWEEN the two locks, its waiter-sweep ran
// before the waiter was registered, stranding the module in `TypecheckBlocked`
// on an already-terminal member that never notifies again → a permanent
// lost-wakeup hang. This test races the gate's check-and-block against the
// member's completion across many iterations and asserts the module is NEVER
// stranded. It is deterministically GREEN with the atomic method (the two
// operations serialize: the scan either sees the member terminal and returns
// `None`, or registers the waiter that the later sweep observes); it would
// FAIL intermittently against the two-lock check-then-act.
#[test]
fn atomic_block_never_strands_on_terminal_member() {
    use std::sync::Arc;

    for _ in 0..256 {
        let sched = Arc::new(CompileScheduler::new());
        let member = mod_path("member");
        let reader = mod_path("reader");
        sched.register_module(member.clone(), no_sexps(), false);
        sched.register_module(reader.clone(), no_sexps(), false);
        let closure = closure_of(&["member"]);

        std::thread::scope(|scope| {
            // t1: the gate's atomic check-and-block for `reader`.
            let s1 = Arc::clone(&sched);
            let closure1 = closure.clone();
            let reader1 = reader.clone();
            let h = scope.spawn(move || {
                s1.block_on_first_unready_closure_member(&reader1, &closure1)
                    .unwrap()
            });
            // t2: `member` completes concurrently (the racing notify-sweep).
            sched.notify_typecheck_done(&member);
            let _ = h.join().unwrap();
        });

        // The structural invariant: whichever order won under the one lock,
        // `reader` is NEVER left parked on the already-terminal `member`.
        // Either the scan observed `member` terminal and the gate returned
        // `None` (reader never blocked), or it registered the waiter that the
        // notify-sweep then observed and requeued. In NO schedule is reader
        // stranded in `TypecheckBlocked` — the lost-wakeup hang the two-lock
        // check-then-act would produce.
        assert_ne!(
            sched.module_pool(&reader),
            Some(ModulePool::TypecheckBlocked),
            "reader must never be stranded in TypecheckBlocked on an \
                 already-terminal member (lost wakeup)"
        );
    }
}

// spec: repl/spec/14-file-watching.md §14.4 — ACT-1006. A failed module's
// cascade has already drained its waiters, so a pool worker that reaches the
// barrier afterwards must fail rather than wait on it: a waiter registered
// then is never woken, and the reload's completion wait parks forever.
#[test]
fn atomic_barrier_gate_fails_importer_of_already_failed_member() {
    let sched = CompileScheduler::new();
    let dep = mod_path("mymod");
    let importer = mod_path("prelude");
    sched.register_module(dep.clone(), no_sexps(), false);
    sched.register_module(importer.clone(), no_sexps(), false);
    sched.notify_typecheck_done(&importer);
    sched.notify_module_failed(
        &dep,
        CranelispError::ModuleError {
            message: "val takes no arguments".to_string(),
            location: ErrorLocation::from_span_file(Span::new(3, 9), None),
        },
    );
    assert!(sched.re_register_module(&importer, no_sexps()));

    let gate = sched.block_on_first_unready_closure_member(&importer, &closure_of(&["mymod"]));

    let err = gate.expect_err("the gate must refuse a closure holding a failed member");
    assert!(
        err.to_string().contains("val takes no arguments"),
        "the refusal carries the failed dependency's error: {err}"
    );
    assert_ne!(
        sched.module_pool(&importer),
        Some(ModulePool::TypecheckBlocked),
        "the importer must not park on a member whose cascade already ran"
    );
    // The worker turns the gate's error into the importer's failure; the
    // reload's completion wait then returns instead of parking.
    sched.notify_module_failed(&importer, err);
    assert!(sched.wait_inmem_complete_blocking().is_err());
}

// ══════════════════════════════════════════════════════════════════════
// S93 signature/body pre-pass — Task 3: per-cluster static-closure memo
// (the body-boundary closure walk runs ONCE per cluster, not once per
// retry-from-top attempt). `cached_static_closure` / `cache_static_closure`.
// ══════════════════════════════════════════════════════════════════════

// spec: design/int/signature-body-prepass.md §3.1 — the memo round-trips a
// ClosureOrder under its fingerprint, returns it on a fingerprint hit (the
// same cluster's retry-from-top), and MISSES on a different fingerprint (a
// distinct cluster on the same module scope — a new REPL form).
#[test]
fn static_closure_memo_hits_on_matching_fingerprint() {
    let sched = CompileScheduler::new();
    let m = mod_path("user");
    sched.register_module(m.clone(), no_sexps(), false);
    let closure = closure_of(&["helper", "util"]);

    // Miss before anything is cached.
    assert_eq!(sched.cached_static_closure(&m, 0xABCD), None);

    // Cache under a fingerprint → a matching probe hits with the same order.
    sched.cache_static_closure(&m, 0xABCD, &closure);
    assert_eq!(
        sched.cached_static_closure(&m, 0xABCD),
        Some(closure.clone()),
        "a matching fingerprint reuses the memoised closure (no re-walk)"
    );

    // A different fingerprint MISSES (a distinct cluster → must recompute).
    assert_eq!(
        sched.cached_static_closure(&m, 0x1234),
        None,
        "a fingerprint miss forces a recompute (correctness across clusters)"
    );
}

// spec: §3.1 — `re_register_module` (source changed) resets the memo, so the
// next cluster re-walks the closure rather than serving a stale one.
#[test]
fn re_register_clears_static_closure_memo() {
    let sched = CompileScheduler::new();
    let m = mod_path("user");
    sched.register_module(m.clone(), no_sexps(), false);
    sched.notify_typecheck_done(&m); // terminal → re-registerable
    let closure = closure_of(&["helper"]);
    sched.cache_static_closure(&m, 0x55, &closure);
    assert_eq!(sched.cached_static_closure(&m, 0x55), Some(closure));

    // Source changed → re-register resets the memo to None.
    assert!(sched.re_register_module(&m, no_sexps()));
    assert_eq!(
        sched.cached_static_closure(&m, 0x55),
        None,
        "a source change re-walks the closure (no stale memo)"
    );
}

// ──────────────────────────────────────────────────────────────────────
// Restore before load and one load entry (`design/int/int.md` §7.1).
// A restorer registers a cached module with its object load held; no claim
// is granted until the hold drops.
// ──────────────────────────────────────────────────────────────────────

/// Take the ladder's next cache-load claim. Only cache-load work may be
/// queued.
fn take_cache_load(sched: &CompileScheduler) -> Option<CachedLoadClaim<'_>> {
    match sched.take_priority_work() {
        Some(PriorityWork::JitCodegen(claim)) => Some(claim),
        Some(other) => panic!("expected only cache-load work, got {other:?}"),
        None => None,
    }
}

/// What a claim request answered, observed across a thread.
#[derive(Debug, PartialEq, Eq)]
enum Answered {
    Claimed,
    Loaded,
    Pending,
    Unavailable,
}

/// Record the answer; a claimed load is completed as loaded.
fn settle(answer: CachedLoadAnswer<'_>) -> Answered {
    match answer {
        CachedLoadAnswer::Claimed(claim) => {
            claim.complete_loaded(&[]);
            Answered::Claimed
        }
        CachedLoadAnswer::Loaded => Answered::Loaded,
        CachedLoadAnswer::Pending => Answered::Pending,
        CachedLoadAnswer::Unavailable => Answered::Unavailable,
    }
}

fn spawn_claim_waiter(
    sched: &std::sync::Arc<CompileScheduler>,
    module: &ModuleFullPath,
) -> (
    std::sync::mpsc::Receiver<Answered>,
    std::thread::JoinHandle<()>,
) {
    let (tx, rx) = std::sync::mpsc::channel();
    let sched = std::sync::Arc::clone(sched);
    let module = module.clone();
    let handle = std::thread::spawn(move || {
        let _ = tx.send(settle(sched.claim_or_await_cached_load(&module)));
    });
    (rx, handle)
}

type Settled = Result<ExecutionReadiness, SchedulerError>;

/// Run the execution wait on its own thread, so a planted fault turns a row
/// RED by timeout instead of hanging the suite.
fn spawn_execution_wait(
    sched: &std::sync::Arc<CompileScheduler>,
) -> std::sync::mpsc::Receiver<Settled> {
    let (tx, rx) = std::sync::mpsc::channel();
    let sched = std::sync::Arc::clone(sched);
    std::thread::spawn(move || {
        let _ = tx.send(sched.wait_cached_loads_settled());
    });
    rx
}

/// Run the named-module in-memory wait on its own thread.
fn spawn_module_wait(
    sched: &std::sync::Arc<CompileScheduler>,
    module: &ModuleFullPath,
) -> std::sync::mpsc::Receiver<Result<(), SchedulerError>> {
    let (tx, rx) = std::sync::mpsc::channel();
    let sched = std::sync::Arc::clone(sched);
    let module = module.clone();
    std::thread::spawn(move || {
        let _ = tx.send(sched.wait_module_inmem_complete_blocking(&module));
    });
    rx
}

const WAITER_STAYS_PARKED: std::time::Duration = std::time::Duration::from_millis(100);
const WAITER_WAKES: std::time::Duration = std::time::Duration::from_secs(5);

/// Register `module` from cache with its hold released and its load claimed
/// by the ladder.
fn claimed_cached_module<'s>(
    sched: &'s CompileScheduler,
    module: &ModuleFullPath,
) -> CachedLoadClaim<'s> {
    drop(sched.register_module_cached(module.clone(), HashSet::new()));
    let claim = take_cache_load(sched).expect("a released load is claimable");
    assert_eq!(claim.module(), module);
    claim
}

// spec: design/int/int.md §7.1 — restore before load: a held load is not
// claimable, while typecheck readiness is published at registration.
#[test]
fn held_cached_load_is_not_claimable_while_signatures_are_ready() {
    let sched = CompileScheduler::new();
    let cached = mod_path("a");
    let waiter = mod_path("user");
    let _hold = sched
        .register_module_cached(cached.clone(), HashSet::new())
        .expect("first registration places the hold");

    sched.register_module(waiter.clone(), no_sexps(), false);
    assert!(matches!(
        sched.take_priority_work(),
        Some(PriorityWork::Typecheck { .. })
    ));
    sched
        .block_for_typecheck(&waiter, &cached, &Symbol::from("*"), Span::SYNTHETIC)
        .unwrap();
    match sched.take_priority_work() {
        Some(PriorityWork::Typecheck { module, .. }) => assert_eq!(module, waiter),
        other => panic!("the whole-module waiter must be satisfied under the hold, got {other:?}"),
    }
    assert!(
        take_cache_load(&sched).is_none(),
        "a held load must not be claimed"
    );
}

// spec: design/int/int.md §7.1 — releasing the hold makes the load claimable
// exactly once.
#[test]
fn released_cached_load_is_claimed_exactly_once() {
    let sched = CompileScheduler::new();
    let cached = mod_path("a");
    let hold = sched.register_module_cached(cached.clone(), HashSet::new());
    drop(hold);

    let claim = take_cache_load(&sched).expect("the released load is claimable");
    assert_eq!(claim.module(), &cached);
    assert!(
        take_cache_load(&sched).is_none(),
        "a claimed load is not re-issued"
    );
}

// spec: design/int/int.md §7.1 — one load entry: the direct claim honours the
// hold and reports a completed load.
#[test]
fn direct_claim_is_pending_while_held_and_loaded_after_completion() {
    let sched = CompileScheduler::new();
    let cached = mod_path("a");
    let hold = sched.register_module_cached(cached.clone(), HashSet::new());

    assert!(matches!(
        sched.try_claim_cached_load(&cached),
        CachedLoadAnswer::Pending
    ));
    drop(hold);
    let CachedLoadAnswer::Claimed(claim) = sched.try_claim_cached_load(&cached) else {
        panic!("a released load must be claimed");
    };
    claim.complete_loaded(&[]);
    assert!(matches!(
        sched.try_claim_cached_load(&cached),
        CachedLoadAnswer::Loaded
    ));
}

// spec: design/int/int.md §7.1 — one load entry: a load the ladder claimed is
// never claimed a second time.
#[test]
fn direct_claim_after_ladder_claim_is_pending() {
    let sched = CompileScheduler::new();
    let cached = mod_path("a");
    let _claim = claimed_cached_module(&sched, &cached);

    assert!(matches!(
        sched.try_claim_cached_load(&cached),
        CachedLoadAnswer::Pending
    ));
}

// spec: design/int/int.md §7.1 — every exit from a restore releases its hold,
// including an early error return.
#[test]
fn hold_released_on_restore_error_path() {
    fn failing_restore(sched: &CompileScheduler, module: &ModuleFullPath) -> Result<(), ()> {
        let _hold = sched.register_module_cached(module.clone(), HashSet::new());
        Err(())?;
        Ok(())
    }

    let sched = CompileScheduler::new();
    let cached = mod_path("a");
    assert!(failing_restore(&sched, &cached).is_err());
    let claim = take_cache_load(&sched).expect("the error exit released the hold");
    assert_eq!(claim.module(), &cached);
}

// spec: design/int/int.md §7.1 — a caller waiting on a held load takes the
// claim itself once the hold drops, so the load never depends on another
// worker being free.
#[test]
fn awaiting_caller_claims_the_load_when_the_hold_drops() {
    let sched = std::sync::Arc::new(CompileScheduler::new());
    let cached = mod_path("a");
    let hold = sched.register_module_cached(cached.clone(), HashSet::new());

    let (rx, waiter) = spawn_claim_waiter(&sched, &cached);
    assert!(
        rx.recv_timeout(WAITER_STAYS_PARKED).is_err(),
        "the waiter must not claim a held load"
    );
    drop(hold);
    let answered = rx
        .recv_timeout(WAITER_WAKES)
        .expect("releasing the hold must wake the waiter");
    assert_eq!(answered, Answered::Claimed);
    waiter.join().unwrap();
    assert!(
        take_cache_load(&sched).is_none(),
        "the ladder must not load it again"
    );
}

// spec: design/int/int.md §7.1 — a waiter on another caller's claim returns
// when that load completes, without loading a second copy.
#[test]
fn awaiting_caller_on_claimed_load_returns_loaded() {
    let sched = std::sync::Arc::new(CompileScheduler::new());
    let cached = mod_path("a");
    let claim = claimed_cached_module(&sched, &cached);

    let (rx, waiter) = spawn_claim_waiter(&sched, &cached);
    assert!(rx.recv_timeout(WAITER_STAYS_PARKED).is_err());
    claim.complete_loaded(&[]);
    let answered = rx
        .recv_timeout(WAITER_WAKES)
        .expect("completion must wake the waiter");
    assert_eq!(answered, Answered::Loaded);
    waiter.join().unwrap();
}

// spec: design/int/int.md §7.1 — a waiter parked on another caller's claim
// wakes without a claim when that load completes as failed.
#[test]
fn awaiting_caller_on_failed_load_returns_unavailable() {
    let sched = std::sync::Arc::new(CompileScheduler::new());
    let cached = mod_path("a");
    let claim = claimed_cached_module(&sched, &cached);

    let (rx, waiter) = spawn_claim_waiter(&sched, &cached);
    assert!(rx.recv_timeout(WAITER_STAYS_PARKED).is_err());
    claim.complete_failed(dummy_error("unresolved symbol"));
    let answered = rx
        .recv_timeout(WAITER_WAKES)
        .expect("a failed completion must wake the waiter");
    assert_eq!(answered, Answered::Unavailable);
    waiter.join().unwrap();
}

// spec: design/int/int.md §7.1 — a failed cached module is never claimed and
// does not stop the ladder from claiming the next load.
#[test]
fn ladder_skips_failed_cached_module_and_claims_the_next() {
    let sched = CompileScheduler::new();
    let failed = mod_path("a");
    let next = mod_path("b");
    drop(sched.register_module_cached(failed.clone(), HashSet::new()));
    drop(sched.register_module_cached(next.clone(), HashSet::new()));
    sched.notify_module_failed(&failed, dummy_error("restore failed"));

    let claim = take_cache_load(&sched).expect("the next load is claimable");
    assert_eq!(claim.module(), &next);
    assert!(take_cache_load(&sched).is_none());
}

// spec: design/int/int.md §7.1 — negative: the hold changes neither an
// uncached module nor a cached module with no object.
#[test]
fn hold_leaves_uncached_and_objectless_modules_unchanged() {
    let sched = CompileScheduler::new();
    let fresh = mod_path("fresh");
    let objectless = mod_path("generic.only");

    sched.register_module(fresh.clone(), no_sexps(), false);
    match sched.take_priority_work() {
        Some(PriorityWork::Typecheck { module, .. }) => assert_eq!(module, fresh),
        other => panic!("expected Typecheck(fresh), got {other:?}"),
    }
    sched.notify_typecheck_done(&fresh);
    sched.notify_inmem_codegen_complete(&fresh, &Symbol::from("main"), true);

    sched.register_module_cached_no_object(objectless.clone(), HashSet::new());
    assert!(take_cache_load(&sched).is_none());
    assert!(matches!(
        sched.try_claim_cached_load(&fresh),
        CachedLoadAnswer::Loaded
    ));
    assert!(matches!(
        sched.try_claim_cached_load(&objectless),
        CachedLoadAnswer::Loaded
    ));
    assert!(sched.wait_inmem_complete().is_ok());
    assert!(matches!(
        sched.try_claim_cached_load(&mod_path("unregistered")),
        CachedLoadAnswer::Unavailable
    ));
}

// spec: design/int/int.md §7.1 — one classification: a fresh registration
// that also sits in the cached set is not a cached-object load, so a claim
// request finds it unavailable and the execution wait ignores it.
#[test]
fn fresh_registration_in_the_cached_set_is_not_a_cached_load() {
    let sched = std::sync::Arc::new(CompileScheduler::new());
    let fresh = mod_path("fresh");
    sched.register_module(fresh.clone(), no_sexps(), false);
    sched.cached_module_insert(fresh.clone());
    assert!(matches!(
        sched.take_priority_work(),
        Some(PriorityWork::Typecheck { .. })
    ));

    assert!(matches!(
        sched.try_claim_cached_load(&fresh),
        CachedLoadAnswer::Unavailable
    ));
    let (rx, waiter) = spawn_claim_waiter(&sched, &fresh);
    assert_eq!(
        rx.recv_timeout(WAITER_WAKES)
            .expect("a claim request on fresh work must not wait"),
        Answered::Unavailable
    );
    waiter.join().unwrap();
    assert!(
        spawn_execution_wait(&sched)
            .recv_timeout(WAITER_WAKES)
            .expect("the execution wait must not wait on fresh work")
            .is_ok()
    );
}

// ──────────────────────────────────────────────────────────────────────
// Load before execution (`design/int/int.md` §7.1): the REPL runs compiled
// code only after no cached-object load is held, claimable or claimed, and
// never after one has failed.
// ──────────────────────────────────────────────────────────────────────

// spec: design/int/int.md §7.1 — U-RC (a): the execution wait does not
// return while a load is held or claimed, and returns ready once it loads.
#[test]
fn execution_wait_blocks_while_a_cached_load_is_held_or_claimed() {
    let sched = std::sync::Arc::new(CompileScheduler::new());
    let cached = mod_path("a");
    let hold = sched.register_module_cached(cached.clone(), HashSet::new());

    let settled = spawn_execution_wait(&sched);
    assert!(
        settled.recv_timeout(WAITER_STAYS_PARKED).is_err(),
        "the wait must not return while the load is held"
    );
    drop(hold);
    let claim = take_cache_load(&sched).expect("the released load is claimable");
    assert!(
        settled.recv_timeout(WAITER_STAYS_PARKED).is_err(),
        "the wait must not return while the load is claimed"
    );
    claim.complete_loaded(&[]);
    assert!(
        settled
            .recv_timeout(WAITER_WAKES)
            .expect("completing the load must wake the wait")
            .is_ok(),
        "a loaded cached module is ready"
    );
}

// spec: design/int/int.md §7.1 — U-RC (b): the wait covers every outstanding
// load, not only the latest or a named one.
#[test]
fn execution_wait_covers_an_earlier_load_after_a_later_one_completes() {
    let sched = std::sync::Arc::new(CompileScheduler::new());
    let earlier = mod_path("x");
    let later = mod_path("y");
    let earlier_claim = claimed_cached_module(&sched, &earlier);
    claimed_cached_module(&sched, &later).complete_loaded(&[]);

    let settled = spawn_execution_wait(&sched);
    assert!(
        settled.recv_timeout(WAITER_STAYS_PARKED).is_err(),
        "the earlier claimed load is still outstanding"
    );
    earlier_claim.complete_loaded(&[]);
    assert!(
        settled
            .recv_timeout(WAITER_WAKES)
            .expect("completing the earlier load must wake the wait")
            .is_ok()
    );
}

// spec: design/int/int.md §7.1 — U-RC (c): a failed cached load refuses
// every later step with that module's failure; no readiness is returned.
#[test]
fn execution_wait_reports_a_failed_cached_load_on_every_call() {
    let sched = std::sync::Arc::new(CompileScheduler::new());
    let cached = mod_path("x");
    claimed_cached_module(&sched, &cached).complete_failed(dummy_error("unresolved symbol"));

    for call in ["first", "second"] {
        match spawn_execution_wait(&sched).recv_timeout(WAITER_WAKES) {
            Ok(Err(SchedulerError::ModuleFailed { module, .. })) => {
                assert_eq!(module, cached, "the {call} call names the failed module");
            }
            other => panic!("the {call} call must refuse with the load failure, got {other:?}"),
        }
    }
}

// spec: design/int/int.md §7.1 — U-RC (d, neg): nothing outstanding means
// ready at once, whatever fresh, objectless or loaded modules exist.
#[test]
fn execution_wait_is_ready_at_once_when_no_cached_load_is_outstanding() {
    let sched = std::sync::Arc::new(CompileScheduler::new());
    let ready_now = |sched: &std::sync::Arc<CompileScheduler>, case: &str| {
        let settled = spawn_execution_wait(sched)
            .recv_timeout(WAITER_WAKES)
            .unwrap_or_else(|_| panic!("{case}: the wait must return at once"));
        assert!(settled.is_ok(), "{case}: expected ready, got {settled:?}");
    };
    ready_now(&sched, "no modules");

    let fresh = mod_path("fresh");
    sched.register_module(fresh.clone(), no_sexps(), false);
    assert!(matches!(
        sched.take_priority_work(),
        Some(PriorityWork::Typecheck { .. })
    ));
    ready_now(&sched, "fresh module mid-typecheck");

    sched.register_module_cached_no_object(mod_path("generic.only"), HashSet::new());
    ready_now(&sched, "cached module with no object");

    claimed_cached_module(&sched, &mod_path("loaded")).complete_loaded(&[]);
    ready_now(&sched, "loaded cached module");
}

// spec: design/int/int.md §7.1 — U-RC (e): shutdown ends the wait on a held
// load, which is reported as incomplete rather than ready.
#[test]
fn execution_wait_returns_at_shutdown() {
    let sched = std::sync::Arc::new(CompileScheduler::new());
    let cached = mod_path("a");
    let _hold = sched.register_module_cached(cached.clone(), HashSet::new());

    let settled = spawn_execution_wait(&sched);
    assert!(settled.recv_timeout(WAITER_STAYS_PARKED).is_err());
    sched.shutdown();
    match settled.recv_timeout(WAITER_WAKES) {
        Ok(Err(SchedulerError::InmemIncomplete { module })) => assert_eq!(module, cached),
        other => panic!("shutdown must end the wait without readiness, got {other:?}"),
    }
}

// ──────────────────────────────────────────────────────────────────────
// A claim always ends (`design/int/int.md` §7.1): dropping it uncompleted
// fails the module and wakes a waiter parked before the drop.
// ──────────────────────────────────────────────────────────────────────

/// A load claimed by the ladder with a claim waiter already parked on it.
fn claimed_load_with_parked_waiter<'s>(
    sched: &'s std::sync::Arc<CompileScheduler>,
    module: &ModuleFullPath,
) -> (CachedLoadClaim<'s>, std::sync::mpsc::Receiver<Answered>) {
    let claim = claimed_cached_module(sched, module);
    let (rx, _waiter) = spawn_claim_waiter(sched, module);
    assert!(
        rx.recv_timeout(WAITER_STAYS_PARKED).is_err(),
        "the waiter parks on the claimed load"
    );
    (claim, rx)
}

/// After an abandoned claim: the waiter wakes without a claim, the module is
/// failed and unclaimed, and the named-module wait reports the failure.
fn assert_abandoned_load_failed(
    sched: &std::sync::Arc<CompileScheduler>,
    module: &ModuleFullPath,
    waiter: std::sync::mpsc::Receiver<Answered>,
) {
    assert_eq!(
        waiter
            .recv_timeout(WAITER_WAKES)
            .expect("an abandoned claim must wake the parked waiter"),
        Answered::Unavailable
    );
    {
        let state = sched.lock();
        let ms = &state.modules[module];
        assert_eq!(ms.cached_load_state(), CachedLoadState::Failed);
        assert_ne!(ms.cached_object_load, CachedObjectLoad::Claimed);
    }
    assert!(matches!(
        spawn_module_wait(sched, module).recv_timeout(WAITER_WAKES),
        Ok(Err(SchedulerError::ModuleFailed { .. }))
    ));
}

// spec: design/int/int.md §7.1 — U-R1 (i): a claim dropped by unwinding out
// of a panicking load fails the module instead of stranding the claim.
#[test]
fn claim_dropped_by_a_panicking_load_fails_the_module() {
    let sched = std::sync::Arc::new(CompileScheduler::new());
    let cached = mod_path("a");
    let (claim, waiter) = claimed_load_with_parked_waiter(&sched, &cached);

    let unwound = std::panic::catch_unwind(std::panic::AssertUnwindSafe(move || {
        let _claim = claim;
        panic!("planted: the load panics while holding its claim");
    }));
    assert!(unwound.is_err());
    assert_abandoned_load_failed(&sched, &cached, waiter);
}

// spec: design/int/int.md §7.1 — U-R1 (ii): a plain drop without completion
// fails the module the same way.
#[test]
fn claim_dropped_without_completion_fails_the_module() {
    let sched = std::sync::Arc::new(CompileScheduler::new());
    let cached = mod_path("a");
    let (claim, waiter) = claimed_load_with_parked_waiter(&sched, &cached);

    drop(claim);
    assert_abandoned_load_failed(&sched, &cached, waiter);
}

// spec: design/int/int.md §7.1 — U-R1 (iii, neg): a completed claim does not
// fail its module when it goes out of scope.
#[test]
fn completed_claim_does_not_fail_the_module() {
    let sched = std::sync::Arc::new(CompileScheduler::new());
    let cached = mod_path("a");
    let (claim, waiter) = claimed_load_with_parked_waiter(&sched, &cached);

    claim.complete_loaded(&[]);
    assert_eq!(
        waiter
            .recv_timeout(WAITER_WAKES)
            .expect("completion must wake the parked waiter"),
        Answered::Loaded
    );
    let state = sched.lock();
    let ms = &state.modules[&cached];
    assert_eq!(ms.cached_load_state(), CachedLoadState::Loaded);
    assert_ne!(ms.pool, ModulePool::Failed);
}

// ══════════════════════════════════════════════════════════════════════
// Failure dependencies (design/int/repl-lifecycle.md §1.2.1): the module
// through which one generation failed, kept on the module state until the
// next registration and returned by the failed-module reset.
// ══════════════════════════════════════════════════════════════════════

// spec: design/int/repl-lifecycle.md §1.2.1 — a waiter failed in the cascade
// records the dependency it waited on; the dependency that failed in its own
// source records nothing.
#[test]
fn cascade_records_the_awaited_dependency() {
    let sched = CompileScheduler::new();
    let (lib, base) = (mod_path("lib"), mod_path("base"));
    sched.register_module(lib.clone(), no_sexps(), false);
    sched.register_module(base.clone(), no_sexps(), false);
    sched
        .block_for_typecheck(&lib, &base, &Symbol::from("*"), Span::SYNTHETIC)
        .unwrap();

    sched.notify_module_failed(&base, dummy_error("undefined variable: nope"));

    assert!(
        sched.is_failed(&lib),
        "precondition: the cascade failed `lib`"
    );
    assert_eq!(
        sched.failure_dependencies(&lib),
        BTreeSet::from([base.clone()])
    );
    assert!(sched.failure_dependencies(&base).is_empty());
}

// spec: design/int/repl-lifecycle.md §1.2.1 — a module that meets an
// already-failed dependency at a dependency wait or at the signature barrier
// records it.
#[test]
fn fail_fast_records_the_failed_dependency_at_both_waits() {
    let sched = CompileScheduler::new();
    let (waiter, gated, base) = (mod_path("waiter"), mod_path("gated"), mod_path("base"));
    for module in [&waiter, &gated, &base] {
        sched.register_module(module.clone(), no_sexps(), false);
    }
    sched.notify_module_failed(&base, dummy_error("boom"));

    assert!(
        sched
            .block_for_typecheck(&waiter, &base, &Symbol::from("*"), Span::SYNTHETIC)
            .is_err()
    );
    assert!(
        sched
            .block_on_first_unready_closure_member(&gated, &closure_of(&["base"]))
            .is_err()
    );

    assert_eq!(
        sched.failure_dependencies(&waiter),
        BTreeSet::from([base.clone()])
    );
    assert_eq!(sched.failure_dependencies(&gated), BTreeSet::from([base]));
}

// spec: design/int/repl-lifecycle.md §1.2.1 — a module that closes a wait
// cycle records the next module on it, at a dependency wait and at the
// signature barrier.
#[test]
fn wait_cycle_records_the_next_module_on_the_cycle() {
    let sched = CompileScheduler::new();
    let (a, b) = (mod_path("a"), mod_path("b"));
    sched.register_module(a.clone(), no_sexps(), false);
    sched.register_module(b.clone(), no_sexps(), false);
    sched
        .block_for_typecheck(&a, &b, &Symbol::from("*"), Span::SYNTHETIC)
        .unwrap();
    let cycle = sched
        .block_for_typecheck(&b, &a, &Symbol::from("*"), Span::SYNTHETIC)
        .unwrap_err();
    assert!(cycle.to_string().contains("b -> a -> b"), "{cycle}");
    assert_eq!(sched.failure_dependencies(&b), BTreeSet::from([a]));

    let barrier = CompileScheduler::new();
    let (c, d) = (mod_path("c"), mod_path("d"));
    barrier.register_module(c.clone(), no_sexps(), false);
    barrier.register_module(d.clone(), no_sexps(), false);
    barrier
        .block_for_typecheck(&c, &d, &Symbol::from("*"), Span::SYNTHETIC)
        .unwrap();
    assert!(
        barrier
            .block_on_first_unready_closure_member(&d, &closure_of(&["c"]))
            .is_err()
    );
    assert_eq!(barrier.failure_dependencies(&d), BTreeSet::from([c]));
}

// spec: design/int/repl-lifecycle.md §1.2.1 — one generation's record is a
// set: a cascade and a failed attempt's dependencies accumulate, and the
// module itself is never its own failure dependency.
#[test]
fn one_generation_accumulates_every_failure_dependency() {
    let sched = CompileScheduler::new();
    let (lib, base, other) = (mod_path("lib"), mod_path("base"), mod_path("other"));
    for module in [&lib, &base, &other] {
        sched.register_module(module.clone(), no_sexps(), false);
    }
    sched
        .block_for_typecheck(&lib, &base, &Symbol::from("*"), Span::SYNTHETIC)
        .unwrap();
    sched.notify_module_failed(&base, dummy_error("boom"));
    sched.record_failure_dependencies(&lib, [other.clone(), lib.clone()]);

    assert_eq!(
        sched.failure_dependencies(&lib),
        BTreeSet::from([base, other])
    );
}

// spec: design/int/repl-lifecycle.md §1.2.1 — a re-registration starts a new
// generation with no failure dependency, and the failed-module reset returns
// each forgotten module with its own.
#[test]
fn re_registration_clears_and_reset_returns_failure_dependencies() {
    let sched = CompileScheduler::new();
    let (lib, base) = (mod_path("lib"), mod_path("base"));
    sched.register_module(lib.clone(), no_sexps(), false);
    sched.register_module(base.clone(), no_sexps(), false);
    sched.record_failure_dependencies(&lib, [base.clone()]);
    sched.notify_module_failed(&lib, dummy_error("dependency 'base' failed"));
    assert!(sched.re_register_module(&lib, no_sexps()));
    assert!(sched.failure_dependencies(&lib).is_empty());

    sched.record_failure_dependencies(&lib, [base.clone()]);
    sched.notify_module_failed(&lib, dummy_error("dependency 'base' failed"));
    sched.notify_module_failed(&base, dummy_error("boom"));
    let mut reset = sched.reset_all_failed_modules();
    reset.sort_by(|left, right| left.module.as_ref().cmp(right.module.as_ref()));
    assert_eq!(
        reset,
        vec![
            ResetModule {
                module: base.clone(),
                failure_dependencies: BTreeSet::new(),
            },
            ResetModule {
                module: lib,
                failure_dependencies: BTreeSet::from([base]),
            },
        ]
    );
}
