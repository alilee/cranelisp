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
        shared.scheduler.register_module(m.clone(), no_sexps(), false);
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
    // Sprint 58 Wave 2c: split inmem_claimed from inmem_done so
    // wait_inmem_complete only sees inmem_done after the cache-hit worker
    // actually finishes loading the .o.
    // ──────────────────────────────────────────────────────────────────────

    // spec: design/int/symbol-table-cache.md §3.2 — claim guard does not
    // pre-set `inmem_done`; only the worker's
    // `notify_inmem_codegen_batch_complete` does.
    #[test]
    fn level4_claim_guard_sets_inmem_claimed_not_inmem_done() {
        let sched = CompileScheduler::new();
        let m = mod_path("cached.dep");
        // Cached module enters TypecheckDone with object_done=true,
        // inmem_done=false, inmem_claimed=false.
        sched.register_module_cached(m.clone(), HashSet::new());
        {
            let state = sched.lock();
            let ms = state.modules.get(&m).unwrap();
            assert!(!ms.inmem_done, "cached module starts with inmem_done=false");
            assert!(!ms.inmem_claimed, "cached module starts with inmem_claimed=false");
            assert!(ms.object_done, "cached module starts with object_done=true");
        }

        // Take level-4 work — should claim, NOT mark done.
        let work = sched.take_priority_work();
        assert!(matches!(work, Some(PriorityWork::JitCodegen(_, _))));
        {
            let state = sched.lock();
            let ms = state.modules.get(&m).unwrap();
            assert!(
                !ms.inmem_done,
                "claim guard MUST NOT pre-set inmem_done — that races against \
                 wait_inmem_complete (Sprint 58 Wave 2c regression guard)"
            );
            assert!(
                ms.inmem_claimed,
                "claim guard sets inmem_claimed so other workers skip this module"
            );
        }

        // Second take must skip this module (claimed).
        let second = sched.take_priority_work();
        assert!(
            second.is_none(),
            "second take_priority_work must skip the inmem_claimed module"
        );

        // Worker reports completion → inmem_done set, claim cleared.
        sched.notify_inmem_codegen_batch_complete(&m, &[]);
        {
            let state = sched.lock();
            let ms = state.modules.get(&m).unwrap();
            assert!(ms.inmem_done, "completion sets inmem_done");
            assert!(
                !ms.inmem_claimed,
                "completion releases the claim atomically with setting done"
            );
        }
    }

    // spec: design/arch/concrete-boundary-type.md §2.5 (Cache-schemes-without-
    //       codegen) + §4-B (FIXME 0387) — a generic-only cached module has NO
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

    // spec: design/int/symbol-table-cache.md §3.2 — wait_inmem_complete
    // distinguishes "claimed but not done" from "done"; cache-hit worker
    // failure must surface as an error before trampoline runs.
    #[test]
    fn wait_inmem_complete_does_not_pass_on_claimed_but_unfinished_module() {
        let sched = CompileScheduler::new();
        let m = mod_path("cached.dep");
        sched.register_module_cached(m.clone(), HashSet::new());

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

    // spec: design/int/symbol-table-cache.md §3.2 — multiple cache-hit
    // modules can be loaded in parallel without the claim guard letting
    // wait_inmem_complete pass prematurely.
    #[test]
    fn level4_multiple_cached_modules_each_claim_independently() {
        let sched = CompileScheduler::new();
        let m1 = mod_path("dep.one");
        let m2 = mod_path("dep.two");
        sched.register_module_cached(m1.clone(), HashSet::new());
        sched.register_module_cached(m2.clone(), HashSet::new());

        // Two takes — each claims one module.
        let w1 = sched.take_priority_work();
        let w2 = sched.take_priority_work();
        let w3 = sched.take_priority_work();

        assert!(matches!(w1, Some(PriorityWork::JitCodegen(_, _))));
        assert!(matches!(w2, Some(PriorityWork::JitCodegen(_, _))));
        assert!(w3.is_none(), "third take must return None — both claimed");

        // Both modules must be claimed but not done.
        {
            let state = sched.lock();
            for path in [&m1, &m2] {
                let ms = state.modules.get(path).unwrap();
                assert!(ms.inmem_claimed);
                assert!(!ms.inmem_done);
            }
        }

        // Complete one. wait_inmem_complete must still fail (the other is
        // still claimed-but-not-done).
        sched.notify_inmem_codegen_batch_complete(&m1, &[]);
        assert!(
            sched.wait_inmem_complete().is_err(),
            "wait_inmem_complete must fail while ANY module is claimed-but-not-done"
        );

        // Complete the other. Now wait succeeds.
        sched.notify_inmem_codegen_batch_complete(&m2, &[]);
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
        sched.register_module_cached(m.clone(), symbols);
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
            .block_for_typecheck(&a, &b, &Symbol::from("foo"))
            .unwrap();
        match sched.take_priority_work() {
            Some(PriorityWork::Typecheck { module, .. }) => {
                assert_eq!(module, b, "blocked module a is skipped; b is returned")
            }
            other => panic!("expected Typecheck(mod_b), got {other:?}"),
        }
    }

    // spec: design/arch/concurrent-pipeline.md §6.2 — notify_symbol_typechecked unblocks
    #[test]
    fn harvest_notify_symbol_typechecked_unblocks_waiter() {
        let sched = CompileScheduler::new();
        let a = mod_path("mod_a");
        let b = mod_path("mod_b");
        sched.register_module(a.clone(), no_sexps(), false);
        sched.register_module(b.clone(), no_sexps(), false);
        let _ = sched.take_priority_work();
        sched
            .block_for_typecheck(&a, &b, &Symbol::from("foo"))
            .unwrap();
        let _ = sched.take_priority_work();
        sched.notify_symbol_typechecked(&b, &Symbol::from("foo"));
        sched.notify_typecheck_done(&b);
        match sched.take_priority_work() {
            Some(PriorityWork::Typecheck { module, .. }) => {
                assert_eq!(module, a, "a unblocks after b's symbol is typechecked")
            }
            other => panic!("expected Typecheck(mod_a) after unblock, got {other:?}"),
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
            .block_for_typecheck(&a, &b, &Symbol::from("bar"))
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
        sched.notify_symbol_typechecked(&a, &Symbol::from("fn_a"));
        sched.notify_typecheck_done(&a);
        let _ = sched.take_priority_work();
        sched.notify_symbol_typechecked(&b, &Symbol::from("fn_b"));
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
