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
            // S91 Pillar-3: importable-symbol indices (empty/unarmed default —
            // this scheduler unit test does not arm the burn-down).
            importable_indices: crate::session_v4::ImportableIndices::default(),
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
            .block_for_typecheck(&a, &b, &Symbol::from("*"))
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
        let closure = dependency_closure(&mod_path("root"), &decls)
            .expect("diamond is acyclic");
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
        let err = dependency_closure(&mod_path("a"), &decls)
            .expect_err("mutual import is a cycle");
        assert!(
            err.cycle.contains(&mod_path("a")) && err.cycle.contains(&mod_path("b")),
            "cycle names both modules: {:?}",
            err.cycle
        );
        // render() produces an `a -> … -> a` diagnostic string.
        let rendered = err.render();
        assert!(rendered.contains("->"), "rendered cycle has edges: {rendered}");
    }

    // spec: §4 — a longer cycle (a → b → c → a) is detected too.
    #[test]
    fn dependency_closure_three_cycle_is_cycle_error() {
        let decls = vec![
            edge("a", &["b"]),
            edge("b", &["c"]),
            edge("c", &["a"]),
        ];
        let err = dependency_closure(&mod_path("a"), &decls)
            .expect_err("3-cycle is a cycle");
        for m in ["a", "b", "c"] {
            assert!(err.cycle.contains(&mod_path(m)), "cycle names {m}: {:?}", err.cycle);
        }
    }

    // spec: §3.1 — modules reachable but absent from the decls (already-loaded
    // or compiler-seeded leaves) are treated as edge-free leaves, never a cycle.
    #[test]
    fn dependency_closure_unlisted_dep_is_leaf() {
        // root imports `seeded`, which is not in the decls list at all.
        let decls = vec![edge("root", &["seeded"])];
        let closure = dependency_closure(&mod_path("root"), &decls)
            .expect("unlisted dep is a leaf, not a cycle");
        let order = &closure.order;
        let pos = |n: &str| order.iter().position(|m| m.as_ref() == n).unwrap();
        assert!(pos("seeded") < pos("root"), "seeded leaf before root: {order:?}");
    }

    // ══════════════════════════════════════════════════════════════════════
    // S93 signature/body pre-pass — Step 2: Phase-A signature publication +
    // barrier (`signature-body-prepass.md` §7 step 2). The terminal pool
    // transition (`notify_typecheck_done`) IS the publication edge — there is no
    // separate `signatures_ready` bit (FIXME 0452 / /arch option i). The barrier
    // (`await_signature_barrier`) reads pool-terminal state directly.
    // ══════════════════════════════════════════════════════════════════════

    fn closure_of(mods: &[&str]) -> ClosureOrder {
        ClosureOrder { order: mods.iter().map(|m| mod_path(m)).collect() }
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
            .register_dep_edge_for_cycle_check(&entry, &dep)
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
            .register_dep_edge_for_cycle_check(&entry, &dep)
            .expect("entry → helper alone is acyclic");

        // Pool worker compiling helper hits `(import [user])` → helper → user.
        // The reverse check follows user.blocked_on = helper → CYCLE.
        let err = sched.block_for_typecheck(&dep, &entry, &Symbol::from("*"));
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
            .block_for_typecheck(&dep, &entry, &Symbol::from("*"))
            .expect("helper → user alone is acyclic");

        // Eval thread now records user → helper, closing the cycle.
        let err = sched.register_dep_edge_for_cycle_check(&entry, &dep);
        assert!(err.is_err(), "user → helper → user is a detected cycle");
        // The entry was NOT failed — it keeps its pre-edge pool (not Failed).
        assert_eq!(
            sched.module_pool(&entry),
            entry_pool_before,
            "a REPL import cycle is an eval error — the entry module is not failed"
        );
        assert!(!sched.is_failed(&entry), "entry must not be in Failed");
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
