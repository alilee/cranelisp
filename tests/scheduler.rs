// tests/scheduler.rs — Unit tests for CompileScheduler (pipeline v4 Step 2)
//
// These tests validate the scheduler's module lifecycle, priority queue,
// waiter/unblock logic, and failure cascade, using only the public API
// from concurrent-pipeline.md §6.
//
// Written BEFORE the implementation exists (spec-first TDD). This file
// will not compile until /int creates src/scheduler.rs and exposes the
// scheduler module from cranelisp::scheduler.

use cranelisp::scheduler::{CompileScheduler, PriorityWork};
use cranelisp_types::{CranelispError, ModuleFullPath, Span, Symbol};

/// Helper: create a dummy CranelispError for testing failure cascades.
fn dummy_error(msg: &str) -> CranelispError {
    CranelispError::ModuleError {
        message: msg.to_string(),
        file: None,
        span: Span { start: 0, end: 0 },
    }
}

// ============================================================
// 1. Module Lifecycle (concurrent-pipeline.md §2)
// ============================================================

// spec: design/arch/concurrent-pipeline.md §2 — register_module default pool
#[test]
fn test_register_module_starts_in_typecheck_next() {
    let mut scheduler = CompileScheduler::new();
    let module = ModuleFullPath::from("test_module");

    scheduler.register_module(module.clone(), false);

    // A module registered with delays_other=false enters TypecheckNext.
    // take_priority_work should return it as a Typecheck work item.
    let work = scheduler.take_priority_work();
    match work {
        Some(PriorityWork::Typecheck(m)) => assert_eq!(m, module),
        other => panic!(
            "Expected Some(Typecheck(test_module)), got {:?}",
            other
        ),
    }
}

// spec: design/arch/concurrent-pipeline.md §2.1 — TypecheckFirst priority
#[test]
fn test_register_module_with_delays_starts_in_typecheck_first() {
    let mut scheduler = CompileScheduler::new();
    let module = ModuleFullPath::from("dep_module");

    scheduler.register_module(module.clone(), true);

    // A module registered with delays_other=true enters TypecheckFirst.
    // take_priority_work at level 1 should return it.
    let work = scheduler.take_priority_work();
    match work {
        Some(PriorityWork::Typecheck(m)) => assert_eq!(m, module),
        other => panic!(
            "Expected Some(Typecheck(dep_module)), got {:?}",
            other
        ),
    }
}

// spec: design/arch/concurrent-pipeline.md §2.1 — TypecheckFirst drained before TypecheckNext
#[test]
fn test_typecheck_first_before_typecheck_next() {
    let mut scheduler = CompileScheduler::new();
    let first_mod = ModuleFullPath::from("first_mod");
    let next_mod = ModuleFullPath::from("next_mod");

    // Register TypecheckNext first, then TypecheckFirst.
    // The priority ladder should return TypecheckFirst before TypecheckNext.
    scheduler.register_module(next_mod.clone(), false);
    scheduler.register_module(first_mod.clone(), true);

    let work1 = scheduler.take_priority_work();
    match work1 {
        Some(PriorityWork::Typecheck(m)) => assert_eq!(
            m, first_mod,
            "Level 1 (TypecheckFirst) should be drained before level 3 (TypecheckNext)"
        ),
        other => panic!("Expected Typecheck(first_mod), got {:?}", other),
    }

    let work2 = scheduler.take_priority_work();
    match work2 {
        Some(PriorityWork::Typecheck(m)) => assert_eq!(m, next_mod),
        other => panic!("Expected Typecheck(next_mod), got {:?}", other),
    }
}

// spec: design/arch/concurrent-pipeline.md §8.1 — register_module_cached
#[test]
fn test_register_module_cached_enters_typecheck_done() {
    let mut scheduler = CompileScheduler::new();
    let module = ModuleFullPath::from("cached_mod");

    let symbols = [Symbol::from("foo"), Symbol::from("bar")]
        .into_iter()
        .collect();
    scheduler.register_module_cached(module.clone(), symbols);

    // A cached module enters TypecheckDone directly.
    // It should NOT appear in take_priority_work as a Typecheck item.
    // (It could appear as JitCodegen at level 4, but per Step 3 scope
    // level 4 returns None. So take_priority_work returns None.)
    let work = scheduler.take_priority_work();
    match work {
        Some(PriorityWork::Typecheck(m)) => panic!(
            "Cached module should NOT appear as Typecheck work, got {:?}",
            m
        ),
        // JitCodegen or None are both acceptable depending on level 4 implementation
        _ => {}
    }
}

// spec: design/arch/concurrent-pipeline.md §2 — TypecheckWorking → TypecheckDone
#[test]
fn test_notify_typecheck_done_moves_to_done() {
    let mut scheduler = CompileScheduler::new();
    let module = ModuleFullPath::from("mod_a");

    scheduler.register_module(module.clone(), false);

    // Take the module (moves to TypecheckWorking).
    let work = scheduler.take_priority_work();
    assert!(matches!(work, Some(PriorityWork::Typecheck(_))));

    // Notify typecheck done (moves to TypecheckDone).
    scheduler.notify_typecheck_done(&module);

    // With inmem codegen also complete, wait_inmem_complete should return Ok.
    // But typecheck done alone doesn't mean inmem done — we need to mark
    // inmem codegen complete too. For a module with no symbols to codegen,
    // notify with no_remaining=true using a dummy symbol.
    //
    // Actually, if the module has no symbols, inmem_done may need explicit
    // handling. Let's test the simplest lifecycle: typecheck done, then
    // inmem codegen complete for the last symbol.
    scheduler.notify_inmem_codegen_complete(&module, &Symbol::from("main"), true);

    let result = scheduler.wait_inmem_complete();
    assert!(
        result.is_ok(),
        "Expected Ok after typecheck+inmem complete, got {:?}",
        result
    );
}

// ============================================================
// 2. Priority Queue (concurrent-pipeline.md §4)
// ============================================================

// spec: design/arch/concurrent-pipeline.md §4 — block_for_macro_codegen populates priority queue
#[test]
fn test_block_for_macro_codegen_adds_priority_entry() {
    let mut scheduler = CompileScheduler::new();
    let module_a = ModuleFullPath::from("mod_a");
    let module_b = ModuleFullPath::from("mod_b");

    // Module B is already typecheck-done (it defines the macro dependency).
    scheduler.register_module(module_b.clone(), false);
    let _ = scheduler.take_priority_work(); // take B
    scheduler.notify_typecheck_done(&module_b);

    // Module A is being typechecked and hits a macro needing B's symbol.
    scheduler.register_module(module_a.clone(), false);
    let _ = scheduler.take_priority_work(); // take A

    // Block A for macro codegen: needs symbol "helper" from module B.
    scheduler.block_for_macro_codegen(
        &module_a,
        vec![(module_b.clone(), Symbol::from("helper"))],
    );

    // The priority queue should now have a BlockingJitCodegen entry.
    let work = scheduler.take_priority_work();
    match work {
        Some(PriorityWork::BlockingJitCodegen(m, s)) => {
            assert_eq!(m, module_b);
            assert_eq!(s, Symbol::from("helper"));
        }
        other => panic!(
            "Expected BlockingJitCodegen(mod_b, helper), got {:?}",
            other
        ),
    }
}

// spec: design/arch/concurrent-pipeline.md §4.3 — priority codegen completion unblocks module
#[test]
fn test_priority_codegen_complete_unblocks() {
    let mut scheduler = CompileScheduler::new();
    let module_a = ModuleFullPath::from("mod_a");
    let module_b = ModuleFullPath::from("mod_b");

    // B is typecheck-done.
    scheduler.register_module(module_b.clone(), false);
    let _ = scheduler.take_priority_work();
    scheduler.notify_typecheck_done(&module_b);

    // A is typechecking.
    scheduler.register_module(module_a.clone(), false);
    let _ = scheduler.take_priority_work();

    // A blocks on macro needing B/helper.
    scheduler.block_for_macro_codegen(
        &module_a,
        vec![(module_b.clone(), Symbol::from("helper"))],
    );

    // Worker picks up the priority codegen.
    let work = scheduler.take_priority_work();
    assert!(matches!(
        work,
        Some(PriorityWork::BlockingJitCodegen(_, _))
    ));

    // Complete the priority codegen.
    scheduler.notify_priority_codegen_complete(&module_b, &Symbol::from("helper"));

    // Module A should now be unblocked and available as Typecheck work.
    let work = scheduler.take_priority_work();
    match work {
        Some(PriorityWork::Typecheck(m)) => assert_eq!(
            m, module_a,
            "Module A should be unblocked after priority codegen completes"
        ),
        other => panic!("Expected Typecheck(mod_a), got {:?}", other),
    }
}

// ============================================================
// 3. Waiter/Unblock Logic (concurrent-pipeline.md §5)
// ============================================================

// spec: design/arch/concurrent-pipeline.md §6.2 — block_for_typecheck
#[test]
fn test_block_for_typecheck_blocks_module() {
    let mut scheduler = CompileScheduler::new();
    let module_a = ModuleFullPath::from("mod_a");
    let module_b = ModuleFullPath::from("mod_b");

    // Register both modules.
    scheduler.register_module(module_a.clone(), false);
    scheduler.register_module(module_b.clone(), false);

    // Worker takes A (moves to TypecheckWorking).
    let work = scheduler.take_priority_work();
    assert!(matches!(work, Some(PriorityWork::Typecheck(_))));

    // A blocks waiting for symbol "foo" from B.
    scheduler.block_for_typecheck(&module_a, &module_b, &Symbol::from("foo"));

    // Now take_priority_work should return B (the other ready module),
    // NOT A (which is blocked).
    let work = scheduler.take_priority_work();
    match work {
        Some(PriorityWork::Typecheck(m)) => assert_eq!(
            m, module_b,
            "Should get module_b since module_a is blocked"
        ),
        other => panic!("Expected Typecheck(mod_b), got {:?}", other),
    }
}

// spec: design/arch/concurrent-pipeline.md §6.2 — notify_symbol_typechecked unblocks waiter
#[test]
fn test_notify_symbol_typechecked_unblocks() {
    let mut scheduler = CompileScheduler::new();
    let module_a = ModuleFullPath::from("mod_a");
    let module_b = ModuleFullPath::from("mod_b");

    scheduler.register_module(module_a.clone(), false);
    scheduler.register_module(module_b.clone(), false);

    // Take A, block it on B's "foo".
    let _ = scheduler.take_priority_work();
    scheduler.block_for_typecheck(&module_a, &module_b, &Symbol::from("foo"));

    // Take B.
    let _ = scheduler.take_priority_work();

    // B typechecks "foo" — should unblock A.
    scheduler.notify_symbol_typechecked(&module_b, &Symbol::from("foo"));

    // Notify B done so it's out of the way.
    scheduler.notify_typecheck_done(&module_b);

    // A should now be available (unblocked, back in TypecheckFirst or TypecheckNext).
    let work = scheduler.take_priority_work();
    match work {
        Some(PriorityWork::Typecheck(m)) => assert_eq!(
            m, module_a,
            "Module A should be unblocked after B's symbol is typechecked"
        ),
        other => panic!(
            "Expected Typecheck(mod_a) after unblock, got {:?}",
            other
        ),
    }
}

// ============================================================
// 4. Failure Cascade (concurrent-pipeline.md §2.3)
// ============================================================

// spec: design/arch/concurrent-pipeline.md §2.3 — cascade failure to waiters
#[test]
fn test_module_failed_cascades_to_waiters() {
    let mut scheduler = CompileScheduler::new();
    let module_a = ModuleFullPath::from("mod_a");
    let module_b = ModuleFullPath::from("mod_b");

    scheduler.register_module(module_a.clone(), false);
    scheduler.register_module(module_b.clone(), false);

    // Take A, block on B's symbol.
    let _ = scheduler.take_priority_work();
    scheduler.block_for_typecheck(&module_a, &module_b, &Symbol::from("bar"));

    // Take B.
    let _ = scheduler.take_priority_work();

    // B fails.
    scheduler.notify_module_failed(&module_b, dummy_error("type error in mod_b"));

    // A should also be Failed (cascade). wait_inmem_complete should return Err.
    let result = scheduler.wait_inmem_complete();
    assert!(
        result.is_err(),
        "Expected Err after cascade failure, got Ok"
    );
}

// spec: design/arch/concurrent-pipeline.md §6.5 — wait_inmem_complete returns Err on failure
#[test]
fn test_wait_inmem_complete_returns_err_on_failure() {
    let mut scheduler = CompileScheduler::new();
    let module = ModuleFullPath::from("failing_mod");

    scheduler.register_module(module.clone(), false);
    let _ = scheduler.take_priority_work();

    // Module fails during typecheck.
    scheduler.notify_module_failed(&module, dummy_error("parse error"));

    let result = scheduler.wait_inmem_complete();
    assert!(
        result.is_err(),
        "wait_inmem_complete should return Err when a module has failed"
    );
}

// ============================================================
// 5. Codegen Completion (concurrent-pipeline.md §2.2)
// ============================================================

// spec: design/arch/concurrent-pipeline.md §2.2 — inmem codegen completes module
#[test]
fn test_inmem_codegen_complete_moves_to_complete() {
    let mut scheduler = CompileScheduler::new();
    let module = ModuleFullPath::from("mod_x");

    scheduler.register_module(module.clone(), false);
    let _ = scheduler.take_priority_work();

    // Typecheck done.
    scheduler.notify_typecheck_done(&module);

    // Inmem codegen for the module's only symbol, marking no_remaining=true.
    scheduler.notify_inmem_codegen_complete(&module, &Symbol::from("main"), true);

    // wait_inmem_complete should return Ok since all modules are done.
    let result = scheduler.wait_inmem_complete();
    assert!(
        result.is_ok(),
        "Expected Ok after typecheck + inmem codegen complete"
    );
}

// spec: design/arch/concurrent-pipeline.md §2, §6.5 — full lifecycle
#[test]
fn test_wait_inmem_complete_ok_when_all_complete() {
    let mut scheduler = CompileScheduler::new();
    let mod_a = ModuleFullPath::from("mod_a");
    let mod_b = ModuleFullPath::from("mod_b");

    scheduler.register_module(mod_a.clone(), false);
    scheduler.register_module(mod_b.clone(), false);

    // Take and typecheck A.
    let _ = scheduler.take_priority_work();
    scheduler.notify_symbol_typechecked(&mod_a, &Symbol::from("fn_a"));
    scheduler.notify_typecheck_done(&mod_a);

    // Take and typecheck B.
    let _ = scheduler.take_priority_work();
    scheduler.notify_symbol_typechecked(&mod_b, &Symbol::from("fn_b"));
    scheduler.notify_typecheck_done(&mod_b);

    // Inmem codegen for both modules.
    scheduler.notify_inmem_codegen_complete(&mod_a, &Symbol::from("fn_a"), true);
    scheduler.notify_inmem_codegen_complete(&mod_b, &Symbol::from("fn_b"), true);

    let result = scheduler.wait_inmem_complete();
    assert!(
        result.is_ok(),
        "Expected Ok when all modules complete full lifecycle"
    );
}

// ============================================================
// 6. Single-Threaded Behavior (concurrent-pipeline.md §10.3)
// ============================================================

// spec: design/arch/concurrent-pipeline.md §10.3 — empty scheduler returns None
#[test]
fn test_take_priority_work_returns_none_when_empty() {
    let mut scheduler = CompileScheduler::new();

    // No modules registered — should return None immediately (no blocking).
    let work = scheduler.take_priority_work();
    assert!(
        work.is_none(),
        "Expected None from empty scheduler, got {:?}",
        work
    );
}

// spec: design/arch/concurrent-pipeline.md §6.5 — shutdown
#[test]
fn test_shutdown_flag() {
    let mut scheduler = CompileScheduler::new();
    let module = ModuleFullPath::from("mod_s");

    scheduler.register_module(module.clone(), false);

    // Shutdown should cause take_priority_work to return None.
    scheduler.shutdown();

    let work = scheduler.take_priority_work();
    assert!(
        work.is_none(),
        "Expected None after shutdown, got {:?}",
        work
    );
}

// ============================================================
// Additional edge cases
// ============================================================

// spec: design/arch/concurrent-pipeline.md §6.5 — wait_inmem_complete with no modules
#[test]
fn test_wait_inmem_complete_ok_when_no_modules() {
    let mut scheduler = CompileScheduler::new();

    // No modules registered — vacuously complete.
    let result = scheduler.wait_inmem_complete();
    assert!(
        result.is_ok(),
        "Expected Ok when no modules registered"
    );
}

// spec: design/arch/concurrent-pipeline.md §2.1 — multiple TypecheckFirst maintains FIFO
#[test]
fn test_typecheck_first_fifo_ordering() {
    let mut scheduler = CompileScheduler::new();
    let mod_a = ModuleFullPath::from("first_a");
    let mod_b = ModuleFullPath::from("first_b");

    // Register two TypecheckFirst modules in order.
    scheduler.register_module(mod_a.clone(), true);
    scheduler.register_module(mod_b.clone(), true);

    // Should come out in FIFO order (VecDeque).
    let work1 = scheduler.take_priority_work();
    match work1 {
        Some(PriorityWork::Typecheck(m)) => assert_eq!(m, mod_a, "FIFO: first registered first"),
        other => panic!("Expected Typecheck(first_a), got {:?}", other),
    }

    let work2 = scheduler.take_priority_work();
    match work2 {
        Some(PriorityWork::Typecheck(m)) => assert_eq!(m, mod_b, "FIFO: second registered second"),
        other => panic!("Expected Typecheck(first_b), got {:?}", other),
    }
}

// spec: design/arch/concurrent-pipeline.md §4.2 — priority queue deduplication
#[test]
fn test_priority_queue_deduplicates_symbols() {
    let mut scheduler = CompileScheduler::new();
    let mod_a = ModuleFullPath::from("mod_a");
    let mod_b = ModuleFullPath::from("mod_b");
    let mod_c = ModuleFullPath::from("mod_c");

    // B is typecheck-done (provides the dependency).
    scheduler.register_module(mod_b.clone(), false);
    let _ = scheduler.take_priority_work();
    scheduler.notify_typecheck_done(&mod_b);

    // A is typechecking and blocks on macro needing B/helper.
    scheduler.register_module(mod_a.clone(), false);
    let work_a = scheduler.take_priority_work();
    assert!(matches!(work_a, Some(PriorityWork::Typecheck(_))));
    scheduler.block_for_macro_codegen(
        &mod_a,
        vec![(mod_b.clone(), Symbol::from("helper"))],
    );

    // C is typechecking and also blocks on the same symbol B/helper.
    // NOTE: We must take C BEFORE the priority entry gets claimed.
    // Register C, take C (level 2 priority entry exists but we need
    // to take C first from level 3... Actually level 2 has priority.
    // So we take the priority codegen item first, then take C.
    scheduler.register_module(mod_c.clone(), false);

    // take_priority_work returns the priority codegen (level 2) before C (level 3).
    let work_priority = scheduler.take_priority_work();
    assert!(
        matches!(work_priority, Some(PriorityWork::BlockingJitCodegen(_, _))),
        "Level 2 priority codegen should be returned before level 3, got {:?}",
        work_priority
    );

    // Now take C from level 3.
    let work_c = scheduler.take_priority_work();
    assert!(matches!(work_c, Some(PriorityWork::Typecheck(_))));

    // C blocks on the same macro dependency B/helper.
    scheduler.block_for_macro_codegen(
        &mod_c,
        vec![(mod_b.clone(), Symbol::from("helper"))],
    );

    // The priority queue should have a new entry for B/helper (C's block)
    // since the old entry was already claimed (Working status).
    // Complete the first priority codegen (from A's block).
    scheduler.notify_priority_codegen_complete(&mod_b, &Symbol::from("helper"));

    // A should be unblocked. Check if the second entry also resolves C.
    // The completion of B/helper should unblock both A and C since C's
    // block was added to the same symbol's unblocks list.
    let mut unblocked = vec![];
    for _ in 0..3 {
        match scheduler.take_priority_work() {
            Some(PriorityWork::Typecheck(m)) => unblocked.push(m),
            Some(PriorityWork::BlockingJitCodegen(_, _)) | Some(PriorityWork::JitCodegen(_, _)) => {
                // Second priority entry for C — complete it too.
                scheduler.notify_priority_codegen_complete(&mod_b, &Symbol::from("helper"));
            }
            None => break,
        }
    }
    unblocked.sort();

    let mut expected = vec![mod_a.clone(), mod_c.clone()];
    expected.sort();

    assert_eq!(
        unblocked, expected,
        "Both A and C should be unblocked by completing the shared dependency"
    );
}
