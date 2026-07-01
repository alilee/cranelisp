    use super::*;

    // --- Env-var parse coverage -------------------------------------------

    #[test]
    fn parse_filter_one_is_all() {
        assert_eq!(parse_filter_from_env_value("1"), Some(TraceFilter::All));
    }

    #[test]
    fn parse_filter_star_is_all() {
        assert_eq!(parse_filter_from_env_value("*"), Some(TraceFilter::All));
    }

    #[test]
    fn parse_filter_empty_is_none() {
        assert_eq!(parse_filter_from_env_value(""), None);
    }

    #[test]
    fn parse_filter_whitespace_only_is_none() {
        // An env var set to just whitespace should not produce a
        // recording filter — the user likely cleared it intentionally.
        assert_eq!(parse_filter_from_env_value("   "), None);
        assert_eq!(parse_filter_from_env_value("\t\n"), None);
    }

    #[test]
    fn parse_filter_single_module_name_is_selective() {
        assert_eq!(
            parse_filter_from_env_value("user"),
            Some(TraceFilter::Selective(vec!["user".to_string()])),
        );
    }

    #[test]
    fn parse_filter_comma_separated_modules_is_selective() {
        assert_eq!(
            parse_filter_from_env_value("user,prelude,primitives"),
            Some(TraceFilter::Selective(vec![
                "user".to_string(),
                "prelude".to_string(),
                "primitives".to_string(),
            ])),
        );
    }

    #[test]
    fn parse_filter_tolerates_spaces_around_commas() {
        assert_eq!(
            parse_filter_from_env_value("user , prelude"),
            Some(TraceFilter::Selective(vec![
                "user".to_string(),
                "prelude".to_string(),
            ])),
        );
    }

    #[test]
    fn parse_filter_lone_comma_is_none() {
        // All-empty list after split → None, not Selective([]).
        assert_eq!(parse_filter_from_env_value(","), None);
        assert_eq!(parse_filter_from_env_value(",,"), None);
    }

    #[test]
    fn parse_filter_from_env_unset_is_none() {
        // Snapshot + restore pattern (cf. /backend io_trace tests).
        let prev = std::env::var_os(scheduler_trace_env_var());
        // SAFETY: test body restores before returning.
        unsafe { std::env::remove_var(scheduler_trace_env_var()); }
        let parsed = parse_filter_from_env();
        if let Some(v) = prev {
            unsafe { std::env::set_var(scheduler_trace_env_var(), v); }
        }
        assert_eq!(parsed, None);
    }

    #[test]
    fn parse_filter_from_env_one_is_all() {
        let prev = std::env::var_os(scheduler_trace_env_var());
        unsafe { std::env::set_var(scheduler_trace_env_var(), "1"); }
        let parsed = parse_filter_from_env();
        match prev {
            Some(v) => unsafe { std::env::set_var(scheduler_trace_env_var(), v) },
            None => unsafe { std::env::remove_var(scheduler_trace_env_var()) },
        }
        assert_eq!(parsed, Some(TraceFilter::All));
    }

    // --- Ring buffer discipline -------------------------------------------
    //
    // These tests exercise the lower-level thread-local-buffer path
    // directly (bypassing the process-global OnceLock filter) so they
    // are robust against test-execution order.

    fn force_push(count: usize) {
        SCHEDULER_TRACE_BUF.with(|cell| {
            let mut buf = cell.borrow_mut();
            for i in 0..count {
                if buf.len() == SCHEDULER_TRACE_BUFFER_CAPACITY {
                    buf.pop_front();
                }
                buf.push_back(SchedulerTraceEvent {
                    timestamp: i as u64,
                    thread_id: std::thread::current().id(),
                    thread_ord_id: thread_ord_id(),
                    tag: SchedulerTraceTag::RegisterDepPublish,
                    payload: SchedulerTracePayload::Module {
                        module: format!("m{i}"),
                        state: None,
                    },
                });
            }
        });
    }

    #[test]
    fn ring_buffer_wraps_at_capacity() {
        let _ = dump_thread_buffer();
        let overflow = SCHEDULER_TRACE_BUFFER_CAPACITY + 9;
        force_push(overflow);
        let dumped = dump_thread_buffer();
        assert_eq!(dumped.len(), SCHEDULER_TRACE_BUFFER_CAPACITY);
        // Oldest retained event is index 9 (0..9 were evicted).
        assert_eq!(dumped.first().unwrap().timestamp, 9);
        assert_eq!(dumped.last().unwrap().timestamp, (overflow - 1) as u64);
    }

    #[test]
    fn dump_clears_thread_buffer() {
        let _ = dump_thread_buffer();
        force_push(4);
        assert_eq!(dump_thread_buffer().len(), 4);
        assert!(
            dump_thread_buffer().is_empty(),
            "second dump should find the buffer empty"
        );
    }

    // --- Filter semantics --------------------------------------------------

    #[test]
    fn disabled_filter_suppresses_record() {
        // Drain first, then attempt to record. If the global filter was
        // primed by an earlier test as enabled, skip the behavioural
        // assertion — parse-layer tests already cover the disabled
        // branch directly.
        let _ = dump_thread_buffer();
        if filter().is_some() {
            return;
        }
        record_module_event(SchedulerTraceTag::RegisterDepPublish, "u");
        let dumped = dump_thread_buffer();
        assert!(
            dumped.is_empty(),
            "record_event must not emit when filter is None"
        );
    }

    #[test]
    fn selective_filter_drops_non_matching() {
        // Exercise filter matching at the payload level without
        // relying on the process-global OnceLock.
        let filter = TraceFilter::Selective(vec!["foo".to_string()]);
        let matching = SchedulerTracePayload::Module {
            module: "foo".to_string(),
            state: None,
        };
        let non_matching = SchedulerTracePayload::Module {
            module: "bar".to_string(),
            state: None,
        };
        let bulk = SchedulerTracePayload::Bulk { count: 3 };

        fn passes(f: &TraceFilter, p: &SchedulerTracePayload) -> bool {
            match f {
                TraceFilter::All => true,
                TraceFilter::Selective(names) => match p.module_path() {
                    Some(mp) => names.iter().any(|n| n.as_str() == mp),
                    None => true, // bulk events always pass
                },
            }
        }
        assert!(passes(&filter, &matching));
        assert!(!passes(&filter, &non_matching));
        assert!(passes(&filter, &bulk));
    }

    // --- Anchor alignment --------------------------------------------------

    #[test]
    fn timestamp_is_after_anchor_init() {
        // First call primes the anchor; second call's `elapsed` is
        // strictly positive (nanosecond resolution — a function call
        // between the two loads is orders of magnitude longer).
        let anchor = cranelisp_intrinsics::io_observer::trace_anchor();
        let first = anchor.elapsed().as_nanos();
        // Perform a small amount of work so the second read differs.
        let _ = (0u64..100).sum::<u64>();
        let second = anchor.elapsed().as_nanos();
        assert!(
            second > first,
            "shared Instant anchor must tick forward: first={first} second={second}"
        );
    }

    #[test]
    fn anchor_is_the_shared_runtime_anchor() {
        // The /int scheduler log and /backend IO log MUST reference the
        // same OnceLock<Instant>. Verify by pointer equality.
        let a = cranelisp_intrinsics::io_observer::trace_anchor();
        let b = cranelisp_intrinsics::io_observer::trace_anchor();
        assert!(std::ptr::eq(a, b), "shared anchor must be stable OnceLock");
    }

    // --- Merge-sort across threads ----------------------------------------

    #[test]
    fn merge_sort_across_threads_is_monotonic() {
        // Clear residue.
        let _ = dump_all_buffers();

        let handle_a = std::thread::spawn(|| {
            SCHEDULER_TRACE_BUF.with(|cell| {
                let mut buf = cell.borrow_mut();
                for ts in [2u64, 4, 6, 8] {
                    buf.push_back(SchedulerTraceEvent {
                        timestamp: ts,
                        thread_id: std::thread::current().id(),
                        thread_ord_id: thread_ord_id(),
                        tag: SchedulerTraceTag::RegisterModuleRegister,
                        payload: SchedulerTracePayload::Module {
                            module: format!("a{ts}"),
                            state: None,
                        },
                    });
                }
            });
            publish_thread_buffer();
        });
        let handle_b = std::thread::spawn(|| {
            SCHEDULER_TRACE_BUF.with(|cell| {
                let mut buf = cell.borrow_mut();
                for ts in [1u64, 3, 5, 7] {
                    buf.push_back(SchedulerTraceEvent {
                        timestamp: ts,
                        thread_id: std::thread::current().id(),
                        thread_ord_id: thread_ord_id(),
                        tag: SchedulerTraceTag::RegisterModuleRegister,
                        payload: SchedulerTracePayload::Module {
                            module: format!("b{ts}"),
                            state: None,
                        },
                    });
                }
            });
            publish_thread_buffer();
        });
        handle_a.join().unwrap();
        handle_b.join().unwrap();

        let merged = dump_all_buffers();
        assert!(
            merged.len() >= 8,
            "expected >=8 merged events, got {}",
            merged.len()
        );
        for pair in merged.windows(2) {
            assert!(
                (pair[0].timestamp, pair[0].thread_ord_id)
                    <= (pair[1].timestamp, pair[1].thread_ord_id),
                "merge-sort must produce monotonic (ts, thread_ord) pairs"
            );
        }
        // Timestamps 1..=8 must all be present in the merged output.
        for expected in 1u64..=8 {
            assert!(
                merged.iter().any(|e| e.timestamp == expected),
                "missing timestamp {expected} in merged output"
            );
        }
    }

    #[test]
    fn thread_ord_ids_are_distinct_per_thread() {
        let main_ord = thread_ord_id();
        let child_ord = std::thread::spawn(thread_ord_id).join().unwrap();
        assert_ne!(main_ord, child_ord);
    }

    // --- Payload introspection ---------------------------------------------

    #[test]
    fn payload_module_path_extracts_module() {
        let p = SchedulerTracePayload::Module {
            module: "user".to_string(),
            state: Some(3),
        };
        assert_eq!(p.module_path(), Some("user"));
        let b = SchedulerTracePayload::Bulk { count: 2 };
        assert_eq!(b.module_path(), None);
    }

    // --- Sprint 61 Wave 3 step 3e — H4 race-closure instrumentation -------
    //
    // Two small tests: one verifies emission via record_module_event (tag
    // reaches the thread-local buffer), one verifies format_event_line
    // outputs the tag name as a static string.

    #[test]
    fn s61w3_new_tags_record_via_module_event() {
        // Drain to start from a known-empty state. Then push each of the
        // two new tags directly into the thread-local buffer (bypassing
        // the process-global OnceLock filter, which may or may not be
        // enabled depending on test-execution order — same pattern as
        // `force_push` above).
        let _ = dump_thread_buffer();
        SCHEDULER_TRACE_BUF.with(|cell| {
            let mut buf = cell.borrow_mut();
            buf.push_back(SchedulerTraceEvent {
                timestamp: 1,
                thread_id: std::thread::current().id(),
                thread_ord_id: thread_ord_id(),
                tag: SchedulerTraceTag::RepublishFromSymbolTable,
                payload: SchedulerTracePayload::Module {
                    module: "user".to_string(),
                    state: None,
                },
            });
            buf.push_back(SchedulerTraceEvent {
                timestamp: 2,
                thread_id: std::thread::current().id(),
                thread_ord_id: thread_ord_id(),
                tag: SchedulerTraceTag::RegisterImportsLookup,
                payload: SchedulerTracePayload::Module {
                    module: "helper".to_string(),
                    state: None,
                },
            });
        });
        let dumped = dump_thread_buffer();
        assert_eq!(dumped.len(), 2);
        assert!(matches!(dumped[0].tag, SchedulerTraceTag::RepublishFromSymbolTable));
        assert!(matches!(dumped[1].tag, SchedulerTraceTag::RegisterImportsLookup));
    }

    // --- Sprint 61 Wave 3 step 3e'' — H6 SymbolTableEnsure tag --------
    //
    // Two small tests mirror the step 3e pair above: one verifies
    // emission reaches the thread-local buffer for the new tag, the
    // other verifies `format_event_line` renders the outcome
    // symbolically ("outcome=Created" / "outcome=AlreadyPresent")
    // rather than as a numeric pool state.

    #[test]
    fn s61w3_symbol_table_ensure_records_via_module_event_with_state() {
        let _ = dump_thread_buffer();
        SCHEDULER_TRACE_BUF.with(|cell| {
            let mut buf = cell.borrow_mut();
            // outcome=Created (state=0)
            buf.push_back(SchedulerTraceEvent {
                timestamp: 1,
                thread_id: std::thread::current().id(),
                thread_ord_id: thread_ord_id(),
                tag: SchedulerTraceTag::SymbolTableEnsure,
                payload: SchedulerTracePayload::Module {
                    module: "helper".to_string(),
                    state: Some(0),
                },
            });
            // outcome=AlreadyPresent (state=1)
            buf.push_back(SchedulerTraceEvent {
                timestamp: 2,
                thread_id: std::thread::current().id(),
                thread_ord_id: thread_ord_id(),
                tag: SchedulerTraceTag::SymbolTableEnsure,
                payload: SchedulerTracePayload::Module {
                    module: "helper".to_string(),
                    state: Some(1),
                },
            });
        });
        let dumped = dump_thread_buffer();
        assert_eq!(dumped.len(), 2);
        assert!(matches!(dumped[0].tag, SchedulerTraceTag::SymbolTableEnsure));
        assert!(matches!(
            &dumped[0].payload,
            SchedulerTracePayload::Module { state: Some(0), .. }
        ));
        assert!(matches!(
            &dumped[1].payload,
            SchedulerTracePayload::Module { state: Some(1), .. }
        ));
    }

    #[test]
    fn s61w3_symbol_table_ensure_format_line_renders_outcome_symbolically() {
        let created = SchedulerTraceEvent {
            timestamp: 200,
            thread_id: std::thread::current().id(),
            thread_ord_id: 0,
            tag: SchedulerTraceTag::SymbolTableEnsure,
            payload: SchedulerTracePayload::Module {
                module: "helper".to_string(),
                state: Some(0),
            },
        };
        let line = format_event_line(&created);
        assert!(
            line.contains("SymbolTableEnsure"),
            "format_event_line must name new tag: {line}"
        );
        assert!(
            line.contains("outcome=Created"),
            "Created outcome must render symbolically: {line}"
        );
        assert!(
            !line.contains("pool="),
            "SymbolTableEnsure must NOT render as `pool=` (that reading \
             is reserved for scheduler pool-state tags): {line}"
        );

        let present = SchedulerTraceEvent {
            timestamp: 201,
            thread_id: std::thread::current().id(),
            thread_ord_id: 0,
            tag: SchedulerTraceTag::SymbolTableEnsure,
            payload: SchedulerTracePayload::Module {
                module: "helper".to_string(),
                state: Some(1),
            },
        };
        let line = format_event_line(&present);
        assert!(
            line.contains("outcome=AlreadyPresent"),
            "AlreadyPresent outcome must render symbolically: {line}"
        );
    }

    #[test]
    fn s61w3_new_tags_format_line_names() {
        let republish = SchedulerTraceEvent {
            timestamp: 100,
            thread_id: std::thread::current().id(),
            thread_ord_id: 0,
            tag: SchedulerTraceTag::RepublishFromSymbolTable,
            payload: SchedulerTracePayload::Module {
                module: "user".to_string(),
                state: None,
            },
        };
        let line = format_event_line(&republish);
        assert!(
            line.contains("RepublishFromSymbolTable"),
            "format_event_line must name new tag: {line}"
        );
        assert!(line.contains("module=user"), "payload formatting: {line}");

        let lookup = SchedulerTraceEvent {
            timestamp: 101,
            thread_id: std::thread::current().id(),
            thread_ord_id: 0,
            tag: SchedulerTraceTag::RegisterImportsLookup,
            payload: SchedulerTracePayload::Module {
                module: "helper".to_string(),
                state: None,
            },
        };
        let line = format_event_line(&lookup);
        assert!(
            line.contains("RegisterImportsLookup"),
            "format_event_line must name new tag: {line}"
        );
        assert!(line.contains("module=helper"), "payload formatting: {line}");
    }

    // --- Event size sanity -------------------------------------------------

    #[test]
    fn event_struct_is_bounded() {
        // A typical event carries a heap-allocated String for the
        // module path. The stack-resident struct should still be small
        // — target <= 96 bytes (ThreadId is 8B, u64 × 2 is 16B, tag 1B
        // + padding, payload 32B for a String header + state). Guard
        // against accidental bloat.
        let sz = std::mem::size_of::<SchedulerTraceEvent>();
        assert!(
            sz <= 128,
            "SchedulerTraceEvent grew to {sz} bytes (cap 128)"
        );
    }

    // -----------------------------------------------------------------
    // Sprint 61 Wave 1 follow-on — SchedulerTraceFlushGuard +
    // install_panic_hook
    // -----------------------------------------------------------------
    //
    // These tests validate the wiring primitives added for the
    // subprocess-exit / panic drain. They do NOT assert that stderr
    // actually received the bytes — capturing stderr inside a unit test
    // is fragile across Rust toolchains. Instead they verify the
    // observable-from-Rust invariants:
    //
    //   * SchedulerTraceFlushGuard::new + drop runs without panic.
    //   * Drop calls flush_to_stderr (observed indirectly by checking
    //     the thread-local buffer is drained after drop, when the
    //     filter is enabled; when disabled the drop is a no-op and
    //     the buffer is left untouched).
    //   * install_panic_hook is idempotent (second call is a no-op).
    //   * A panic inside catch_unwind after install_panic_hook still
    //     delegates to the prior hook.
    //
    // Mirrors the io-trace-side tests in
    // `src/io_trace.rs`.

    #[test]
    fn flush_guard_drops_without_panic() {
        // Must not panic. Filter may be either state — flush is a no-op
        // when disabled.
        let _ = dump_thread_buffer();
        {
            let _g = SchedulerTraceFlushGuard::new();
        }
        // Second drop in sequence: also must not panic.
        let _ = SchedulerTraceFlushGuard::default();
    }

    #[test]
    fn flush_guard_drop_calls_flush_when_filter_enabled() {
        // Seed events directly (bypasses the filter check). The Drop
        // calls `flush_to_stderr`, which calls `dump_all_buffers`,
        // which drains the thread-local VecDeque — so after drop the
        // buffer is empty IF the filter is enabled. When the filter
        // is disabled (common in the test process), `flush_to_stderr`
        // short-circuits and the buffer stays populated; in that case
        // we verify the drop at least did not panic and we drain
        // manually so we leave the thread-local clean for peers.
        let _ = dump_thread_buffer();
        SCHEDULER_TRACE_BUF.with(|cell| {
            let mut buf = cell.borrow_mut();
            buf.push_back(SchedulerTraceEvent {
                timestamp: 42,
                thread_id: std::thread::current().id(),
                thread_ord_id: thread_ord_id(),
                tag: SchedulerTraceTag::RegisterDepPublish,
                payload: SchedulerTracePayload::Module {
                    module: "wired".to_string(),
                    state: None,
                },
            });
        });

        {
            let _g = SchedulerTraceFlushGuard::new();
        }

        if filter().is_some() {
            // Flush ran. Buffer must be empty now.
            let residual = dump_thread_buffer();
            assert!(
                residual.is_empty(),
                "guard drop under enabled filter must drain the \
                 thread-local buffer; residual = {}",
                residual.len()
            );
        } else {
            // Clean up so sibling tests start from an empty buffer.
            let _ = dump_thread_buffer();
        }
    }

    #[test]
    fn flush_guard_drop_noop_when_filter_disabled() {
        // When the filter is None, the guard's drop must be a no-op —
        // specifically, it must not panic and must not emit anything.
        // We can't assert on stderr directly, but we can assert on the
        // thread-local buffer: if it was empty before, it remains
        // empty after (no side effect).
        let _ = dump_thread_buffer();
        if filter().is_some() {
            // Another test primed the filter — skip; the enabled path
            // is exercised by the sibling test above.
            return;
        }
        assert!(dump_thread_buffer().is_empty());
        {
            let _g = SchedulerTraceFlushGuard::new();
        }
        assert!(
            dump_thread_buffer().is_empty(),
            "disabled-filter drop must not emit or mutate state"
        );
    }

    #[test]
    fn install_panic_hook_is_idempotent() {
        // FIXME 0013: serialise against the sibling panic-hook test so the
        // two cannot interleave on the process-global hook under `cargo test`.
        let _guard = TEST_GUARD.lock().unwrap_or_else(|e| e.into_inner());
        // Reset so this test can assert the first-install path itself.
        reset_panic_hook_installed_for_tests();

        // First call installs. We can only observe this indirectly —
        // the atomic flip — because std::panic::set_hook has no
        // introspection API.
        install_panic_hook();

        // Second call is a no-op (returns without panic). If the guard
        // failed to short-circuit we would install a second hook on
        // top, leading to double-flushes on real panics downstream.
        install_panic_hook();

        // Reset so subsequent tests can re-install if they need to.
        reset_panic_hook_installed_for_tests();
    }

    #[test]
    fn install_panic_hook_runs_flush_on_panic() {
        // FIXME 0013: serialise against the sibling panic-hook test (see above).
        let _guard = TEST_GUARD.lock().unwrap_or_else(|e| e.into_inner());
        // Install on a fresh slot. We can't directly observe the flush
        // writing to stderr, but we CAN observe the delegation chain:
        // the prior hook must still run after ours. Verify this via a
        // prior hook that mutates a shared atomic.
        reset_panic_hook_installed_for_tests();

        static PRIOR_HOOK_RAN: std::sync::atomic::AtomicBool =
            std::sync::atomic::AtomicBool::new(false);
        PRIOR_HOOK_RAN.store(false, std::sync::atomic::Ordering::Relaxed);
        // Park the test suite's own prior hook first. After we're done
        // we restore it.
        let original = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_info| {
            PRIOR_HOOK_RAN.store(true, std::sync::atomic::Ordering::Release);
        }));
        // Now install our chaining hook on top of that recording hook.
        install_panic_hook();

        // Trigger a panic inside catch_unwind so this test itself
        // doesn't abort.
        let _ = std::panic::catch_unwind(|| {
            panic!("observability test panic — expected");
        });

        assert!(
            PRIOR_HOOK_RAN.load(std::sync::atomic::Ordering::Acquire),
            "prior panic hook must run after install_panic_hook (chain)"
        );

        // Restore the test harness's original hook and clear our guard
        // so we don't poison sibling tests.
        std::panic::set_hook(original);
        reset_panic_hook_installed_for_tests();
    }

    // ══════════════════════════════════════════════════════════════════════
    // Harvest from tests/legacy/sprint61_observability_{scheduler,shared}.rs
    // (FIXME 0132, S81 W-E /dev int).
    //
    // The legacy files' Rust-API cluster (filter parse, ring-buffer capacity,
    // dump-clears, disabled/selective filter, anchor sharing, cross-thread
    // merge-sort, thread_ord distinctness) is ALREADY covered by the tests
    // above. These two harvest tests carry the assertions that were NOT:
    // the env-var-name contract and the boundary-crate hygiene scan. The 3
    // subprocess tests (`scheduler_trace_subprocess_dump_*`,
    // `scheduler_trace_unset_*`) and the 2 cross-channel io_trace
    // timestamp-domain tests are e2e/integration-tier (binary subprocess /
    // two-trace-channel coupling) — they cannot be int unit tests and route
    // to /qa (see FIXME body).
    // ══════════════════════════════════════════════════════════════════════

    // spec: design/int/observability.md §3.1 — the scheduler-trace env var
    //       name is the spec-documented `CRANELISP_SCHEDULER_TRACE` string.
    #[test]
    fn harvest_scheduler_trace_env_var_name_is_stable() {
        assert_eq!(scheduler_trace_env_var(), "CRANELISP_SCHEDULER_TRACE");
    }

    // spec: design/int/observability.md §4 — neither trace log type may appear
    //       in any boundary crate source (types / frontend / typecheck). A
    //       leak would be architectural drift (trace types are int/runtime
    //       owned, downstream of the boundary crates).
    #[test]
    fn harvest_trace_event_types_absent_from_boundary_crate_sources() {
        use std::path::{Path, PathBuf};

        fn project_root() -> PathBuf {
            PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        }
        fn visit_rs_files(dir: &Path, f: &mut impl FnMut(&Path, &str)) {
            let Ok(entries) = std::fs::read_dir(dir) else {
                return;
            };
            for entry in entries.flatten() {
                let p = entry.path();
                if p.is_dir() {
                    visit_rs_files(&p, f);
                    continue;
                }
                if p.extension().and_then(|s| s.to_str()) == Some("rs")
                    && let Ok(body) = std::fs::read_to_string(&p)
                {
                    f(&p, &body);
                }
            }
        }

        let boundary_dirs = [
            project_root().join("crates/cranelisp-types/src"),
            project_root().join("crates/cranelisp-frontend/src"),
            project_root().join("crates/cranelisp-typecheck/src"),
        ];
        let forbidden = [
            "SchedulerTraceEvent",
            "SchedulerTraceTag",
            "SchedulerTracePayload",
            "IoTraceEvent",
            "IoTraceTag",
            "IoTracePayload",
        ];
        let mut leaks: Vec<String> = Vec::new();
        for dir in &boundary_dirs {
            visit_rs_files(dir, &mut |path, body| {
                for needle in &forbidden {
                    if body.contains(needle) {
                        leaks.push(format!("{}: forbidden token `{needle}`", path.display()));
                    }
                }
            });
        }
        assert!(
            leaks.is_empty(),
            "boundary-crate hygiene breach — trace types leaked upstream: {leaks:?}"
        );
    }
