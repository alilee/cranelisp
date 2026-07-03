    use super::*;
    // S87 §2: types formerly reached via the parent's `use cranelisp_types`
    // glob (the impl moved to `lifecycle.rs`); import them directly now.
    use cranelisp_types::{ModuleEntry, Sexp};

    fn test_session(priority_workers: usize) -> (CompilerSession, PathBuf) {
        // Use a unique temp dir per call as project_root so no stray
        // prelude.cl is found. The caller is responsible for removing
        // the dir after the test (or letting the OS reclaim /tmp).
        let stamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0);
        let pid = std::process::id();
        let tmp_root = std::env::temp_dir()
            .join(format!("cranelisp-wave4-{}-{}", pid, stamp));
        std::fs::create_dir_all(&tmp_root).expect("create test project_root");
        let settings = SessionSettings {
            no_color: true,
            no_cache: true,
            codegen_behaviour: CodegenBehaviour::InMemoryAndObject,
            priority_workers,
            nice_workers: 0,
            run_mode: RunMode::Repl,
        };
        let mut s = CompilerSession::new(settings, tmp_root.clone(), "user");
        s.set_lib_dirs(vec![]);
        (s, tmp_root)
    }

    // spec: persistent-workers.md §4.2 — workers park on the priority-work
    // condvar and wake when register_module enqueues work.
    #[test]
    fn persistent_worker_park_and_wake() {
        let (mut s, root) = test_session(1);
        // Worker has been spawned in `new()` and is parked. Register a
        // trivial module — the notify_all on `priority_work_available`
        // wakes the worker.
        let p = root.join("wake.cl");
        s.register_module_with_source("wake", "(defn zero [] 0)", &p)
            .expect("register_module_with_source should succeed");
        // After return: wait_inmem_complete_blocking has observed inmem_done.
        assert!(
            !s.shared.scheduler.is_failed(&ModuleFullPath::from("wake")),
            "module must not have failed",
        );
        // The worker is parked again now (no more work). Shutdown joins it.
        s.shutdown();
        let _ = std::fs::remove_dir_all(&root);
    }

    // spec: persistent-workers.md §5.2 — Drop while work is enqueued calls
    // shutdown() which signals + joins. No panic, no leak.
    #[test]
    fn shutdown_under_load_no_panic() {
        let (mut s, root) = test_session(2);
        // Register a module. workers begin processing.
        let p = root.join("load.cl");
        s.register_module_with_source("load", "(defn a [] 1) (defn b [] 2)", &p)
            .expect("register_module_with_source should succeed");
        // Immediately shutdown (workers may still be mid-loop).
        s.shutdown();
        // Calling shutdown a second time is idempotent.
        s.shutdown();
        let _ = std::fs::remove_dir_all(&root);
    }

    // spec: persistent-workers.md §9.1 — concurrent module registrations
    // all complete; no lost updates.
    #[test]
    fn concurrent_register_module_two_modules_complete() {
        let (mut s, root) = test_session(2);

        // Register module A.
        s.register_module_with_source(
            "concA",
            "(defn a [] 10)",
            &root.join("concA.cl"),
        )
        .expect("register concA");

        // Register module B while A is complete but workers still parked.
        // The persistent pool handles the second registration without
        // respawning anything.
        s.register_module_with_source(
            "concB",
            "(defn b [] 20)",
            &root.join("concB.cl"),
        )
        .expect("register concB");

        // Both modules should be complete (inmem_done), neither failed.
        assert!(!s.shared.scheduler.is_failed(&ModuleFullPath::from("concA")));
        assert!(!s.shared.scheduler.is_failed(&ModuleFullPath::from("concB")));
        s.shutdown();
        let _ = std::fs::remove_dir_all(&root);
    }

    // spec: persistent-workers.md §9.1 — reload_module through the same
    // persistent pool as register_module. Re-register → workers wake →
    // recompile → inmem_done.
    #[test]
    fn reload_during_compile_race_completes() {
        let (mut s, root) = test_session(2);

        // Write a real file so reload_module can read from disk.
        let file_path = root.join("reload_target.cl");
        std::fs::write(&file_path, "(defn original [] 1)\n")
            .expect("seed reload_target.cl");

        // Initial register via the source-explicit path.
        s.register_module_with_source(
            "reload_target",
            "(defn original [] 1)",
            &file_path,
        )
        .expect("initial register");

        // Overwrite with new content and trigger reload.
        std::fs::write(&file_path, "(defn updated [] 2)\n")
            .expect("rewrite reload_target.cl");
        let module = ModuleFullPath::from("reload_target");
        s.reload_module(&module, &file_path)
            .expect("reload should succeed via persistent workers");

        // Module must be in a non-failed state after reload. The post-reload
        // symbol table should carry `updated` (the new defn).
        assert!(!s.shared.scheduler.is_failed(&module));
        let has_updated = s.shared.symbol_tables
            .get(&module)
            .map(|t| t.get("updated").is_some())
            .unwrap_or(false);
        assert!(has_updated, "reloaded module must carry the new defn");

        s.shutdown();
        let _ = std::fs::remove_dir_all(&root);
    }

    // spec: repl/spec.md §3.1 — `/disasm` re-derives the disassembly on demand
    // (Decision 41 / int.md §8.2.1): the handler resolves the symbol in the
    // current module, reads the eagerly-captured `code_size`, and forwards to
    // `cranelisp_backend::produce_disasm` — it does NOT read a stored `disasm`
    // field. On a compiled fn the output MUST carry the `; disasm for` header
    // and a `0x` address line, and MUST NOT be the dead "no disassembly
    // available" string. This pins the S87 rewire at the wiring seam.
    #[test]
    fn handle_disasm_rederives_native_code_for_compiled_fn() {
        let (mut s, root) = test_session(1);
        // Compile a trivial defn into the entry module ("user"), the REPL
        // cursor's default current module — so `handle_disasm`'s
        // `current_module_path()` resolution finds it.
        s.register_module_with_source("user", "(defn zero [] 0)", &root.join("user.cl"))
            .expect("register_module_with_source should compile zero");

        let out = s.handle_disasm("zero");
        assert!(
            out.contains("; disasm for zero"),
            "compiled fn MUST produce the re-derived disasm header, got: {out}"
        );
        assert!(
            out.contains("0x"),
            "re-derived disasm MUST contain native address/byte lines (0x), got: {out}"
        );
        assert!(
            !out.contains("no disassembly available"),
            "compiled fn MUST NOT hit the dead-path string, got: {out}"
        );
        s.shutdown();
        let _ = std::fs::remove_dir_all(&root);
    }

    // S78 in-call-stack restructure: the former
    // `register_dep_for_eval_publish_then_register_is_observable_to_downstream`
    // test probed the deleted `module_sexps` publish-before-register mechanism
    // (the cross-thread parking map is gone — sexps ride the work packet). It
    // is retired; the dep-load behaviour it guarded is covered e2e by the
    // FQ-autoload / dep-chain suite and the H5-replay gate
    // (`tests/repl_persist_race.rs`).

    // spec: design/int/s77-int-restructure.md §3.3 — a dep-registration site
    // (caller blocked on the dep) uses `delays_other=true`, landing the dep in
    // `ModulePool::TypecheckFirst`. After S78 this is the `register_module`
    // call inside `drive_module_dep` / the structural form handlers (the
    // session-side `register_dep_for_eval` no longer registers — the gap-drive
    // already did). Asserts the scheduler contract the priority ordering
    // depends on, against the new packet-carrying `register_module` signature.
    #[test]
    fn dep_registration_uses_delays_other_true() {
        use crate::scheduler::{CompileScheduler, ModulePool};

        fn empty_sexps() -> std::sync::Arc<[Sexp]> {
            std::sync::Arc::from(Vec::new())
        }

        let scheduler = CompileScheduler::new();
        let dep = ModuleFullPath::from("sprint60_e2_dep_pool");

        scheduler.register_module(dep.clone(), empty_sexps(), true);

        let pool = scheduler.module_pool(&dep)
            .expect("dep must be registered");
        assert_eq!(
            pool,
            ModulePool::TypecheckFirst,
            "register_module(_, _, true) MUST land the dep in TypecheckFirst \
             (the scheduler contract the dep-drive priority depends on; \
             observed {:?})",
            pool,
        );

        // Negative: `false` lands the dep in TypecheckNext (entry-module
        // placement).
        let other = ModuleFullPath::from("sprint60_e2_dep_pool_neg");
        scheduler.register_module(other.clone(), empty_sexps(), false);
        let neg_pool = scheduler.module_pool(&other)
            .expect("neg dep must be registered");
        assert_eq!(
            neg_pool, ModulePool::TypecheckNext,
            "register_module(_, _, false) MUST land the dep in TypecheckNext \
             (observed {:?})",
            neg_pool,
        );
    }

    // ══════════════════════════════════════════════════════════════════════
    // Harvest from tests/legacy/wave4_g9.rs (FIXME 0119, S81 W-E /dev int).
    //
    // The legacy file's park/wake, shutdown-under-load, concurrent-register,
    // and reload-during-compile scenarios are ALREADY covered by the tests
    // above (`persistent_worker_park_and_wake`, `shutdown_under_load_no_panic`,
    // `concurrent_register_module_two_modules_complete`,
    // `reload_during_compile_race_completes`). These three harvest tests carry
    // the assertions the existing cluster does NOT: the N-module concurrent
    // register with per-defn `code.is_some()` codegen-population checks, the
    // per-worker JIT isolation across two live sessions (+ a two-thread
    // concurrency guard), and the `thread::scope`-absent close-gate grep.
    // ══════════════════════════════════════════════════════════════════════

    // spec: design/int/persistent-workers.md §4.3 — register enqueues; workers
    //       drain. Stronger than the 2-module check: every defn's `code` field
    //       must be populated after the persistent pool finalizes codegen.
    #[test]
    fn harvest_concurrent_register_many_modules_codegen_populated() {
        let (mut s, root) = test_session(4);
        const MODULE_COUNT: usize = 10;
        for i in 0..MODULE_COUNT {
            let name = format!("modA{i}");
            let file = root.join(format!("{name}.cl"));
            let src = format!("(defn f{i} [] {})", i as i64);
            s.register_module_with_source(&name, &src, &file)
                .unwrap_or_else(|e| panic!("register {name} failed: {e}"));
        }
        for i in 0..MODULE_COUNT {
            let mp = ModuleFullPath::from(format!("modA{i}").as_str());
            assert!(
                !s.shared.scheduler.is_failed(&mp),
                "modA{i} must not be Failed after concurrent register"
            );
            let table = s
                .shared
                .symbol_tables
                .get(&mp)
                .unwrap_or_else(|| panic!("symbol table missing for modA{i}"));
            match table.get(&format!("f{i}")) {
                Some(ModuleEntry::Def { code, .. }) => assert!(
                    code.is_some(),
                    "defn f{i} in modA{i}: code must be Some after persistent-worker codegen"
                ),
                other => panic!("expected Def for f{i} in modA{i}, got {other:?}"),
            }
        }
        s.shutdown();
        let _ = std::fs::remove_dir_all(&root);
    }

    // spec: design/int/persistent-workers.md §4.5 — one JIT per priority worker
    //       (thread-local). Two live sessions with colliding defn names MUST
    //       not share a JIT or leak code pointers; A's shutdown MUST NOT
    //       invalidate B.
    #[test]
    fn harvest_per_worker_jit_isolation_across_sessions() {
        use std::sync::{Arc, Barrier};

        let (mut a, root_a) = test_session(1);
        let (mut b, root_b) = test_session(1);
        a.register_module_with_source("iso", "(defn f [] 111)", &root_a.join("iso.cl"))
            .expect("register into A");
        b.register_module_with_source("iso", "(defn f [] 222)", &root_b.join("iso.cl"))
            .expect("register into B");

        let mp = ModuleFullPath::from("iso");
        for (label, sess) in [("A", &a), ("B", &b)] {
            let tab = sess
                .shared
                .symbol_tables
                .get(&mp)
                .unwrap_or_else(|| panic!("{label}.iso symbol table must exist"));
            match tab.get("f") {
                Some(ModuleEntry::Def { code, .. }) => {
                    assert!(code.is_some(), "{label}.iso/f code must be populated")
                }
                other => panic!("expected Def for {label}.iso/f, got {other:?}"),
            }
        }

        // Shutdown A; B must remain operational.
        a.shutdown();
        let _ = std::fs::remove_dir_all(&root_a);
        b.register_module_with_source("post_a", "(defn g [] 333)", &root_b.join("post_a.cl"))
            .expect("B must still work after A is dropped");
        let post_mp = ModuleFullPath::from("post_a");
        assert!(!b.shared.scheduler.is_failed(&post_mp));
        {
            let b_tab = b
                .shared
                .symbol_tables
                .get(&post_mp)
                .expect("B.post_a symbol table must exist");
            match b_tab.get("g") {
                Some(ModuleEntry::Def { code, .. }) => {
                    assert!(code.is_some(), "B.post_a/g code must be populated after A shutdown")
                }
                other => panic!("expected Def for B.post_a/g, got {other:?}"),
            }
        }
        b.shutdown();
        let _ = std::fs::remove_dir_all(&root_b);

        // Concurrency guard: two sessions operated from their own threads must
        // not deadlock or race (no static/global JIT coupling).
        let barrier = Arc::new(Barrier::new(2));
        let b1 = Arc::clone(&barrier);
        let t1 = std::thread::spawn(move || {
            let (mut s, root) = test_session(1);
            b1.wait();
            s.register_module_with_source("p1", "(defn f [] 1)", &root.join("p1.cl"))
                .expect("p1 register");
            s.shutdown();
            let _ = std::fs::remove_dir_all(&root);
        });
        let t2 = std::thread::spawn(move || {
            let (mut s, root) = test_session(1);
            barrier.wait();
            s.register_module_with_source("p2", "(defn f [] 2)", &root.join("p2.cl"))
                .expect("p2 register");
            s.shutdown();
            let _ = std::fs::remove_dir_all(&root);
        });
        t1.join().expect("thread 1 must not panic");
        t2.join().expect("thread 2 must not panic");
    }

    // spec: design/int/persistent-workers.md §11 acceptance criterion 2 —
    //       `thread::scope` must appear zero times outside `#[cfg(test)]` in
    //       the worker lifecycle files (session_v4.rs / worker.rs / scheduler.rs).
    #[test]
    fn harvest_thread_scope_absent_outside_cfg_test() {
        let src_root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
        let files = [
            src_root.join("session_v4.rs"),
            src_root.join("worker.rs"),
            src_root.join("scheduler.rs"),
        ];
        let mut offenders: Vec<String> = Vec::new();
        for path in &files {
            let content = std::fs::read_to_string(path)
                .unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
            for (lineno, line) in strip_cfg_test_regions(&content) {
                let trimmed = line.trim_start();
                if trimmed.starts_with("//")
                    || trimmed.starts_with("///")
                    || trimmed.starts_with("//!")
                    || trimmed.starts_with("/*")
                    || trimmed.starts_with('*')
                {
                    continue;
                }
                if line.contains("thread::scope") {
                    offenders.push(format!("{}:{}: {}", path.display(), lineno, line.trim()));
                }
            }
        }
        assert!(
            offenders.is_empty(),
            "G9 close gate: `thread::scope` live references outside `#[cfg(test)]`:\n{}",
            offenders.join("\n")
        );
    }

    /// Brace-balanced scanner: return `(line_number, line)` pairs for live
    /// (non-`#[cfg(test)]`) code. Not a full parser — handles the
    /// attribute-on-its-own-line style used in this codebase.
    fn strip_cfg_test_regions(content: &str) -> Vec<(usize, String)> {
        let lines: Vec<&str> = content.lines().collect();
        let mut live: Vec<(usize, String)> = Vec::new();
        let mut i = 0;
        while i < lines.len() {
            let trimmed = lines[i].trim_start();
            if trimmed.starts_with("#[cfg(test)]") {
                i += 1;
                while i < lines.len() && lines[i].trim_start().starts_with("#[") {
                    i += 1;
                }
                if i >= lines.len() {
                    break;
                }
                let item_trim = lines[i].trim_end();
                let opens_block = lines[i].contains('{') && !item_trim.ends_with(';');
                if !opens_block && item_trim.ends_with(';') {
                    i += 1;
                    continue;
                }
                let mut depth: i32 = 0;
                let mut seen_open = false;
                while i < lines.len() {
                    for ch in lines[i].chars() {
                        match ch {
                            '{' => {
                                depth += 1;
                                seen_open = true;
                            }
                            '}' => depth -= 1,
                            _ => {}
                        }
                    }
                    i += 1;
                    if seen_open && depth <= 0 {
                        break;
                    }
                }
                continue;
            }
            live.push((i + 1, lines[i].to_string()));
            i += 1;
        }
        live
    }

    // spec: repl/spec.md §18.8 — S102 W5R B-1 (data-loss Blocker). A successful
    // reload makes the new file content the authority: the reloaded module's
    // retained degraded-startup `failed_forms` MUST be dropped (and the §14.4
    // error block lifted) so the next regen does not re-append stale broken
    // text over the user's external repair — silently undoing the hand-edit
    // and re-poisoning the file for the next restart.
    #[test]
    fn reload_success_drops_failed_forms_and_error_block() {
        let (mut s, root) = test_session(2);

        let file_path = root.join("repairme.cl");
        std::fs::write(&file_path, "(defn fixed [] 1)\n").expect("seed repairme.cl");
        s.register_module_with_source("repairme", "(defn fixed [] 1)", &file_path)
            .expect("initial register");
        let module = ModuleFullPath::from("repairme");

        // Simulate degraded-startup residue: a broken FailedForm retained for
        // the module + the module error-blocked (the §18.8 state).
        s.failed_forms.insert(
            module.clone(),
            vec![FailedForm {
                symbol: Some("broken".into()),
                error: "undefined variable: nope".to_string(),
                text: "(defn broken [] nope)".to_string(),
            }],
        );
        s.error_modules.insert(module.clone());

        // External repair: the user hand-edited the file; the watcher-driven
        // reload succeeds.
        std::fs::write(&file_path, "(defn fixed [] 1)\n(defn broken [] 2)\n")
            .expect("rewrite repairme.cl");
        s.reload_module(&module, &file_path)
            .expect("reload of the repaired file succeeds");

        assert!(
            !s.failed_forms.contains_key(&module),
            "reload success MUST drop the module's stale failed forms — \
             regen would otherwise re-append the broken text after the repair"
        );
        assert!(
            !s.error_modules.contains(&module),
            "reload success MUST lift the module's §14.4 error block"
        );

        s.shutdown();
        let _ = std::fs::remove_dir_all(&root);
    }

    // spec: repl/spec.md §18.8 — S102 W5R M-1. `/reset` clears `error_modules`
    // but MUST also clear `failed_forms` (invariant: a non-empty failed set
    // implies membership in `error_modules`; clearing one without the other
    // leaves regen re-appending stale broken text with the eval gate open).
    #[test]
    fn reset_command_clears_failed_forms_with_error_modules() {
        let (mut s, root) = test_session(1);

        let module = ModuleFullPath::from("user");
        s.failed_forms.insert(
            module.clone(),
            vec![FailedForm {
                symbol: Some("broken".into()),
                error: "type error".to_string(),
                text: "(defn broken [] nope)".to_string(),
            }],
        );
        s.error_modules.insert(module.clone());

        let mut out: Vec<u8> = Vec::new();
        let _ = s.dispatch_command(crate::repl::ReplCommand::Reset, &mut out);

        assert!(
            s.error_modules.is_empty(),
            "/reset clears the error block"
        );
        assert!(
            s.failed_forms.is_empty(),
            "/reset MUST clear failed_forms with error_modules — \
             a dangling failed set keeps re-appending stale text on regen"
        );

        s.shutdown();
        let _ = std::fs::remove_dir_all(&root);
    }
