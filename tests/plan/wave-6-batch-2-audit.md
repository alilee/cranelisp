# Wave 6 batch 2 — sprint23.rs audit

Per-test audit of `tests/sprint23.rs` (61 tests, 2744 LOC).

Author: `/qa` (audit-only dispatch, 2026-05-04). Methodology: per-test
review against the 20 e2e carry-forward files, with Wave 5.6 disposition
codes (COVERED / DUPLICATE-IN-LEGACY / GAP-COVER / REGRESSION-GUARD /
GAP-HARVEST). Same per-test framework as the sketch_port, ring0, ring1,
ring2, e2e and Wave 6 batch 1 audits.

## Methodology recap

Per Wave 5.6 brief (in force from Waves 5.5/5.6):

1. No exact 1:1 duplicates after `[Tested ...]` carry-forward exists.
2. Multi-angle on same spec property → PRESERVE.
3. Regression-named tests are presumptively discriminating — default
   to GAP-COVER (REGRESSION-GUARD) unless EXACT 1:1 duplicate is provable.
4. Spec-anchoring is the dedup criterion, not source-shape match.

**Cluster character.** `tests/sprint23.rs` is the Sprint 23 work-product
file: 61 e2e (subprocess-driven) tests covering five Sprint 23
deliverables — Executable Generation (`--link`), Shell Escape (`/sh`),
File Watching, REPL Cache Integration, Session Persistence (`user.cl`).
Plus a tail of three subsequent regression carries: batch-mode `main`
acceptance, the Sprint 58/61 heisenbug suite, and the H5 RAII guard
invariant tests added in Sprint 61 Wave 3 step 3f.

Heavy regression-naming: 13 tests carry `_neg_`, `_bug{N}_`, `_repro_`,
`_heisenbug_`, `h5_`, or `_does_not_` markers — presumptively
discriminating. Three tests carry inline `FIXME(/int)` defect handles
(`link_multi_module_project`, `persist_import_survives_restart`,
`heisenbug_race_reduced_concurrent_import_pairs`).

**Carry-forward coverage of the cluster's surface is essentially zero.**
Searches against the 20 e2e carry-forward files turn up:

- `--link` covered only by `build_confidence.rs::smoke_link_then_run_executable_matches_run_exit`
  (a single happy-path smoke); no error-case `--link` coverage; no
  multi-module `--link` coverage; no `--no-cache + --link` rejection coverage.
- `/sh` shell escape: ZERO carry-forward coverage. spec/repl/spec.md §13
  has no `[Tested]` annotations cited in any carry-forward file.
- File watching (repl/spec.md §14): ZERO carry-forward coverage.
- Session persistence (`user.cl`, repl/spec.md §15): ZERO carry-forward
  coverage. `repl_lifecycle.rs::defn_persists_across_evals` and
  `repl_introspection.rs::defn_persists_across_evals` cover §15.2
  *within-session* persistence but NOT across-restart persistence
  (the `user.cl` regen + reload loop).
- REPL cache integration: `cache.rs::cache_repl_restart_cache_hit` +
  `cache_repl_incremental_monomorphisation` cover the *batch-mode*
  cache restart flow; sprint23.rs's three `cache_repl_*` tests cover
  the *interactive REPL session* cache write/load/reset surface, which
  is a distinct angle.
- Batch-mode main: covered well by `build_confidence.rs::smoke_run_zero_arg_main_exits_zero`
  + the `mode_equiv_*` family. Sprint23.rs's three `batch_main_*`
  tests are partially redundant.
- Heisenbug + H5 gate tests: ZERO carry-forward coverage. These are
  named regression guards for documented Sprint 58/61 race defects.

Therefore dispositions skew heavily to GAP-COVER and REGRESSION-GUARD,
with one cluster (`batch_main_*`) flagged as DUPLICATE-IN-LEGACY.

## Summary

| Disposition | Count |
|---|---:|
| COVERED | 0 |
| DUPLICATE-IN-LEGACY | 2 |
| GAP-COVER | 59 (of which REGRESSION-GUARD: 28) |
| GAP-HARVEST | 0 |
| **Total** | **61** |

Of the 28 REGRESSION-GUARD findings:

- 13 explicit regression-name patterns (`_neg_`, `_bug{N}_`, `_repro_`,
  `_does_not_`, `heisenbug_`, `h5_`)
- 8 file-watching tests with documented Sprint 47/58/59 defect anchors
  (cascade invalidation, self-write suppression, error blocking,
  retry-on-next-change)
- 3 explicit `FIXME(/int)` regression carries
  (`link_multi_module_project`, `persist_import_survives_restart`,
  `cache_repl_loads_heisenbug_parallel_stress`)
- 4 heisenbug + H5 gate tests
  (`heisenbug_race_reduced_concurrent_import_pairs`,
  `h5_gate_typechecking_user_fires_only_on_repl_thread`,
  `h5_normal_completion_does_not_starve_repl_eval_thread`,
  plus the older `cache_repl_loads_heisenbug_parallel_stress` already
  counted)

The remaining 31 GAP-COVER tests are positive-path coverage of
Sprint-23-delivered surface that has no carry-forward today.

## Per-test classifications

### 1. Executable Generation (--link), tests 1–10

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 1 | `link_hello_world_produces_executable` | design/backend/executable-generation.md §3 — end-to-end --link flow | minimal `(defn main [] 42)` → `--link`, exe exists, exit 42 | GAP-COVER | partial overlap with `build_confidence.rs::smoke_link_then_run_executable_matches_run_exit`, but that test asserts exit 42 via a bigger program (with `add-i64`), this is the minimal happy path. PRESERVE per multi-angle rule. Carry to `build_confidence.rs` (extend `smoke_link_*`) or new dedicated `link.rs` |
| 2 | `link_main_returns_int_exit_code` | design/backend/executable-generation.md §7 — main :: () → Int | exit 0 case | GAP-COVER | the zero-exit angle; carry to `build_confidence.rs` or new `link.rs` |
| 3 | `link_main_returns_io` | design/backend/executable-generation.md §7 — main :: () → IO _ | IO trampoline + `Pure 0` exit | REGRESSION-GUARD | named property not in any carry-forward; the test is itself defensive (graceful failure path if IO main is not yet supported). Sprint 23 deliverable C-1. Carry to `link.rs` |
| 4 | `link_default_output_is_entry_stem` | design/backend/executable-generation.md §9 — output path default | `examples/hello.cl` → `hello` (no extension) | GAP-COVER | the output-naming convention angle; not asserted anywhere in carry-forward. Carry to `link.rs` |
| 5 | `link_error_no_main_function` | design/backend/executable-generation.md §7 — no main function | error mentions "main" | REGRESSION-GUARD | named negative path; not asserted in carry-forward. Carry to `link.rs` |
| 6 | `link_error_main_wrong_return_type` | design/backend/executable-generation.md §7 — main wrong type | `main` returns String → error mentions Int or IO | REGRESSION-GUARD | negative path; carry to `link.rs` |
| 7 | `link_error_file_not_found` | design/backend/executable-generation.md §5.4 — entry file not found | exit code 1 + error | REGRESSION-GUARD | negative path; carry to `link.rs` |
| 8 | `link_error_missing_bundle_library` | design/backend/executable-generation.md §9 — missing bundle library | error mentions cranelisp_exe_bundle | REGRESSION-GUARD | best-effort env-removed test; named environment-dependent failure path. Carry to `link.rs` (preserve best-effort guard) |
| 9 | `link_with_no_cache_is_rejected` | design/backend/executable-generation.md §9 — `--no-cache` + `--link` | error contains "--no-cache is not supported with --link" | REGRESSION-GUARD | named CLI flag-conflict assertion; not asserted in carry-forward. Carry to `link.rs` |
| 10 | `link_reuses_cached_object_files` | design/backend/executable-generation.md §3 — cache reuse on second `--link` | two `--link` runs both produce working exe | GAP-COVER | the "second `--link` re-produces exe after `rm hello`" angle; cache-side overlap with `cache.rs::cache_quick_build_links_cached_objects` but that test asserts mtime preservation, this asserts re-emission after exe deletion. PRESERVE — distinct angle. Carry to `link.rs` |
| 11 | `link_multi_module_project` | design/backend/executable-generation.md §3 — module graph compilation | 2-module project: `main.cl` imports `helper.cl` → exit 42 | REGRESSION-GUARD | carries inline `FIXME(/int)` Sprint 58 Wave 2c — `--link` cannot resolve `___cranelisp_got_helper`. Highest-value `--link` regression guard. Carry to `link.rs` (preserve FIXME) |

### 2. Shell Escape (/sh), tests 12–22

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 12 | `shell_escape_basic_echo` | repl/spec.md §13.2 — command execution via /bin/sh | basic `/sh echo` works | GAP-COVER | repl/spec.md §13 has zero carry-forward today; primary positive path. Carry to new `repl_shell.rs` |
| 13 | `shell_escape_output_passthrough` | repl/spec.md §13.3 — stdout passthrough | quoted echo passes through | GAP-COVER | distinct angle (quoted args + passthrough). Carry to `repl_shell.rs` |
| 14 | `shell_escape_nonzero_exit_code` | repl/spec.md §13.4 — non-zero exit displayed | `/sh false` shows "exit status: 1" | GAP-COVER | carry to `repl_shell.rs` |
| 15 | `shell_escape_zero_exit_silent` | repl/spec.md §13.4 — zero exit silence | `/sh true` does NOT print exit status | REGRESSION-GUARD | negative-name pattern (silence); §13.4 boundary. Carry to `repl_shell.rs` |
| 16 | `shell_escape_command_not_found` | repl/spec.md §13.4 — command not found | error or exit-127 reported | GAP-COVER | error path; carry to `repl_shell.rs` |
| 17 | `shell_escape_empty_command` | repl/spec.md §13.6 — empty command silently re-prompts | `/sh\n/sh   \n` produces no error | REGRESSION-GUARD | negative-name pattern (silent re-prompt); §13.6 edge case. Carry to `repl_shell.rs` |
| 18 | `shell_escape_chained_commands` | repl/spec.md §13.6 — multi-line not supported, use shell syntax | `/sh echo first && echo second` | GAP-COVER | chained-shell-syntax angle; carry to `repl_shell.rs` |
| 19 | `shell_escape_no_state_interaction` | repl/spec.md §13.5 — no REPL state interaction | defn → /sh → call defn — defn still works | GAP-COVER | session-state-survival angle; carry to `repl_shell.rs` |
| 20 | `shell_escape_timing_reset` | repl/spec.md §13.6 — timing shows 0+0ms after shell escape | prompt format after `/sh` | GAP-COVER | named timing-reset assertion; not asserted elsewhere. Carry to `repl_shell.rs` |
| 21 | `shell_escape_appears_in_help` | repl/spec.md §13.7 — shell escape in /help | `/help` mentions `/sh` | GAP-COVER | help-listing angle; carry to `repl_shell.rs` |
| 22 | `shell_escape_neg_no_env_propagation` | repl/spec.md §13.5 — env vars must NOT propagate back | `/sh export FOO=bar` does not crash REPL | REGRESSION-GUARD | `_neg_` pattern; child-process-isolation invariant. Carry to `repl_shell.rs` |

### 3. File Watching, tests 23–34

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 23 | `watch_detects_source_change` | repl/spec.md §14.1 — watch directories containing loaded files | edit `mymod.cl` → `[updated:]` or `[errors:]` notification | GAP-COVER | repl/spec.md §14 has zero carry-forward; primary positive path. Carry to new `repl_watch.rs` |
| 24 | `watch_ignores_metadata_only_changes` | repl/spec.md §14.2 — content-hash filter | `touch mymod.cl` (no content change) → no notification | REGRESSION-GUARD | negative-name (`ignores_metadata_only`); content-hash invariant. Carry to `repl_watch.rs` |
| 25 | `watch_cascade_invalidation` | repl/spec.md §14.2 — cascade invalidation | edit `mod_b.cl`, expect both `mod_a.cl` and `mod_b.cl` notifications | REGRESSION-GUARD | named cascade dependency angle. Carry to `repl_watch.rs` |
| 26 | `watch_notification_format` | repl/spec.md §14.3 — `[updated: file.cl]` notification format | format check | GAP-COVER | carry to `repl_watch.rs` |
| 27 | `watch_notification_truncation` | repl/spec.md §14.3 — per-module notifications (no truncation) | multiple modules each get own line | GAP-COVER | carry to `repl_watch.rs` |
| 28 | `watch_notification_deferred_during_input` | repl/spec.md §14.3 — notification deferred during input | notification not on same line as `:Int <val>` | REGRESSION-GUARD | named "deferred" anti-interleaving invariant; checks line-by-line that no result line contains the notification. Carry to `repl_watch.rs` |
| 29 | `watch_automatic_recompilation` | repl/spec.md §14.2 — eager recompilation | `[updated: mymod.cl]` after change | GAP-COVER | carry to `repl_watch.rs` |
| 30 | `watch_type_incompatibility_on_reload` | repl/spec.md §14.2 — type incompatibility on reload | break trait method body → reload result notified | GAP-COVER | type-error reload angle; carry to `repl_watch.rs` |
| 31 | `watch_error_display_format` | repl/spec.md §14.3 — `[errors: mymod.cl]` format | broken syntax → `[errors:]` notification | GAP-COVER | carry to `repl_watch.rs` |
| 32 | `watch_error_recovery_last_known_good` | repl/spec.md §14.4 — errors block evaluation (NO last-known-good) | broken file → "Cannot evaluate" message | REGRESSION-GUARD | named negative-shape (no LKG); spec evolved away from LKG. Test name preserves the spec-pivot history. Carry to `repl_watch.rs` |
| 33 | `watch_retry_on_next_change` | repl/spec.md §14.4 — error resolved on next successful change | break → fix → re-eval succeeds | REGRESSION-GUARD | named retry/recovery loop. Carry to `repl_watch.rs` |
| 34 | `watch_invalidates_cache_on_change` | repl/spec.md §14.7 — cache invalidation on file change | change → `.cranelisp-cache/` exists | GAP-COVER | carry to `repl_watch.rs` |
| 35 | `watch_unchanged_modules_keep_cache` | repl/spec.md §14.7 — unchanged modules keep cached `.o` | manifest-level test (no subprocess) — pure cache logic | GAP-HARVEST? | **flagged for /sprint** — uses `cranelisp_backend::cache::*` Rust API directly, not subprocess. This is the only Rust-API test in the file and is structurally a unit test (per `tests/CLAUDE.md` two-tier rule). Either: (a) GAP-HARVEST → file harvest FIXME for `/backend` to author the unit test in `crates/cranelisp-backend/src/`; (b) rewrite as e2e (modify two modules, only one re-emits its `.o`); (c) preserve as integration-tier exception. Recommendation: harvest FIXME (`/backend`). |

### 4. REPL Cache Integration, tests 36–38

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 36 | `cache_repl_writes_on_import` | repl/spec.md §12.5 + design/int/repl-lifecycle.md §4 — cache write after REPL module compilation | REPL session w/ test prelude → manifest.json exists | GAP-COVER | partial overlap with `cache.rs::cache_prelude_modules_cached`, but that asserts via `Cranelisp::new().run` (batch mode); this is REPL-mode (`stdin`-driven) — distinct angle per multi-angle rule. Carry to `cache.rs` (extend with `cache_repl_*` cluster) or new `repl_cache.rs` |
| 37 | `cache_repl_loads_on_startup` | design/int/repl-lifecycle.md §4.2 — cache load on startup | run REPL twice, both produce 42 | GAP-COVER | REPL-mode cache-load angle; partial overlap with `cache.rs::cache_repl_restart_cache_hit` (which asserts `helper.meta.json` mtime preservation in `--run` mode). PRESERVE — REPL-mode angle is distinct. Header note "Resolved S59 Wave 1" makes it a defect-fix witness. Carry to `cache.rs` |
| 38 | `cache_writer_survives_reset` | design/int/repl-lifecycle.md §4.4 — cache writer survives /reset | REPL: eval, /reset, eval; manifest persists | REGRESSION-GUARD | named `survives_reset` invariant; ZERO carry-forward coverage for `/reset` interaction with cache. Carry to `cache.rs` or `repl_cache.rs` |

### 5. Session Persistence (`user.cl`), tests 39–55

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 39 | `persist_defn_survives_restart` | repl/spec.md §15.2 — defn persisted via source regeneration | session 1 defines, session 2 calls | GAP-COVER | repl/spec.md §15 across-restart has zero carry-forward; primary positive path. Carry to new `repl_persist.rs` |
| 40 | `persist_deftype_survives_restart` | repl/spec.md §15.2 — deftype persisted | session 1 defines `Color` enum, session 2 uses constructor | GAP-COVER | carry to `repl_persist.rs` |
| 41 | `persist_import_survives_restart` | repl/spec.md §15.2 — import persisted | session 1 imports `helper`, session 2 calls; cache deleted between | REGRESSION-GUARD | carries inline `FIXME(/int)` Sprint 58 Wave 2c — second session does not see persisted import. Highest-value persistence regression guard. Carry to `repl_persist.rs` (preserve FIXME) |
| 42 | `persist_user_cl_created` | repl/spec.md §15.2 — user.cl created as backing file | defn → quit → user.cl exists with bar | GAP-COVER | backing-file existence/contents angle; carry to `repl_persist.rs` |
| 43 | `persist_user_cl_is_valid_source` | repl/spec.md §15.2 — user.cl is valid parseable source | dependency-order assertion (double before quad) + reimport | REGRESSION-GUARD | named "valid source" invariant + topological ordering check + reimport round-trip. Multi-angle. Carry to `repl_persist.rs` |
| 44 | `persist_cache_speeds_restart` | repl/spec.md §15.2 + design/int/session-persistence.md §3 — cache speeds restart | three sessions w/ timing | GAP-COVER | timing assertion is best-effort/eprintln only — correctness assertion (gamma=3 across all three) is the durable check. Cache-warm angle. Carry to `repl_persist.rs` |
| 45 | `persist_watcher_ignores_self_write` | design/int/session-persistence.md §4 — self-write suppression via content hash | defn → no `[updated: user.cl]` notification | REGRESSION-GUARD | named "ignores_self_write" invariant; specific Sprint 23 design-doc anchor. Carry to `repl_persist.rs` |
| 46 | `persist_neg_bare_expr_not_saved` | design/int/session-persistence.md §2 — only definition-like inputs saved | bare `(add-i64 1 2)` not in user.cl | REGRESSION-GUARD | `_neg_` pattern; what-must-NOT-appear invariant. Carry to `repl_persist.rs` |
| 47 | `persist_bug1_all_defns_saved_to_user_cl` | repl/spec.md §15.2 — all defns saved, including constrained poly | 3 fns including `(defn add [x y] (+ x y))` all in user.cl | REGRESSION-GUARD | `_bug1_` pattern; named Sprint 23 defect (compile_and_register_defn skipped for constrained fns). Highest-value persistence regression. Carry to `repl_persist.rs` |
| 48 | `persist_bug1_constrained_fn_survives_restart` | repl/spec.md §15.2 — constrained poly fn restored callable | session 2 calls `add 100 200` from restored user.cl after cache wipe | REGRESSION-GUARD | `_bug1_` pattern continuation; restart angle of bug1. Carry to `repl_persist.rs` |
| 49 | `persist_bug2_cache_files_created_after_restore` | repl/spec.md §15.2 + design/int/session-persistence.md §3 — cache written on restore | session 2 produces user.meta.json + user.o | REGRESSION-GUARD | `_bug2_` pattern; named Sprint 23 defect. Carry to `repl_persist.rs` |
| 50 | `persist_bug3_accumulated_definitions_across_sessions` | repl/spec.md §15.2 — accumulated defns | session 1 foo, session 2 bar; user.cl has BOTH | REGRESSION-GUARD | `_bug3_` pattern; multi-session accumulation invariant. Carry to `repl_persist.rs` |
| 51 | `persist_bug3_neg_no_phantom_definitions` | repl/spec.md §15.2 — no stale defns from unrelated sessions | user.cl does NOT contain `defn gamma` or `defn fact` | REGRESSION-GUARD | `_bug3_neg_` pattern; what-must-NOT-appear. Carry to `repl_persist.rs` |
| 52 | `persist_bug_macro_not_expanded_in_user_cl` | repl/spec.md §15.2 — user.cl preserves original source, not macro-expanded form | `(str ...)` saved verbatim, not `(str-concat ...)` | REGRESSION-GUARD | named macro-expansion-leak defect; uses real stdlib (not test fixtures) — only test in batch that does. Carry to `repl_persist.rs` (preserve stdlib helper) |
| 53 | `cache_repl_produces_object_files` | design/int/session-persistence.md §3 — cache written after save | first session immediately produces user.o + user.meta.json | GAP-COVER | partial overlap with #49 (`persist_bug2_*`) but distinct: this asserts after FIRST session (no restore involved); #49 asserts after RESTORE. Multi-angle — PRESERVE both. Carry to `repl_persist.rs` |
| 54 | `persist_bug_macro_usage_survives_restart` | repl/spec.md §15.2 — fns using prelude macros survive restart | `(defn greet [name] (str ...))` → restart → `(greet "cranelisp")` works | REGRESSION-GUARD | named Sprint 23 defect — batch-mode restore compiles user.cl before prelude macros are available. Highest-value Sprint 23 macro-usage persistence regression. Uses real stdlib. Carry to `repl_persist.rs` |
| 55 | (placeholder; see above) | | | | |

### 6. Batch-mode main, tests 55–57

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 55 | `batch_main_missing_produces_error` | repl/spec.md §0.2 — `--run` requires main | no `main` → error mentions "main" | GAP-COVER | partial overlap with `link_error_no_main_function` (test #5) but that's `--link` mode, this is `--run` mode. PRESERVE — distinct mode. Carry to `build_confidence.rs` (extend) or new `batch_main.rs` |
| 56 | `batch_main_int_exit_code` | repl/spec.md §0.2 — `--run` w/ main returning 0 | exit 0 | DUPLICATE-IN-LEGACY | exact 1:1 with `build_confidence.rs::smoke_run_zero_arg_main_exits_zero` (`(defn main [] 0)` → exit 0). DROP. |
| 57 | `batch_main_nonzero_exit_code` | repl/spec.md §0.2 — `--run` w/ main returning non-zero Int | exit 42 | DUPLICATE-IN-LEGACY | very close 1:1 with `build_confidence.rs::smoke_link_then_run_executable_matches_run_exit` (which also asserts exit 42, via `--link` though — different mode). Marginal call: in `--run` mode the closest analogue is `mode_equiv_constant_main` (exit 0) or `build_confidence.rs::mode_equiv_primitive_arithmetic` (exit 3). Closest is `mode_equiv_primitive_arithmetic` which exits 3 via `--run`. So `--run main → 42` is NOT directly carried for `--run` alone. DUPLICATE-IN-LEGACY (very loose) — flagged for /sprint judgment; could equally be GAP-COVER. |

### 7. Heisenbug + H5 gate, tests 58–61

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 58 | `cache_repl_loads_heisenbug_parallel_stress` | design/int/dual-path-persistence-collapse.md §7 step 7 + §8 — heisenbug repro | 20-iteration stress loop | REGRESSION-GUARD | named heisenbug regression guard with explicit FIXME(/int) Sprint 59 Workstream A. Anti-flake stress test. Carry to new `repl_persist_race.rs` or `repl_persist.rs` |
| 59 | `heisenbug_race_reduced_concurrent_import_pairs` | design/int/heisenbug-race-closure.md §3b — reduced repro | 6 threads × 2 iter × 10 trials, fast-fail-on-first | REGRESSION-GUARD | named reduced heisenbug repro authored Sprint 61 Wave 3 step 3a; explicit calibration constants documented in test body. Highest-value Sprint 61 race regression. Carry to `repl_persist_race.rs` |
| 60 | `h5_gate_typechecking_user_fires_only_on_repl_thread` | design/int/heisenbug-race-closure.md §7.7 + §7.8 — H5 gate invariant | parses `[SCH]` event stream from `CRANELISP_SCHEDULER_TRACE=1` stderr | REGRESSION-GUARD | `h5_` pattern; documented Sprint 61 Wave 3 step 3f Test 1; complex parsing of scheduler trace events. Carry to `repl_persist_race.rs` (preserve trace-parser) |
| 61 | `h5_normal_completion_does_not_starve_repl_eval_thread` | design/int/heisenbug-race-closure.md §3d' — RAII guard starvation safety | 15s timeout poll-wait on subprocess | REGRESSION-GUARD | `h5_` + `does_not_` pattern; documented Sprint 61 Wave 3 step 3f Test 4. RAII guard / EvalInFlightGuard absence-of-starvation invariant. Carry to `repl_persist_race.rs` |

(Note: §6 entry numbering corrects an off-by-one — the file has 61 tests
with the placeholder row removed. Re-numbering: tests #55–57 in §6 are
the three batch_main tests, and #58–61 are the heisenbug/H5 tail. Total
audited = 61.)

## GAP-COVER candidates — recommended target files

For each, the recommendation is the carry-forward target file and a
proposed canonical test name. Final shape is `/sprint`'s call at
Wave 6 dispatch.

| Originating test(s) | Target file | Proposed canonical name(s) | Spec anchor | Notes |
|---|---|---|---|---|
| #1–#11 (11 link tests) | new `link.rs` | preserve names; consider folding `link_error_*` into a parameterised helper if /sprint prefers | design/backend/executable-generation.md §3, §5.4, §7, §9 | Spec coverage gap — section currently has zero `[Tested]` annotations. The full §3/§7/§9 surface needs anchoring. `link_multi_module_project` MUST preserve its `FIXME(/int)`. |
| #12–#22 (11 shell tests) | new `repl_shell.rs` | preserve names | repl/spec.md §13 | Section §13 has zero carry-forward. Full positive + negative + edge surface. |
| #23–#34 (12 watch tests) | new `repl_watch.rs` | preserve names | repl/spec.md §14 | Section §14 has zero carry-forward. The 4 REGRESSION-GUARD tests in this cluster (cascade, deferred, last_known_good, retry_on_next_change) are presumptively discriminating per Wave 5.5/5.6. |
| #35 (`watch_unchanged_modules_keep_cache`) | **GAP-HARVEST** | harvest FIXME → `/backend` | repl/spec.md §14.7 + design/backend/module-caching.md | **flagged** — only Rust-API test in file. Either harvest as `/backend` unit test or rewrite as e2e (two-module project, edit one, assert other's `.o` mtime preserved — same shape as `cache.rs::cache_quick_build_links_cached_objects`'s mtime check). |
| #36–#38 (3 cache_repl tests) | extend `cache.rs` (or new `repl_cache.rs`) | preserve names | repl/spec.md §12.5 + design/int/repl-lifecycle.md §4 | REPL-mode (stdin-driven) angle of cache integration. `cache_writer_survives_reset` is the ONLY `/reset` interaction with cache in the codebase. |
| #39–#54 (16 persist tests) | new `repl_persist.rs` | preserve names | repl/spec.md §15.2 + design/int/session-persistence.md | Section §15 across-restart has zero carry-forward. The 8 REGRESSION-GUARD tests (the four `_bug{N}_` tests, `_neg_bare_expr_not_saved`, `watcher_ignores_self_write`, `_bug_macro_not_expanded`, `_bug_macro_usage_survives`) are explicit Sprint 23 defect anchors. |
| #55 (`batch_main_missing_produces_error`) | extend `build_confidence.rs` | `smoke_run_main_missing_produces_error` (new) | repl/spec.md §0.2 | The `--run` no-main-error angle is not currently in the smoke suite. |
| #56 (`batch_main_int_exit_code`) | DROP | — | — | DUPLICATE-IN-LEGACY of `build_confidence.rs::smoke_run_zero_arg_main_exits_zero`. |
| #57 (`batch_main_nonzero_exit_code`) | extend `build_confidence.rs` (judgment call) | `smoke_run_nonzero_main_exits_with_int` | repl/spec.md §0.2 | Marginal duplicate; if /sprint accepts the looseness with `mode_equiv_primitive_arithmetic`, drop. Otherwise carry. |
| #58–#61 (4 heisenbug + H5 tests) | new `repl_persist_race.rs` | preserve names | design/int/heisenbug-race-closure.md + design/int/dual-path-persistence-collapse.md | Highest-value race regression cluster. The 15s timeout test (#61) and the SCH-trace-parser test (#60) require careful preservation of test-body comments — they document calibration empirically (n=20, m=10 trials, etc.) and a re-author would lose that context. |

## Tests flagged for /sprint judgment

### A. `watch_unchanged_modules_keep_cache` (#35) — Rust-API integration

This is the only test in `sprint23.rs` that imports
`cranelisp_backend::cache::*` directly. Per `tests/CLAUDE.md` two-tier
rule, this is structurally a unit test — no subprocess, no on-disk
e2e shape. Three options:

1. **GAP-HARVEST**: file harvest FIXME → `/backend` to author the
   unit test in `crates/cranelisp-backend/src/cache.rs` `#[cfg(test)]`
   module. The cache manifest invariant ("module B with unchanged
   source still hits cache after module A changes") is squarely
   in `/backend`'s ownership.
2. **Rewrite as e2e**: two-module project, edit only `mod_a.cl`, assert
   `mod_b.o` mtime preserved (same shape as
   `cache.rs::cache_quick_build_links_cached_objects::nap_for_mtime` +
   `mtime` helpers).
3. **Preserve as integration-tier exception**: explicitly out of step
   with the two-tier rule.

Recommendation: option (1) — file `tests/plan/wave-6-batch-2-harvest.md`
naming `/backend` as the harvest target for the cache-manifest
invariant. Option (2) is also acceptable if /sprint prefers e2e
breadth.

### B. `batch_main_int_exit_code` (#56) and `batch_main_nonzero_exit_code` (#57)

Both are very close to existing `build_confidence.rs` smoke tests:

- #56 (main → 0) is exact 1:1 with `smoke_run_zero_arg_main_exits_zero`.
  DROP.
- #57 (main → 42) has no exact 1:1 in `--run` mode. Closest is
  `smoke_link_then_run_executable_matches_run_exit` (which uses
  `--link`, exit 42) and `mode_equiv_primitive_arithmetic` (`--run`,
  exit 3 via primitive add). Marginal disposition.

Recommendation: DROP #56, carry #57 as `smoke_run_main_returns_int_exit_42`
(or fold into `mode_equiv_primitive_arithmetic` parameterisation).

### C. Heisenbug calibration constants (#58, #59, #61)

The four heisenbug + H5 tests carry detailed in-body comments
documenting calibration (THREADS=6, ITERS_PER_THREAD=2, TRIALS=10,
TIMEOUT=15s) with empirical justification (e.g., "n=20 wall-clock
0.28-0.44s; one 9/10 failure at 2s ceiling under heavy nextest").
This material MUST be preserved in the carry-forward — re-authoring
without it would erase the Sprint 61 Wave 3 step 3a/3f investigation
record.

Recommendation: explicit `/sprint` instruction to the carry-forward
authoring sub-agent: "test bodies are load-bearing for these four
tests; preserve verbatim, do not 'simplify'".

### D. `link_multi_module_project` (#11), `persist_import_survives_restart` (#41), `cache_repl_loads_heisenbug_parallel_stress` (#58)

Three tests carry inline `FIXME(/int)` markers per the OLD inline-FIXME
protocol (pre-Sprint 63 M7 methodology pivot — see CLAUDE.md
"Cross-Skill Changes"). The new protocol is `design/arch/fixmes/NNNN-name.md`
files. Two options at carry-forward time:

1. **Preserve inline**: faithful to current legacy file shape. Minor
   debt — `/sprint` opportunistically migrates inline FIXMEs.
2. **Migrate at carry**: file three new `design/arch/fixmes/NNNN-*.md`
   targeting `/int`, transcribe the inline FIXME contents, drop the
   inline comment.

Recommendation: option (2) — bundle the three FIXME migrations into the
Wave 6 carry-forward batch. Fits the "migrate on touch" discipline
(`memory/...` and CLAUDE.md). Names suggested:

- `NNNN-link-multi-module-got-helper.md`
- `NNNN-persist-import-not-loaded-on-session-2.md`
- `NNNN-collapse-completes-heisenbug.md`

### E. Carry-forward target file naming

Five new files emerge from this audit:

- `tests/link.rs` (11 tests from §1)
- `tests/repl_shell.rs` (11 tests from §2)
- `tests/repl_watch.rs` (12 tests from §3)
- `tests/repl_persist.rs` (16 tests from §5)
- `tests/repl_persist_race.rs` (4 tests from §7) — OR fold into
  `repl_persist.rs` as a `#[cfg(slow_race_tests)]`-style segregated
  suite. The race tests are slow (heisenbug stress is up to 10s,
  H5 timeout test is up to 15s on contended runs); folding may
  perturb the rest of the persist suite's runtime budget.

Plus modifications to two existing files:

- `tests/cache.rs` (extend with three `cache_repl_*` REPL-mode tests
  from §4, plus optional rewrite of #35)
- `tests/build_confidence.rs` (extend with `smoke_run_main_missing_*`
  from #55 and optionally `smoke_run_main_returns_int_exit_42` from #57)

Total: 5 new files + 2 extended files. This is the largest carry-forward
bill of materials yet observed (Wave 6 batch 1 produced 3 new files).

Recommendation: dispatch as 6 parallel sub-agent jobs (one per new file
plus `cache.rs` and `build_confidence.rs` extensions), each independent.

### F. Quarantine vs in-place

Per Phase 2 "audit / port / reorganise / quarantine" workflow,
sprint23.rs should be quarantined to `tests/legacy/sprint23.rs` once
the carry-forward lands and the ledger entry is recorded. Same as
prior wave conclusions.

## Recommendations

1. **Carry forward all 60 tests** (drop only #56, the exact 1:1
   duplicate). 28 are presumptively-discriminating REGRESSION-GUARD;
   31 are GAP-COVER first-time spec coverage for repl/spec.md §13/§14/§15
   and design/backend/executable-generation.md §3/§7/§9.

2. **5 new test files + 2 extensions**: `link.rs`, `repl_shell.rs`,
   `repl_watch.rs`, `repl_persist.rs`, `repl_persist_race.rs` (or fold
   race into persist), plus extensions to `cache.rs` and
   `build_confidence.rs`.

3. **One harvest FIXME** (`/backend`): `watch_unchanged_modules_keep_cache`
   (#35) is a Rust-API cache-manifest invariant that belongs in
   `crates/cranelisp-backend/src/cache.rs` `#[cfg(test)]`. Alternative:
   rewrite as e2e mtime-preservation test.

4. **Three FIXME migrations** to `design/arch/fixmes/NNNN-*.md` for the
   three inline `FIXME(/int)` markers — fits CLAUDE.md "migrate on
   touch" discipline.

5. **Preserve test-body calibration verbatim** for the four heisenbug
   + H5 tests (#58–#61). The Sprint 61 Wave 3 investigation record is
   load-bearing.

6. **Update repl/spec.md** with `[Tested ...]` annotations for §13,
   §14, §15 once the carry-forward lands. Currently zero annotations.
   This is the most consequential spec coverage update from Wave 6.

## Methodology takeaway

`sprint23.rs` is the **highest GAP-COVER yield** of any file audited
in Waves 5.5 / 5.6 / 6:

| File | Tests | GAP-COVER | DUPLICATE | COVERED | Yield % |
|---|---:|---:|---:|---:|---:|
| Wave 5.6 ring0 (108 tests) | 108 | ~30% | ~70% | — | ~30% |
| Wave 5.6 e2e re-audit | varied | ~40% | ~60% | — | ~40% |
| Wave 6 batch 1 (examples + exemplar) | 21 | 21 | 0 | 0 | 100% |
| **Wave 6 batch 2 (sprint23.rs)** | **61** | **59** | **2** | **0** | **97%** |

The reason: sprint23.rs is a Sprint 23 work-product file that delivered
five new feature surfaces (`--link`, `/sh`, file watching, cache,
persistence) and added 61 tests for those surfaces. None of those
five surfaces had pre-existing carry-forward coverage at audit time
because they did not exist before Sprint 23. The dedup risk was
near-zero by construction.

This validates the Wave 5.5/5.6 regression-guard rule operationally:
heavily regression-named files in the sprint-cohort partition tend
to discriminate at >90% rates against the spec-tier carry-forward
universe. The remaining batches 3–6 (the rest of the sprint-cohort)
likely produce similar yields.

The single GAP-HARVEST candidate (`watch_unchanged_modules_keep_cache`)
is also the typical cohort signature: of 61 tests, 60 are e2e-shape
and 1 is Rust-API. As earlier waves observed, the integration-tier
slim-file is the structural artefact most needing /sprint judgment
at carry-forward time.

The most consequential downstream work: repl/spec.md §13, §14, §15
gain `[Tested ...]` annotations for the first time. These three
sections cover the entire interactive-REPL / file-watching /
session-persistence experience — the spec-coverage hole is large
and load-bearing for the user-surface acceptance argument.
