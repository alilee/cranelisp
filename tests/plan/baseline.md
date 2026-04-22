# Baseline Failure Ledger

Owned by `/qa`. Verified at every sprint open and every sprint close.

## Discipline

Every test currently failing in `cargo nextest run --no-fail-fast` MUST have an entry in this file. There are no other legitimate places for a failing test to live: `#[ignore]` hides the fact, and undocumented failure relies on institutional memory.

**Allowed dispositions:**

- `under-investigation` — owner is actively reducing or fixing; target sprint names when the work lands.
- `out-of-scope (owner=/skill)` — a real defect that is not in the current sprint's scope; target sprint names when it will be picked up. An owning skill MUST be named.
- `exemplar-gap (owner=/port)` — a failure that lives in `exemplar/` (a Cranelisp-level test, not a cargo test) and reflects a real language or runtime defect surfaced by the exemplar. Owner is always `/port` for the repro; the underlying fix may be owned by a compiler skill which is named in the entry's `underlying-owner` field.

**Explicitly NOT allowed:**

- `flaky` — never. Local tests are deterministic; if a test fails intermittently, the cause is a real race, ordering bug, or uninitialised state. "Flaky" closes investigation prematurely and forfeits the regression guard. Per user directive 2026-04-21: *"we need to be really clear about 'flaky' — that is not a thing in local tests."*
- `timing-sensitive` — equivalent to flaky. Tests that assume a particular scheduling order are either testing something real (name it and pin it) or they are incorrectly written (fix them).
- `documented race` — the race is the bug. Fix it.
- `pre-existing` — historical dispositions rely on commit-SHA amnesia. "Pre-existing" is not a disposition: the same tests either get a real disposition (`under-investigation` + target sprint, or `out-of-scope (owner=/skill)` + target sprint) or they are deleted.

**Required fields per entry:**

- Test name (fully-qualified: `binary::test_function_name`)
- Current commit SHA (short form)
- Exact stderr signature (2–5 line excerpt, quoted verbatim)
- Owning skill (`/qa`, `/int`, `/backend`, `/port`, etc.)
- Target sprint
- Disposition + one-sentence rationale

A failing test without all six fields is treated as a sprint-blocking issue. `/sprint` MUST refuse to close a sprint that contains unentered failures.

## Current Entries (as of 2026-04-22, sprint 61 Wave 3 step 3f, SHA `35062ca`)

> **Sprint 60 close update (2026-04-21)**: under full-suite pressure (multiple consecutive `cargo nextest run --no-fail-fast`), two races fire intermittently at ~30% rate. Single-run verification showed 1837/0 and `/qa` originally recorded only the exemplar entry below. 8-run stress verification under close revealed the races. Per user directive "flaky is not a thing in local tests," these are recorded as real races under `under-investigation (sprint 61)` and a dedicated stabilisation sprint opens next. FQTypeName migration slides to Sprint 62.

> **Sprint 61 Phase 3a coverage note (2026-04-22)**: Wave-2 test-plan coverage for both carried cargo-test failures has been derived in `tests/plan/ring4.md §"Sprint 61 — Stabilisation test cases"`. The heisenbug race entry maps to §Slice 3 (T-S3-{1..H3}, 5 test cases). The `21-hello-io.cl` exit 201 entry maps to §Slice 4 (T-S4-* placeholders; most deferred until the Slice 4 readout selects among H4-1/H4-2/H4-3 per `design/backend/io-trampoline-trace.md §10`). Entries are NOT removed — fixes have not landed. Removal happens at Sprint 61 close per the close-time verification protocol below.

> **Sprint 61 Wave 1 close update (2026-04-22, SHA `a9028c0`)**: Slice 0 observability infrastructure landed (/int scheduler trace + /backend IO trampoline trace, 25 + 18 unit tests, panic-hook flush wiring in `src/main.rs`). `/qa` authored 19 Slice-0 integration tests. 16 pass; 3 IO tests fail because they depend on `examples/21-hello-io.cl` completing cleanly — the Slice 4 defect blocks trampoline-event emission before the SIGABRT. These three are ledgered below and flip green at Slice 4 close. A fourth test (`io_trace_off_path_subprocess_completes_within_generous_ceiling`) passes in isolation but fires under concurrent nextest load — ledgered as a harness robustness concern, NOT flaky, owner `/qa`, to be fixed in Wave 5 or carried to S62. S60 carries (`sprint23::cache_repl_loads_heisenbug_parallel_stress`, `examples_run::every_example_file_runs_under_examples_prelude`) remain current — Slice 3 and Slice 4 have not yet run.

### Cargo test suite

| Field | Value |
|---|---|
| Test name | `sprint23::heisenbug_race_reduced_concurrent_import_pairs` |
| SHA | `35062ca` |
| Stderr / observable signature | `reduced heisenbug repro fired across 10 trials (N failure(s)): [trial K] tT iI session 1: import+call failed` — body: `Error: type error at 9..28: 'helper-val' not found in module 'helper'` followed by `Error: type error at 1..11: undefined variable: helper-val`. Occasional codegen-phase variant: `module error at 0..0: module 'helper' failed: codegen error at 0..23: compile_to_module: symbol 'helper-val' missing from module 'helper' at GOT-data emission`. Post-H6-fix: same signature fires at reduced rate (~5–10% under 6-thread contention vs. ~80% pre-fix). |
| Owning skill | `/int` (proposed fix site: `crates/cranelisp-typecheck/src/checker.rs::ensure_module_exists`; typecheck-crate ownership tension flagged for /arch at step 3d'' — see `design/int/heisenbug-race-closure.md §8.3.5` risk 7) |
| Target sprint | Sprint 61 Wave 3 close — **disposition open**, pending `/sprint` decision at close: (a) open in-sprint H7 cycle to chase the residue, or (b) accept-and-defer to S62 concurrency audit. `/qa` does NOT pick; ledger captures current state. |
| Disposition | `under-investigation (sprint 61 Wave 3 — H6 fix LANDED, partial closure, residue remains; disposition open at close)` |
| Rationale | **H5 closed (Wave 3 step 3e')**: scheduler-claim race fixed via `eval_in_flight` + `EvalInFlightGuard` RAII; post-fix log `tests/sprint61/race-evidence/post-fix-h5-35062ca.log` confirms H5 signature gone (no `ModuleStateTypechecking user` on worker after `ModuleStateUnblocked user`). **H6 identified and fixed (Wave 3 step 3e'')**: non-atomic compare-then-set race in `TypeCheckEnv::ensure_module_exists` (+14 LOC in `crates/cranelisp-typecheck/src/checker.rs::ensure_module_exists`, rewritten to DashMap atomic `entry(path).or_insert_with(...)`). **Effect of H6 fix**: stress runs show rate drop from ~80% → 5–10% under `--test-threads=6`; stress observed 3/25 failures at 6-thread contention. **Residue is REAL** — same `'helper-val' not found in module 'helper'` signature persists at reduced rate; post-fix dumps confirm identical shape. **Interpretation**: H6 closed the most-frequent race; the residue is either a lower-frequency sibling of H6 (second non-atomic path into the same symbol-table merge) or a distinct H7 race further down the import/GOT-emission pipeline. H5 regression guards (`sprint23::h5_gate_typechecking_user_fires_only_on_repl_thread` + `sprint23::h5_normal_completion_does_not_starve_repl_eval_thread`) still pass 5/5 — no H5 regression from H6 fix. **User + /review methodology concern (2026-04-22)**: single stress-run 0/N gate has low statistical power and doesn't systematically exercise interleaving space; methodology pivot (audit + loom + structured interleaving tests) under consideration as S62 primary workstream. Options at close: (a) **continue in Wave 3** — open H7 design-and-fix cycle now; (b) **defer to S62** — accept residue as carried concurrency debt, let S62 concurrency audit + methodology pivot subsume it. `/sprint` decides at Wave 3 close; `/qa` ledgers current state only. Full H6 write-up in `design/int/heisenbug-race-closure.md §7.10` + §8.3. |

#### Resolved mid-sprint (Wave 3 step 3e')

- **`sprint23::cache_repl_loads_heisenbug_parallel_stress`** (S60 carry, SHA `d270a36`) — **RESOLVED**. Passes 58/59 in full sprint23 suite at SHA `35062ca`. Resolved by H5 fix (`eval_in_flight` scheduler-side worker-claim suppression landed in Wave 3 step 3e' per `design/int/heisenbug-race-closure.md §3e'`); the reduced harness `sprint23::heisenbug_race_reduced_concurrent_import_pairs` (authored step 3a) replaces it as the active regression surface, now targeting the H6 data-plane residue carried to S62.

| Field | Value |
|---|---|
| Test name | `examples_run::every_example_file_runs_under_examples_prelude` |
| SHA | `d270a36` |
| Stderr / observable signature | `21-hello-io.cl: exit=201 (allowed [101, 133, 141])` — an IO-using example exits with a code NOT in the expected-or-signal-artefact accept list. Exit 201 (= 0xC9) is neither SIGTRAP (133), SIGPIPE (141), nor the example's nominal exit (101). |
| Owning skill | `/backend` (suspected) or `/platform` (stdio DLL under pressure) — investigation needed |
| Target sprint | Sprint 61 (stabilisation) |
| Disposition | `under-investigation (sprint 61)` |
| Rationale | Surfaced during 8-run close-time stress. Passes reliably in isolation (5/5); fails intermittently under full-suite pressure. Distinct shape from the heisenbug race — involves the platform IO path and possibly a subprocess-stdin race with `read-line`. Sprint 61 should reduce the repro (replicate under pressure with a 1-test load), then diagnose. Candidates: (a) stdio DLL buffer ordering under concurrent subprocess loads, (b) IO trampoline continuation-state leak under concurrent evals, (c) nextest-level subprocess-environment crosstalk. |

#### Sprint 61 Wave 1 — Slice-4-dependent failures

The following three tests were authored in Wave 1 as part of the Slice-0 observability integration suite (`tests/sprint61_observability_io.rs`). Each drives `examples/21-hello-io.cl` with `CRANELISP_IO_TRACE=1` and asserts properties of the emitted trampoline event stream. All three fail because the example itself aborts (Slice 4 defect — the `examples_run::every_example_file_runs_under_examples_prelude` entry above) before a clean trampoline exit sequence can be produced. They flip green automatically when Slice 4 closes; no independent fix is required.

| Field | Value |
|---|---|
| Test name | `sprint61_observability_io::io_trace_hello_io_emits_full_trampoline_sequence` |
| SHA | `a9028c0` |
| Stderr / observable signature | Subprocess running `examples/21-hello-io.cl` with `CRANELISP_IO_TRACE=1` exits with SIGABRT (exit 134 / signal 6) before emitting a matched `TrampolineEnter ... TrampolineExit` pair. Assertion fails on absent `TrampolineExit` event in the captured stderr trace dump. |
| Owning skill | TBD at Slice 4 readout (`/backend` or `/platform` per `sprints/SPRINT.md §Wave 4`) |
| Target sprint | Sprint 61 Slice 4 |
| Disposition | `under-investigation (sprint 61 Slice 4)` |
| Rationale | Test is correctly authored against `design/backend/io-trampoline-trace.md §3` (TrampolineEnter/Exit pairing). The failure is a dependency on the Slice 4 `21-hello-io.cl` exit-201/abort defect — the trampoline cannot emit `TrampolineExit` because the process aborts mid-execution. Flips green when Slice 4 closes per `sprints/SPRINT.md §Wave 4 close`. |

| Field | Value |
|---|---|
| Test name | `sprint61_observability_io::io_trace_hello_io_observes_core_sequential_event_types` |
| SHA | `a9028c0` |
| Stderr / observable signature | Same subprocess SIGABRT on `examples/21-hello-io.cl` with `CRANELISP_IO_TRACE=1`; assertion fails because the truncated trace dump does not contain the expected taxonomy coverage (`TrampolineEnter`, `BindEnter`, `PlatformEffect`, `TrampolineExit` at minimum). |
| Owning skill | TBD at Slice 4 readout (`/backend` or `/platform`) |
| Target sprint | Sprint 61 Slice 4 |
| Disposition | `under-investigation (sprint 61 Slice 4)` |
| Rationale | Same Slice 4 dependency as above. Test validates `design/backend/io-trampoline-trace.md §3` taxonomy; the abort truncates the event stream before the full sequential taxonomy is exercised. Flips green when Slice 4 closes. |

| Field | Value |
|---|---|
| Test name | `sprint61_observability_io::io_trace_platformeffect_carries_scheduling_class_byte` |
| SHA | `a9028c0` |
| Stderr / observable signature | Same subprocess SIGABRT on `examples/21-hello-io.cl` with `CRANELISP_IO_TRACE=1`; assertion fails because no `PlatformEffect` event with a populated `scheduling_class: u8` payload reaches stderr before the abort. |
| Owning skill | TBD at Slice 4 readout (`/backend` or `/platform`) |
| Target sprint | Sprint 61 Slice 4 |
| Disposition | `under-investigation (sprint 61 Slice 4)` |
| Rationale | Same Slice 4 dependency. Test validates `design/backend/io-trampoline-trace.md §3 PlatformEffect payload` + Decision 26 (`scheduling_class` byte). The abort truncates the trace before a `PlatformEffect` for the stdio print call can be observed. Flips green when Slice 4 closes. |

#### Sprint 61 Wave 1 — Harness robustness concern

| Field | Value |
|---|---|
| Test name | `sprint61_observability_io::io_trace_off_path_subprocess_completes_within_generous_ceiling` |
| SHA | `a9028c0` |
| Stderr / observable signature | Subprocess wall-clock exceeds the 5-second off-path ceiling defined in the test (assertion: `elapsed < Duration::from_secs(5)`). Fires only under concurrent `cargo nextest run` load — multiple parallel subprocess-invoking tests contend on stdio DLL load + JIT warmup and push tail latency past 5s. Isolation runs complete well under 500 ms. |
| Owning skill | `/qa` |
| Target sprint | Sprint 61 Wave 5 (preferred) or Sprint 62 |
| Disposition | `under-investigation (sprint 61 Wave 5 or S62)` |
| Rationale | NOT flaky per `memory/feedback_repros_join_suite.md` and user directive 2026-04-21: the test is measuring subprocess completion time under an off-path (no-trace) ceiling, and concurrent nextest load genuinely exceeds that ceiling — this is a harness-robustness issue, not a compiler race. Two fix candidates: (a) widen the ceiling to a value that survives worst-case concurrent load while still catching real trace-overhead regressions (requires microbenchmark calibration per `design/backend/io-trampoline-trace.md §9 AC 2`), or (b) move the test into a nextest `serial` test group or rewrite using `assert_example_ran_cleanly` helper so concurrent load does not perturb the measurement. `/qa` investigates in Wave 5 if the slot is available; otherwise ledgered to S62. |

#### Escaped carries — surfaced Sprint 61 Wave 3 workspace stress (2026-04-22, SHA `35062ca`)

During Sprint 61 Wave 3 workspace stress verification, `/sprint` surfaced six tests that should have been ledgered during prior sprint closes but were not. All map to Sprint 59 Defect 6 (exemplar solver segfault/stack-overflow on full 81-cell grids) or downstream dependencies on it. Sprint 60 closed Defects 4 + 5 but Defect 6 was only partially addressed — the aborted-puzzle algorithmic path in `eliminate` was fixed in Wave 2, but the deep-recursion stack-overflow path in `propagate`/`solve` on full grids remains. These failures pre-date Sprint 61 and escaped Sprint 58/59/60 close-time verification — most likely because close-time runs were narrow-target rather than full-workspace.

**Note on one test the pre-ledger handoff listed as failing**: `sprint59_defects456_repro::d6_exemplar_eliminate_from_peers_does_not_segv` was named in the handoff brief as one of five failing `d6_exemplar_*` tests, but it **passes consistently** at SHA `35062ca` — verified 2/2 in isolation and 1/1 under concurrent load with the other four. Only four `d6_exemplar_*` tests are genuinely failing. This is noted here rather than silently dropped so `/sprint` can reconcile the handoff count (5 claimed → 4 actual).

| Field | Value |
|---|---|
| Test name | `sprint59_defects456_repro::d6_exemplar_propagate_only_does_not_segv` |
| SHA | `35062ca` |
| Stderr / observable signature | Subprocess running reduced repro (`exemplar/d6_propagate_only.cl` — single `propagate` call on a real 17-clue puzzle, no backtracking) crashes with `exit=None` (killed by signal, no exit code). Child-process stderr: `thread 'main' (...) has overflowed its stack` followed by `fatal runtime error: stack overflow, aborting`. Test panic: `d6_exemplar_propagate_only: child process crashed with exit=None (139=SIGSEGV, 133=SIGTRAP, None=killed by signal). This is the reduced reproduction of the underlying defect.` |
| Owning skill | `/port` (repro owner per ledger §"Allowed dispositions") with underlying-owner `/backend` (deep-recursion stack overflow in JIT'd `propagate` / constraint-propagation recursion on 81-cell Vec-copying ADT traversal — see `exemplar/CLAUDE.md §Known Issues`) |
| Target sprint | **Sprint 62 — flag for `/sprint` disposition at close; disposition is open.** Sprint 61 scope did not include Defect 6 resolution; Wave 2 closed Defects 4+5 but Defect 6 was deliberately carried. `/sprint` decides at Wave 3 close whether this ledger entry maps to an in-S62 /port or /backend workstream, or rolls forward again with re-triage. |
| Disposition | `exemplar-gap (owner=/port, underlying-owner=/backend)` |
| Rationale | Surfaced during Sprint 61 Wave 3 workspace stress — was failing before Sprint 61 opened but never ledgered. The test is the Sprint 59 /qa-authored reduced repro for Defect 6, narrowing the crash from the full solver down to a single `propagate` pass. Since it still reproduces at SHA `35062ca`, the underlying defect has not been resolved and the reduction remains a valid regression surface. Per `memory/feedback_repros_join_suite.md`, reductions enter the ledger until the fix lands. No action in S61 — flagged for /sprint disposition decision at close. |

| Field | Value |
|---|---|
| Test name | `sprint59_defects456_repro::d6_exemplar_propagate_single_pass_does_not_segv` |
| SHA | `35062ca` |
| Stderr / observable signature | Subprocess running reduced repro (`exemplar/d6_one_pass.cl` — a single call to `propagate-pass-helper g 0`, no fixpoint loop) crashes with `exit=None`. Child-process stderr: `thread 'main' (...) has overflowed its stack` / `fatal runtime error: stack overflow, aborting`. Same panic shape as the `propagate_only` entry above. |
| Owning skill | `/port` with underlying-owner `/backend` (same deep-recursion stack overflow — narrows the defect further by removing the fixpoint loop; `propagate-pass-helper` alone overflows) |
| Target sprint | **Sprint 62 — flag for `/sprint` disposition at close; disposition is open.** |
| Disposition | `exemplar-gap (owner=/port, underlying-owner=/backend)` |
| Rationale | Sibling reduction of `d6_exemplar_propagate_only`. Isolates the crash further — removing the fixpoint loop and calling `propagate-pass-helper` directly still overflows, proving the recursive structure *inside* one pass (Vec-copying over 81-cell Grid ADT) is the cost centre, not the outer `loop until fixpoint`. Small-repro value per `memory/feedback_repros_join_suite.md`: the shrunk source means shrunk CLIF, which `/clif` or `CRANELISP_CODEGEN_TRACE=1` can dump for codegen inspection when /backend takes this up. |

| Field | Value |
|---|---|
| Test name | `sprint59_defects456_repro::d6_exemplar_solve_all_dots_does_not_segv` |
| SHA | `35062ca` |
| Stderr / observable signature | Subprocess running reduced repro (`exemplar/d6_all_dots.cl` — `solve` on an all-dots / empty 81-cell puzzle, which should converge fast) crashes with `exit=None`. Child-process stderr: `thread 'main' (...) has overflowed its stack` / `fatal runtime error: stack overflow, aborting`. Same panic shape. |
| Owning skill | `/port` with underlying-owner `/backend` (deep-recursion stack overflow in `solve` even on an empty grid, where constraint propagation has no work and backtracking should never recurse deeply — proves the defect is structural, not puzzle-difficulty-dependent) |
| Target sprint | **Sprint 62 — flag for `/sprint` disposition at close; disposition is open.** |
| Disposition | `exemplar-gap (owner=/port, underlying-owner=/backend)` |
| Rationale | Sibling reduction that isolates the defect from puzzle complexity. An empty 81-cell grid has every cell as `Candidates 0b111111111`; `solve` should trivially return (no elimination work) or enter a short, balanced search. Stack-overflowing here indicates recursive Vec/ADT copying costs that scale with grid size, not constraint count. Distinguishes the bug from "hard puzzle → deep backtracking" hypotheses. |

| Field | Value |
|---|---|
| Test name | `sprint59_defects456_repro::d6_exemplar_solve_minimal_puzzle_no_io_does_not_segv` |
| SHA | `35062ca` |
| Stderr / observable signature | Subprocess running reduced repro (`exemplar/d6_repro_no_io.cl` — `solve` on a real 17-clue puzzle, no IO path, returns an Int count of determined cells) crashes with `exit=None`. Child-process stderr: `thread 'main' (...) has overflowed its stack` / `fatal runtime error: stack overflow, aborting`. Additional stderr preamble when run under concurrent nextest load includes cache `.meta.json` write failures (`nice-worker: .meta.json write failed for compare.eq: ... No such file or directory (os error 2)`), which is a concurrent-cache-write artefact not related to the underlying stack-overflow defect. |
| Owning skill | `/port` with underlying-owner `/backend` (stack overflow in solver without involving the IO trampoline — isolates the defect from Defect 4/5 residues and from the `examples_run` IO subprocess-flake path) |
| Target sprint | **Sprint 62 — flag for `/sprint` disposition at close; disposition is open.** |
| Disposition | `exemplar-gap (owner=/port, underlying-owner=/backend)` |
| Rationale | The "no-IO control surface" reduction authored in Sprint 59: proves that the crash is in `solve`/`propagate`, not in the IO trampoline path. Paired with the `solver.cl::main` end-to-end entry below (the `wave6_demo_repros` test), this reduction confirms the defect is purely in the pure-core solver. Concurrent-cache-write stderr is a Sprint 61 Wave 3 workspace-stress artefact — orthogonal to the defect but ledgered so /sprint can see the signature verbatim. |

| Field | Value |
|---|---|
| Test name | `wave6_demo_repros::exemplar_solver_does_not_stack_overflow_on_small_puzzle` |
| SHA | `35062ca` |
| Stderr / observable signature | Subprocess running `cranelisp --run exemplar/solver.cl` (full solver with IO) crashes with `exit=None`. Child-process stdout shows the puzzle board printed cleanly (Sprint 57 Wave 6 IO path is fine), then stderr: `thread 'main' (...) has overflowed its stack` / `fatal runtime error: stack overflow, aborting`. Test panic: `exemplar solver crashed with exit=None. Per Defect 6 (exemplar/CLAUDE.md Known Issues) propagate/solve stack-overflow on full 81-cell grids. Once /backend resolves this, /port can re-enable test-easy-puzzle, test-hard-puzzle, test-unsolvable in exemplar/solver.cl.` |
| Owning skill | `/port` (repro owner) with underlying-owner `/backend` (same deep-recursion stack overflow; this is the end-to-end entry point for Defect 6 — the broadest and most faithful repro) |
| Target sprint | **Sprint 62 — flag for `/sprint` disposition at close; disposition is open.** |
| Disposition | `exemplar-gap (owner=/port, underlying-owner=/backend)` |
| Rationale | The authoritative regression surface for Defect 6 — drives the full `exemplar/solver.cl` through the same entry point the user would hit via `--run`. Confirms the IO plumbing (`platform stdio`, `print`, `bind`, `Pure`) works up to the solve step (puzzle board prints cleanly) and isolates the crash to `propagate`/`solve` on the 81-cell grid. Per `exemplar/CLAUDE.md §Known Issues`, `/port` has disabled `test-easy-puzzle`, `test-hard-puzzle`, `test-unsolvable` inline submodules pending Defect 6 resolution; when /backend resolves the stack-overflow root cause, /port re-enables those and this entry resolves. |

### Exemplar-level tests (non-cargo)

*No current exemplar-level failing entries. The S60-carried `exemplar/solver.cl::test-unsolvable` was resolved in Sprint 61 Wave 2; see "Resolved this sprint" below. The Defect 6 stack-overflow failures are captured above as cargo tests (`d6_exemplar_*` and `wave6_demo_repros::exemplar_solver_*`), not as non-cargo entries — per `memory/feedback_repros_join_suite.md` the cargo-level reductions are the durable record.*

## Resolved this sprint (Sprint 61 Wave 2, 2026-04-22)

Per §Close-time Verification Protocol item 3 — entries removed from the ledger because the tests now pass on HEAD (working tree at SHA `b140ec5`, pre-commit). Preserved here as a one-line rationale trail for the sprint close report.

- **`sprint61_wave2::exemplar_solver_correctness::eliminate_on_same_value_given_returns_none`** (T-S2-1) — PASSING 5/5. Resolved by /port's Layer 1 fix in `exemplar/solver.cl::eliminate` (handle `(Given v)`/`(Solved v)` same-value cells by returning `None`) combined with /backend's Layer 3 fix at `crates/cranelisp-backend/src/compiler/mod.rs::is_last_use` which unblocked the naive Layer 1 patch from regressing valid puzzles.
- **`sprint61_wave2::exemplar_solver_correctness::inline_adt_arg_wrapping_vec_preserves_len`** (T-S2-2) — PASSING 5/5. Resolved by /backend's Layer 3 fix at `crates/cranelisp-backend/src/compiler/mod.rs::is_last_use` (consuming-arg RC emission for inline ADT constructors wrapping a Vec no longer drops the inner Vec's length before callee match-unwrap).
- **`exemplar/solver.cl::test-unsolvable`** (S60 carry, exemplar-level non-cargo) — superseded and closed. Root cause was a two-layer defect: Layer 1 algorithmic hole in `eliminate` (/port) plus Layer 3 compiler bug in consuming-arg RC (/backend) that regressed the naive Layer 1 fix. Both fixes landed in Wave 2 (`crates/cranelisp-backend/src/compiler/mod.rs::is_last_use` + `exemplar/solver.cl::eliminate`). The two cargo tests above now serve as the durable regression record; the exemplar-level test remains in `exemplar/solver.cl` but is no longer the authoritative failure record.

## Close-time Verification Protocol

`/sprint` MUST re-verify every entry in this file at sprint close:

1. Check out the commit named in the entry's SHA field and run the test.
2. Confirm the test still fails with the same stderr signature.
3. One of:
   - **Resolved** — the test now passes on HEAD. Remove the entry from this file and note the removal in the sprint close report.
   - **Still failing, same signature** — entry is current. If the target sprint has passed, update it; the owning skill MUST justify the slip in the close report.
   - **Still failing, different signature** — the underlying defect has shifted. Update SHA, signature, and (if relevant) owner in-place; do not delete. A changed signature usually means an unrelated interacting defect landed; investigate before accepting the update.
4. If a new failure appeared during the sprint that does not have an entry, `/sprint` MUST block close until `/qa` adds it per the required-fields list above.

This protocol runs at every close — no exceptions. "We're in a hurry" is how flaky dispositions creep in.

**Note — stress-run statistical power (2026-04-22, Sprint 61 Wave 3)**: Single stress-run verification alone is insufficient proof of race closure. Sprint 61 `/review` + user methodology concern (2026-04-22) identified that N-run 0/N gate has low statistical power and doesn't exercise interleaving space systematically — a race that fires at 5% per run can pass a 20-run 0/N gate ~36% of the time under H0. `/sprint` is considering a methodology pivot — audit + `loom` + structured interleaving tests — as S62 primary workstream to replace the N-run gate for concurrency defects. This note is informational and does NOT itself change protocol discipline: until the pivot is accepted, the tiered N-run gate in `.claude/commands/sprint.md` Phase 6 remains the close criterion. It is a flag that `/qa` and `/sprint` carry into S62 planning.
