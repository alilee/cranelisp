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

## Current Entries (as of 2026-04-22, sprint 61 Wave 1 close, SHA `a9028c0`)

> **Sprint 60 close update (2026-04-21)**: under full-suite pressure (multiple consecutive `cargo nextest run --no-fail-fast`), two races fire intermittently at ~30% rate. Single-run verification showed 1837/0 and `/qa` originally recorded only the exemplar entry below. 8-run stress verification under close revealed the races. Per user directive "flaky is not a thing in local tests," these are recorded as real races under `under-investigation (sprint 61)` and a dedicated stabilisation sprint opens next. FQTypeName migration slides to Sprint 62.

> **Sprint 61 Phase 3a coverage note (2026-04-22)**: Wave-2 test-plan coverage for both carried cargo-test failures has been derived in `tests/plan/ring4.md §"Sprint 61 — Stabilisation test cases"`. The heisenbug race entry maps to §Slice 3 (T-S3-{1..H3}, 5 test cases). The `21-hello-io.cl` exit 201 entry maps to §Slice 4 (T-S4-* placeholders; most deferred until the Slice 4 readout selects among H4-1/H4-2/H4-3 per `design/backend/io-trampoline-trace.md §10`). Entries are NOT removed — fixes have not landed. Removal happens at Sprint 61 close per the close-time verification protocol below.

> **Sprint 61 Wave 1 close update (2026-04-22, SHA `a9028c0`)**: Slice 0 observability infrastructure landed (/int scheduler trace + /backend IO trampoline trace, 25 + 18 unit tests, panic-hook flush wiring in `src/main.rs`). `/qa` authored 19 Slice-0 integration tests. 16 pass; 3 IO tests fail because they depend on `examples/21-hello-io.cl` completing cleanly — the Slice 4 defect blocks trampoline-event emission before the SIGABRT. These three are ledgered below and flip green at Slice 4 close. A fourth test (`io_trace_off_path_subprocess_completes_within_generous_ceiling`) passes in isolation but fires under concurrent nextest load — ledgered as a harness robustness concern, NOT flaky, owner `/qa`, to be fixed in Wave 5 or carried to S62. S60 carries (`sprint23::cache_repl_loads_heisenbug_parallel_stress`, `examples_run::every_example_file_runs_under_examples_prelude`) remain current — Slice 3 and Slice 4 have not yet run.

### Cargo test suite

| Field | Value |
|---|---|
| Test name | `sprint23::cache_repl_loads_heisenbug_parallel_stress` |
| SHA | `d270a36` |
| Stderr / observable signature | `iteration N: session 1 should successfully import and call helper-val: ... Error: type error at 9..28: 'helper-val' not found in module 'helper'` + `Error: type error at 1..11: undefined variable: helper-val` |
| Owning skill | `/int` (scheduler + worker publish/flag ordering) |
| Target sprint | Sprint 61 (stabilisation) |
| Disposition | `under-investigation (sprint 61)` |
| Rationale | Sprint 60 Round 5 attempted fix at `src/scheduler.rs::is_typechecked` + `worker.rs` gate reduced the rate but did NOT eliminate the race. Under full-suite pressure the symbol-table-seeded-before-populated window still opens. ~30% fail rate on 8-run stress at close. Documented in `design/backend/defects-456-reduction.md §"Wave 2 Round 4 — heisenbug stress isolation"`. Sprint 61 re-opens the investigation; candidates: (a) strengthen `is_typechecked` to include symbol-table-non-empty check, (b) move symbol publication into the critical section that sets the pool state, (c) invert the typecheck-worker loop so pool transitions fire AFTER symbol publication. |

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

### Exemplar-level tests (non-cargo)

### Exemplar-level tests (non-cargo)

| Field | Value |
|---|---|
| Test name | `exemplar/solver.cl::test-unsolvable` (run via `/run-tests` inside the exemplar, not a cargo test) |
| SHA | `f78adf3` |
| Stderr / observable signature | `(Some "puzzle with two 5s in row 0 should be unsolvable")` — solver returns `Success` on a grid with two `5`s in row 0 where it should return `Unsolvable`. Symptom in `--run` main: "Solution" board with duplicate values in row 0 (e.g. `4 5 3 \| 9 2 1 \| 6 7 7`). |
| Owning skill | `/port` (repro authored), `/qa` (narrow integration test handoff pending), `/backend` (suspected underlying codegen/RC interaction) |
| Target sprint | Sprint 61 |
| Disposition | `exemplar-gap (owner=/port)` with `underlying-owner=/backend` |
| Rationale | `test-unsolvable` was re-enabled in Wave 3 commit `f78adf3` after Defects 4–6 resolved. The solver's `eliminate` no-ops when called on a same-value `Given`/`Solved` cell; patching it to return `None` breaks valid puzzles, implicating peers iteration, Vec COW, or match-arm sharing rather than pure algorithmic logic. `FIXME(/qa)` and `FIXME(/backend)` are filed in `exemplar/solver.cl` lines 380–406 documenting the investigation notes. `/qa` will own narrowing this into a compile-time integration test once `/port` hands off minimal repro per `memory/feedback_cross_skill_minimal_repro.md`. |

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
