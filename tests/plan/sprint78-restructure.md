# Sprint 78 — int restructure: test plan (Phase 3 / `/qa`)

**Status:** PHASE 3 DESIGN — test plan only. No `.rs` authored here (Phase 5
Stage 1 authors the failing tests). Owner: `/qa`.

**Grounding documents:**
- `sprints/SPRINT.md` — scope + Settled decisions (OQ-1 → (b) block-on-scheduler;
  OQ-3 → delete `eval_in_flight` guard gated on a retained H5-replay regression
  test green under `CRANELISP_SCHEDULER_TRACE` stress).
- `design/int/s77-int-restructure.md` §3.5 (why H5/heisenbug cannot recur — the
  soundness claim these tests *evidence, not assert*), §6 (test-regrounding
  implications), §3.4 (OQ-2 cycle-rejection), §5 (step decomposition).
- Memory: `feedback_failing_not_ignored`, `feedback_repros_join_suite`,
  `feedback_validate_tests_against_spec`.

## 0. Framing — this is a regression + soundness plan, not new spec coverage

The restructure is **behaviour-preserving re-plumbing**: `cluster::process_cluster`
becomes the single Pass-0/1/2 orchestration with in-call-stack dependency
threading; the cross-thread `module_sexps`/`suspend_states` parking maps delete
(`SharedState` 16 → 14 fields). The language surface does not change. Therefore
this plan is dominated by:

1. **Soundness evidence** — the in-call-stack model must be *validated under
   `CRANELISP_SCHEDULER_TRACE` stress*, not asserted (SPRINT.md §"Soundness
   obligation"). The H5-replay gate (§1) is the load-bearing test: it GATES the
   OQ-3 guard deletion.
2. **Regression guards** — the existing behaviour-pinning suite must stay green
   *by construction* (§4). Any test that pins *mechanism* (`module_sexps`,
   `suspend_states`, `eval_in_flight`, `ProcessResult::Blocked`, saved
   resume-index, or the `"no parsed sexps for module"` error string that the
   deleted map produced) must reground to the *observable outcome*.
3. **Structural target guard** — the relocated `shared_state_field_count` tracker
   (§3) becomes the standing guard that the maps do not creep back.

"Flaky" is a **banned disposition** on this project (`feedback_failing_not_ignored`,
`feedback_repros_join_suite`). A stress test that intermittently fails is a defect,
not a tolerated cost — it either holds deterministically across the iteration
budget or it has found a real race.

---

## 1. The H5-replay gate test (load-bearing — gates OQ-3 guard deletion)

### Purpose

Replays the H5 race (`s77-int-restructure.md` §3.5) and proves the observable
outcome is deterministic under scheduler-trace stress. **This test gates Step 3
(deletion of `eval_in_flight` + `register_dep_for_eval` republish dance +
`republish_module_sexps_from_symbol_table`).** It must be green *before* the guard
is deleted and stay green *after*. Per `feedback_repros_join_suite` it joins the
suite eternally.

### The H5 scenario (from §3.5)

The race: an eval thread (t1) discovers dep `helper`; before t1 arms its guard, a
worker (t2) has already typechecked `helper`, fired
`notify_typecheck_done(helper)` → `try_unblock_locked(user)`, and begun
typechecking `user` — re-reading `module_sexps[user]` that t1 may not have
re-published. The two-input shape that drives it:

```
helper.cl:  (defn helper-val [] 99)
REPL stdin: (import [helper [helper-val]])
            (helper-val)
            /quit
```

The asserted-correct outcome: stdout contains `99` (the import + call succeeds),
**deterministically**, every iteration.

### Test spec

- **File / name:** `tests/repl_persist_race.rs::h5_replay_gate_deterministic_under_scheduler_stress`
  (lands alongside the existing H5 suite so the regrounded and new tests co-locate).
- **Harness:** `helpers::e2e::Cranelisp` builder (the existing H5 tests pre-date
  the builder and use raw `Command`; the new gate test SHOULD use the builder for
  consistency — it exposes `.repl()`, `.file()`, `.with_prelude(...)`,
  `.env("CRANELISP_SCHEDULER_TRACE", "1")`, `.stdin(...)`, `.output()` →
  `CrOutput { stdout, stderr, status }`). Prelude `PreludeVariant::TestStandard`
  (the import + bare-call shape needs the helper module only; no operators are
  load-bearing — `PreludeVariant::None` is acceptable and preferred if it
  reproduces, per the reduction discipline).
- **Stress shape:** loop `ITERATIONS` times, **recreating the `Cranelisp` builder
  and its tmpdir each iteration** (the builder is single-shot; a fresh tmpdir per
  iteration is the isolation discipline from `tests/CLAUDE.md` §"Fresh Temp
  Directory per Test"). Each iteration runs one subprocess with
  `CRANELISP_SCHEDULER_TRACE=1`.
- **`CRANELISP_SCHEDULER_TRACE=1`** is set on every iteration. Two reasons: (a)
  the trace plumbing changes timing — running *under* the trace is the stress
  condition the soundness obligation names; (b) on any failure the `[SCH]` event
  stream is captured in `stderr` for diagnosis (the test prints it on assertion
  failure, per the existing H5-gate test's pattern).

### What "green under stress" concretely means

- **`ITERATIONS = 50`.** Calibrated against the existing budget: the existing
  `cache_repl_loads_heisenbug_parallel_stress` runs 20 iterations under the <30s
  /qa runtime budget; this test runs one subprocess per iteration (lighter than
  the 2-session cache-delete shape), so 50 is affordable. **Phase 5 Stage 1
  authors at 50 and `/dev` MUST time the run** (`feedback_time_test_runs`); if 50
  iterations exceed ~5s wall for this single test, reduce to the largest count
  that fits the budget and record the calibration in the test comment. The
  iteration count is a *minimum confidence floor*, not a magic number — the H5
  flake was historically ~1/1755, so 50 deterministic passes is not statistical
  proof; it is a structural-reopening tripwire (matching the existing suite's
  explicit reasoning at `repl_persist_race.rs:138-141`).
- **Asserted every iteration:** `stdout.contains("99")` — the import + call
  produced the correct value. This is the *observable outcome*, not an internal-
  state probe.
- **Determinism = zero failures across all iterations.** A single iteration that
  does not contain `99` fails the test loudly with the iteration index + the
  captured `[SCH]` stderr dump. There is no tolerance threshold, no retry, no
  "N-of-M" allowance — those would encode the banned "flaky" disposition.
- **Flakiness detection:** the test is run repeatedly in CI via `cargo nextest run`
  (which parallelises across binaries, applying additional scheduler pressure).
  Because the assertion is binary (all 50 pass or the test fails), a true race
  surfaces as a failing test, never as a silently-tolerated flake. If the test
  ever fails post-deletion, **OQ-3 is wrong** — the guard removal reintroduced the
  race, and Step 3 must revert until the in-call-stack model is corrected.

### Gating relationship

- **Before Step 3** (guard still present): this test is authored and MUST be green
  (it validates the target behaviour holds with the guard in place — establishing
  the baseline the deletion must preserve).
- **Step 3 deletes the guard** only after this test is green.
- **After Step 3:** this test re-runs and MUST stay green with the guard gone.
  Green-here-too is the soundness evidence that the guard's reason-for-being
  evaporated (§3.5).

### Disposition of the existing H5 mechanism-probing tests

The existing `h5_gate_typechecking_user_fires_only_on_repl_thread` parses `[SCH]`
events and asserts on the `eval_in_flight`-suppressed worker-queue-push *mechanism*
(`repl_persist_race.rs:388`). **This test pins mechanism that Step 3 deletes** —
the `eval_in_flight` flag, the `try_unblock_locked` → suppressed-push signature.
Once the guard is gone there is no flag to gate, and the `[SCH]` signature it
asserts the *absence* of may legitimately change shape. **Reground:** replace its
mechanism assertion (no second `Typechecking user` on the worker thread *because
the flag suppressed the push*) with the observable-outcome assertion (the
two-input import sequence produces `99` deterministically — which the new gate
test §1 already covers). The mechanism-gate test is **retired into / subsumed by**
the new `h5_replay_gate_deterministic_under_scheduler_stress`; its `// spec:`
back-trace to `heisenbug-race-closure.md §7.7/§7.8` regrounds to the observable
parity property. `/dev` confirms in Phase 5 whether any residual `[SCH]`-level
invariant survives the deletion worth a separate assertion; if not, the gate test
is the single durable H5 guard.

---

## 2. OQ-2 mutual-import cycle-rejection test

### Purpose

Confirm the in-call-stack shape preserves the scheduler's cycle detection
(`detect_cycle_locked`, Decision 30) — and crucially that the cycle-rejection path
**fires before any wait** (SPRINT.md OQ-2; §3.4: `block_for_typecheck` runs
`detect_cycle_locked` *before* adding the waiter). A 2-node M↔N mutual import must
produce a clean circular-dependency error, not a deadlock or a hang.

### Why a new test (the existing one is insufficient for OQ-2)

`tests/spec_08_modules.rs::module_cycle_detection_neg` exists and asserts a
3-node chain (`main → a → b → a`) is rejected. But the OQ-2 obligation is
specifically about the **2-node mutual import** (M imports N, N imports M) under
the in-call-stack drive — the exact shape §3.4 reasons about ("W blocks M on N; a
worker blocks N on M; the second `block_for_typecheck` detects the M→N→M cycle").
The existing 3-node test does not exercise the tightest mutual-import cycle, and it
does not assert the *timeout/liveness* property (that rejection happens promptly,
not after a hang). A new, tighter test is owed.

### Test spec

- **File / name:** `tests/spec_08_modules.rs::mutual_import_cycle_rejected_before_wait_neg`
  (negative test — `_neg` suffix per the naming convention).
- **`// spec:`** `spec/08-modules.md §8.10 — circular module imports MUST be
  rejected`. (Same spec anchor as the existing 3-node test; this is the 2-node
  in-call-stack variant.)
- **Harness:** `Cranelisp` builder, `--run` mode (cycle detection is a
  compile-time property independent of mode; `--run` is the simplest).
- **Scenario (tightest 2-node mutual import):**
  ```
  main.cl:  (import [m [f]])
            (defn main [] (f))
  m.cl:     (import [n [g]])
            (defn f [] (g))
  n.cl:     (import [m [f]])      ; closes the m↔n cycle
            (defn g [] (f))
  ```
  (A direct `main → m → n → m` 2-node cycle between `m` and `n`; `main` is the
  entry.)
- **Assertions (positive + liveness):**
  1. `!out.status.success()` — the program is rejected (matching the existing
     test's assertion shape; the diagnostic text need not say "cycle" per the
     existing test's note — that is a UX gap, not a spec violation).
  2. **Liveness:** the subprocess **terminates** (does not hang). The `Cranelisp`
     builder exposes `.timeout(Duration)`; the test sets a tight bound (e.g. 10s)
     so a *deadlock regression* surfaces as a timeout failure, not an infinitely-
     hanging test. This is the OQ-2 "fires before any wait" evidence: rejection is
     prompt, not after a block-and-deadlock.
- **Negative-coverage note:** this is a `_neg` test by construction (it asserts a
  wrong thing — silent success / a hang — does NOT happen). It upgrades the
  §8.10 spec annotation toward `[Tested+Neg]` for the 2-node mutual case.

---

## 3. Relocated `shared_state_field_count` guard

### Current state

`tests/facade_pif_rows.rs::shared_state_field_count_matches_facade_after_pif`
(line 590) counts `pub` fields in `pub struct SharedState` in
`src/session_v4.rs` and asserts `<= 14`. It currently **fails at 16** (SPRINT.md
§Notes: the 1 failure in the S77 close ledger). Per FIXME 0298 it introspects an
int-*internal* struct, so it does not belong in the **boundary-conformance** file
`facade_pif_rows.rs`.

### Relocation (coordinated with design §6)

- **Move OUT of** `tests/facade_pif_rows.rs` (boundary-conformance — public-API +
  facade rows only).
- **Into** an int-internal structural-target tracker. **Landing file:**
  `tests/regression.rs` is the canonical home for int-internal structural guards
  that are not boundary-conformance and not a single spec-section behaviour
  (it already hosts cross-cutting regression guards). If `/dev`/`/sprint` prefer
  a dedicated file, `tests/int_internal_targets.rs` is the alternative — but a new
  file adds a `mod helpers;` + harness boilerplate cost for a single test, so
  `regression.rs` is the recommended landing. **`/qa` authors the relocation in
  Phase 5 Stage 1** (delete from `facade_pif_rows.rs`, add to `regression.rs`).
- **Assertion after relocation:** `field_count == 14` (tighten from `<= 14` to
  `== 14` once Step 2 lands, per design §6 action 2 — "Tighten to `== 14` once
  landed if no slack is wanted"). Rationale: the restructure removes exactly 2
  fields (`module_sexps`, `suspend_states`) from 16; `register_dep_for_eval` /
  republish removal sheds *methods, not fields*, so the count is exactly 14.
  Phase 5 `/dev` confirms the post-Step-2 count; if a transient field of slack is
  genuinely needed, fall back to `<= 14` with a comment naming the slack field.
- **Status until Step 2 lands:** **failing-not-ignored** at 16 (it is in scope
  this sprint). It is NOT `#[ignore]`'d — per `feedback_failing_not_ignored` the
  in-scope failure is the loud signal. It flips green when Step 2 deletes the maps.
- **`// spec:`** regrounds from the facade anchor to the design-target anchor:
  `design/int/s77-int-restructure.md §2.3 — SharedState drops 16 → 14 fields after
  module_sexps/suspend_states deletion`. (Note: FIXME 0298's W-Retire — facade
  reorg — runs AFTER the restructure, NOT in S78; until then the facade's
  `module_sexps`/`suspend_states` rows are a stale-but-harmless tombstone, and
  THIS relocated tracker is the durable guard that the rows reached target —
  design §8.)
- **Standing-guard role:** after the restructure this test is the permanent guard
  that `module_sexps`/`suspend_states` (and any equivalent cross-thread in-progress
  parking map) do not creep back onto `SharedState`.

---

## 4. Behaviour-preservation set (must stay green by construction)

These existing tests pin behaviour the restructure MUST NOT change. For each:
(a) the real test name (VERIFIED in-tree); (b) whether it pins *behaviour* or
*mechanism*; (c) reground action if it asserts on a deleted internal.

| # | Test (verified real name) | File | Pins | Reground action |
|---|---|---|---|---|
| 4.1 | `defn_before_import_resumes_correctly_after_dep_load` | `spec_08_modules.rs:894` | **Behaviour** — a defn declared *before* an import survives the dep-load suspension (§8.10.1). Asserts clean stderr (no error text). In the retry-from-top model the forms-before-import are always re-processed, so the property holds by construction (design §5 Step 4, OQ-4). | **Keep green unchanged.** Does NOT assert on `pass2_resume_index`/`suspend_states`/saved-index — it asserts the observable property (clean compile). No reground needed. ⚠ Carries a `XXX(/backend) FIXME 0149` deferred `assert_exit(42)` (run-mode SEGV on this shape) — that is a *separate downstream* defect, out of S78 scope; do NOT let the restructure be blamed for it, and do NOT enable the exit assertion this sprint. |
| 4.2 | `cache_repl_loads_heisenbug_parallel_stress` | `repl_persist_race.rs:127` | **Behaviour** — 20-iteration import-then-restart stress; asserts stdout `99` both sessions. | **Keep green unchanged.** Observable-outcome assertion only; no internal probe. The "ONE orchestrator per module" comment regrounds naturally (the in-call-stack model is the stronger one-orchestrator guarantee). |
| 4.3 | `heisenbug_race_reduced_concurrent_import_pairs` | `repl_persist_race.rs:206` | **Behaviour** — 6-thread × 2-pair concurrent import repro; asserts no "not found in module" signature, stdout `99`. | **Keep green unchanged.** Observable-outcome (helper-val resolves). Carries residual H6/H7 surface note — if it begins failing post-restructure, that is a real regression to triage, not a tolerable flake. |
| 4.4 | `h5_gate_typechecking_user_fires_only_on_repl_thread` | `repl_persist_race.rs:388` | **MECHANISM** — parses `[SCH]` events, asserts the `eval_in_flight`-suppressed worker-queue-push signature (the *absence* of a second `Typechecking user` on the worker thread *because the flag suppressed the push*). | **MUST REGROUND** (§1 last subsection). The asserted mechanism (`eval_in_flight` gate) is deleted by Step 3. Reground to the observable parity outcome — subsumed by the new `h5_replay_gate_deterministic_under_scheduler_stress` (§1). `/dev` confirms in Phase 5 whether any surviving `[SCH]` invariant warrants a separate assertion; default is to retire this test into the gate test. |
| 4.5 | `h5_normal_completion_does_not_starve_repl_eval_thread` | `repl_persist_race.rs:582` | **MECHANISM-adjacent** — asserts the RAII `EvalInFlightGuard` does not starve the eval thread on the normal-completion path (the guard's `Drop` clears `eval_in_flight`). | **MUST REGROUND** — the `EvalInFlightGuard` deletes with Step 3 (the whole starvation class is about the guard's RAII discipline). The *observable* property it protects (the normal import+call completes, does not hang) regrounds to a liveness assertion: the import+call subprocess terminates and yields `helper-val=42` within a timeout. The guard-specific reasoning retires. |
| 4.6 | `repl_dep_load_no_race_with_persistent_workers` | `repl_persist_race.rs:718` | **MECHANISM-derived assertion** — asserts the **absence** of the error string `"no parsed sexps for module"` (emitted when a worker dequeued a Typecheck task before `module_sexps` was published). | **MUST REGROUND** — `module_sexps` deletes (Step 2), so the `"no parsed sexps for module"` error string can no longer be produced; the assertion becomes vacuously true and stops guarding anything. Reground to assert the **positive** observable outcome: the REPL `(import [collections.list [Cons Nil]])` + `(Cons 1 Nil)` produces a successful result (stdout shows the constructed value / no error). This converts a "wrong-string-absent" guard into a "right-outcome-present" guard — strictly stronger. |
| 4.7 | `module_cycle_detection_neg` | `spec_08_modules.rs:203` | **Behaviour** — 3-node `main→a→b→a` import cycle is rejected (`!status.success()`). | **Keep green unchanged.** Observable rejection; complements the new tighter 2-node §2 test. Add `.timeout()` liveness if convenient (cheap robustness against a deadlock regression), but not required. |
| 4.8 | FQ-autoload / dep-chain e2e suite: `import_dependency_compiles_correctly` (`:322`), `nested_dependency_chain_compiles` (`:433`), `multi_dot_module_path_in_import` (`:408`), `import_below_use_still_available_before_definitions` (`:293`), `multiple_import_forms_in_one_module` (`:863`) | `spec_08_modules.rs` | **Behaviour** — dependency-resolution + FQ-autoload (the Pass-1-already-in-call-stack path §2.2.1 the restructure generalizes). All assert observable exit codes (`assert_exit(N)`). | **Keep green unchanged.** All assert observable outcomes (exit codes), none probe internals. These are the regression spine that the in-call-stack dep-drive preserves dependency resolution. |
| 4.9 | Cluster-atomicity / staging tests: `process_form_dispatch_macro_after_import_succeeds_in_one_eval`, `..._begin_cluster_resolves_mutual_forward_ref`, `..._bare_forward_ref_errors_clearly`, `..._function_gap_does_not_speculatively_jit` | `tests/process_form_dispatch.rs` | **Behaviour** — staging commit-on-Ok / discard-on-Err contract. The staging core moves files (`worker.rs` → `cluster.rs`) but its contract is identical (design §6 "Cluster-atomicity tests … unchanged"). | **Keep green unchanged — VERIFIED (Phase 3).** Assertions are all *observable* outcomes (stdout `:primitives/Int 42`, `/list` shows `g` not `f`, no `JitWrite` GOT-trace for the gapped fn). `process_cluster`/`process_module_forms` appear in **comments only**, never in an assertion; `ProcessResult::Blocked` is never asserted. No reground owed. |

**Mechanism-pinned tests requiring reground (summary):** 4.4, 4.5, 4.6 (all in
`repl_persist_race.rs`, all coupled to the `eval_in_flight`/`module_sexps`
internals Step 2/3 delete). All reground to **observable outcomes** (deterministic
correct value / liveness / positive success), never to a new internal. The
reground is part of Step 6 (test-regrounding), gated as below. **4.9 verified
clean in Phase 3** — no reground owed (observable-outcome assertions only).

---

## 5. Gate map — Phase-5 step → gating test(s)

Per design §5 the `/dev` landing order is **(Steps 1+2 together, indivisible
red→green) → Step 3 → Step 4 → Step 5 → Step 6**. `/qa` authors the failing tests
in Phase 5 Stage 1 *before* the per-crate cycles (QA-first). The gate map tells
`/sprint` which test(s) must be green for each step to advance.

| Phase-5 step | What it does | Gating test(s) — must be green to advance | Notes |
|---|---|---|---|
| **Steps 1+2** (indivisible, build-red span) | Lift Pass-0/1/2 into `cluster::process_cluster`; carry sexps on the packet; in-call-stack gap-drive; **delete `module_sexps` + `suspend_states`** | **§3** `shared_state_field_count` (relocated) flips 16 → 14/`==14`; **§4.1** `defn_before_import_resumes...`; **§4.2/4.3** heisenbug stress suite; **§4.8** FQ-autoload/dep-chain suite; **§4.9** cluster-atomicity. **§1** H5-replay gate green *with guard still present*. **§4.6** reground (the `"no parsed sexps"` guard becomes vacuous once the map is gone — reground concurrently). | The build is red *between* 1 and 2 (expected — facade-walk-leaves-build-broken). Baseline regen at the END of the span only. This is the center of gravity + entire risk. |
| **Step 3** delete `eval_in_flight` guard | Remove `EvalInFlightGuard` + `eval_in_flight` flag + `register_dep_for_eval` republish + `republish_module_sexps_from_symbol_table` | **GATE: §1** `h5_replay_gate_deterministic_under_scheduler_stress` MUST be green under `CRANELISP_SCHEDULER_TRACE` stress (50 iterations, zero failures) **both before AND after the deletion**. Plus **§4.5** reground (starvation test loses the guard it probes). Plus **§4.4** reground (H5 gate mechanism test retires into §1). | **This is the OQ-3 gate.** If §1 ever fails post-deletion, OQ-3 is wrong — revert Step 3. SPRINT.md: "delete, gated on H5 test." |
| **Step 4** retire `process_module_forms` | Delete the legacy per-form loop; thin `handle_typecheck_work_shared` | **§4.1** `defn_before_import_resumes...` stays green (Defect-B / OQ-4 "resume restarts Pass 2 from 0" preserved-by-construction — retry-from-top has no saved index). **§4.9** cluster-atomicity stays green. | Mostly deletion once 1–2 land. |
| **Step 5** scheduler cleanup | Remove `resume_from_form`/`set_resume_from_form`/dead `PriorityEntry`/`BlockingJitCodegen` | Whole behaviour-preservation set (§4) stays green. No new gate test — dead-code removal. | Risk LOW per design. |
| **Step 6** reground tests | Relocate `shared_state_field_count`; reground the mechanism-pinned tests | **§3** lands in `regression.rs` at `==14`; **§2** new mutual-import cycle-rejection test authored + green; **§4.4/4.5/4.6** regrounds committed (mechanism → observable). Full suite green except known-deferred (FIXME 0149 run-mode SEGV on §4.1's shape — out of scope). | The `// spec:` annotations reground from facade/mechanism anchors to design-target/observable anchors. |

---

## 6. New tests owed (authored Phase 5 Stage 1 by `/qa`)

| Test | File | Type | Spec/design anchor |
|---|---|---|---|
| `h5_replay_gate_deterministic_under_scheduler_stress` | `repl_persist_race.rs` | e2e stress (50 iter, `CRANELISP_SCHEDULER_TRACE=1`) | `s77-int-restructure.md §3.5` — H5 cannot recur (observable parity) |
| `mutual_import_cycle_rejected_before_wait_neg` | `spec_08_modules.rs` | e2e negative + liveness | `spec/08-modules.md §8.10` (2-node in-call-stack variant); `s77 §3.4` |
| `shared_state_field_count_matches_facade_after_pif` → relocated as `shared_state_field_count_at_target_14` | `regression.rs` (FROM `facade_pif_rows.rs`) | structural target guard | `s77 §2.3` — 16 → 14 fields |

**Regrounds owed (existing tests, edited in Step 6):** §4.4, §4.5, §4.6 to
observable outcomes; §4.9 verification of `process_form_dispatch.rs` assertions.

---

## 7. Phase-3 exit assessment

**Does this plan give `/dev` + `/qa` enough to author failing tests in Phase 5
Stage 1?** **Yes**, with two non-blocking calibration caveats:

1. **§1 iteration count (50)** is a calibration floor; `/dev` times the run in
   Phase 5 and adjusts down only if the <30s suite budget is threatened, recording
   the calibration in-test.
2. **§3 landing file** (`regression.rs` recommended; `int_internal_targets.rs`
   alternative) — `/sprint`/`/dev` may ratify either; the *assertion* (`==14`) and
   the *out-of-facade_pif_rows* move are fixed.

The entire behaviour-preservation set (§4) has been read and classified in
Phase 3 — including `process_form_dispatch.rs` (§4.9), which is verified clean
(observable-outcome assertions only, no mechanism coupling). No file in the set is
left unread.

**Nothing is blocked on a missing spec or design decision.** OQ-1 (b), OQ-3
(delete-gated-on-§1), OQ-2 (cycle-before-wait), OQ-4 (Defect-B preserved-by-
construction) are all settled in SPRINT.md; the tests evidence them. No FIXME is
owed to `/spec`, `/arch`, or `/design` from this plan — the restructure is
int-interior re-plumbing with no language-surface change.
