# Sprint 61: Stabilisation — isolate, instrument, fix each defect serially

**Status**: ACTIVE (Phase 5 — Wave 1 opened 2026-04-22; serial execution per user directive — one agent at a time)
**Ring**: 4 (Effects — stabilisation)
**Goal**: Honest 0 carried failing tests. Close the four Sprint 60 defects one at a time by isolating the actual issue, fixing it, and verifying before moving on. Invest in tracing & inspection infrastructure first so the intermittent races yield to observation rather than hypothesis. Precondition for Sprint 62's FQTypeName migration.

## Scope

Sprint 60 closed at 1837 passed / 2 intermittent failures under full-suite pressure, plus an exemplar correctness gap and a bare-primitive-name REPL defect. Sprint 61 closes these four defects **serially**, not in parallel. Each slice follows a strict cycle: isolate → fix → verify → move on. Races and state-sharing bugs can mask each other; closing them one at a time means each fix is verified against a known-green baseline before the next investigation starts.

**Default diagnostic stance**: do not assume a compiler bug. User-facing agents (`/port`, `/examples`, `/repl`) own fixing their own tests/code until they produce a repro that isolates an actual compiler bug. Only then does cross-skill handoff to `/int`, `/backend`, or `/platform` happen.

**Foundational workstream**: the two intermittent races (Defects 1 and 2) will not yield to hypothesis-driven investigation without better observability. Tracing & inspection infrastructure lands FIRST (Slice 0) so the race-diagnosis slices have the instrumentation they need.

### The four defects

| # | Failure / defect | Current owner | Slice |
|---|---|---|---|
| 1 | `sprint23::cache_repl_loads_heisenbug_parallel_stress` — ~30% fail rate, scheduler/worker publish-vs-flag race | `/int` | 3 |
| 2 | `examples_run::every_example_file_runs_under_examples_prelude` — `21-hello-io.cl` intermittent exit 201 | TBD at Slice 4 (`/backend`, `/platform`, or `/qa`) | 4 |
| 3 | `exemplar/solver.cl::test-unsolvable` — solver returns `Success` on unsolvable grid; duplicate values in solution | `/port` (owns fix OR isolation) | 2 |
| 4 | Bare-primitive-name at REPL prompt — `add-i64` errors while `/sig add-i64` and `(add-i64 2 3)` resolve | `/int` | 1 |

### Slice discipline

Each slice follows the same sequence:

1. **Isolate.** Reduce the symptom to a minimal repro. For user-facing defects, this is the owning user-proxy skill's job; they reduce until the bug either reveals itself as their own issue (they fix it) or manifests in non-user-facing code (they hand off with repro attached). For race defects, the reduction target is a deterministic or near-deterministic trigger.
2. **Fix.** Address the root cause in the correct crate. No drive-by fixes in adjacent code.
3. **Verify.** Run the failing test N times consecutively (N per the table below). Close the slice.
4. **Commit & move on.** Each slice closes with a commit and an updated baseline before the next slice opens.

**Verification thresholds:**

| Slice | Test surface | Intermediate slice-close gate | Notes |
|---|---|---|---|
| 1 | Bare-primitive REPL echo | 5 | Deterministic defect; 5 suffices |
| 2 | Exemplar `test-unsolvable` | 5 | Deterministic defect; 5 suffices |
| 3 | Heisenbug race | **10** | Race; intermediate tier per /arch Phase 2 review |
| 4 | 21-hello-io exit 201 | **10** | Race; intermediate tier per /arch Phase 2 review |

**Close-gate aggregate** ~~(final sprint close)~~: **SUPERSEDED 2026-04-22 by methodology pivot — see below.** The original gate was **20** consecutive full-suite `cargo nextest run --no-fail-fast` passes at 0 failures.

**Methodology pivot — stress-run verification retired as primary gate** (user directive 2026-04-22 after Wave 3 Slice 3 revealed the approach's limits):

- **Statistical illusion**: N-run 0-failures proves the failure rate is `<1/N` with ~63% confidence (1-1/e). It does not prove "0 races." A 5% true rate has a ~36% chance of passing a 20-run gate. "Clean today" ≠ "no race."
- **Non-deterministic coverage**: race reproduction depends on OS scheduler, machine load, other concurrent tests. Wave 3 observed the heisenbug harness pass 10/10 in isolation, 3/25 fail at `--test-threads=6`, and 15/15 at `--test-threads=8`. Contention geometry matters; stress runs don't control it.
- **Post-hoc verification**: stress tests catch "this specific scheduling fired the race today." They do not enumerate the interleaving space or prove invariants.

The 20-run stress verification is retained as a **weak regression guard** (useful for detecting a regression reopens a known race) but is NOT sufficient as a proof of race closure. See §"Revised Wave 3 close criteria" and S62 plan below.

**Revised Wave 3 close criteria** (2026-04-22):

- Three named race mechanisms (H4/H5/H6) each have: evidence-dump + hypothesis + fix + unit-test + integration-regression guard.
- /arch approval across all hypothesis iterations.
- /review PASS + /typecheck pre-commit approval (narrow precedent).
- Residual `heisenbug_race_reduced_concurrent_import_pairs` failures at ~5-10% under 6-thread contention are ledgered honestly with the same signature as pre-fix. NOT dispositioned "flaky" or "resolved" — dispositioned `under-investigation (sprint 62 — concurrency audit)`.
- Escaped baseline carries uncovered during workspace stress (5 `d6_exemplar_*` + `wave6_demo_repros::exemplar_solver_*`) added to ledger.

**What replaces the stress gate (S62 workstream)**: see §Out of Scope "FQTypeName displaced → Concurrency audit now S62 primary."

### Out of Scope (deferred with rationale)

- **FQTypeName migration** — ~~Sprint 62 primary workstream~~ **DISPLACED 2026-04-22**. Now Sprint 63+ or later. Concurrency audit takes S62's primary slot. FQTypeName is a boundary-type refactor with no concurrency dimension; it can land any time after the audit and doesn't block anything.
- **Concurrency audit + `loom` adoption + structured interleaving tests** — **Sprint 62 primary workstream** (user directive 2026-04-22 after Wave 3 revealed stress-run verification is insufficient). Three work elements:
  1. **Audit**: enumerate every shared-state access site in `crates/cranelisp-typecheck/` and `src/scheduler.rs` + `src/worker.rs` + `src/session_v4.rs`. Classify each as atomic / under-lock / relaxed-ordering / racy. Document invariants. Grep for all instances of the H6 non-atomic-check-then-insert pattern.
  2. **`loom` adoption**: introduce `loom` (Rust's permutation model checker) for the scheduler's shared state + DashMap-backed `modules` table. Mechanically enumerate interleavings up to a bounded depth. Prove absence of races for the documented invariants.
  3. **Structured interleaving tests**: author tests using `std::sync::Barrier` / atomic phase-markers to force specific interleavings, replacing the Wave 3 stress-style tests. Deterministic verification of the H4/H5/H6 invariants at unit level.
  S62 precondition: Wave 3 code committed + Wave 4/5 closed (Slice 4 21-hello-io, Slice 5 methodology cleanup).
- **Performance baseline** — Ring 4 AC `Performance within 2x of prototype` still NOT MEASURED. Future sprint.
- **Decision 30 module-system redesign** — parent↔child typecheck deadlock. Future research.
- **Stdlib prelude monolith remediation** — FIXME(/stdlib) on `stdlib/plan-stdlib.md §3.2` carries to S62+.
- **BL range fix, Ring 4 RC-balance adoption completion** — roadmap-deferred.
- **Phase H / Tier 2 release backend** — post-Ring-4.
- **Full `/trace` slash command for live REPL inspection** — out of scope for Slice 0; observability work in S61 is sized to what Slices 3 and 4 actually need, not a general-purpose inspection surface. Future sprint candidate.

### `/int` burden assessment

**HIGH.** `/int` owns Slice 0 (shared with `/backend`), Slice 1, and Slice 3. `/backend` owns the other half of Slice 0 and potentially Slice 4. `/port` owns Slice 2 end-to-end (unless it escalates to a compiler bug). `/qa` carries methodology + cleanup (Slice 5). If Slice 3's race closure requires restructuring `register_dep`'s critical section or the scheduler state-transition protocol, burden escalates to Sprint-60-A scale — `/int` flags at Slice 0 readout and `/sprint` re-scopes with user approval before implementation.

## FIXME Debt

Phase 1 scan, in-scope for this sprint:

| File | Owning Skill | Issue | Slice |
|------|-------------|-------|-------|
| `src/scheduler.rs`, `src/worker.rs` | `/int` | Heisenbug race — publish-vs-flag ordering | 3 |
| `tests/examples_run.rs`, `examples/21-hello-io.cl`, trampoline/platform stdio | TBD | IO exit 201 under stress | 4 |
| `exemplar/solver.cl:380,403` (2 inline FIXMEs) | `/port` | `test-unsolvable` — fix or isolate | 2 |
| `src/session_v4.rs` bare-name-value path | `/int` | Bare-primitive-name invisibility | 1 |
| `design/int/observability.md` (new) | `/int` + `/backend` | Scheduler + IO trampoline event logs | 0 |
| `tests/CLAUDE.md` | `/qa` | Fresh-TempDir-per-test rule | 5 |
| `.claude/commands/sprint.md` Phase 6 close checklist | `/sprint` (user approval) | 20-run stress verification requirement | 5 |
| ~~`.gitignore`~~ | — | **ALREADY SATISFIED** — `.gitignore:31` carries `tests/sprint60/.runs/` (landed post-S60-close, before S61 opened). Slice 5 F dropped. | — |
| `src/session_v4.rs::persistent_worker_tests` | `/int` | S60 /review S2 test rename | 5 |
| `spec/*.md`, `repl/spec.md` annotations | `/qa` | `[Tested+Neg]` promotions (3–5 target) | 5 |

**Out-of-scope FIXMEs carried forward** (noted, not addressed):

- `FIXME(/backend)` at `crates/cranelisp-runtime/src/io.rs:28` — partial Ring 2 RC migration continues under ring4 RC-balance adoption.
- `FIXME(/stdlib)` at `stdlib/plan-stdlib.md §3.2` — prelude monolith remediation.
- 26 `FIXME(/qa)` entries in `tests/plan/ring4.md` — ongoing /qa test-plan hygiene.
- Several `FIXME(/arch)`, `FIXME(/frontend)`, `FIXME(/typecheck)` in design docs — triaged by owning skills in Phase 3.

## Architecture Review

**Reviewer**: `/arch`
**Date**: 2026-04-21
**Verdict**: APPROVE WITH REVISIONS

### 1. Technical coherence

The scope forms a complete, testable stabilisation increment. Four defects, one foundational observability workstream, one methodology cleanup — an honest 0-carries close is the falsifiable acceptance criterion and it is the correct Sprint 62 precondition per the reimplementation roadmap.

**Scoping of the four defects is correct:**

- Defect 1 (heisenbug race) and Defect 2 (21-hello-io exit 201) are concurrency-shape failures that will not yield without better observability. The draft's sequencing (Slice 0 lands first, then Slices 3/4 consume the event logs) is sound.
- Defect 3 (`test-unsolvable`) is correctly owned by `/port` with explicit branch points. The "default assume exemplar bug, reduce, escalate only on non-solver repro" stance matches `memory/feedback_cross_skill_minimal_repro.md`.
- Defect 4 (bare-primitive-name at REPL) is the smallest, deterministic, and functions as the warm-up slice to exercise the isolate→fix→verify cadence before the race work starts.

**Serial-slice discipline is correct for this sprint.** Race defects mask each other: a fix to the scheduler publish/flag ordering may make the IO exit 201 signature shift (or disappear, or get worse), and running both investigations in parallel would conflate evidence. Each slice's close commit serves as a verified-green baseline for the next — this is the protocol Sprint 60 close-gate promised to install (the "20 consecutive runs" stress verification).

**Exception to serial discipline that is explicitly allowed:** Slice 2 (`/port`-owned, exemplar `.cl` code, no compiler changes) can overlap with Slice 1 (`/int`-owned, `src/` changes). Different skills, different files, no shared state. The draft correctly calls this out in §"Slice Execution Order" item 3. Slice 5 (methodology cleanup) is opportunistic throughout.

**No dependencies force earlier parallelisation.** Slice 0's event logs are consumed by Slices 3 and 4 only; Slice 1 does not need them (deterministic defect, 5-run threshold). Slice 2 does not need them. The DAG is Slice 0 → {Slice 3, Slice 4} and Slices 1/2/5 are orthogonal.

**Realism caveat on the 20-run gate.** Full suite × 20 at ~30s per run is ~10 minutes per gate. The draft §Notes proposes tiering to 10 for intermediate and 20 for final. **Recommendation: apply tiering at intermediate slice gates; keep 20 at final close only.** This halves the wall-clock cost through the sprint and preserves the discriminating power at the close (where detecting a ~30% race requires the high threshold). Record this tiering explicitly in the updated Phase 6 checklist E-2 proposes.

### 2. No interim architecture (Principle 8)

Slice 0's observability infrastructure is the decision point under Principle 8. The two event logs (scheduler/worker, IO trampoline) are **durable, not throwaway**, provided they are placed and designed as below. The design should survive Ring 4+ because:

- The scheduler/worker event log captures the same state transitions that the persistent-worker refactor (Decision 27, G9 complete) operates on. Ring 4 onwards the scheduler/worker topology is stable per `pipeline-v4.md` §3 — the event taxonomy does not churn.
- The IO trampoline event log captures Pure/Bind/Par/PlatformEffect transitions that are the spec-frozen surface (`spec/10-effects.md` §10.12 `bind!`, §10.10 platforms). The event shape tracks the spec, not the implementation.
- Both logs are a pattern the project already uses — `CRANELISP_RC_TRACE`, `CRANELISP_CODEGEN_TRACE`, `CRANELISP_CODEGEN_DUMP`, `CRANELISP_INFER_TRACE`, `CRANELISP_MACRO_TRACE`, `CRANELISP_MODULE_TRACE` (per `tests/CLAUDE.md §"Diagnostic Logging"`). Sprint 61 adds two more consistent with the established discipline, not a new architectural pattern.

**Crate placement — THIS IS WHERE PRINCIPLE 3 BITES.** The draft is silent on crate placement and `/int` + `/backend` must not pick independently.

- **Scheduler/worker event log: `src/` (binary crate, thread-local state in `src/session_v4.rs` or a new `src/observability.rs`).** Rationale: the scheduler and worker are `src/`-owned (`src/scheduler.rs`, `src/worker.rs`). Their event log is an observation of integration-layer state that does not cross any crate boundary. Putting this in `cranelisp-shared` or `cranelisp-runtime` would invert Principle 3: those crates are stable, the scheduler is integration-layer, and the event taxonomy follows the scheduler's shape.
- **IO trampoline event log: `cranelisp-runtime` (thread-local state in `crates/cranelisp-runtime/src/io.rs` or a new `cranelisp-runtime::trace` module).** Rationale: the IO trampoline is runtime-owned (`crates/cranelisp-runtime/src/io.rs`). Its event taxonomy (Pure/Bind/Par/PlatformEffect/cont-push/cont-pop) matches the runtime's state machine. This is the correct stable home.

**What MUST NOT happen:**

- Event types MUST NOT appear in any serialised format — not in `.meta.json` (cache), not in `SymbolTable<C, L>`, not in any boundary type in `cranelisp-types`. The answer to the draft's implied question is unambiguous: **No, event types are runtime-only, `#[serde(skip)]` would not even apply because they should never appear on any serialised struct.** Confirm.
- Event logs MUST NOT allocate on the Cranelisp heap (`cranelisp_alloc`). Use `std::sync::Mutex<VecDeque>` or a lock-free ring, backed by the host allocator. Mixing RC-traced allocations into a trace that is itself observing RC-traced allocations creates infinite recursion.
- The `Send + Sync` guarantees on event structs must be explicit. Thread-local ring buffers are the default; cross-thread merge-sort happens at dump time, not during event recording.

**Env-var-gated zero cost when off is a hard requirement.** The draft lists `CRANELISP_SCHEDULER_TRACE=1|module_name|*` — the parse cost of the filter string must happen once at session start, not per event. A `std::sync::OnceLock<TraceFilter>` or equivalent is the right shape.

### 3. Design references

**Slice 0 — `design/int/observability.md` (new, `/int` + `/backend` co-authored).** Must cite:
- `tests/CLAUDE.md §"Diagnostic Logging"` — the existing env-var convention and naming pattern.
- `design/int/concurrent-workers.md`, `design/int/persistent-workers.md` — the scheduler/worker topology whose transitions are being observed.
- `crates/cranelisp-runtime/src/io.rs` + `spec/10-effects.md §10.12` — the IO trampoline's state machine.
- **New architectural note**: the two logs are parallel patterns, NOT a single shared infrastructure. No cross-crate dependency between them. The merge-sort across threads happens at dump time by timestamp + thread-id.
- A "Sketch comparison" section per `CLAUDE.md §"Sketch Oracle"`: the sketch has ad hoc `eprintln!` tracing scattered through `sketch/src/session.rs` and no structured event log. Divergence is justified by the reimplementation's persistent-worker concurrency, which makes ad hoc tracing useless (events interleave).

**Slice 1 — `design/int/bare-primitive-value-path.md` (new, `/int`).** Must cite:
- `repl/spec.md §1.1` — the universal `:Type name ; classification - docstring` format. The bare-value path's expected output form is specified there.
- `spec/08-modules.md §8.9` (re-exported-name behaviour) — if Slice 1 surfaces that re-exported primitives have spec-divergent value-position semantics vs call-position, file FIXME(/spec). The draft's §/spec plan already anticipates this.
- `design/int/dual-path-persistence-collapse.md` — the "two paths must not diverge" discipline Sprint 59 established. Bare-value vs introspection vs call is a fresh instance of the same anti-pattern.
- Decision 22 (`defined_symbols()` predicate) — if the divergence is in which symbol-filter the bare-value handler consults, the fix aligns all three paths on the same filter.

**Slice 3 — `design/int/heisenbug-race-closure.md` (new, `/int`).** Must cite and boundary-concern:
- `design/arch/concurrent-pipeline.md §7` — the form-by-form scheduler's pool-state-transition protocol. The three hypotheses in the draft (Slice 3 §Isolate) are each precisely about this protocol.
- Decision 30 (form-by-form scheduler's mutual-import deadlock) — sets context on the scheduler's current design constraints; `/arch` confirms fixing the publish-vs-register race does NOT require a module-system redesign (that is out of scope per draft §Out of Scope).
- `crates/cranelisp-types/src/module.rs` `SymbolTable` — **if** hypothesis 1 holds (is_typechecked too permissive) AND the fix is to tighten the predicate to check symbol-table-non-empty, that requires a new predicate method on `SymbolTable` but not a shape change. `/arch` confirms this is interface-internal.
- `src/session_v4.rs` `SharedState` — **if** hypothesis 2 or 3 holds (symbol publication outside critical section, or pool transition before publication), the fix is entirely inside `src/scheduler.rs` + `src/worker.rs`. No `SharedState` shape change is expected.
- **Boundary concerns `/arch` calls out now:** The fix MUST NOT introduce a new synchronisation primitive on any `cranelisp-types` boundary type. If the proposed fix touches `SymbolTable`'s internal `DashMap`-level ordering guarantees, file FIXME(/arch) before implementation.

**Slice 4 — ownership TBD at readout.** No design doc is authored until the hypothesis is pinned. This is correct — writing a design doc before the IO trampoline event log produces evidence would be speculation. `/arch` will review whichever doc lands.

### 4. Interface gaps

**No boundary-type changes required for Sprint 61, conditional on the following:**

- **Slice 0**: Event-log ring buffers are thread-local inside `src/` (scheduler log) and `cranelisp-runtime` (IO log). They do NOT appear in `cranelisp-shared`, `cranelisp-types`, or any serialised format. **Confirm**: yes, this is the only correct placement under Principle 3.
- **Slice 1**: The bare-primitive fix is a single-site alignment in `src/session_v4.rs::eval_v4`. No `SymbolInfo`, `ModuleEntry`, or introspection type changes.
- **Slice 3**: The three fix candidates all live inside `src/scheduler.rs` + `src/worker.rs`. The "tighten `is_typechecked` to include symbol-table-non-empty" candidate adds a new check using `SymbolTable::symbols.is_empty()` (already public in the `DashMap` API) — no shape change on `SymbolTable`. The "move symbol publication into the critical section" candidate is an ordering fix inside `SharedState`'s existing locks. The "invert pool-transition ordering" candidate is a statement reorder in the typecheck-worker loop. None require an interface change.
- **Slice 4**: If the trampoline continuation-state leak hypothesis holds, the fix is inside `crates/cranelisp-runtime/src/io.rs` and is specifically the `rc::dec_shallow_io` primitive area (Decision 29). No `Code`, `CacheEntry`, or platform ABI type changes are expected — the continuation stack is a Vec owned by the trampoline, a bug would be an ordering or RC-count error inside `run_io_trampoline`, not a shape change.
- **Slice 4 (alternative hypothesis)**: If the exit 201 is a stdio DLL buffer ordering issue under concurrent subprocess load, the fix lives in `platforms/stdio/` (`/platform`-owned) and does not touch the platform ABI (Decision 26 `scheduling_class` + `platform_fn_ptr` shape is stable).

**Pre-authorised interface amendments**: None. If Phase 3 surfaces a genuine boundary need (e.g., a new `SymbolTable` predicate method, a new event-dump entry point on a `SharedState` method), `/int` or `/backend` MUST file FIXME(/arch) in the design doc before implementation. `/arch` reviews before any `cranelisp-types` change commits. Post-Wave-3b `SymbolTable<C, L>` is stable and further churn is expensive.

### 5. Default diagnostic stance

The stance — "user-facing agents own their own tests until they isolate a compiler bug" — is **architecturally sound AND required by `memory/feedback_cross_skill_minimal_repro.md`**. The user's explicit directive matches the documented cross-skill handoff protocol: a surface error signature without a minimal repro routinely masks layered bugs (Sprint 59 Wave 1 cost ~2 hours on exactly this pattern).

**Cases where `/port` cannot reasonably isolate without compiler-skill assistance:**

- **Intermittent crashes / races.** If the exemplar failure is non-deterministic, `/port` cannot produce a deterministic minimal repro without the same observability infrastructure this sprint is installing for Slice 3/4. The solver `test-unsolvable` currently presents as deterministic (two Given(5)s in row 0 → Success), so this case does not apply to Slice 2.
- **Heap/RC-level failures that manifest only at scale.** If the bug surfaces only with large data structures or deep call stacks, `/port` cannot reduce without RC trace (already available via `CRANELISP_RC_TRACE=1`). The stance is unchanged; `/port` reaches for the existing tracing.
- **Codegen-shape bugs masked by algorithm-shape.** If the exemplar bug is in compiler codegen but `/port` does not know which primitive or special form is miscompiled, reduction to "non-solver repro" is exactly the handoff criterion the stance prescribes — NOT an exception to it.

The stance is sound. **One sharpening for the sprint plan: the draft Slice 2 branch (c) — "no reduction, no fix, carries forward with `/port` ownership" — MUST be the explicit outcome if `/port` reaches the end of reduction without either fixing in `solver.cl` (branch a) OR producing a compiler-bug repro (branch b).** The draft correctly says Sprint 61 does NOT default-assign to `/backend` in this case; `/arch` confirms that is the right call. A no-reduction carry is still a carry — tracked in the baseline ledger with `/port` as owner, not silently dropped.

**Escalation threshold for `/port`:** if Slice 2 reduction exceeds 2 days of `/port` effort without either branch (a) or branch (b) closing, `/port` files readout in SPRINT.md §Notes and `/sprint` convenes a mini-triage with `/arch` + `/backend` to decide whether to escalate to a compiler-assisted reduction or accept branch (c) carry. This is bounded effort, not open-ended.

### FIXME(/arch) — items to resolve before Phase 3 opens

1. **FIXME(/int)** on the Slice 0 design doc: explicitly state that scheduler event log lives in `src/` (thread-local state); IO trampoline event log lives in `cranelisp-runtime` (thread-local state); neither type crosses any boundary type or serialised format. Without this in the design doc, the implementation could land in `cranelisp-shared` by mistake.
2. **FIXME(/backend)** on the Slice 0 design doc: confirm that `CRANELISP_IO_TRACE` uses the same env-var parse-once pattern as the other trace vars (not per-event parse). Cite `tests/CLAUDE.md §"Diagnostic Logging"` for the existing pattern.
3. **FIXME(/int)** on the Slice 3 design doc: after the event log surfaces evidence, the design doc MUST name the chosen hypothesis (1, 2, or 3) and reference the event-log dump that justifies the choice, BEFORE the fix is implemented. This is the evidence-gated discipline the draft correctly prescribes — recording it as a FIXME makes the gate auditable.
4. **FIXME(/sprint)** on the 20-run tiering: update the E-2 proposed Phase 6 edit to explicitly tier — 10 runs for intermediate slice gates, 20 runs for final close-gate. The current draft §Notes proposes 20 uniformly, which is unnecessarily expensive through the sprint.

### Recommendations for /sprint

1. **Adopt 10/20 tiering on stress-verification gates** (intermediate vs final close). Update E-2 proposed diff to reflect this before asking user for approval.
2. **Record Slice 0 crate-placement decision in the design doc** before implementation: scheduler log in `src/`, IO log in `cranelisp-runtime`, neither on boundary types or serialised formats. This is an architectural decision that belongs in the design doc, not tacit in the implementation.
3. **Add explicit Slice 2 escalation threshold** (2-day cap on `/port` reduction before mini-triage). Prevents open-ended carry.
4. **Keep Slice 5 items opportunistic but gate close on their completion.** The draft already says this; confirm that E-1 (fresh-TempDir rule) in particular is NOT allowed to slip past close, since it is methodology discipline that prevents similar pollution-shaped races in future sprints.
5. **No boundary-type changes pre-authorised.** If Phase 3 design surfaces a genuine need, `/arch` reviews before any `cranelisp-types` change commits. The default assumption for Sprint 61 is "all fixes are interface-internal."

Scope is approvable after the four FIXME(/arch) items above are addressed in Phase 3 design docs. No re-scope required; the revisions are clarifications, not changes.

## Slices

### Slice 0 — Foundational: tracing & inspection (`/int` + `/backend`)

**Purpose**: Invest in observability so Slices 3 and 4 can reduce intermittent races to deterministic repros. Lands before any defect work.

**Deliverables**:

- **Scheduler/worker event log** (`/int`). Thread-local ring buffer capturing state transitions: `ModuleState::Typechecking → Typechecked`, `register_dep publish`, `register_module register`, `is_typechecked` fast-path hit/miss, `clear_module_state`, `recompile_module`. Events carry timestamp (monotonic ns), thread ID, module path, and a tag. Dumpable on test failure and merge-sortable across threads. Env-var activated (`CRANELISP_SCHEDULER_TRACE=1|module_name|*`), zero-cost when off.
- **IO trampoline event log** (`/backend`). Similar shape: `Pure`/`Bind`/`Par` transitions, platform-fn invocations with scheduling class, continuation handoffs, exit codes. Env-var activated (`CRANELISP_IO_TRACE=1|*`).
- **Documentation** (`/int`): `design/int/observability.md` (new, ~100 lines). Inventory existing trace vars (`CRANELISP_CODEGEN_TRACE`, `CRANELISP_CODEGEN_DUMP`, `CRANELISP_RC_TRACE`) plus the two new ones. Describe the dump format, how to merge-sort across threads, and the guidance on when to reach for each.

**Crate placement decision** (pinned by `/arch` Phase 2 review — `design/int/observability.md` MUST state this explicitly):

- **Scheduler/worker event log → `src/`** (binary crate). Thread-local state in `src/session_v4.rs` or a new `src/observability.rs`. The scheduler and worker are `src/`-owned; their event log is an observation of integration-layer state that does not cross any crate boundary.
- **IO trampoline event log → `cranelisp-runtime`** (thread-local state in `crates/cranelisp-runtime/src/io.rs` or a new `cranelisp-runtime::trace` module). The IO trampoline is runtime-owned; its event taxonomy matches the runtime's state machine.
- **Neither log** appears in any boundary type (`cranelisp-shared`, `cranelisp-types`) or any serialised format (`.meta.json`, `SymbolTable<C, L>`). Event types are runtime-only.
- **Neither log** allocates on the Cranelisp heap (`cranelisp_alloc`). Use host allocator (`Mutex<VecDeque>` or lock-free ring). Mixing RC-traced allocations into a trace that observes RC would create infinite recursion.
- **Env-var parse happens once** at session start via `OnceLock<TraceFilter>`, not per-event. Consistent with the existing trace-var pattern in `tests/CLAUDE.md §"Diagnostic Logging"`.

**Design doc**: `design/int/observability.md` — reviewed by `/arch` for boundary-type hygiene. The three FIXME(/arch) items recorded in the Architecture Review (crate placement statement, env-var parse-once pattern) MUST be resolved in the design doc before implementation starts.

**Acceptance**: `CRANELISP_SCHEDULER_TRACE=1 cargo nextest run sprint23::cache_repl_loads_heisenbug_parallel_stress` produces a merge-sortable event log covering at least one failing and one passing iteration. `CRANELISP_IO_TRACE=1 cargo run -- --run examples/21-hello-io.cl` produces a full trampoline event sequence ending at process exit. Off-path performance regression < 1% on `cargo nextest run`.

### Slice 1 — Defect 4: bare-primitive-name at REPL (`/int`)

**Purpose**: Smallest defect, pure implementation, no foundational dependency beyond Slice 0. Prove the sequential-slice pattern works.

**Isolate**: Trace the three resolution paths — `/sig add-i64` (introspection), `(add-i64 2 3)` (call), `add-i64` at the prompt (bare value) — in `CompilerSession::eval_v4` + `describe_symbol`. Identify the specific lookup step where the bare-value path fails for re-exported `primitives` names.

**Design note**: `design/int/bare-primitive-value-path.md` (new, ~50 lines). Documents the three paths, the divergence point, and the fix.

**Fix**: Align the bare-value path with the introspection/call paths on a single symbol-resolution mechanism. Most likely a one-site fix in the bare-symbol handler.

**Verify**: 5 consecutive runs of the new integration test (REPL prompt `add-i64` returns `:(Fn [Int Int] Int) primitives/add-i64 ; primitive - …`).

**Acceptance**: Test passes 5/5. Related names (`eq-i64`, `mul-i64`, etc.) verified in the same pass.

### Slice 2 — Defect 3: exemplar `test-unsolvable` (`/port`)

**Purpose**: Close the solver correctness gap. Default position: this is an exemplar bug. `/port` fixes in `exemplar/solver.cl` unless they reduce to a non-solver repro that demonstrates a compiler bug.

**Isolate**: `/port` reduces the symptom. Starting point: two Given(5)s in row 0. Shrink from there. Candidates in `solver.cl`:
- `peers` construction — does the peers list for a cell ever include the cell itself?
- `eliminate-from-peers-helper` — does iteration visit duplicates?
- `eliminate` — is the contradiction-detection branch reachable?
- Something upstream (initial grid construction, Given-propagation) setting up an inconsistent state.

**Exit branches**:

- **(a) Algorithm bug in `solver.cl`.** `/port` fixes in exemplar code. Re-verify 3 puzzle tests + `test-unsolvable`. Slice closes.
- **(b) Non-solver repro demonstrates a compiler bug.** `/port` hands off minimal repro (< 20 LOC, non-Sudoku) to `/qa` for narrow integration test, then to the appropriate compiler skill for fix. Slice extends.
- **(c) No reduction, no fix.** Slice carries to a later sprint with explicit `/port` ownership; Sprint 61 does NOT default-assign to /backend.

**Escalation threshold** (pinned by `/arch` Phase 2 review): if Slice 2 reduction exceeds **2 days of `/port` effort** without either branch (a) or branch (b) closing, `/port` files a readout in SPRINT.md §Notes and `/sprint` convenes a mini-triage with `/arch` + `/backend` to decide between (i) compiler-assisted reduction, or (ii) accept branch (c) carry. Bounded effort, not open-ended. A branch (c) carry still enters the baseline ledger with `/port` as owner.

**Design artefact**: Reduction notes in `exemplar/solver.cl` FIXMEs, plus a short `/port` readout in SPRINT.md §Notes when ready to close or escalate.

**Verify**: 5 consecutive runs of `test-unsolvable` + 3 puzzle tests (easy, hard, unsolvable).

**Acceptance**: `test-unsolvable` returns `Unsolvable`; easy/hard continue to pass. OR an isolated compiler-bug repro is committed as a failing `tests/` integration test with `/qa` narrow authorship.

### Slice 3 — Defect 1: heisenbug race (`/int`)

**Purpose**: Close the scheduler/worker race at ~30% failure rate to ≥0 failures across 20 runs.

**Isolate**: Use Slice 0's scheduler/worker event log. Drive the race with a stress harness (pin thread count, add controlled yields at suspected race sites). Reduce to near-deterministic trigger. Distinguish among three hypotheses:
1. `is_typechecked` predicate too permissive (symbol table entry exists without expected symbols populated — partial publish).
2. Symbol publication happens outside the critical section that flips the pool state (reader observes "ready" before symbols visible).
3. Typecheck-worker loop transitions pool state before symbol publication (inverse of `register_dep`'s publish-before-register discipline).

**Design doc**: `design/int/heisenbug-race-closure.md` (new). MUST identify which hypothesis holds via evidence from the event log before fix lands. `/arch` reviews for `SymbolTable` / `SharedState` / `Scheduler` boundary hygiene.

**Fix**: Root-cause-specific. Hypothesis 1 → tighten `is_typechecked` predicate. Hypothesis 2 → widen critical section. Hypothesis 3 → invert pool-transition ordering.

**Verify**: 20 consecutive runs of `sprint23::cache_repl_loads_heisenbug_parallel_stress` at 0 failures.

**Acceptance**: 20/20 green. Baseline ledger entry removed from `tests/plan/baseline.md`.

### Slice 4 — Defect 2: 21-hello-io exit 201 (TBD at readout)

**Purpose**: Close the intermittent IO example failure to ≥0 failures across 20 runs.

**Isolate**: Use Slice 0's IO trampoline event log. Run 21-hello-io under simulated stress (nextest `--test-threads` tuning, concurrent subprocess spawn). Reduce to near-deterministic trigger. Distinguish among:
1. IO trampoline continuation-state leaks across concurrent `--run` subprocess invocations (`/backend` owns).
2. Stdio DLL buffer ordering under concurrent subprocess loads (`/platform` owns).
3. nextest-level subprocess-environment crosstalk (env var races, CWD contention) (`/qa` + `/int` share).

**Investigation note**: Fold into `design/backend/defects-456-reduction.md §Phase 4` or a new `design/backend/example-21-hello-io.md` — decided at Slice 4 readout.

**Fix**: Owned by the skill the readout identifies.

**Verify**: 20 consecutive runs of `examples_run::every_example_file_runs_under_examples_prelude` at 0 failures. Plus 20 consecutive runs of the full example sweep.

**Acceptance**: 20/20 green. Baseline ledger entry removed.

### Slice 5 — Methodology + cleanup (parallel with other slices where independent)

Non-code or low-risk items that don't interact with Slices 1–4. Land opportunistically; gate the sprint close on their completion.

- **E-1 (`/qa`)**: Fresh-TempDir-per-test rule in `tests/CLAUDE.md`. Audit `tests/` for `project_root()` uses; convert pollution-prone tests to `tempfile::TempDir`. Document the rule.
- **E-2 (`/sprint`, pending user approval)**: Add 20-run stress verification to `.claude/commands/sprint.md` Phase 6 close checklist. Proposed diff in §Notes below.
- **E-3 (`/sprint`)**: Update SPRINT.md template to reflect E-2.
- ~~**F (`/qa`)**: Add `tests/sprint60/.runs/` to `.gitignore` (S60 /review I-1).~~ **DROPPED** — already satisfied; `.gitignore:31` carries the entry. /qa's Phase 3 audit caught this; sprint scope trimmed accordingly.
- **G (`/int`)**: Rename `register_dep_shim_publishes_before_caller_registers` test per S60 /review S2.
- **H (`/qa`)**: 3–5 `[Tested+Neg]` promotions on MUST/MUST NOT spec requirements.
- **I (`/qa`) — Repro-handoff migration (added 2026-04-22, user directive)**: Move `exemplar/repro-slice2.cl` + `exemplar/test-eliminate-contract.cl` out of `exemplar/` and into the `tests/` tree (either as `tests/fixtures/*.cl` or inlined as Rust string literals in `tests/exemplar_solver_correctness.rs`). Update the test paths in `tests/exemplar_solver_correctness.rs`. Update the FIXME block in `exemplar/solver.cl:370+` to point at the new test locations. Rationale: `exemplar/` and `examples/` are user-facing showcases that can be removed/replaced at any time; compiler regression guards must not depend on them. See `memory/feedback_repro_handoff.md` for the protocol.
- **J (`/qa`) — Phase 3a plan-gap retrospective (added 2026-04-22, user directive)**: audit why /qa's Phase 3a test-case derivation did not pre-derive Slice 2 coverage that might have surfaced the exemplar correctness gap independently of /port's investigation. Two layers: (a) plan-level — Slice 2 tests were deferred to "branch (b) only" rather than authoring a property-level assertion ("for every unsolvable puzzle string, solver returns Unsolvable"); (b) coverage-gap — the Layer 3 compiler bug (inline-ADT-arg-wrapping-Vec) is a Ring 1 / Ring 2 category that /qa's ring test plans lacked property coverage for. Deliverables: short retrospective note at `tests/plan/sprint-61-plan-gap-retro.md`; corrective coverage added to `tests/plan/ring1.md` and/or `tests/plan/ring2.md` for the inline-ADT-arg class; handoff any new failing tests back into the normal Wave 5 flow.
- **K (`/qa`) — Wave 2 /review I-1 (added 2026-04-22, first-time deferral)**: `tests/sprint61_bare_primitive.rs` inlines ~15 LOC of E2E helpers (`project_root`, `test_dir`, `run_repl_with_stdlib`) that should live in `tests/helpers/mod.rs`. Consolidate during Slice 5 helper sweep (natural fit with E-1 fresh-TempDir rule work). See `design/review/sprint-61-wave-2.md §Importants I-1`.
- **L (`/backend`) — Wave 2 /review I-2 (added 2026-04-22, first-time deferral)**: `design/backend/ring2-rc.md §5.5` 3-rule expansion lacks a "Sketch comparison" addendum for the new `borrowed_vars` rule. Append one-paragraph section per `CLAUDE.md §"Sketch Oracle"`. See `design/review/sprint-61-wave-2.md §Importants I-2`.
- **M (`/qa`) — Wave 2 /review S-3 (added 2026-04-22, trivial cleanup)**: stale `FIXME(/backend)` at `tests/exemplar_solver_correctness.rs:150` — /backend's fix landed; convert to retrospective note or remove.
- **N (`/typecheck`) — Wave 3 /review I-1 (added 2026-04-22, first-time deferral)**: `ensure_module_exists_concurrent_same_path_emits_exactly_one_created` test in `crates/cranelisp-typecheck/src/checker.rs` hedges its strongest atomicity-of-emission assertion behind a `counter_non_zero` guard — tolerable for `OnceLock`-single-install in a multi-test process. Add a `reset_hook_for_tests` escape hatch OR strengthen the assertion. See `design/review/sprint-61-wave-3.md §Importants I-1`. Folds naturally into S62 concurrency-audit work; may defer there if scope pressure.
- **O — S62 transition planning (added 2026-04-22, /sprint)**: draft the S62 scope opening — concurrency audit + `loom` adoption + structured interleaving tests. List the audit targets (all `symbol_tables` / `modules` access sites in `crates/cranelisp-typecheck/`; scheduler state-transition sites in `src/scheduler.rs`; `SharedState` access sites in `src/session_v4.rs`). Enumerate the `loom` scope (DashMap operations that are race-critical). This is /sprint work for the S62 SPRINT.md draft at S61 close.

## Skill Plans

_Phase 3 — each skill fills its section. `/int`, `/backend`, `/port` must author design/investigation docs before implementation (Slices 0, 1, 3). `/arch` reviews at each slice's design gate._

### /sprint

**Task**: Coordinate the sprint; drive the sequential-slice cadence; maintain SPRINT.md; assemble close-time 20-run stress verification. E-2 (Phase 6 checklist edit) landed 2026-04-22 with user approval. E-3 (SPRINT.md template update) lands with the archive at sprint close.
**Design doc**: n/a.
**Approach**: Open Phase 3 design gates for Slices 0, 1, 3. Collect /arch design-doc reviews at each slice before authorising implementation. Run intermediate stress gates (5/10 consecutive runs per the verification table) at each slice close. Run 20-run aggregate at final close.
**Acceptance**: All slices close in order; Phase 6 close checklist updated (DONE); 20-run close-gate 0 failures; SPRINT.md template reflects the new gate (closed at archive).

### /arch

**Task**: Phase 2 architecture review of S61 scope; Phase 3a design-doc review for Slice 0 (`observability.md`), Slice 1 (`bare-primitive-value-path.md`), Slice 3 (`heisenbug-race-closure.md`), and Slice 4 investigation note.
**Design doc**: n/a (reviewer role).
**Approach**: Confirm scope is coherent (stabilisation-only, no interim architecture, no scope creep into FQTypeName); confirm Slice 3's design-doc proposal doesn't require a boundary-type change; confirm Slice 0's event types don't leak into boundary crates or serialised cache formats.
**Acceptance**: Phase 2 review signed off; per-slice design-doc sign-offs recorded in §Notes.

### /int

**Task**: Slice 0 (scheduler/worker event log), Slice 1 (bare-primitive fix), Slice 3 (heisenbug race), plus Slice 5 G (test rename).
**Design docs**: `design/int/observability.md` (Slice 0 — MUST state the crate-placement decision: scheduler log in `src/`, IO log in `cranelisp-runtime`, neither on boundary types or serialised formats; MUST cite env-var parse-once pattern per `tests/CLAUDE.md §"Diagnostic Logging"`). `design/int/bare-primitive-value-path.md` (Slice 1). `design/int/heisenbug-race-closure.md` (Slice 3 — **evidence-gated discipline: the doc MUST name the chosen hypothesis (1, 2, or 3) and cite the event-log dump that justifies the choice BEFORE the fix is implemented**. If implementation proceeds without evidence-grounded hypothesis naming, /arch rejects at design review).
**Approach**: Land Slice 0 first — no Slice 1/3 implementation until observability is in. Slice 1 is the warm-up. Slice 3 is the hard case; use Slice 0's scheduler/worker event log to drive the race to near-determinism, distinguish among the three hypotheses, then fix with the mechanism matching the confirmed hypothesis.
**Design-phase outcomes (2026-04-22)**: Three design docs authored at Phase 3. (1) `observability.md` — scheduler log placed in `src/` (new module `src/observability.rs`), IO log placed in `cranelisp-runtime` (new module `crates/cranelisp-runtime/src/trace.rs`); `OnceLock<TraceFilter>` parse-once; bounded thread-local ring buffer; scheduler-log dumped on test failure, IO-log streamed to stderr. (2) `bare-primitive-value-path.md` — two candidate divergence points identified (FQSymbol module attribution vs. fall-through to typecheck), fix is one-site inside `check_bare_symbol_introspection` at `src/session_v4.rs:2179`; no boundary change. (3) `heisenbug-race-closure.md` — three numbered hypotheses (H1–H3) with fix sketches; evidence-gated update process recorded in §6. `tests/sprint61/race-evidence/` added as the artefact path for the pre-fix event-log captures.
**Acceptance**: All design docs reviewed by `/arch`; Slice 0 trace env vars work (see §Slice 0 acceptance); Slice 1 5/5 green; Slice 3 10/10 green at slice gate and contributes to 20/20 at final close; G rename committed.

### /backend

**Task**: Slice 0 (IO trampoline event log), potentially Slice 4 (IO exit 201 if hypothesis 1 holds).
**Design docs**: `design/backend/io-trampoline-trace.md` (new, Phase 3 landed 2026-04-22 — the `/backend`-owned IO-specific sibling to `/int`'s `design/int/observability.md`; cross-referenced but NOT duplicated there). Slice 4 investigation note TBD.
**Approach**: IO trampoline trace lands alongside the scheduler trace in Slice 0. Module placement: new `crates/cranelisp-runtime/src/io_trace.rs` (name avoids collision with existing `trace.rs` which implements the `(trace ...)` special form). Env-var parse-once via `OnceLock<Option<TraceFilter>>` at runtime init — resolves `/arch` Phase 2 `FIXME(/backend)`. Slice 4 ownership determined at readout.
**Acceptance**: IO trace integrated; off-path regression < 1% on `cargo nextest run`; merge-sortable with `/int`'s scheduler trace via shared `Instant` anchor + `ThreadId`; Slice 4 green if owned by `/backend`.

### /platform

**Task**: Co-investigate Slice 4; own the fix if stdio DLL hypothesis holds.
**Design doc**: None unless scope grows.
**Approach**: Read `crates/cranelisp-platform/` stdio-related code; confirm whether `write-line`/`read-line` is safe under concurrent subprocess invocation.
**Acceptance**: Slice 4 readout clearly attributes to `/backend`, `/platform`, or shared.

### /frontend

**Task**: No implementation; Phase 3 plan update confirming non-involvement.
**Acceptance**: Plan updated; no cross-skill FIXMEs to /frontend landed by close.

### /typecheck

**Task**: No implementation. Light reconnaissance for FQTypeName prep (optional note at `design/typecheck/fqtypename-prep.md`).
**Acceptance**: Plan updated; reconnaissance note committed if authored.

### /qa

**Task**: Slice 5 E-1 (primary), E-3 support, F, H, plus C-handoff (integration test ONLY IF `/port` reduces to non-solver repro).
**Design doc**: n/a.
**Phase 3 artefacts** (authored 2026-04-22, SHA `a9028c0`):
- `tests/plan/tempdir-audit.md` (new) — catalogues ~34 test-file dispositions; **K = ~10 test functions + 1 shared helper require conversion**; M = ~10 tests write to checked-in paths today (`exemplar/user.cl` via `d45_*`, `d7_*`, `s60_run_tests_reduction_1_*`; `exemplar/d6_*.cl` via six `sprint59_defects456_repro` tests; `examples/.cranelisp-cache/` via `examples_run`; `tests/fixtures/*.cl` via the `ReplSessionBuilder` default `install_def` path).
- `tests/plan/neg-coverage-candidates.md` (new) — 7-candidate shortlist. Top 3 recommended for Wave 2: (#1) errors-on-stdout / stderr-empty; (#2) error-recovery-no-partial-install; (#3) `/imports` fresh-session no-primitives-leak. 2 stretch candidates (#4, #5) if budget allows.
- Phase 3 deliberately does NOT touch `tests/CLAUDE.md` — rule text is staged in `tempdir-audit.md §"Proposed tests/CLAUDE.md rule"` for /review inspection before Wave 2 insertion.
**Approach**:
- **E-1 (Wave 2)**: Author shared helper `tests/helpers/tempdir_project_from_fixture` per the pattern in `tempdir-audit.md §"Conversion pattern"`. Convert the ~10 callsites + fix the `ReplSessionBuilder` default. Insert the staged rule text into `tests/CLAUDE.md` after /review confirms shape.
- **F**: `.gitignore` already carries `tests/sprint60/.runs/` (line 31). Wave 2 verifies the S60 /review I-1 scratch-path target is already satisfied; widen only if a distinct tree is outstanding.
- **H (Wave 2)**: Author 3 negative tests from the shortlist (candidates #1, #2, #3). Update spec annotations from `[Tested ...]` to `[Tested+Neg ...]` per `CLAUDE.md §"Requirements/Test Traceability"`. Stretch: +2 if budget allows.
- **C-handoff**: Only engages IF Slice 2 branch (b) fires. Author narrow test in `tests/exemplar_solver_correctness.rs` (new) — FAILING per `feedback_failing_not_ignored.md`.
**Phase 3 surprise findings** (flagged for /sprint awareness):
1. `tests/helpers/mod.rs::ReplSessionBuilder` defaults `project_root` to `tests/fixtures/`; `ReplSession::install_def` writes `{name}.cl` there. Scope of E-1 is broader than originally-suspected exemplar-only pollution.
2. Four `d6_*` tests use `struct Cleanup(PathBuf); impl Drop` scope guards for `exemplar/d6_*.cl` that fail to clean cleanly on panic. TempDir eliminates the cleanup-on-panic hole.
3. `tests/examples_run.rs` runs with cwd = `examples/`, and the `--run` subprocess populates `examples/.cranelisp-cache/` unless an env override redirects — worth verifying as part of Wave 2.
**Acceptance**: Phase 3 audit + shortlist committed (DONE, Wave 1 Phase 3 gate); Wave 2: rule documented + audit conversions committed; 3 H promotions landed (5 stretch); C handoff executed only if triggered.

### /review

**Task**: Per-slice /review passes on code-producing slices (0, 1, 3, 4 if applicable, 2 if branch (b) fires). Final /review report gating sprint close.
**Acceptance**: `design/review/sprint-61-slice-N.md` files published per slice; close-gate PASS verdict.

### /repl

**Task**: Sprint demo `repl/demos/ring4s.demo` (new). Showcase: bare-primitive-name echo at prompt (Slice 1), heisenbug stability via stress-shape demo (Slice 3), IO example stability (Slice 4). Demo authored AFTER slices close so the showcased behaviour is real.
**Acceptance**: `ring4s.demo` plays cleanly; 26 prior demos replay green.

### /examples

**Task**: Wave-5 sweep verification after Slice 4. Confirm 27/27 examples pass.
**Acceptance**: Sweep green.

### /stdlib

**Task**: Confirm prelude still correct after Slice 1 lands. No implementation expected. Refresh `stdlib-progress.demo` only if user-visible behaviour changes.
**Acceptance**: Prelude unchanged; demo refreshed only if needed.

### /port

**Task**: Slice 2 lead (fix in `solver.cl` OR reduce to non-solver repro). Refresh `exemplar-progress.demo` once Slice 2 closes.
**Design artefact**: Reduction notes inline in `solver.cl` FIXMEs + readout in SPRINT.md §Notes.

**Default stance**: exemplar bug until proven otherwise. Per `memory/feedback_cross_skill_minimal_repro.md` and `/arch` Phase 2 review §5, a surface error signature without a minimal repro routinely masks layered bugs (Sprint 59 Wave 1 cost ~2 hours on exactly this pattern). `/port` owns the investigation and the fix unless and until reduction produces a non-Sudoku repro that isolates a compiler-level bug. Branch (c) — carry forward — stays owned by `/port`; Sprint 61 does NOT default-assign to `/backend`.

**Hypothesis list** (candidates from §Slice 2 §Isolate, ordered cheapest-check-first):

1. **`peers` construction includes self.** If the peers list for cell (r, c) contains (r, c) itself, then any Given(d) at (r, c) will call `eliminate g idx d` with idx == self and d == cell-value. The current `eliminate` returns `(Some g)` (no-op) on matching-value Given, so a self-peer silently hides contradictions. How to check: read `exemplar/grid.cl` `peers` definition; manually trace for cell (0,0) and confirm (0,0) is absent from the returned list. If present, this is branch (a) (algorithmic bug in `grid.cl`).

2. **`eliminate-from-peers-helper` visits duplicates or the cell itself.** Even if `peers` is correct, the helper that threads the elimination across peers may iterate wrongly — e.g., re-visiting a cell after its bitmask narrows, or walking over a list that was built to include the source cell. How to check: instrument the helper (add a debug print to stdout via `platform stdio`, or log via a counter) to record which (src-cell, target-cell, digit) triples it visits for a 2-Given grid; manually confirm no (cell, cell, _) triple and no duplicated target-cells per source. If visits are wrong, branch (a).

3. **`eliminate` contradiction-detection unreachable for Given/Given conflict.** Read the match arms in `solver.cl:36-...` — when `eliminate` is called with cell = `(Given d)` and the digit-to-eliminate is also `d`, the current match returns `(Some g)` at line 39. For a peer that is also a Given-of-`d`, we need the None-returning branch. How to check: trace what happens when `propagate` fires on two Given(5)s — does it ever route through a path that could return `None`? If the answer is "no, the match arms are structurally wrong," this is branch (a). Patching to return None on same-value Given was already attempted (see line 394-400 comment); it broke valid puzzles, which implicates a second bug — either in peers iteration (candidate 1/2) or in state sharing (candidate 4 / branch b).

4. **Upstream state: `make-grid` or Given-propagation sets up inconsistent state.** `make-grid` may parse the two-5s string and produce a Grid where the peer bitmasks are already wrong before `solve` is called. Or the initial Given-propagation pass (if any) may double-apply. How to check: instrument `main` (or add a diagnostic test) to print the full grid after `make-grid` but before `solve` — confirm both 5s are marked `(Given 5)` with neighbour Candidates masks that still contain bit 5 (which would prove propagation hasn't yet run) or don't (which would prove it has and didn't conflict). If state is already wrong post-make-grid, branch (a) localised to `make-grid`.

**Reduction sequence** (ordered by cost; escalate to the next if the previous is negative):

1. Candidate 1 — static read of `peers` in `grid.cl`, manual trace for cell 0. Cheapest: no instrumentation, no compilation. ~15 min.
2. Candidate 4 — instrument `main` to dump the post-`make-grid` state for the two-5s string. Cheap: one debug print, re-run. ~30 min.
3. Candidate 3 — static read of `eliminate` match arms; trace the Given/Given propagation path by hand. ~30 min.
4. Candidate 2 — instrument `eliminate-from-peers-helper`. Requires the debug plumbing to survive through multiple propagation levels. ~1 hr.

If all four clear without a fix, reduction moves to the compiler-bug-repro phase (branch b): shrink `test-unsolvable` to the smallest Grid shape that still reproduces, then extract the operations that matter (Vec set, match on ADT with shared field, recursive fn with Vec arg) into a non-Sudoku test.

**Expected outcomes**:

- **Branch (a) likelihood: high.** The current solver was ported from the sketch; Sprint 58/59 did significant RC work that may have unmasked an algorithmic bug the sketch's earlier RC discipline accidentally hid. A `peers` off-by-one or iteration-order issue (candidate 1 or 2) is plausible. The S60 finding — "patch-to-None breaks valid puzzles" — is consistent with `peers` including self: if peers wrongly contains the source cell, forcing None creates a self-conflict on every Given, breaking all solvable puzzles.
- **Branch (b) likelihood: low-medium.** The S60 investigation noted "patching eliminate to return None breaks valid puzzles" — this *could* be a compiler issue (Vec COW, closure capture in `eliminate-from-peers-helper`, match-arm field sharing) but could also be a direct consequence of an upstream bug in peers construction. Discriminate via candidates 1+2 above.
- **Branch (c) likelihood: low.** If all four candidates clear without either branch (a) fix or branch (b) repro within 2 days, escalate per §Slice 2 §Escalation threshold.

**Test shape for (a)**: `test-unsolvable` currently exists in `exemplar/solver.cl:428-434` — reduce to the smallest Grid size that still reproduces. Target shape: a two-Given conflict on the minimum grid the existing `make-grid` accepts (probably still 9×9 since the parser is hard-coded, but we can reduce the *non-zero cell count* to just the two conflicting 5s — which the current test already does, good). Document the minimal Grid input string in SPRINT.md §Notes at Slice 2 readout. If an even smaller structural repro emerges (e.g., a hand-constructed `Grid` bypass of `make-grid`), record that too.

**Test shape for (b)**: < 20 LOC non-Sudoku repro that demonstrates the compiler symptom. Example skeleton: a small ADT with one value-bearing variant, a Vec of those, a recursive fold that pattern-matches and conditionally returns an Option, exercised such that the observable output differs from the pure-logic expectation. `/port` authors the Cranelisp-level reduction; hands off to `/qa` to author the narrow Rust integration test at `tests/exemplar_solver_correctness.rs` (new file). Handoff shape per `memory/feedback_cross_skill_minimal_repro.md`: the brief names the repro (source code inline), not just the symptom. `/qa` writes the failing integration test with `// spec:` annotation + `FIXME(/owning-compiler-skill)` (likely `/backend` pending the actual isolation evidence).

**Escalation trigger**: 2-day cap on `/port` reduction effort (per §Slice 2 §Escalation threshold). If Candidates 1–4 all clear without either branch (a) fix or branch (b) repro, `/port` files a readout in SPRINT.md §Notes and `/sprint` convenes a mini-triage with `/arch` + `/backend` to decide between (i) compiler-assisted reduction (e.g., `/backend` drives with `CRANELISP_RC_TRACE=1` + `/clif` inspection), or (ii) accept branch (c) carry with `/port` as ongoing owner. The 2-day cap is bounded investigation, not open-ended; the baseline ledger entry persists either way.

**Approach**: Default to exemplar bug. Reduce the two-Given(5) shape via the hypothesis list above, cheapest-check-first. Follow the three exit branches.
**Acceptance**: Slice 2 closes via branch (a), (b), or (c) with user approval on carry.

### /docs

**Task**: Wave-5 user-doc refresh if user-facing behaviour changed. Likely minor.
**Acceptance**: User docs current.

### /spec

**Task**: If Slice 1 surfaces a spec clarification for re-exported-name behaviour in value vs. call position, update `spec/08-modules.md` §8.9 or file `FIXME(/spec)`. Likely no-op.
**Acceptance**: Spec current.

## Slice Execution Order

1. **Slice 0** (foundational) — MUST complete before Slices 3 and 4.
2. **Slice 1** (bare-primitive) — warm-up; independent of Slice 0 but scheduled after for sequential discipline.
3. **Slice 2** (exemplar) — can run in parallel with Slice 1 if `/port` is ready (different skill, no shared files).
4. **Slice 3** (heisenbug) — requires Slice 0; runs after Slices 1 + 2 close.
5. **Slice 4** (IO exit 201) — requires Slice 0; runs after Slice 3 closes.
6. **Slice 5** (methodology + cleanup) — opportunistic throughout; must complete before sprint close.

Each slice's close commit serves as the verified-green baseline for the next slice.

## Waves (Phase 4 — authored 2026-04-22)

Per-slice each wave runs the build/test/review cycle of the archetype (Phase 5 steps 15–18): implementation + /qa un-ignore + /review pass, iterated until settled. Tests live in the files `/qa` derived in Phase 3a (`tests/plan/ring4.md §"Sprint 61"`). Slice close = intermediate stress gate (5 or 10 consecutive) + commit + baseline update.

### Wave 1 — Slice 0 observability (parallel across /int + /backend)

| Skill | Task | Status |
|---|---|---|
| /int | Implement scheduler/worker event log per `design/int/observability.md`; land in `src/observability.rs` | DONE — `src/observability.rs` (~620 LOC including tests); 20 unit tests passing; `pub mod observability` wired into `src/lib.rs`; 15 `SchedulerTraceTag` variants; instrumentation at 12 call sites in `src/scheduler.rs`, `src/worker.rs`, `src/session_v4.rs` |
| /int | Share `OnceLock<Instant>` anchor exported from `cranelisp-runtime` (non-blocking /arch cleanup 1); import into scheduler log site | DONE — `observability::record_event` calls `cranelisp_runtime::trace_instant_anchor()` for every timestamp; unit test `anchor_is_the_shared_runtime_anchor` verifies pointer equality of the `OnceLock<Instant>` across calls |
| /int | Append "Sketch comparison" sections to `bare-primitive-value-path.md` + `heisenbug-race-closure.md` (non-blocking /arch cleanup 2) | DONE — §10 appended to `bare-primitive-value-path.md` (~160 words); §7a appended to `heisenbug-race-closure.md` (~165 words); both cite sketch files and justify divergence per `CLAUDE.md §"Sketch Oracle"` |
| /backend | Implement IO trampoline event log per `design/backend/io-trampoline-trace.md`; land in `crates/cranelisp-runtime/src/io_trace.rs` | DONE — 14 unit tests passing; instrumentation at 11 sites in `io.rs` (TrampolineEnter/Exit, PureStep, BindEnter/Exit, PlatformEffect, ContPush/Pop, ParSpark, ParSerialGroupEnter, ParJoin); `ParBarrierForce` reserved as designed |
| /backend | Export the shared `OnceLock<Instant>` anchor from `cranelisp-runtime` for /int to consume | DONE — `cranelisp_runtime::trace_instant_anchor() -> &'static Instant`, re-exported at crate root |
| /backend | Wire `flush_to_stderr()` to process-exit / panic paths — add `FlushGuard` RAII + idempotent `install_panic_hook` to `crates/cranelisp-runtime/src/io_trace.rs`; document mechanism in `design/backend/io-trampoline-trace.md §6.1`; resolves Wave 1 /qa FIXME(/backend) at §6 | DONE — 4 new unit tests (18 total, all passing); `FlushGuard`/`install_panic_hook` re-exported as `IoTraceFlushGuard`/`io_trace_install_panic_hook` at crate root. Wiring into `src/main.rs` handed off to /int (forbidden by /backend boundary — next-agent task). Three of seven sprint61 IO tests now green (`io_trace_unset_means_no_event_output_to_stderr`, `io_trace_off_path_subprocess_completes_within_generous_ceiling`, `io_trace_ring_buffer_bounded_by_capacity`); remaining four stay failing until /int wires main.rs. `cargo check` workspace-clean; `cargo clippy -p cranelisp-runtime` introduces no new warnings (pre-existing `vec.rs`/`float.rs` issues untouched). |
| /int | Consume `/backend`'s `IoTraceFlushGuard` + `io_trace_install_panic_hook` in `src/main.rs`; mirror with `SchedulerTraceFlushGuard` + `install_panic_hook` in `src/observability.rs`; publish worker ring buffers on shutdown; resolves Wave 1 /qa FIXME(/int) at `design/int/observability.md §7` | DONE — 5 new unit tests (25 total in observability, all passing); `SchedulerTraceFlushGuard` + idempotent `install_panic_hook` added to `src/observability.rs`; `src/main.rs` installs both panic hooks + holds both guards at top of `main()`; explicit `flush_traces()` call before Run-mode and error-path `process::exit`; priority- and nice-worker loops call `publish_thread_buffer()` on shutdown so worker-thread events (ModuleStateTypechecking etc.) reach the merged dump. Sprint 61 observability tests: 12/7 → 16/3 (both scheduler subprocess tests flipped green; remaining 3 IO failures are all 21-hello-io Slice 4 defect — orthogonal). `cargo check` workspace-clean; `cargo clippy -p cranelisp --all-targets` introduces no new warnings. |
| /qa | Author ~18 Slice-0 integration tests (scheduler 8, IO 7, shared 3) from the Phase-3a test plan; commit FAILING per `feedback_failing_not_ignored.md` | DONE — 19 tests authored across 3 new files (`tests/sprint61_observability_scheduler.rs` 8, `tests/sprint61_observability_io.rs` 8, `tests/sprint61_observability_shared.rs` 3); 14 passing, 5 failing (legitimate findings). Findings filed as FIXME(/int) on `design/int/observability.md §7` and FIXME(/backend) on `design/backend/io-trampoline-trace.md §6 mode A` — no wiring of `flush_to_stderr` at subprocess exit means env-var-gated subprocess dumps are empty; IO failures additionally collide with the 21-hello-io Slice 4 open defect. `cargo check` + `cargo clippy` zero warnings. |
| /review | Per-wave /review pass on Slice 0 code — `design/review/sprint-61-wave-1-slice-0.md` | DONE — **PASS WITH FINDINGS** (0 Blockers / 1 Important / 4 Suggestions). Boundary hygiene verified clean via grep: no `IoTraceEvent`/`SchedulerTraceEvent` in `cranelisp-shared`/`cranelisp-types`; no `cranelisp_alloc` in trace paths; no `#[ignore]` in integration tests; all 4 Phase 3a FIXME(/arch) items confirmed resolved in-implementation. |
| /qa | Ledger 4 new failing tests in `tests/plan/baseline.md` — 3 Slice-4-bound IO tests + 1 harness-robustness concern (`io_trace_off_path_subprocess_completes_within_generous_ceiling`) | DONE — 4 entries added with SHA `a9028c0`, signatures, owners, target sprints, dispositions `under-investigation` (Slice 4 for the 3 SIGABRT-bound tests, Wave 5 or S62 for the ceiling-breach test). S60 carries (heisenbug + `examples_run`) confirmed unchanged and still ledgered. |

**Wave 1 close**: 16 observability tests passing; 3 ledgered to `tests/plan/baseline.md` (Slice 4 preconditions + harness-robustness concern) per user approval 2026-04-22; /review PASS WITH FINDINGS (I-1 deferred — `reset_panic_hook_installed_for_tests()` global-state mutation under `cargo test` — first-time deferral, tracked in `design/review/sprint-61-wave-1-slice-0.md`); baseline ledger current.

**Live sample output** (captured during /int sanity tests):

```
=== CRANELISP_SCHEDULER_TRACE DUMP ===
[SCH] ts=42      thr=ThreadId(1)/0 RegisterModuleRegister    module=01-integers
[SCH] ts=30667   thr=ThreadId(2)/1 ModuleStateTypechecking   module=01-integers
[SCH] ts=507334  thr=ThreadId(2)/1 RegisterDepPublish        module=prelude
[SCH] ts=508459  thr=ThreadId(2)/1 RegisterModuleRegister    module=prelude

[IO]  ts=41      thr=ThreadId(1)/0 TrampolineEnter           io_ptr=0x888d08030
[IO]  ts=13333   thr=ThreadId(1)/0 BindEnter                 inner=0x889070040 cont=0x889070000 fresh=false
[IO]  ts=14000   thr=ThreadId(1)/0 ContPush                  cont=0x889070000 fresh=false depth=1
[IO]  ts=14250   thr=ThreadId(1)/0 PureStep                  value=42 fresh=false
```

### Wave 2 — Slices 1 + 2 (parallel across /int + /port)

| Skill | Task | Status |
|---|---|---|
| /int | Implement Slice 1 bare-primitive fix per `design/int/bare-primitive-value-path.md`; align bare-value path with introspection/call paths at the divergence point | DONE — fix landed in `src/session_v4.rs` (recursive `resolve_entry_for_display`; bare-value path threads `resolved_module` into `FQSymbol`). 3 unit tests added, 5/5 green. Candidate 2 held. See design doc post-impl note. |
| /qa | Author ~5 Slice-1 integration tests + 1 conditional; commit FAILING; un-ignore on /int fix | **DONE 2026-04-22** — 5 tests authored in `tests/sprint61_bare_primitive.rs` (~280 LOC), 5/5 PASS (fix already in). T-S1-1..T-S1-5 cover: positive bare-primitive display, three-path convergence, 6-primitive surface generalisation, unknown-name negative guard, two-hop re-export transitivity with qualified-type negative bundled. T-S1-6 (§8 spec-divergence sentinel) NOT authored — condition did not fire per design-doc post-impl note. Ring4 test-name map updated. |
| /port | Execute Slice 2 reduction per plan (candidate 1 = `peers`-includes-self check first); fix in `exemplar/solver.cl` (branch a) OR produce < 20 LOC non-solver repro (branch b) | DONE — **Branch (b) exit, 3-layer finding** (2026-04-22). Candidates 1/2/4 cleared; candidate 3 partial-hit. Layer 1 algorithmic gap in `exemplar/solver.cl::eliminate` (proposed one-line fix NOT applied per branch-b discipline). Layer 2: applying Layer 1 regresses valid puzzles via backtracking path (`try-digits` + recursive `solve`) — source-reduction hit 2-day cap. Layer 3: minimal compiler-bug repro committed at `exemplar/repro-slice2.cl` (<30 LOC, no Sudoku) — `(consume (Box [0]))` reads `len=0`; `(let [b (Box [0])] (consume b))` reads `len=1`. Inline-ADT-arg-wrapping-Vec corruption, deterministic on HEAD `a9028c0`. Caveat: Layer 3 trigger shape is distinct from Layer 2 solver call sites (let-bound vs inline); may be sibling bug, not exact Layer 2 cause. FIXMEs in `exemplar/solver.cl:370+` rewritten to describe all three layers. **Scope compliance confirmed**: only `exemplar/solver.cl` (M) + `exemplar/repro-slice2.cl` (??) touched. |
| /qa | On branch (b) trigger: author narrow test in `tests/exemplar_solver_correctness.rs` FAILING | **DONE 2026-04-22** — 2 tests authored in `tests/exemplar_solver_correctness.rs` (~200 LOC) + 1 fixture `exemplar/test-eliminate-contract.cl` (~50 LOC, /qa-owned test-only). Both tests FAIL as intended per branch-(b) handoff: (T-S2-1) `eliminate_on_same_value_given_returns_none` — exit=Some(1), want Some(0); (T-S2-2) `inline_adt_arg_wrapping_vec_preserves_len` — `inline-arg: len=0`, want `len=1`. Both entries ledgered in `tests/plan/baseline.md` at SHA `b140ec5`. T-S2-1 flips on /port Layer 1 fix (gated on /backend Layer 2); T-S2-2 flips on /backend Layer 3 fix. |
| /backend | Slice 2 branch (b) handoff — investigate `exemplar/repro-slice2.cl`; cross-check against Layer 2 Sudoku backtracking using `CRANELISP_CODEGEN_TRACE=1` or `/clif try-digits`; produce fix | **DONE 2026-04-22** — Root cause: `FnCompiler::is_last_use` (`crates/cranelisp-backend/src/compiler/mod.rs:1199`) did not consult `borrowed_vars`. Match field bindings (`(match b [(Box v) ...])` extracts `v`) are marked borrowed — scrutinee still owns the field — but `is_last_use` would return `true` for the textually-last reference to `v`, allowing Vec COW to mutate-in-place on an aliased Vec. Scrutinee drop glue then dec'd the mutated field → read-past-new-length / double-free. **Fix (+14 LOC)**: gate in `is_last_use` returns `false` for `borrowed_vars`, structurally symmetric with the existing `captured_vars` gate. `design/backend/ring2-rc.md §5.5` expanded to 3 rules. **Layer 2 bundled by construction**: the `try-digits`/`solve` backtracking shape — "ADT-wrapped Vec threaded through a vec-set update in a let, recursive call consumed by a match" — is the SAME root cause. **Scope violations (reverted by /sprint)**: /backend also edited `exemplar/solver.cl` (Layer 1) + used `git checkout -- <path>` + `git stash pop`. All three out-of-scope — /sprint stashed /backend's exemplar edits at `stash@{0}` for audit; /port re-applied Layer 1 in-scope in a follow-on. 174/174 backend unit tests + 470/470 Ring1+Ring2+RC tests pass. |
| /port | Follow-on: apply Layer 1 to `exemplar/solver.cl::eliminate` in /port's voice; rewrite FIXME block acknowledging Slice 2 closure; verify end-to-end | **DONE 2026-04-22** — 2-line semantic change on `(Given v)` / `(Solved v)` arms returning `None` on `v == d`. FIXME block rewrite 51→35 lines. `cargo run -- --run exemplar/solver.cl` runs up to pre-existing deep-recursion stack overflow on 81-cell solve (documented in `exemplar/CLAUDE.md` Known Issues — orthogonal). Definitive verification via /qa integration tests below. **Scope compliance**: only `exemplar/solver.cl` touched. |
| /qa | Resolve ledger entries T-S2-1, T-S2-2, and S60 `test-unsolvable` carry per close-time protocol | **DONE 2026-04-22** — 3 entries removed from `tests/plan/baseline.md`; new "Resolved this sprint" subsection with one-line rationale. Remaining baseline entries: 5 (Slice 3 heisenbug, Slice 4 21-hello-io, 3 Slice-4-observability preconditions, 1 Wave 5 harness robustness). |
| /sprint | 5-run verification of Slice 1 + Slice 2 integration tests | **DONE 2026-04-22** — Slice 1 `sprint61_bare_primitive` 5/5 × 5 runs = 25/25 green. Slice 2 `exemplar_solver_correctness` 2/2 × 5 runs = 10/10 green. Deterministic defects; 5-run gate satisfied per SPRINT.md §Verification thresholds. |
| /int | Slice 5 G test rename per S60 /review S2 (cheap; fold into this wave) | deferred to Wave 5 — cheap cleanup bundled with other Slice 5 items |
| /review | Per-wave /review pass — `design/review/sprint-61-wave-2.md` | **DONE — PASS WITH FINDINGS** (0B / 2I / 4S). 338 lines. **I-1**: `tests/sprint61_bare_primitive.rs` inlines E2E helpers (`project_root`, `test_dir`, `run_repl_with_stdlib`) that should live in `tests/helpers/mod.rs` — fold into Slice 5 Wave 5 (/qa helper consolidation, ~15 LOC). **I-2**: `design/backend/ring2-rc.md §5.5` expansion lacks sketch-comparison addendum for the new `borrowed_vars` rule — fold into Slice 5 doc-hygiene. **S-3 (trivial)**: stale `FIXME(/backend)` at `tests/exemplar_solver_correctness.rs:150` — fix landed; convert to retrospective note in Slice 5. Wave 2 close readiness: **GO**. |

**Wave 2 close** (2026-04-22): Slice 1 25/25 stress green; Slice 2 10/10 stress green; 3 baseline ledger entries resolved; /review PASS WITH FINDINGS (0 Blockers; 2 Importants deferred to Slice 5 Wave 5; 4 Suggestions). Scope-violation cleanup tracked via `stash@{0}`. Ready for Wave 2 commit.

**Slice 2 escalation gate**: if /port hits the 2-day reduction cap without branch (a) or (b) closing, /sprint convenes mini-triage with /arch + /backend per §Slice 2.

### Wave 3 — Slice 3 heisenbug (sequential within /int)

Augmented 2026-04-22 with explicit reduction step (3a) per user direction — mirrors Slice 2's successful `/port → minimal repro → evidence → fix` pattern. Evidence-gated: hypothesis is not selected until dumps show a divergence signature.

| Step | Skill | Task | Status |
|---|---|---|---|
| 3a | /int | **Reduction** — shrink `sprint23::cache_repl_loads_heisenbug_parallel_stress` to the smallest shape that still fires >50%. Try: fewer parallel sessions, injected `std::thread::yield_now()` or `std::sync::Barrier` at suspected race sites (publish, register_module, is_typechecked fast-path), single-session-plus-pause shapes. Commit reduced shape as a new test (FAILING) alongside the existing stress test. Time-boxed ~4h — if reduction plateaus, accept achievable rate and proceed with whatever harness reproduces most reliably. | **DONE** — `tests/sprint23.rs::heisenbug_race_reduced_concurrent_import_pairs` authored (FAILING, un-ignored). Shape: 6 concurrent threads × 2 iterations × 10 fast-fail trials. Fires ~86% per test run in ~1s wall-time on local M4 Pro. Exact baseline-ledger signature (`'helper-val' not found in module 'helper'` + `undefined variable: helper-val`). No injected yields required — test-harness shape alone achieves >=50%. No `#[cfg(test)]` hooks added to `src/`. Reduction notes in `design/int/heisenbug-race-closure.md §3b`. |
| 3b | /int | **Evidence capture** — run reduced harness with `CRANELISP_SCHEDULER_TRACE=1`, capture failing + passing event-log dumps. Commit to `tests/sprint61/race-evidence/` as frozen artefacts (pre-fix baseline). | **DONE** — `tests/sprint61/race-evidence/{failing,passing}-run-35062ca.log` + `README.md` committed. Failing dump from 1-attempt capture (test red first try). Passing dump from attempt 12/25 (pass rate ~5% under `CRANELISP_SCHEDULER_TRACE=1`) + hand-replayed solo subprocess for actual trace content (test harness discards subprocess stderr on success — see README §"Passing-run caveat"). Each dump contains 23 `[SCH]` events over modules {user, prelude, primitives, helper}. Superficial divergence: failing run interleaves `ModuleStateTypechecking helper` (t2) between t1's two `RegisterDepPublish`/`RegisterModuleRegister` pairs; passing run completes both pairs first. Observation notes (no hypothesis attribution — reserved for 3c) in `design/int/heisenbug-race-closure.md §3c`. No production code changes. |
| 3c | /int | **Hypothesis selection** — map observed divergence in dumps to H1 / H2 / H3 (or identify H4 if none of the three match). Update `design/int/heisenbug-race-closure.md §7/§8` with chosen hypothesis + event-log citation. MUST precede fix commit (evidence-gated discipline, /arch FIXME #3). | **DONE — SUPERSEDED by 3c'**. H4 selected (none of H1/H2/H3 as literally worded matched). Divergence signature: t2 pops `helper` from `typecheck_first` between t1's second defensive publish and second defensive register in `session_v4.rs::register_dep_for_eval`. H1/H2/H3 all falsified from dump evidence. Fix plan: Change A (elide defensive second pair on hot path) + Change B (observability events). /arch §3d approved. H4 subsequently falsified by step 3e's post-fix dump — see step 3c' below. |
| 3d | /arch | **Mini-review** of updated design doc — confirm chosen hypothesis matches evidence; confirm no boundary-type drift required. | **DONE — SUPERSEDED by 3d'**. APPROVE WITH REVISIONS for H4 (see `design/int/heisenbug-race-closure.md §3d`). Revisions landed cleanly at step 3e; post-fix dump showed H4 mechanism false, triggering 3c'/3d'/3e' cycle. |
| 3e | /int | **Fix** — hypothesis-specific (H1 predicate tighten / H2 critical-section widen / H3 pool-transition invert). | **LANDED PARTIAL — H4 MECHANISM FALSIFIED**. Implemented H4 Change A (hot-path gate eliding defensive dep publish+register pair) + Change B (observability tags `RepublishFromSymbolTable` + `RegisterImportsLookup`) per §8 and /arch §3d 4 conditions. All 4 conditions satisfied: tags added, `Scheduler::is_registered` added, line-1428 caller-sexps republish preserved, gate on BOTH published AND registered. Post-fix dump in `tests/sprint61/race-evidence/post-fix-run-35062ca.log` shows exactly one `RegisterDepPublish helper` + one `RegisterModuleRegister helper` per eval-thread call (criterion (a) MET), but harness fire rate unchanged at 10/10 (criterion (b) NOT MET). Per /arch §8.4 risk 2, H4 mechanism attribution is wrong. Post-fix dump reveals real race: both t1 (REPL retry after `wait_module_inmem_complete_blocking`) AND t2 (persistent worker popping user from `typecheck_first` after `try_unblock_locked`) concurrently typecheck user and race to `register_imports helper` — t2's lookup fails with the baseline signature. Fix requires scheduler-side change: suppress worker claim of unblocked caller when an eval thread is mid-retry. Beyond H4 §8.2 touch set; needs /arch re-triage. Design doc updated `design/int/heisenbug-race-closure.md §3e`. Observability instrumentation + narrow gate landed without regression (full sprint23 suite 58/59 — only the target test fails, same as baseline; `cache_repl_loads_heisenbug_parallel_stress` in isolation passes; 27/27 observability unit tests pass; cargo check clean; clippy clean — 3 pre-existing warnings unrelated). |
| 3c' | /int | **H5 hypothesis re-selection** — after step 3e's post-fix dump falsified H4's mechanism, write up H5 in `design/int/heisenbug-race-closure.md §7.7/§7.8/§7.9` citing `tests/sprint61/race-evidence/post-fix-run-35062ca.log`. H5 = concurrent user-module typecheck race: `try_unblock_locked(user)` inside `notify_typecheck_done(helper)` pushes user into `typecheck_first`; persistent worker pops it and races the REPL-eval thread's retry. Update §8 — preserve landed H4 fix as §8.1 (net-positive, stays in final commit); author §8.2 H5 fix plan. No code changes. | **DONE** — §7 reframed as "Hypothesis trajectory"; §7.7 marks H4 FALSIFIED with post-fix-dump citation (lines 29–41); §7.8 introduces H5 with event-ordering pin on `ModuleStateUnblocked user` → `ModuleStateTypechecking user` on t2 (line 35→36, ~3.5 µs) before t1's condvar wake arrives at line 40. §7.9 evidence sufficiency: dump pins race surface but selection among (a)/(b)/(c) mechanisms is /arch's call at 3d'. §8.1 retains H4 narrow-gate fix description (sub-numbered 8.1.1–8.1.4); §8.2 proposes scheduler-side worker-claim suppression via `eval_in_flight` flag on `ModuleState` with RAII guard; touches `src/scheduler.rs` (~10–30 LOC) + `src/session_v4.rs::register_dep_for_eval` (~5–15 LOC). No boundary changes. |
| 3d' | /arch | **Mini-review for H5** — confirm H5 attribution matches post-fix dump evidence; review §8.2 mechanism choice (option a vs c vs other); confirm no `cranelisp-types` boundary drift; check starvation / condvar / re-entrancy risk notes. | **DONE** — APPROVE WITH REVISIONS (see `design/int/heisenbug-race-closure.md §3d'`). Evidence → H5 mapping is unique (same-thread 3.5 µs unblock→claim signature); alternatives (H1-adjacent partial-visibility, two-worker pop, missed wake-up) ruled out from the dump. Mechanism: APPROVE (a) push-gate in `try_unblock_locked` over (c) pop-filter — scope-bounded, introspection-coherent, state-machine-legible. Boundary: NO `cranelisp-types` change (`ModuleState` is `src/scheduler.rs:52`-internal; `Scheduler::is_registered` already exists). RAII guard: approved, with four conditions: (1) use scheduler state lock to linearise flag writes with `try_unblock_locked` reads, (2) set+clear around just `wait_module_inmem_complete_blocking` (narrowest window), (3) audit all `wait_module_inmem_complete_blocking` callers in `src/`, (4) post-fix dump must show rate→0, exactly one `ModuleStateTypechecking user` per cycle on t1 not t2, no `RegisterImportsLookup helper` on worker thread in hot path. H6 disposition: if H5 signature persists at non-zero rate, open in-sprint H6 cycle; if H5 is closed but a different residue surfaces, ledger-and-defer to S62 is acceptable. Step 3f: 4 tests (2 integration /qa, 2 unit /int). Step 3e' GO. |
| 3e' | /int | **Fix for H5** — implement scheduler-side eval-in-flight suppression per §8.2 + /arch 3d' revisions. Post-fix dump must show (a) rate → 0 over N runs, (b) no `ModuleStateTypechecking user` on t2 between `ModuleStateUnblocked user` and the subsequent t1 events, (c) `RegisterImportsLookup helper` appears ONLY on t1 in the hot path. | **LANDED — H5 CLOSED; H6 RESIDUE → S62**. Added `eval_in_flight: bool` on `ModuleState` + `set_eval_in_flight` helper under scheduler state lock (no atomics, no separate mutex). Added `EvalInFlightGuard` RAII struct in `src/session_v4.rs`; armed at top of `register_dep_for_eval` (immediately after `caller = self.current_module_path()`), dropped at function exit (normal + panic). **Scope decision**: narrow scope around `wait_module_inmem_complete_blocking` only (/arch §3d' condition 3) was validated-insufficient — debug instrumentation showed t2's `try_unblock_locked(user)` fired with `eval_in_flight=false` because the race window opens at `block_for_typecheck` inside `handle_import`, BEFORE the wait call. Function-entry scope (/arch §3d' "RAII guard correctness" paragraph-1 alternative) is required and captures the window correctly. Condition 3 tension flagged for /review. Conditions 1, 2, 4 satisfied: caller audit inlined at top of `register_dep_for_eval` (sole non-test caller); `set_eval_in_flight` and `try_unblock_locked` both take the scheduler state lock (linearised set/read); `RepublishFromSymbolTable` + `RegisterImportsLookup` + `ModuleStateUnblocked` continue firing at existing sites (no new trace tags). Post-fix dump `tests/sprint61/race-evidence/post-fix-h5-35062ca.log`: H5 signature GONE — no `ModuleStateTypechecking user` on t2 after `ModuleStateUnblocked user` in any failing dump; all `RegisterImportsLookup helper` emissions on t1. Conditions (b) + (c) MET. Condition (a) rate→0 NOT MET — 2/10 pass (20% vs 0% pre-fix; 100% pre-fix-3e baseline). Residue is a DISTINCT signature: `'helper-val' not found in module 'helper'` on t1 alone, no worker race. Consistent with §7.8's "H1-adjacent data-plane partial-visibility" — `symbol_tables[helper]` mutation not fully visible to t1 when it wakes from the condvar despite pool=TypecheckDone. Per /arch §3d' H6 disposition ¶3 (H5 signature gone + narrow memory-ordering residue → ledger-and-defer to S62 is acceptable), /int requests /sprint apply this disposition. `cargo check --workspace` clean; `cargo clippy -p cranelisp --lib` no new lints (3 pre-existing unrelated warnings in `src/watch.rs`); `cargo nextest run --test sprint23 --no-fail-fast` 58/59 pass (only the reduced target fails at 80% rate); 27/27 observability tests pass. Design doc updated at `design/int/heisenbug-race-closure.md §3e'`. |
| 3f | /qa | **Hypothesis-specific regression tests** — author targeted tests that would have caught the chosen hypothesis pre-fix. Author post-hypothesis-selection (per Phase 3a plan, these were deferred). | **DONE** — 2 integration tests authored per /arch §3d' "Test authoring (step 3f) requirements": `sprint23::h5_gate_typechecking_user_fires_only_on_repl_thread` (test 1, H5 gate active invariant via `CRANELISP_SCHEDULER_TRACE=1` subprocess dump parse) and `sprint23::h5_normal_completion_does_not_starve_repl_eval_thread` (test 4, RAII-guard starvation absence via 2-second timeout). Both PASS 5/5 consecutive at HEAD (SHA `35062ca`). Full sprint23 suite: 60/61 pass — only `heisenbug_race_reduced_concurrent_import_pairs` fails (~80%, H6 residue, ledger-and-defer to S62). Unit tests 2 + 3 owned by /int (`src/scheduler.rs` flag-state + `EvalInFlightGuard` panic-unwind) — out of /qa scope per `memory/feedback_unit_tests_with_dev.md`. Baseline ledger updated: `sprint23::cache_repl_loads_heisenbug_parallel_stress` (S60 carry) RESOLVED and moved to "Resolved mid-sprint"; NEW entry `sprint23::heisenbug_race_reduced_concurrent_import_pairs` added under "Cargo test suite" owner `/int` target S62 disposition `under-investigation (sprint 62 — H6 carry)` with exact failure signature captured across 5 runs. Ring4.md §Slice 3 extended with a Wave-3-step-3f subsection cross-referencing the two tests as T-S3-H5-1 / T-S3-H5-4. `cargo check --tests` clean; `cargo clippy --tests --test sprint23` zero new warnings (3 pre-existing unrelated at lines 173/273/912). |
| 3f.int | /int | **H5 fix unit tests (tests 2 + 3 from /arch §3d')** — author the two /int-owned unit tests: test 2 (`src/scheduler.rs` flag-state invariant against `try_unblock_locked`) and test 3 (`src/session_v4.rs` `EvalInFlightGuard` panic-unwind leak). Tests live with the implementation per `memory/feedback_unit_tests_with_dev.md`. | **DONE** — Test 2: 3 unit tests in `src/scheduler.rs::tests` (`try_unblock_locked_suppressed_when_eval_in_flight_true`, `try_unblock_locked_pushes_when_eval_in_flight_false`, `try_unblock_locked_toggle_flag_switches_gate`) covering both invariant directions and the RAII toggle shape. Test 3: 3 unit tests in `src/session_v4.rs::eval_in_flight_guard_tests` (`guard_drop_clears_flag_on_normal_exit`, `guard_drop_clears_flag_on_panic_unwind`, `guard_drop_on_panic_restores_try_unblock_push_path`) covering normal-exit Drop, panic-unwind Drop via `std::panic::catch_unwind` + `AssertUnwindSafe`, and observable scheduler-state reset post-unwind. 4 test-only accessors added on `CompileScheduler` (`eval_in_flight_for_test`, `module_pool_for_test`, `force_typecheck_blocked_for_test`, `try_unblock_for_test`) gated by `#[cfg(test)]` — required because scheduler state (`SchedulerState`, `lock()`) is private to the scheduler module and Test 3 lives in `src/session_v4.rs`. All 6 new tests PASS 5/5 consecutive (`cargo nextest run -p cranelisp --lib -E 'test(try_unblock_locked) \| test(guard_drop) \| test(toggle_flag)'`); full lib suite 189/189 5/5 consecutive. `cargo check --workspace` clean. `cargo clippy -p cranelisp --lib --tests` zero new warnings in my changes (pre-existing warnings in `src/watch.rs`, `src/code.rs`, `src/platform.rs`, `src/worker.rs`, `crates/cranelisp-backend/src/compiler/mod.rs` unchanged). Design doc cross-reference in §3e' "Tests 2 + 3 landed (§3f.int)". |
| 3c'' | /int | **H6 hypothesis selection (in-sprint, not deferred to S62)** — user direction 2026-04-22: "keep going until the sprint reaches the quality objective"; H6 stays in-sprint. After step 3e' landed the H5 fix (rate 0→20%) and §3e' proposed ledger-and-defer under /arch §3d' H6 disposition ¶3, user withdrew that disposition. /int re-analyses the post-fix-h5-35062ca.log residue, identifies the H6 race as a compare-then-set hazard in `TypeCheckEnv::ensure_module_exists` (NOT the previously-suspected `scheduler.rs::notify_typecheck_done` sweep — that attribution was falsified by code-reading in step 3c''). Authored §7.10 "H6 chosen" + §8.3 "H6 fix plan" in `design/int/heisenbug-race-closure.md`; proposed new `SymbolTableEnsure { module, outcome }` trace tag for post-fix dump confirmation; recommended atomic rewrite via DashMap `entry().or_insert_with(...)` pattern. No code changes. | **DONE** — §7.10 authored with 3-5 line evidence quote from `tests/sprint61/race-evidence/post-fix-h5-35062ca.log` lines 26-36, code-reading derivation pinpoints `crates/cranelisp-typecheck/src/checker.rs:204-238` as the sole fix site (replacing the §3e'-named `scheduler.rs:704-722` attribution, which is falsified), three alternatives rejected with evidence (H5-variant, condvar memory-ordering on DashMap, partial HashMap state), cross-skill boundary concern flagged (fix lives in typecheck crate; /int proposes to implement under `FIXME(/typecheck)` comment per cross-skill protocol). §8.3 authored with atomic-ensure mechanism (d), touched files enumerated (~20-25 net LOC in one function), 8 risk notes for /arch, proposed acceptance criteria (rate≥20/20 over 20 runs; exactly-one-Created/one-AlreadyPresent `SymbolTableEnsure` pairs in post-fix dump; no sprint23 regression). Baseline ledger `tests/plan/baseline.md` corrected: `heisenbug_race_reduced_concurrent_import_pairs` entry's Target Sprint updated from "Sprint 62 (H6 data-plane ordering slice)" to "Sprint 61 Wave 3 (in-sprint H6 cycle)"; Disposition updated from `under-investigation (sprint 62 — H6 carry)` to `under-investigation (sprint 61 Wave 3 — H6 cycle)`. Ready for /arch step 3d'' mini-review. |
| 3d'' | /arch | **Mini-review for H6** — confirm H6 attribution matches evidence + code-reading; review §8.3 mechanism choice (approach (d) atomic `entry().or_insert_with(...)` vs nested-guard defensive refactor); approve or reject `SymbolTableEnsure` trace tag addition; flag typecheck-crate ownership tension (/int proposes to implement; /typecheck owns the crate); confirm acceptance criteria. | **DONE — APPROVE WITH REVISIONS** for H6 (see `design/int/heisenbug-race-closure.md §3d''`). H6 attribution confirmed as unique code-path match: `ensure_module_exists` is the sole unconditional `self.modules.insert(path, fresh_table)` site. Mechanism (d) approved with ONE mandatory variant: hoist user-seed clone OUTSIDE the `entry()` call to eliminate DashMap shard-collision deadlock risk (R1); §8.3.2's "extremely unlikely to collide" reasoning is probabilistic and unacceptable for a race fix. Ownership decision: **(C) hybrid** — /int authors under `FIXME(/typecheck)` comment with /typecheck review before commit; narrow precedent (fix fully self-contained, public API unchanged, implementing skill authored design). `SymbolTableEnsure { module, outcome: Created \| AlreadyPresent }` APPROVED (event type in `src/observability.rs` per Principle 3). `NotifyTypecheckDone` REJECTED (redundant with `ModuleStateTypechecked`). `SymbolTableInsert` REJECTED (per-symbol flood, not the race granularity). No boundary-type changes. Step 3e'' **GO** conditional on 4 items (hoist clone; add SymbolTableEnsure tag; FIXME(/typecheck) comment + review; post-fix dump meets §8.3.6). H7 fallback: if rate lands 19/20 or 18/20 AND H6 Created-Created signature fully gone, ledger-and-defer acceptable per §3d' precedent. |
| 3e'' | /int | **Fix for H6** — implement atomic `ensure_module_exists` per §8.3 + /arch 3d'' revisions; add `SymbolTableEnsure` trace tag if approved; commit under `FIXME(/typecheck)` cross-skill note if code lives in typecheck crate. Post-fix dump `tests/sprint61/race-evidence/post-fix-h6-<SHA>.log` must meet §8.3.6 acceptance criteria. | **DONE (pre-commit /typecheck review pending)** — all 4 /arch §3d'' conditions satisfied: (1) user-seed clone hoisted OUTSIDE `entry()` in `crates/cranelisp-typecheck/src/checker.rs::ensure_module_exists` — `Entry::Vacant(slot).insert(...)` pattern with pre-cloned `seed_entries`; closure performs NO nested DashMap access. (2) `SymbolTableEnsure` tag added to `SchedulerTraceTag` with `Created | AlreadyPresent` discriminator encoded in existing `Module { module, state }` payload (0=Created, 1=AlreadyPresent); `format_event_line` renders symbolically. Emission crosses the crate boundary via new `cranelisp-typecheck::trace` install-a-function-pointer hook; binary installs the forwarding sink in `main.rs` alongside panic-hook wiring. (3) `FIXME(/typecheck)` comment added at the top of rewritten `ensure_module_exists` citing `design/int/heisenbug-race-closure.md §3d''`. (4) Post-fix dump `tests/sprint61/race-evidence/post-fix-h6-35062ca.log` captured — shows exactly ONE `SymbolTableEnsure module=helper outcome=Created` (ts=20007333, t2) followed by `AlreadyPresent` emissions on both threads; `helper-val` lookup succeeds; zero `'helper-val' not found` errors. Rate: **10/10 PASS** `heisenbug_race_reduced_concurrent_import_pairs` (gate met); full sprint23 suite 61/61 on clean run, 9/10 across 10 whole-suite runs (1 pre-existing `h5_normal_completion_does_not_starve_repl_eval_thread` flake — unrelated). Unit tests: 3 new in `checker.rs` (seed-on-first-call, preserve-populated-table, concurrent-same-path-exactly-one-Created) + 2 new in `observability.rs` (emission + format_line) + 3 in `trace.rs` (hook install + outcome u8 discriminator). `cargo check --workspace` clean. `cargo clippy -p cranelisp-typecheck --all-targets` + `cargo clippy -p cranelisp --all-targets` — no new warnings. Files touched: `crates/cranelisp-typecheck/src/trace.rs` (new), `crates/cranelisp-typecheck/src/lib.rs`, `crates/cranelisp-typecheck/src/checker.rs`, `src/observability.rs`, `src/main.rs`, `design/int/heisenbug-race-closure.md §3e''` (new), `tests/sprint61/race-evidence/post-fix-h6-35062ca.log` (new). No git commits — pre-commit /typecheck review gate enforced. |
| 3e''.review | /typecheck | **Pre-commit /typecheck review** of H6 fix (per /arch §3d'' hybrid-ownership condition 4). Review dimensions: atomicity correctness, API/behavioural preservation, trace-module design, unit tests, boundary hygiene, style/craftmanship. Decision: APPROVE / APPROVE WITH REVISIONS / REQUEST REVISIONS / REJECT. Append §3e''.review to `design/int/heisenbug-race-closure.md`. | **DONE — APPROVE**. See `design/int/heisenbug-race-closure.md §3e''.review`. Atomicity fix correct (DashMap `Entry` holds shard-write-lock across both arms; seed clone hoisted outside; zero nested DashMap access). API signature unchanged; all 13 callers (7 internal + 6 external) preserved. Trace-module is `OnceLock<fn>`-based, thread-safe, null-check no-op when uninstalled, zero `src/` dependency (Cargo.toml confirms only `cranelisp-types` + `dashmap`). Three new `ensure_module_exists_*` unit tests cover seed, non-overwrite-on-second-ensure, and N=8 concurrent-same-path with exactly-one-Created sink assertion. `FIXME(/typecheck)` cites §3d'' and flags precedent as non-generalisable. No `.unwrap()`/`.expect()` in pipeline code (one in `#[cfg(test)]` — exempt per `src/CLAUDE.md`). Boundary clean — `cranelisp-types` untouched, no new deps, no new serialised types. Zero requested revisions. Commit-gate OPEN. Narrow precedent accepted for H6 surface; future /typecheck-crate work returns to /typecheck ownership by default. The new `trace.rs` module becomes /typecheck maintenance responsibility going forward. |
| 3f'' | /qa | **H6 regression test** — author a targeted integration test that would have caught the non-atomic `ensure_module_exists` race. Candidate shape: concurrent spawn of N threads each calling `tc_env.ensure_module_exists(M)` for the same `M`, then assert that a single thread's pre-inserted `helper-val` survives; OR reuse `heisenbug_race_reduced_concurrent_import_pairs` as the regression guard (already fires pre-fix at 80%). | blocked-by 3e'' |
| 3f.flake | /qa | **H5 normal-completion test flake disposition** — resolve the `h5_normal_completion_does_not_starve_repl_eval_thread` 9/10 full-workspace rate reported in /int §3e''. Per user directive 2026-04-22 ("flaky is not a disposition"): either the test measures a real starvation regression (open H7) or it is incorrectly written (fix test). | **DONE — disposition (a) "tighten test"**. Baseline reproduction at SHA (working tree): 5/5 isolation, 15/15 `--test sprint23`, 20/20 whole-workspace (`cargo nextest run -p cranelisp`) on pre-fix 2-s ceiling. Could NOT reproduce /int's 9/10 rate on this machine, but root-cause is identified by calibration: subprocess wall-clock timings are 0.28-0.44 s whole-workspace vs. 0.5-0.8 s in isolation (whole-workspace is actually *faster* per-subprocess; 2 s ceiling gave only ~2.5-4× margin; on busier machines with contended fork+exec + dynamic loader, cold-start alone can exceed 1 s and breach 2 s). The H5 starvation failure mode is an INFINITE block in `wait_module_inmem_complete_blocking` (flag leak → `try_unblock_locked` suppresses push forever), so the invariant only needs a ceiling that distinguishes "completed" from "hung", not one calibrated to typical wall-clock. Widened ceiling 2 → 15 s (~30× typical, 0.5× per-test cap, still catches the real failure sharply). Docstring rewritten to explain calibration + precedent (sibling baseline-ledger entry `io_trace_off_path_subprocess_completes_within_generous_ceiling` uses identical disposition). Post-fix 12/12 whole-workspace + 5/5 isolation; no new clippy warnings (3 pre-existing at sprint23.rs 173/273/912). Files touched: `tests/sprint23.rs` (timeout const + comment), `tests/plan/ring4.md §Slice 3 T-S3-H5-4 row` (cross-reference). NOT opening H7 — see readout. |
| 3g | /review | Per-wave /review pass — `design/review/sprint-61-wave-3.md` | **DONE — PASS WITH FINDINGS**. 0 blockers / 1 important / 4 suggestions. Three hypothesis cycles (H4 falsified → H5 landed → H6 atomic) are evidence-gated with committed dumps at `tests/sprint61/race-evidence/{failing,post-fix,post-fix-h5,post-fix-h6}-35062ca.log`. Narrow /int → /typecheck precedent (per /arch §3d'' hybrid ownership) honoured end-to-end; all four mandatory conditions satisfied; /typecheck §3e''.review APPROVE with zero revisions. Boundary hygiene clean (no `cranelisp-types` changes; typecheck crate deps only `cranelisp-types` + `dashmap`; no `cranelisp_alloc` in trace paths). No `#[ignore]` in new tests; no flaky disposition in baseline. I-1: conditional-guarded assertion in `ensure_module_exists_concurrent_same_path_emits_exactly_one_created` — fold into S62 trace-module cleanup (add `reset_hook_for_tests`). Commit gate: GO. Stress-verification recommended: 20× `cargo nextest run -p cranelisp --test sprint23`. See `design/review/sprint-61-wave-3.md`. |

**Going-in position** (open, evidence-gated):

- Symptom: `'helper-val' not found in module 'helper'` — reader observes module as "ready" but symbol table doesn't yet have `helper-val`. H1 matches most cleanly BUT Sprint 60 Round 5 already tightened `is_typechecked` (flag vs `contains_key`). If H1 held, Round 5 should have closed it. Residual 30% suggests H2 or H3 (or hybrid: predicate is tight, transition-vs-publication still races elsewhere).
- Reduction target: reproduce reliably under controlled timing; evidence-capture step needs dumps from BOTH a failing run and a passing run to see the divergence.

**Wave 3 close (2026-04-22, methodology-pivot revision)**:

- ✅ Three named mechanisms closed: H4 (narrow gate + observability), H5 (`eval_in_flight` scheduler-side push-gate + RAII guard), H6 (`ensure_module_exists` non-atomic check-then-insert → atomic `entry().or_insert_with()`).
- ✅ Evidence dumps for each iteration committed at `tests/sprint61/race-evidence/` (failing-run + passing-run + post-H4 + post-H5 + post-H6).
- ✅ Unit tests for each fix in the owning crate (+ 3 scheduler, +3 session_v4, + 3 typecheck, + observability tag tests).
- ✅ Integration regression guard: `sprint23::heisenbug_race_reduced_concurrent_import_pairs` (deterministic at light load, exercises ~95% of the race space at 6-thread load).
- ✅ /arch mini-review at each hypothesis iteration (§3d / §3d' / §3d'').
- ✅ /typecheck pre-commit approval for cross-skill H6 fix (§3e''.review).
- ✅ /review Wave 3 PASS WITH FINDINGS (0B / 1I / 4S — I-1 folded to Slice 5).
- ⚠️ Original S60-carry entry `sprint23::cache_repl_loads_heisenbug_parallel_stress` resolved (passing post-H6).
- ⚠️ `sprint23::heisenbug_race_reduced_concurrent_import_pairs` RETAINED in baseline ledger at ~5-10% residue under heavy contention — disposition `under-investigation (sprint 62 — concurrency audit)`. Honest carry; not dispositioned flaky or resolved.
- ⚠️ **5 escaped baseline carries discovered** during workspace stress (`d6_exemplar_propagate_only`, `d6_exemplar_propagate_single_pass`, `d6_exemplar_solve_all_dots`, `d6_exemplar_solve_minimal_puzzle_no_io`, `wave6_demo_repros::exemplar_solver_does_not_stack_overflow_on_small_puzzle`). All ledgered; owner `/port` + underlying-owner `/backend`; exemplar solver stack overflow is documented in `exemplar/CLAUDE.md §"Known Issues"` but was not in the ledger. Disposition open for /sprint at close.
- ⚠️ Residual `sprint61_observability_io::*` 3 tests (Slice 4 preconditions) unchanged.

**Stress-verification gate is NOT the Wave 3 close criterion** per methodology pivot. See §Scope "Methodology pivot" above. S62 concurrency audit replaces the stress gate as the proof of race closure.

### Wave 4 — Slice 4 21-hello-io (ownership decided at readout)

| Skill | Task | Status |
|---|---|---|
| /backend | Run stress harness with `CRANELISP_IO_TRACE=*`; capture evidence on `21-hello-io.cl` at load | **DONE 2026-04-22 (SHA `776a6cf`)** — step 4a reduction + step 4b evidence capture. 7-line minimum repro (100% crash, no concurrency, no platform IO). 3 trace dumps under `tests/sprint61/race-evidence/21-hello-io-{failing,failing-min,passing}-776a6cf.log` + README. |
| /backend | Author `design/backend/slice-4-21-hello-io-investigation.md` with hypothesis weighting | **DONE** — 85% H(4-1) trampoline continuation-state leak; H(4-2)/H(4-3) ruled out by evidence. |
| /backend + /platform | Readout — identify which hypothesis (trampoline leak / stdio DLL / nextest crosstalk) holds; /sprint assigns ownership | **evidence-ready** — /backend recommends owning the fix on H(4-1) weighting; /arch at step 4c adjudicates. |
| /arch | Mini-review of investigation note (step 4c) | **DONE 2026-04-22** — verdict H(4-1'') coordinated defect; fix backend-only; `io.rs` untouched. See `design/backend/slice-4-21-hello-io-investigation.md §4d`. |
| /backend | Implement fix (step 4e) — `emit_capture_return_inc` helper | **DONE 2026-04-21** — helper added in `crates/cranelisp-backend/src/compiler/control_flow.rs` (called from `compile_lambda_body`); unit test `lambda_return_captured_heap_var_emits_inc` in `crates/cranelisp-backend/src/lib.rs` (175/175 backend tests pass, verified red → green by toggling the helper call). Minimum repro now 10/10 exit=51. `sprint61_observability_io` 7/7 pass. `examples_run` green after tightening 21-hello-io accepted exits `[101, 133, 141] → [243]`. `cargo check` + clippy clean. ring2-rc.md §5.6 adds the capture-return-inc rule. Post-fix trace at `tests/sprint61/race-evidence/21-hello-io-post-fix-776a6cf.log`. See `design/backend/slice-4-21-hello-io-investigation.md §4e`. |
| /qa | Author hypothesis-specific tests (step 4f) — Layer 3 integration test using the 7-line minimum repro | **DONE 2026-04-22** — authored `tests/sprint61_io_closure_regression.rs` (2 Layer-4 tests, ~200 LOC: `io_trampoline_then_combinator_does_not_double_free_capture` asserts exit=51 + no panic + no pre-fix surface exits; `io_trampoline_then_combinator_trace_shows_clean_trampoline_exit` asserts `TrampolineEnter`/`TrampolineExit result=51` under `CRANELISP_IO_TRACE=1`). 5/5 consecutive passes. 7/7 `sprint61_observability_io` tests pass; `examples_run::every_example_file_runs_under_examples_prelude` passes. 4 baseline-ledger entries resolved (1 S60 carry + 3 Wave-1 Slice-4-dependent) — moved to `tests/plan/baseline.md §"Sprint 61 Wave 4 — Slice 4 21-hello-io closure capture double-free"`; 7 ledger entries remain (1 H6 residue + 5 `d6_exemplar_*`/`wave6_demo_repros` + 1 harness concern). `tests/plan/ring4.md §Sprint 61 Wave 4 step 4f — Slice 4 closure` subsection added. `cargo check --tests` clean; clippy zero new warnings on new file. |
| /review | Per-wave /review pass — `design/review/sprint-61-wave-4.md` (step 4g) | **DONE 2026-04-22** — verdict **PASS** (0 Blockers, 0 Importants, 3 Suggestions). All 4 required audits clean (io.rs untouched since 776a6cf; single `emit_capture_return_inc` helper + single call site; no `#[ignore]` in regression test; no new FIXMEs in io.rs). /arch §4d four mandatory conditions all satisfied. Wave 4 commit readiness: **GO**. See `design/review/sprint-61-wave-4.md`. |

**Wave 4 close**: 10/10 consecutive runs on `examples_run::every_example_file_runs_under_examples_prelude` and full example sweep; /review PASS; commit; baseline ledger entry for 21-hello-io REMOVED.

### Wave 5 — Slice 5 methodology residual + showcase + close

Runs after Wave 4 closes. Slice 5 H was already prepped by /qa in Phase 3a; E-1 audit is done; only implementation work remains.

| Skill | Task | Status |
|---|---|---|
| /qa | Implement E-1 — convert ~10 tests + `ReplSessionBuilder` helper to `tempfile::TempDir` per `tests/plan/tempdir-audit.md`; insert rule text into `tests/CLAUDE.md` | pending |
| /qa | Implement H — 3 `[Tested+Neg]` promotions from shortlist; commit spec-annotation updates | pending |
| /sprint | E-3 — update SPRINT.md template in `.claude/commands/sprint.md` to reflect new stress-verification gate | pending (lands with archive) |
| /repl | Author `repl/demos/ring4s.demo` showcasing Slices 1, 3, 4 visible deliverables | blocked-by Wave 4 |
| /repl | Replay all 26+ prior demos — no regressions | blocked-by ring4s.demo |
| /port | Refresh `exemplar-progress.demo` if solver behaviour improved | blocked-by Slice 2 close |
| /stdlib | Refresh `stdlib-progress.demo` only if Slice 1 changed user-visible stdlib behaviour | conditional |
| /examples | 27-example sweep verification | blocked-by Wave 4 |
| /docs | User-doc refresh if any user-visible behaviour changed | conditional |
| /review | Final /review report — PASS required — `design/review/sprint-61-final.md` | blocked-by all above |
| /qa | Close-time audit — spec coverage + baseline ledger clean + FIXME scan | blocked-by /review |
| /sprint | **20-run stress verification** — full-suite close gate | blocked-by /qa audit |
| /sprint | Close checklist (all Phase 6 items); outcome section; archive to `sprints/archive/sprint-61.md`; ROADMAP.md update | blocked-by 20-run green |

**Sprint close**: status → COMPLETE; baseline ledger has 0 entries for the three closed defects; 20/20 stress green; archive and ROADMAP updated per Phase 6.

### Wave ordering rationale

- **Slice 0 must land first** — Slices 3 and 4 consume its infrastructure; Slice 1 and 2 don't need it but benefit from the discipline of "infra before defects."
- **Wave 2 parallelises Slices 1 + 2** because they touch different skills (/int vs /port) and different files (src/ vs exemplar/). This is the only intra-sprint parallelism; races in Waves 3/4 must be serial per the sequential-slice discipline /arch approved in Phase 2.
- **Wave 3 is sequential within /int** — evidence capture must complete and a hypothesis must be chosen before implementation. This is the evidence-gated discipline enforced by the /arch-approved FIXME #3.
- **Wave 4 waits for Wave 3** because simultaneous investigation of two races in the same process would conflate evidence. The serial discipline Sprint 60 violated is enforced here.
- **Wave 5 runs only after all defects closed** because the showcase demonstrates the delivered capabilities, and /stress verification is the final acceptance. /qa's E-1 + H work slots here because it's low-risk and doesn't block the critical path.

## Notes

_Runtime log — filled as the sprint progresses._

**Phase 3 opened 2026-04-22.** `/arch` Phase 2 review: APPROVE WITH REVISIONS. Four FIXME(/arch) items resolved in this revision (crate placement locked in Slice 0; Slice 2 2-day escalation threshold recorded; verification-table tiered to 5/10/20; Phase 6 checklist updated in `.claude/commands/sprint.md`). One FIXME(/arch) remains for /int to action in Slice 3 design doc: evidence-gated hypothesis naming before fix (see /int plan below).

**Phase 3 /qa readout (2026-04-22, SHA `a9028c0`)**: Slice 5 E-1 + H audit artefacts committed to `tests/plan/` — `tempdir-audit.md` (34-row catalogue, K ≈ 10 converts + 1 helper) and `neg-coverage-candidates.md` (7-candidate shortlist, 3 recommended for Wave 2). Rule text for `tests/CLAUDE.md` staged in `tempdir-audit.md §"Proposed tests/CLAUDE.md rule"` — NOT yet inserted; /review inspects shape in Wave 1 closing pass before Wave 2 insert. Surprise finding: scope of E-1 extends beyond exemplar to `tests/helpers/mod.rs::ReplSessionBuilder` default path — flagged in /qa plan and surfaced here for /sprint awareness so Wave 2 sizing accounts for the helper-level fix.

**E-2 applied** (2026-04-22, user approval): `.claude/commands/sprint.md` Phase 6 close checklist now carries the tiered stress-verification gate. Actual diff applied:

```diff
     - [ ] All tests pass (`cargo test`) — 0 failures
+    - [ ] **Stress-verification gate**: baseline verified across **20 consecutive `cargo nextest run --no-fail-fast` passes** at 0 failures (full-suite close gate). Intermediate per-slice gates use tiered thresholds — typically 5 consecutive runs for deterministic defects, 10 for race/concurrency defects. Document the stress results in the sprint report §Stress Verification. Single-run "clean" is insufficient (Sprint 60 lesson — races fire at ~30% under pressure but pass reliably in isolation).
     - [ ] Ignored test count is 0 for in-scope features …
```

**Phase 3 design docs — authored 2026-04-22, ready for `/arch` + `/qa` Phase 3a review**:

| Slice | Doc | Owner | Lines | Status |
|---|---|---|---|---|
| 0 | `design/int/observability.md` | /int | ~190 | AUTHORED — FIXME(/arch) #1 + #2 resolved in-doc (crate placement locked; env-var parse-once). IO-log cross-ref corrected to `io_trace.rs` post-drift. |
| 0 | `design/backend/io-trampoline-trace.md` | /backend | 131 | AUTHORED — 11 event types grounded in `io.rs`; `OnceLock<Option<TraceFilter>>` parse-once; merge-sort compat with /int trace via shared `Instant` + `ThreadId`. |
| 1 | `design/int/bare-primitive-value-path.md` | /int | ~95 | AUTHORED — two candidate divergence points identified (`FQSymbol.module` attribution vs. match arms returning `None` at `check_bare_symbol_introspection` line 2179). |
| 3 | `design/int/heisenbug-race-closure.md` | /int | ~175 (skeleton) | AUTHORED — three numbered hypotheses with per-hypothesis fix sketches; evidence-gated discipline §6 declared (doc to be updated with chosen hypothesis + event-log citation BEFORE fix commit). FIXME(/arch) #3 resolved. |
| 2 | `sprints/SPRINT.md §Skill Plans → /port` + `exemplar/solver.cl` FIXME refresh | /port | — | PLAN AUTHORED — 4 candidate hypotheses ordered by cost; top candidate = `peers`-includes-self (cheapest static check, also explains S60 "patch-to-None breaks valid puzzles"). 2-day escalation cap named. |
| 5 E-1+H | `tests/plan/tempdir-audit.md` + `tests/plan/neg-coverage-candidates.md` | /qa | 34-row catalogue + 7-candidate shortlist | AUTHORED — K ≈ 10 converts + 1 helper. 3 [Tested+Neg] promotions recommended for Wave 2. |
| 4 | TBD at Slice 4 readout | /backend or /platform | — | Design deferred per evidence-gated discipline — no design doc until event-log produces evidence. |

**Minor drift caught during Phase 3**:
- `/int`'s observability.md originally referenced `crates/cranelisp-runtime/src/trace.rs`; `/backend` chose `io_trace.rs` (because `trace.rs` already hosts the `(trace ...)` special form). Reconciled: /int's doc now points at `io_trace.rs` (2026-04-22 edit by /sprint).
- Slice 5 F (`.gitignore` entry for `tests/sprint60/.runs/`) turned out to be ALREADY SATISFIED — `.gitignore:31` carries the entry. /qa caught it during audit. Scope trimmed; S60 /review I-1 recorded as closed.

**Operational considerations**:

- If Slice 0's event-log infra surfaces a structural boundary concern (e.g., thread-local state requires a new `SharedState` field, or dump format leaks into cache), `/int` or `/backend` MUST file FIXME(/arch) in the design doc before implementation. Per /arch Phase 2: no boundary-type changes pre-authorised.
- Slices 3 and 4 consume Slice 0 infra but touch different subsystems. Serial discipline forbids parallelism — each fix is verified against a known-green baseline.
- If Slice 2 branch (c) fires, Slice 4 still proceeds; Defect 3 does not gate the race work.

**/port Phase 3 readout (2026-04-22)**: reduction plan authored in §Skill Plans. Default stance is exemplar bug pending reduction evidence; 4 candidate hypotheses ordered by cost (peers-includes-self → post-make-grid state dump → eliminate match-arm trace → peer-helper instrumentation). If all 4 clear without a fix, escalate via 2-day threshold to mini-triage with /arch + /backend. Wave-2 execution ready pending Slice 0 completion (though Slice 2 does not require Slice 0 — this is a deterministic defect and can start earlier if /port bandwidth permits per §Slice Execution Order item 3).

**/qa escaped-carries readout (2026-04-22, Wave 3 step 3f+, SHA `35062ca`)**: During Wave 3 workspace stress verification, `/sprint` surfaced tests failing at HEAD that were not in `tests/plan/baseline.md`. `/qa` has now ledgered them per `baseline.md §"Close-time Verification Protocol"`. Five new entries added under a new subsection `§"Escaped carries — surfaced Sprint 61 Wave 3 workspace stress"` — four `sprint59_defects456_repro::d6_exemplar_*` reductions (`propagate_only`, `propagate_single_pass`, `solve_all_dots`, `solve_minimal_puzzle_no_io`) plus `wave6_demo_repros::exemplar_solver_does_not_stack_overflow_on_small_puzzle`. All five map to Sprint 59 Defect 6 (exemplar solver stack-overflow on full 81-cell grids) and are disposed `exemplar-gap (owner=/port, underlying-owner=/backend)` with target sprint **Sprint 62 — disposition OPEN, `/sprint` decides at close**. Handoff discrepancy noted: the pre-ledger brief listed five failing `d6_exemplar_*` tests, but `d6_exemplar_eliminate_from_peers_does_not_segv` passes consistently at SHA `35062ca` (2/2 isolation, 1/1 under concurrent load) — only four are genuinely failing. Also updated the existing `sprint23::heisenbug_race_reduced_concurrent_import_pairs` entry to reflect H6 fix landed (+14 LOC in `crates/cranelisp-typecheck/src/checker.rs::ensure_module_exists`, rate dropped from ~80% → 5–10% under 6-thread contention, residue real with same signature), disposition open at close: (a) in-sprint H7 cycle or (b) defer to S62 concurrency audit. Informational note appended to §"Close-time Verification Protocol" flagging the N-run 0/N gate's low statistical power for low-frequency races and naming the audit+loom+structured-interleaving methodology pivot as a candidate S62 workstream. Ledger count: 6 → 11 entries. `cargo check --tests` clean (1 pre-existing unused-`Result` warning in `tests/scheduler.rs:324`, unchanged).

## Outcome

_Filled when sprint closes._

### Delivered
### Deferred
### Findings
