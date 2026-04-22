# Heisenbug race closure: Slice 3 of Sprint 61

**Owner**: `/int`
**Status**: DESIGN — SKELETON (Sprint 61 Phase 3, 2026-04-22)
**Reviewers**: `/arch` (boundary-type hygiene)

**Evidence-gated discipline** (per `/arch` Phase 2 FIXME item #3, see
§6 below): this doc will be updated with the chosen hypothesis and the
event-log dump citation BEFORE any fix commit lands. The skeleton
below names three candidate hypotheses and fix sketches; exactly ONE
of them will be selected after Slice 0's scheduler event log produces
evidence. The rejected hypotheses are preserved in the archive for
auditability.

## 1. Problem

`sprint23::cache_repl_loads_heisenbug_parallel_stress` fails at ~30%
under full-suite pressure. Sprint 60 Round 5 reduced the rate but did
not eliminate it. Baseline ledger entry: `tests/plan/baseline.md`.

Symptom: a reader thread observes a module's scheduler state advance
to "typecheck done / ready", then reads the module's symbol table and
does not find symbols that the writer thread eventually does publish.
Diagnosed as a publish-vs-flag ordering race.

## 2. Three hypotheses

Numbered for citation stability in subsequent updates.

### H1 — `is_typechecked` predicate too permissive

`Scheduler::is_typechecked` (`src/scheduler.rs:1010`) returns true when
the module's `ModulePool` is `TypecheckDone` or `Complete`. But the
symbol table for that module may be present (seeded by
`ensure_module_exists`) without the Defs having been inserted yet — a
partial-publish window. The reader passes the predicate but reads
before the Defs arrive.

### H2 — Symbol publication outside critical section

Symbols are published to `shared.symbol_tables` via separate operations
from the one that flips the pool state to `TypecheckDone`. If the
pool flip is visible (via atomic/DashMap) before the symbol insertions
become visible, a reader observes "ready" → reads → misses symbols.
The `register_dep` shim in `worker.rs:1342` already enforces
publish-before-register via `publish_dep_sexps` preceding the
scheduler notify (line 1382), but the same discipline may not cover
the post-typecheck symbol publication into `symbol_tables`.

### H3 — Typecheck-worker loop transitions pool state before symbol publication

Inverse of H2's assumption. The typecheck worker loop (in
`src/worker.rs`) may call `notify_typecheck_done` (observed at line
3440 and mentioned at line 895) BEFORE the check_result's symbols are
merged into `symbol_tables`. H2 says "publication happens but outside
the locked region"; H3 says "the pool transitions happen first, then
the publication happens". Both result in the same reader-observable
symptom but different fix sites.

## 3. Investigation plan

Gated on Slice 0 landing (scheduler event log).

1. Run the stress harness with `CRANELISP_SCHEDULER_TRACE=*` to see
   every pool transition and every `register_dep publish` /
   `is_typechecked` fast-path event across all threads.
2. Capture **one failing run** and **one passing run** with the same
   seed/thread-count. Save to `tests/sprint61/race-evidence/`
   (outside `.gitignore`d paths; these become test-plan artifacts).
3. Merge-sort events across threads (dump-time merge-sort per
   `design/int/observability.md §7`).
4. For each run, identify the ordering between:
   - `notify_typecheck_done` (pool flip to `TypecheckDone`)
   - symbol insertion into `shared.symbol_tables[module]`
   - reader's `is_typechecked` fast-path hit returning true
   - reader's subsequent `symbol_tables[module].get(name)` miss
5. Map the observed ordering to H1, H2, or H3.

**Falsification rules**:

- H1 holds if the failing run shows `is_typechecked → true` while the
  symbol table for that module has a size less than expected (symbols
  missing). Cross-check via a diagnostic probe in the reader path
  that dumps table size.
- H2 holds if symbol insertion and the pool flip are serialised
  under different locks, and the failing run shows the flip event
  ordered BEFORE the insertion event on a consistent timeline.
- H3 holds if inspection of the worker loop shows the pool flip
  happens before the symbol-merge step unconditionally, independent
  of lock ordering.

## 4. Fix sketches (all three; only one is implemented)

### H1 fix

Tighten `is_typechecked` to include a symbol-table-non-empty check.
After the pool-state check, also assert `symbol_tables[module]
.symbols.is_empty() == false`. `SymbolTable::symbols` is the public
DashMap field, so this uses an already-public API. No
`cranelisp-types` shape change.

Touches: `src/scheduler.rs::is_typechecked`.

Risk: ordering sensitivity. If the pool flips to `TypecheckDone`
BEFORE symbols are inserted (H3 territory), this fix still fails. H1
specifically assumes the flip happens AFTER insertion but the two
operations are under different memory-ordering regimes.

### H2 fix

Widen the critical section in `register_dep` / the scheduler's pool
transition to include symbol publication. Currently the sequence is:

1. acquire symbol_tables lock
2. insert symbols
3. release symbol_tables lock
4. acquire scheduler state lock
5. flip pool to TypecheckDone
6. release scheduler state lock

Fix: fold (1)–(3) into the scope of (4)–(6), i.e., take both locks in
a consistent order and release both only after the pool flip. Or:
move the symbol insertion inside the scheduler state lock via a
single `shared.commit_typecheck_done(module, symbols)` method that
holds both locks (or a single lock covering both).

Touches: `src/session_v4.rs::SharedState`, `src/worker.rs` (worker
loop's publish site).

Risk: lock contention. Widening the critical section may slow
concurrent typecheck throughput. Measure with the off-path < 1%
budget.

### H3 fix

Invert pool-transition ordering in the typecheck-worker loop. If the
current sequence is `notify_typecheck_done → insert_symbols`, change
to `insert_symbols → notify_typecheck_done`. This mirrors the
publish-before-register discipline in `register_dep` (worker.rs:1342,
comment at 1382-1397 enforcing "publish BEFORE scheduler notify").

Touches: `src/worker.rs` (wherever the post-typecheck publication
currently happens, likely around `notify_typecheck_done` at line
3440).

Risk: waiter wake-up. Readers woken by `notify_typecheck_done` must
not race ahead of the symbol insertion — but since symbol insertion
precedes the notify in this fix, waiters see symbols already
published by the time they observe the flag. The risk is if any
other writer path also flips the pool state; auditing all transition
call sites is part of the fix.

## 5. Boundary concerns (per /arch Phase 2)

Per Architecture Review §3–4:

- **H1 fix** uses `SymbolTable::symbols.is_empty()` (already public
  DashMap API). **No shape change on `SymbolTable`.** No
  `cranelisp-types` boundary change.
- **H2 fix** is entirely inside `src/scheduler.rs` + `src/worker.rs`
  + `SharedState` (`src/session_v4.rs`). Uses existing locks;
  re-orders their acquisition or merges their scope. No new
  synchronisation primitive on any `cranelisp-types` boundary type.
- **H3 fix** is a statement reorder in `src/worker.rs`. No boundary
  change.

**Pre-authorisation**: none. If evidence reveals a boundary need
(e.g., a `SymbolTable` atomic publish method signalling version
change, or a scheduler-state field that must move to a shared
type), this doc is updated with `FIXME(/arch)` BEFORE
implementation. `/arch` reviews before any `cranelisp-types` commit.

## 6. Evidence-gated discipline

Per `/arch` Phase 2 FIXME item #3 (SPRINT.md §Architecture Review
line 183):

> After the event log surfaces evidence, the design doc MUST name
> the chosen hypothesis (1, 2, or 3) and reference the event-log
> dump that justifies the choice, BEFORE the fix is implemented.

This section is the tracked acknowledgement of that gate. The doc
will be updated as follows after Slice 0 ships:

- Add `## 7. Evidence` section with the scheduler-trace dump excerpt
  (the 10–30 events bracketing the publish/flag race) and the
  ordering analysis that maps to H1/H2/H3.
- Add `## 8. Chosen hypothesis` naming exactly one of H1/H2/H3 with
  a one-paragraph rationale referencing §7.
- Remove the §4 fix sketches for the two rejected hypotheses (keep
  in git history), leaving only the implemented one.
- Only then open the fix implementation.

Skipping this gate — implementing a fix without event-log evidence —
is exactly the behaviour `/arch` review rejects. The gate is
auditable via git blame on this doc.

## 7. Cross-references

- `design/arch/concurrent-pipeline.md §7` — form-by-form scheduler's
  pool-state-transition protocol (what the three hypotheses are each
  about).
- **Decision 30** — context on scheduler constraints.
  `/arch` confirms the fix does NOT require module-system redesign;
  Decision 30 (parent↔child typecheck deadlock, module-system
  redesign) remains out of scope per SPRINT.md §"Out of Scope".
- `crates/cranelisp-types/src/module.rs::SymbolTable` — boundary
  type whose internal DashMap ordering H1 depends on. `symbols`
  field is public; no shape change expected.
- `src/session_v4.rs::SharedState` — owns both symbol_tables and the
  scheduler. H2 fix may merge locking scope here.
- `src/scheduler.rs::is_typechecked` (line 1010) — H1's direct
  target. Current predicate checks only pool state.
- `src/worker.rs::register_dep` (line 1342) + `publish_dep_sexps`
  (line 1309) — existing publish-before-register discipline (Sprint
  58 W6 Defect 1, Sprint 59 Workstream A §7). H3 extends the same
  discipline to post-typecheck symbol publication.
- `src/worker.rs::notify_typecheck_done` call at line 3440 — H3's
  likely fix site.
- Sprint 60 Wave 2 Round 4 — the earlier publish-vs-flag fix that
  reduced but did not eliminate the rate. Referenced at
  `src/scheduler.rs:1005-1009`. This slice is the completion of that
  work.
- `memory/feedback_cross_skill_minimal_repro.md` — the reduction
  discipline this sprint operates under.

## 7a. Sketch comparison

Per `CLAUDE.md §"Sketch Oracle"`. The sketch has no equivalent race
because it has no equivalent concurrency: `sketch/src/schedule.rs` and
the sketch's REPL / batch pipelines drive compilation on a single
thread — register, typecheck, codegen, execute all happen in program
order, and the sketch's `sketch/audits/` inventory notes no
persistent-worker topology exists there. There is consequently no
sketch-side `is_typechecked` fast-path, no publish-before-register
discipline, and no publish-vs-flag race of any shape. The
reimplementation's scheduler + persistent worker pool (Decision 27,
G9 complete; `design/arch/concurrent-pipeline.md §7`) is the
architectural divergence that introduces this class of race. The
divergence is spec-mandated — Decision 27's persistent-worker
topology is a precondition for Ring 4's parallelism work and is not
reversible — so H1/H2/H3 must be solved inside the concurrent shape
rather than by reverting to the sketch's serial pattern.

## 8. Testing

- **Slice gate**: 10 consecutive runs of
  `sprint23::cache_repl_loads_heisenbug_parallel_stress` at 0
  failures.
- **Final close contribution**: 20 consecutive full-suite
  `cargo nextest run --no-fail-fast` passes at 0 failures.
- **Regression coverage**: the failing-repro test is already in the
  suite (`sprint23::cache_repl_loads_heisenbug_parallel_stress`);
  the fix commit turns its observed fail-rate to 0. Keeping the
  stress test in the suite per `memory/feedback_repros_join_suite.md`
  guards against regression.
- **Evidence artefact**: `tests/sprint61/race-evidence/{failing,
  passing}.trace` committed alongside the fix, so the chosen
  hypothesis is auditable after the fact.
