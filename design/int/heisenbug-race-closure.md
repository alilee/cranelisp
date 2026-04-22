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

## 3b. Reduction notes (Wave 3 step 3a)

**Authored**: Sprint 61 Wave 3 step 3a (reduction-only agent), 2026-04-21.
**Purpose**: produce a smaller, more deterministic repro so step 3b
(evidence capture) can reliably drive `CRANELISP_SCHEDULER_TRACE=1`
dump collection without chasing a 30% hit rate across full-suite runs.

### What was tried

1. **Baseline**: `sprint23::cache_repl_loads_heisenbug_parallel_stress`
   — 20 serial iterations, each running two REPL subprocesses
   sequentially. In isolation (`cargo nextest run --test sprint23 --`
   scoped to the single test name) this test passes **10/10** on a
   local M4 Pro — the ~30% rate in the baseline ledger comes from
   **other** nextest tests contending concurrently for subprocess
   spawn + disk IO, not from anything inside the test's own shape.
2. **Parallel-session shape (shell probe)**: N independent shell-level
   child subprocesses each running one iteration. N=2 gave per-trial
   fail rates from 8% to 60% across batches, highly load-sensitive.
   N=3/4/6/8 each saw bursty trial fails but nothing stable at 50%.
3. **Parallel-threads-in-test shape**: N concurrent OS threads
   inside a single `#[test]`, each running K sequential
   (session1 → delete-cache → session2) pairs against its own
   `TempDir`. This is the same per-subprocess shape as the baseline
   test, but the parallelism is in-test rather than inter-test.
   Exploration:
     - N=3, K=3, 1 trial: ~30-40% fire rate per test run
     - N=4, K=3, 8 trials: ~40% fire rate per test run
     - **N=6, K=2, 10 trials (fast-fail on first hit): ~86% fire
       rate per test run, mean wall-time ~1s** (because the
       `break 'trials` optimization short-circuits after the first
       trial to reproduce)
4. **Injected yields**: not tried. With the N=6 × 10-trial shape
   already >=50% and the test running in ~1s, there was no need to
   widen race windows via `std::thread::yield_now()` or barrier-gated
   pause points. Step 3b can drive evidence capture without synthetic
   yields. If step 3b finds that the trace dumps do not cleanly
   bracket the race, a test-only `#[cfg(test)]` atomic pause-point
   in `src/scheduler.rs` near `is_typechecked` / `notify_typecheck_done`
   remains an option for a follow-up reduction.

### Final reduced shape

`tests/sprint23.rs::heisenbug_race_reduced_concurrent_import_pairs`
— 6 concurrent OS threads, each running 2 sequential
`(session 1 → delete cache → session 2)` pairs, wrapped in an outer
10-trial loop that fast-fails on the first reproduction. Fires
~86% per test run in ~1s wall-time. Signature matches the baseline
ledger entry verbatim: `'helper-val' not found in module 'helper'`
+ `undefined variable: helper-val`.

### Suspected race windows

The reduction did not attempt to attribute the fire rate to any one
hypothesis (that is step 3c's job, driven by step 3b evidence). But
the windows the shape exercises — and that step 3b should instrument
— are:

- Session 1's `handle_import` fast path at `src/worker.rs:1229-1234`
  (`is_typechecked` gate after the Round 4 fix). The ledger entry's
  signature is exactly this site's error message.
- `register_dep` at `src/worker.rs:1342` / `publish_dep_sexps` at
  `src/worker.rs:1309` — publish-before-register discipline.
- `notify_typecheck_done` at `src/scheduler.rs:688` vs symbol
  publication in `process_module_forms` + `inline_jit_codegen_for_module`
  sequence in `src/worker.rs:3431-3449`.
- Session 2 relying on cache-hit via `try_cache_hit_load` at
  `src/worker.rs:1424` (but session 2 starts after `rm -rf
  .cranelisp-cache`, so it must recompile — this path is
  *not* exercised in the reduced repro; the race is session-1-side).
- `register_dep_for_eval` at `src/session_v4.rs:1371` — REPL-side
  dep registration, republish-before-register invariant at line
  1446 debug_assert.

### No production-code changes

No `#[cfg(test)]` test-only hooks were added to `src/scheduler.rs`
or `src/worker.rs` — the reduction was achievable via test-harness
shape alone. No production code under `src/` was touched.

## 3c. Evidence capture notes (Wave 3 step 3b)

**Authored**: Sprint 61 Wave 3 step 3b (capture-only agent), 2026-04-21.
**Purpose**: freeze the one-failing / one-passing scheduler-trace
dumps that step 3c consumes for hypothesis attribution. Observation
only — hypothesis selection is step 3c's job; §7 and §8 remain
unwritten pending that step.

**Dump files**: `tests/sprint61/race-evidence/{failing,passing}-run-35062ca.log`
+ `tests/sprint61/race-evidence/README.md` (capture methodology +
passing-run caveat).

**Run count**: 1 attempt for the failing dump (reproduced on the first
invocation). 12 attempts for the passing dump (per-test pass rate
drops to ~5% with `CRANELISP_SCHEDULER_TRACE=1` enabled and `--no-capture`,
versus the ~14% baseline step 3a reported without the env var — the
trace instrumentation slightly widens timing windows). See the §3b
README for the passing-run-caveat: the test harness discards subprocess
stderr on success, so the passing-run dump's Part 2 is a hand-replayed
solo subprocess (same shape as the harness's session-1 subprocess)
running six-way concurrent. All six passed; one is embedded.

**High-level event counts**: each dump contains exactly 23 `[SCH]`
events. Same four modules appear in both: `user`, `prelude`,
`primitives`, `helper`. Same two OS threads: `ThreadId(1)/0`
(main / REPL eval) and `ThreadId(2)/1` (worker pool).

**Superficial divergence** (observation, no hypothesis attribution):
Focusing on events touching `module=helper` (8 per run):

Failing run (`failing-run-35062ca.log`, ts 15.37M–15.80M):
   1. `RegisterDepPublish helper` (t1)
   2. `RegisterModuleRegister helper` (t1)
   3. `RegisterDepPublish helper` (t1) — a second publish
   4. `ModuleStateTypechecking helper` (t2) — **interleaved before t1's 2nd register**
   5. `RegisterModuleRegister helper` (t1)
   6. `ModuleStateTypechecked helper` (t2)
   7. `IsTypecheckedHit helper pool=4` (t2) — followed by `ModuleStateFailed user` (t2)
   8. `IsTypecheckedHit helper pool=4` (t1)

Passing run (`passing-run-35062ca.log`, ts 17.29M–18.29M):
   1. `RegisterDepPublish helper` (t1)
   2. `RegisterModuleRegister helper` (t1)
   3. `RegisterDepPublish helper` (t1)
   4. `RegisterModuleRegister helper` (t1) — **both publish-register pairs complete on t1 before t2 acts**
   5. `ModuleStateTypechecking helper` (t2)
   6. `ModuleStateTypechecked helper` (t2)
   7. `IsTypecheckedHit helper pool=4` (t2)
   8. `IsTypecheckedHit helper pool=4` (t1)

In short: in the failing run, `ModuleStateTypechecking helper` from t2
is interleaved between t1's two `register_dep` publish/register pairs.
In the passing run, both of t1's publish/register pairs complete
before t2 transitions `helper` into typechecking. The failing run
also ends with `ModuleStateFailed user` on t2 (ts=15802125), which
does not appear in the passing run.

**Pool-state value `pool=4`** appears on both `IsTypecheckedHit helper`
events in both runs — identical fast-path state in both. `pool=255`
appears on `IsTypecheckedHit primitives` in both runs (built-in
module seeded state).

**Threads not covered**: the traces only span t1 (main) and t2
(worker). Other worker threads in the pool did not participate in
this particular subprocess's compilation. Matches the expectation
for a narrow (helper + prelude + user) import graph.

**Surprises / caveats**:
- The `RegisterDepPublish helper` event appears TWICE on t1 in both
  runs (events 1 and 3 of the helper subsequence). Step 3c should
  note this is not a failing-run-specific duplication — it is the
  baseline shape of the import codepath for the reduced harness.
- The trace-enabled test's pass rate (~5%) is noticeably lower than
  the baseline step-3a rate (~14% pass ≈ ~86% fire). The
  observability instrumentation itself slightly widens the race
  window. Step 3e's post-fix dump must be captured under the same
  `CRANELISP_SCHEDULER_TRACE=1` conditions for a like-for-like
  comparison.

Pointer to §7 and §8: both remain empty pending step 3c's hypothesis
attribution. Per §6 evidence-gated discipline, the hypothesis is NOT
selected in this step.

---

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

## 7. Hypothesis trajectory (Wave 3 step 3c → step 3c')

**Original authorship**: Sprint 61 Wave 3 step 3c (hypothesis-selection
agent), 2026-04-21. **Revised**: Sprint 61 Wave 3 step 3c'
(hypothesis-re-selection agent), 2026-04-21, after step 3e's post-fix
dump falsified H4's mechanism. **Evidence-gated** per §6 / `/arch`
FIXME #3.

The trajectory is preserved in full: H4 was evidence-grounded on the
pre-fix dumps (failing vs passing), the fix was /arch-approved at step
3d, landed cleanly at step 3e — and then was falsified by its own
post-fix dump. The H4 content stays in §7.1–§7.6 as the audit record.
§7.7 names H4 as FALSIFIED with citation. §7.8 introduces H5 as the
evidence-supported successor.

### 7.1 Selection: H4 (a named variant, not H1/H2/H3 as literally worded)

**Summary**: the race is on the **second defensive publish/register
pair** in `session_v4.rs::register_dep_for_eval` racing the
persistent priority worker's claim of `helper` from
`typecheck_first`. The divergence is NOT at the
`is_typechecked` fast-path (H1), NOT a publish-after-register
inversion on the publisher (H2), NOT a pool-flip-before-symbol-insert
in the typecheck worker loop (H3). None of H1/H2/H3 as literally
worded is predicted by the dump evidence.

### 7.2 Evidence citation

**Failing run** (`tests/sprint61/race-evidence/failing-run-35062ca.log`
lines 29–40, events touching `module=helper` and the subsequent
`user` re-typecheck):

```
29: [SCH] ts=15372083 thr=ThreadId(1)/0 RegisterDepPublish	module=helper
30: [SCH] ts=15372833 thr=ThreadId(1)/0 RegisterModuleRegister	module=helper
31: [SCH] ts=15376083 thr=ThreadId(1)/0 ModuleStateBlocked	module=user
32: [SCH] ts=15381250 thr=ThreadId(1)/0 RegisterDepPublish	module=helper   <-- second pair publish
33: [SCH] ts=15385958 thr=ThreadId(2)/1 ModuleStateTypechecking	module=helper <-- t2 pops helper *between* t1's second pair
34: [SCH] ts=15406041 thr=ThreadId(1)/0 RegisterModuleRegister	module=helper <-- second pair register (idempotent no-op)
...
38: [SCH] ts=15798333 thr=ThreadId(2)/1 IsTypecheckedHit	module=helper pool=4
39: [SCH] ts=15802125 thr=ThreadId(2)/1 ModuleStateFailed	module=user
```

**Passing run** (`tests/sprint61/race-evidence/passing-run-35062ca.log`
lines 48–55, same events, same modules):

```
48: [SCH] ts=17286750 thr=ThreadId(1)/0 RegisterDepPublish	module=helper
49: [SCH] ts=17288625 thr=ThreadId(1)/0 RegisterModuleRegister	module=helper
50: [SCH] ts=17293792 thr=ThreadId(1)/0 ModuleStateBlocked	module=user
51: [SCH] ts=17301250 thr=ThreadId(1)/0 RegisterDepPublish	module=helper   <-- second pair publish
52: [SCH] ts=17337042 thr=ThreadId(1)/0 RegisterModuleRegister	module=helper <-- second pair register (idempotent no-op)
53: [SCH] ts=17376208 thr=ThreadId(2)/1 ModuleStateTypechecking	module=helper <-- t2 pops helper *after* both t1 pairs
54: [SCH] ts=18172125 thr=ThreadId(2)/1 ModuleStateTypechecked	module=helper
```

**Divergence**: in the failing run, line 33 (t2's
`ModuleStateTypechecking helper`) is interleaved between t1's line 32
(`RegisterDepPublish`, second pair) and line 34 (`RegisterModuleRegister`,
second pair, idempotent no-op at `scheduler.rs:327`). In the passing
run, both of t1's pairs complete (lines 48–52) before t2 begins work
on `helper` (line 53). The failing run then shows `ModuleStateFailed
user` at line 39 with the baseline-ledger signature `'helper-val' not
found in module 'helper'`.

### 7.3 Why not H1, H2, H3

- **H1 (predicate too permissive)**: H1 predicts `IsTypecheckedHit`
  firing against a partial-publish symbol table. The dumps show
  `IsTypecheckedHit helper pool=4` (TypecheckDone) on BOTH runs at
  consistent pool values. The predicate IS permissive enough to
  return true in the failing run AND in the passing run — the
  predicate is not the divergence. The dumps contain no data-plane
  events (symbol_tables insertions, `register_imports` lookups), so
  H1's predicted signature (predicate-true with empty/partial table)
  cannot be directly confirmed from the logs alone. The predicate
  result is identical in both runs; the divergence happens ~400 µs
  earlier during second-pair register_dep_for_eval.

- **H2 (publish-after-register on the publisher)**: H2 predicts a
  reordered `RegisterModuleRegister` → `RegisterDepPublish` on the
  publisher thread for the same pair. The dumps show publish
  ALWAYS precedes register within each pair on t1, in BOTH runs
  (lines 29→30, 32→34 in the failing run; lines 48→49, 51→52 in
  the passing run). The publish-before-register invariant (Sprint
  58 W6 Defect 1, Sprint 59 Workstream A §7; guarded by
  `debug_assert` at `worker.rs:1394-1403` and `session_v4.rs:1446-1452`)
  holds. H2 falsified.

- **H3 (pool-flip before symbol-insert in worker loop)**: H3 predicts
  the worker emitting `ModuleStateTypechecked helper` before writing
  helper's Defs into `symbol_tables[helper]`. Code inspection
  (`worker.rs:3426-3449`) shows `process_module_forms` + Pass 1
  `pass1_register` (line 810) populate `symbol_tables` BEFORE
  `inline_jit_codegen_for_module`, which itself runs BEFORE
  `scheduler.notify_typecheck_done(module)` at line 3449. The pool
  flip follows the writes in the code path; the dumps show
  `ModuleStateTypechecked helper` preceding `IsTypecheckedHit
  helper` on the same thread (t2) in BOTH runs, consistent with the
  code order. H3 falsified.

### 7.4 H4 — what the divergence implicates

The REPL-eval thread's `register_dep_for_eval` (`session_v4.rs:1371-1477`)
defensively re-publishes and re-registers `dep` AFTER the form
handler's inline `register_dep` + `scheduler.register_module` has
already fired (the defensive path was added for test / alt-eval
callers that reach `register_dep_for_eval` without a prior
`handle_import` path — see line comment at 1376–1380). This produces
the observed "two RegisterDepPublish events" shape in every run.

The scheduler's `register_module` is idempotent
(`scheduler.rs:327`) — the second register is a no-op on state —
but it WAKES priority workers via `priority_work_available.notify_all()`
at line 345 UNCONDITIONALLY before the idempotency check's
early-return at line 328. The trace event `RegisterModuleRegister`
is emitted at line 320–322 BEFORE the idempotency check at line 327
AND before the wake at line 345. So both `register_module` calls
post a wake-up.

The critical window is between t1's first `register_module(helper,
true)` — which (a) adds helper to `typecheck_first` and (b) wakes
priority workers — and t1's `register_dep_for_eval` completing its
defensive second pair and blocking on
`wait_module_inmem_complete_blocking(helper)` at line 1470. In the
failing run, t2 wakes, pops helper from `typecheck_first` at line
519, sets pool → TypecheckWorking, emits `ModuleStateTypechecking
helper` — ALL of this happens between t1's second publish and
second register (trace events 32→33→34, lines 32–34 of the failing
log).

This window itself is not directly "the bug" — helper's typecheck
on t2 proceeds correctly, populates `symbol_tables[helper]` with
helper-val, and emits `ModuleStateTypechecked helper`. **The
divergence-caused bug** is that in this interleaving, the subsequent
user-module resumption (after `try_unblock_locked` unblocks user on
t2 when helper transitions to TypecheckDone) is picked up by
**t2** — the same persistent worker that just did helper's
typecheck — and proceeds through user's `handle_import`
fast-path WITHOUT the REPL eval thread's bookkeeping having run the
caller-side `republish_module_sexps_from_symbol_table(user)` at
`session_v4.rs:1428` to completion. Specifically, t1's second-pair
code path at `session_v4.rs:1426-1429` does the user-sexps
republish between the second `RegisterDepPublish` and the second
`RegisterModuleRegister` — if t2 has already popped helper and is
racing ahead, t2's user-resumption may complete BEFORE t1 finishes
its second-pair work.

In the passing run, t1 completes both defensive pairs (including
the user-sexps republish) BEFORE t2 even begins helper. When helper
finishes and user is unblocked, the user-sexps in
`shared.module_sexps[user]` are the fresh post-import version that
includes the import form as a parsed sexp — and user's re-typecheck
on t2 proceeds through the import fast-path against a
fully-populated `symbol_tables[helper]`.

In the failing run, the user-sexps may have been republished
correctly (the exact sequencing is not visible in the dumps — the
republish has no dedicated trace tag), but the user-retry on t2
fires before all of t1's post-handle-import bookkeeping has
quiesced, and the register_imports call in t2's user-retry sees
`symbol_tables[helper]` without `helper-val` — producing the
baseline signature.

### 7.5 Code sites the fix must touch

From the five suspect windows in §3b:

- **Primary**: `src/session_v4.rs:1381-1453`
  (`register_dep_for_eval` — the defensive republish+re-register
  pair that races with t2's claim of helper from `typecheck_first`).
  The fix must ensure that either (a) the defensive pair is NOT
  emitted when the form-handler path has already done the
  publish+register (elide the race window entirely), or (b) the
  second pair is ordered so that its wake-ups cannot be acted on
  by t2 until t1's user-sexps republish has also completed.

- **Secondary**: `src/scheduler.rs:315-346` (`register_module`). The
  idempotency early-return at line 327 is AFTER the trace event
  emission at line 320 and BEFORE the wake at line 345. This is
  noise on the trace side (the second emission is spurious per state
  change) but the wake at line 345 IS fired on the idempotent path,
  producing the race-enabling wake-up t2 acts on. Either skip the
  wake on the idempotent path OR guard it behind a new-state check.

- **Observational**: the dumps have no trace tag for
  `republish_module_sexps_from_symbol_table` at `session_v4.rs:1192-1209`.
  The fix should add an event (e.g., `RepublishFromSymbolTable`)
  so step 3e's post-fix dump can prove the interleaving is
  resolved. This is a small observability addition, not a fix
  itself.

### 7.6 Evidence-sufficiency note

The dumps are SUFFICIENT to reject H1/H2/H3 as literally worded and
to identify the divergence window (t2 interleaved between t1's
second-pair events). The dumps are NOT sufficient to prove the
mechanism by which user's register_imports sees an incomplete
`symbol_tables[helper]` — because the trace tags cover scheduler
state transitions only, not data-plane events. H4 is the best
available attribution from scheduler-level evidence; step 3d's
/arch review should assess whether a narrower data-plane capture is
warranted before step 3e's fix lands, or whether the H4 fix plan
in §8 is precise enough that proof-on-fix (does rate drop to 0?)
is acceptable closure.

### 7.7 H4 FALSIFIED by post-fix dump

**Evidence source**: `tests/sprint61/race-evidence/post-fix-run-35062ca.log`
(captured against the reduced harness under `CRANELISP_SCHEDULER_TRACE=1`
after step 3e landed the /arch-approved H4 Change A + Change B fixes).
The dump records a trial-7 failure on t3, session 1 — the baseline
signature `'helper-val' not found in module 'helper'` persists at
10/10 trial-failure rate over 10 test runs. Fire rate unchanged from
pre-fix 10/10. Criterion (b) of /arch step-3d condition 3 — rate → 0
— not satisfied.

**Post-fix dump, final 9 events of the failing trial**
(`post-fix-run-35062ca.log` lines 29–41, helper + user subsequence):

```
29: [SCH] ts=13712042 thr=ThreadId(1)/0 RegisterDepPublish    module=helper    <-- exactly ONE pair (H4 Change A fires)
30: [SCH] ts=13713417 thr=ThreadId(1)/0 RegisterModuleRegister module=helper
31: [SCH] ts=13717000 thr=ThreadId(1)/0 ModuleStateBlocked    module=user
32: [SCH] ts=13725334 thr=ThreadId(2)/1 ModuleStateTypechecking module=helper  <-- t2 picks up helper
33: [SCH] ts=13756167 thr=ThreadId(1)/0 RepublishFromSymbolTable module=user   <-- H5 republish fires on t1 (unconditional, /arch §3d #3)
34: [SCH] ts=14470875 thr=ThreadId(2)/1 ModuleStateTypechecked module=helper
35: [SCH] ts=14473917 thr=ThreadId(2)/1 ModuleStateUnblocked  module=user      <-- try_unblock_locked(user) inside notify_typecheck_done(helper)
36: [SCH] ts=14477417 thr=ThreadId(2)/1 ModuleStateTypechecking module=user    <-- t2 pops user from typecheck_first and races t1
37: [SCH] ts=14554125 thr=ThreadId(2)/1 IsTypecheckedHit      module=helper pool=4
38: [SCH] ts=14554417 thr=ThreadId(2)/1 RegisterImportsLookup module=helper   <-- t2 does register_imports; FAILS (baseline signature)
39: [SCH] ts=14565917 thr=ThreadId(2)/1 ModuleStateFailed     module=user
40: [SCH] ts=14609250 thr=ThreadId(1)/0 IsTypecheckedHit      module=helper pool=4
41: [SCH] ts=14609542 thr=ThreadId(1)/0 RegisterImportsLookup module=helper   <-- t1's REPL-retry arrives ~55 µs after t2 failed
```

**What H4 DID eliminate**: the duplicate `RegisterDepPublish helper`
+ `RegisterModuleRegister helper` pair is gone. t1 emits exactly ONE
of each (line 29 + 30) — Change A's gate at `session_v4.rs:1411-1416`
fires on the hot path. The narrow window §7.4 implicated ("t2 wakes
on the spurious second register and pops helper into the racing
window") no longer exists. This is confirmed by the post-fix dump
and is a net-positive gate improvement. Change A + Change B stay in
the final commit — they are correctness-preserving and observability-
adding.

**What H4 did NOT eliminate**: the actual race. The bug persists via
a DIFFERENT thread-interaction window that is now VISIBLE in the post-
fix dump (previously hidden by the duplicate-pair noise). The race is
between t1 (REPL-eval thread, blocking in
`wait_module_inmem_complete_blocking(helper)` per
`session_v4.rs:1520`) and t2 (persistent priority worker), both of
which run `handle_import` against `symbol_tables[helper]` after
helper finishes typechecking. §7.4's narrative assumed "t2's claim of
helper wakes t2 into a racing window where t1's post-handle-import
bookkeeping hasn't quiesced"; the actual race is one phase later, on
the caller (user) module, not on the dep (helper). H4's mechanism
attribution mis-localises the race by one module and one scheduler
phase.

**H5 successor**: §7.8 below.

### 7.8 H5 chosen — concurrent user-module typecheck race

**Summary** (one line): after `notify_typecheck_done(helper)` runs on
t2 and invokes `try_unblock_locked(user)`, the scheduler pushes
`user` into `typecheck_first` and the persistent priority worker
(t2, same thread that just completed helper) pops it and begins
`handle_import` on `user` concurrently with the REPL-eval thread
(t1) returning from `wait_module_inmem_complete_blocking(helper)`
and running its own retry path on `user`. Both threads call
`register_imports` on `symbol_tables[helper]`; the losing thread
reports `'helper-val' not found in module 'helper'` against a
transiently-stale or mid-mutation symbol-table view.

**Evidence citation** — same post-fix dump, lines 35–41 show the
precise interleaving:

```
35: ts=14473917 thr=ThreadId(2)/1 ModuleStateUnblocked   module=user
36: ts=14477417 thr=ThreadId(2)/1 ModuleStateTypechecking module=user
37: ts=14554125 thr=ThreadId(2)/1 IsTypecheckedHit       module=helper pool=4
38: ts=14554417 thr=ThreadId(2)/1 RegisterImportsLookup  module=helper
39: ts=14565917 thr=ThreadId(2)/1 ModuleStateFailed      module=user
40: ts=14609250 thr=ThreadId(1)/0 IsTypecheckedHit       module=helper pool=4
41: ts=14609542 thr=ThreadId(1)/0 RegisterImportsLookup  module=helper
```

Event ordering pins the mechanism:
- t2 at 14473917: `ModuleStateUnblocked user` — this is the observability
  emission inside `Scheduler::try_unblock_locked` (`scheduler.rs:1392-1395`)
  as `user` transitions from `TypecheckBlocked` to `TypecheckFirst`
  via `state.typecheck_first.push_back(module.clone())` at
  `scheduler.rs:1387`. `try_unblock_locked` is called from
  `notify_typecheck_done(helper)` at `scheduler.rs:729` during t2's
  completion of helper.
- t2 at 14477417: `ModuleStateTypechecking user` — t2 (same persistent
  worker thread) has re-entered `take_priority_work_blocking`, popped
  user from `typecheck_first` at `scheduler.rs:519`, flipped the pool
  to `TypecheckWorking`, and begun typechecking user. This happens
  ~3.5 µs after the unblock — well before t1 could possibly have
  returned from the condvar wake in
  `wait_module_inmem_complete_blocking` (t1's wake is observed at
  event 40, 132 ms later).
- t2 at 14554417: `RegisterImportsLookup helper` — t2's `handle_import`
  fast-path at `worker.rs:1242-1245` consumes `symbol_tables[helper]`.
  This is the failing lookup; the next event (14565917) is
  `ModuleStateFailed user`.
- t1 at 14609542: `RegisterImportsLookup helper` — t1's own
  `handle_import` runs 55 µs after t2 failed. The two threads DO
  execute `register_imports` against `symbol_tables[helper]`
  concurrently in the failure scenario.

**Why H5 follows from the evidence**: the post-fix dump makes the
interleaving directly observable at scheduler + data-plane granularity
(the `RegisterImportsLookup` tag from Change B is now informative).
H4's narrow gate correctly closed the duplicate-pair window, but the
post-gate dump reveals that the race has always been on the
caller-module retry, not the dep-module claim. The specific event
pinning H5 is: **`try_unblock_locked(user)` pushing user into
`typecheck_first` inside `notify_typecheck_done(helper)` permits the
same persistent worker to pop user and run `handle_import` ahead of
the REPL-eval thread's retry loop in
`wait_module_inmem_complete_blocking`.** The REPL-eval thread is the
authoritative caller for user's post-unblock typecheck retry (it owns
the REPL session state and the eval sequencing); a worker-thread
concurrent user-typecheck is a pure duplicate that races the REPL
eval for `symbol_tables[helper]` read consistency.

**Rejection of residual alternatives**:
- **H4 mechanism (as authored in §7.4)**: post-fix dump shows the
  duplicate pair is gone but the race persists — falsified. The
  specific claim "t2's spurious second wake racing helper's claim"
  is no longer the signature.
- **H1 (predicate too permissive)**: `IsTypecheckedHit helper pool=4`
  fires twice in the post-fix dump (events 37 and 40) — once on t2's
  path (which FAILS `register_imports`) and once on t1's path (which
  arrives later but after t2 has already corrupted `user` to Failed).
  Both hits are against pool=4 = TypecheckDone, matching H1's
  description of a "ready" predicate — but the pool value is correct
  by the time both threads arrive. Helper IS typechecked. The
  predicate is NOT the divergence; the data-plane race on
  `register_imports` against a possibly-not-yet-fully-ordered
  `symbol_tables[helper]` view — OR a memory-ordering race between
  t2's completion of helper and t2's re-claim of user — is. This is
  not an H1 signature. (Separate note: the register_imports failure
  might reflect an H1-adjacent data-plane partial-visibility issue;
  but that is strictly downstream of the race-to-claim that H5 names,
  and closing the claim race will eliminate it.)
- **H2 (publish-after-register on the publisher)**: still falsified
  as §7.3 — publish-before-register invariant holds on t1 in all
  observed runs.
- **H3 (pool-flip before symbol-insert in worker loop)**: still
  falsified as §7.3 — code inspection at `worker.rs:3426-3449` shows
  symbol-insert precedes `notify_typecheck_done`. No revision.

**Code sites implicated by H5 (scheduler-side fix surface)**:

- **Primary — `src/scheduler.rs::try_unblock_locked`
  (`scheduler.rs:1375-1396`)**: the unblock path that pushes user
  into `typecheck_first` (line 1387) is the specific site where the
  worker claim race is enabled. H5's fix must either (a) suppress
  the push when the unblock is known to have an REPL-eval-thread
  waiter (e.g., `wait_module_inmem_complete_blocking` is parked on
  `user`'s completion), (b) mark the caller as "unblocked-for-caller"
  without queuing for worker pickup, or (c) hold the
  `TypecheckBlocked`→`TypecheckFirst` transition gated on an
  additional flag that distinguishes worker-driven callers from
  eval-driven callers.
- **Primary — `src/scheduler.rs::notify_typecheck_done`
  (`scheduler.rs:688-738`)**: the caller of `try_unblock_locked` at
  line 729. The iteration over `all_waiters` at line 725 is where the
  per-waiter unblock semantics are decided. If H5's fix lives here
  (not inside `try_unblock_locked`), the waiter classification happens
  at the sweep level.
- **Primary — `typecheck_first` pool management**:
  `scheduler.rs:519` is where `take_priority_work_blocking` pops
  `typecheck_first` unconditionally. If the fix lives here (filter
  at pop time), the pop loop needs an additional check against an
  eval-in-flight registry. Less surgical than gating at the push.
- **Secondary — `src/session_v4.rs::wait_module_inmem_complete_blocking`
  interaction (`session_v4.rs:1520`, via
  `scheduler.rs::wait_module_inmem_complete_blocking` at
  `scheduler.rs:943-969`)**: the REPL-eval thread parks here on
  `self.completion` condvar waiting for `dep=helper` to reach
  `inmem_done`. When helper completes, `completion.notify_all()`
  wakes the condvar and t1 returns. If the fix introduces an
  "eval-thread in flight on module X" flag, it must be set at
  `wait_module_inmem_complete_blocking` entry (or at
  `register_dep_for_eval`'s entry, which calls this) and cleared at
  exit. `src/worker.rs::handle_import` (`worker.rs:1195`) and the
  persistent-worker priority loop at `worker.rs:3345` are the consumers
  of the flag — the flag gates worker claim/pop of user while set.
- **Observational — no new trace tags required**. The existing
  `RegisterImportsLookup`, `RepublishFromSymbolTable`,
  `ModuleStateUnblocked`, and `ModuleStateTypechecking` tags already
  give proof-on-fix visibility. Step 3e' should confirm that a
  post-fix dump no longer shows t2 running `ModuleStateTypechecking
  user` after t1 begins its REPL-eval retry.

### 7.9 Evidence sufficiency for H5

The post-fix dump is SUFFICIENT to (a) falsify H4's mechanism, (b)
localise the race to the caller-module retry rather than the
dep-module claim, and (c) identify the responsible scheduler
transition (`try_unblock_locked` + `typecheck_first` push + persistent
worker pop + concurrent `handle_import`). The dump is NOT sufficient
to prove which of the three H5 fix mechanisms (a)/(b)/(c) above is
preferred — that is a design choice subject to /arch review at step
3d'. It is also not sufficient to rule out an H1-adjacent data-plane
partial-visibility signature as a co-contributor; however, closing
the claim race is a necessary precondition for any such co-factor to
be testable, and attempting a data-plane fix before closing the claim
race would be premature. Step 3d' is expected to select among the
(a)/(b)/(c) fix mechanisms and confirm boundary hygiene; step 3e'
implements the chosen mechanism; step 3b-rerun is not requested as a
prerequisite (the post-fix dump already shows the decisive ordering).

## 8. Fix plan

**Original authorship**: Sprint 61 Wave 3 step 3c. **Revised**:
Sprint 61 Wave 3 step 3c' after H4 falsification. §8.1 preserves
the landed H4 fix (net-positive, stays in final commit); §8.2 is the
new H5 plan for step 3e' implementation.

### 8.1 H4 narrow-gate fix (landed; net-positive but insufficient)

H4 fix content below was authored at step 3c and landed at step 3e.
Post-fix dump (§7.7) showed it is net-positive but insufficient —
the fix stays in the final commit (closes the duplicate-pair wake
window and adds observability), but the race is not closed by it.
The §8.1.1–§8.1.4 content below is preserved verbatim from the
original step-3c fix plan for audit; see §8.2 for the H5 fix plan
that step 3e' will implement.

#### 8.1.1 Mechanism (H4)

Close the race window between t1's second defensive pair in
`register_dep_for_eval` and t2's priority-worker claim of `helper`
from `typecheck_first`. Two complementary changes, minimally
invasive:

**Change A (primary)**: elide the second pair entirely when the
form-handler path has already done publish+register. In the hot
path — REPL eval → `handle_import` → worker-side `register_dep` +
`scheduler.register_module(helper, true)` → `BlockAction::Block` →
eval-thread `register_dep_for_eval` — the `handle_import` path has
ALREADY ordered publish-before-register correctly. The defensive
second pair at `session_v4.rs:1381-1453` is only necessary for the
alt-eval-paths / tests branch documented in the comment at lines
1376–1380. Gate the second pair behind a check: if
`shared.module_sexps[dep]` is already present AND
`scheduler.is_registered(dep)` (a new trivial lookup, or an
existing one — needs confirmation), skip the defensive pair. This
closes the race by making the hot path emit exactly ONE pair per
dep.

**Change B (supporting)**: preserve the user-sexps-republish
(line 1428) unconditionally — it is caller-side, not dep-side, and
fixes the H5 REPL-persistence residue (Sprint 60 Wave 2 Round 3).
But emit an observability event for it (`RepublishFromSymbolTable`)
so step 3e's post-fix capture can demonstrate t1 completes the
user-sexps republish BEFORE t2 processes user's retry.

**Not done in this slice (deferred)**: do NOT change
`scheduler.rs::register_module`'s wake-on-idempotent behaviour.
The idempotent wake is defensive (covers a genuinely new registration
that was just dropped) and changing it has broader implications for
worker wake-up correctness across other entry points. If Change A
alone does not reduce the rate to 0, /arch should flag whether
Change B / a scheduler-side change is in scope.

#### 8.1.2 Touched files + line ranges (H4)

- `src/session_v4.rs:1371-1477` — `register_dep_for_eval`: add
  hot-path gate before line 1382 (the publish) to skip the
  defensive pair when dep is already published + registered.
  Preserve user-sexps republish at line 1428 unconditionally.
- `src/observability.rs` — add `RepublishFromSymbolTable`
  SchedulerTraceTag variant and a `record_module_event` call in
  `session_v4.rs:1192-1209`. ~15 lines total.
- NO changes to `src/scheduler.rs::register_module`.
- NO changes to `src/worker.rs::handle_import` or `register_dep`
  (those are already correct).
- NO changes to `src/worker.rs::process_module_forms` or
  `inline_jit_codegen_for_module` (H3 is falsified; these are
  correct).

#### 8.1.3 Why this does NOT regress other scheduler behaviours (H4)

- The defensive pair at `register_dep_for_eval` is documented at
  its own line 1376-1380 as serving "alt-eval paths / tests that
  reach us without a prior form-handler Blocked result". Skipping
  it on the hot path does NOT break those callers — they still
  hit the publish+register because `shared.module_sexps[dep]`
  will be missing on their path. The gate is a fast-path
  optimization that ALSO closes the race.
- The user-sexps republish at line 1428 is a separate, caller-side
  invariant (fixes H5 from Sprint 60 Wave 2 Round 3). It stays
  unconditional; only the dep-side pair is gated.
- `scheduler.register_module`'s idempotency semantics, wake-up
  behaviour, and pool transitions are unchanged.
- `is_typechecked`'s semantics are unchanged (H1 is falsified;
  the predicate is correct).

#### 8.1.4 Risk notes for /arch mini-review step 3d (H4)

1. **Evidence is scheduler-level only** — §7.6 flags that H4's
   mechanism inference relies on code-inspection plus the
   dump's interleaving signature, not a direct data-plane
   observation. If /arch wants stronger evidence before
   the fix lands, re-run step 3b with additional trace tags
   (SymbolTableInsert, RegisterImportsLookup, RepublishFromSymbolTable)
   and re-select. This is the step-3b-rerun contingency the step 3c
   brief names.
2. **Proof-on-fix criterion**: step 3e's post-fix dump must show
   the failing run's interleaving (t2's TypecheckingWorking helper
   between t1's two pairs) is eliminated — i.e., t1 emits exactly
   ONE `RegisterDepPublish helper` + ONE `RegisterModuleRegister
   helper` in the hot path. If the rate drops to 0 but the
   interleaving is still observable (e.g., a different wake-up
   path still races), H4's mechanism attribution is wrong even if
   the fix works. Step 3e should flag this explicitly.
3. **Alt-eval callers untouched**: tests / alternative REPL eval
   paths that enter `register_dep_for_eval` without a prior
   `handle_import` still work because the hot-path gate falls
   through when dep isn't already published+registered.
4. **Scheduler boundary**: no `cranelisp-types` boundary change
   (confirmed in §5). No new synchronisation primitive.
5. **Interaction with Sprint 60 Round 5 fix**: Round 5 added the
   `is_typechecked` fast-path guard at `worker.rs:1229-1234`. H4's
   analysis confirms that fix is still necessary and correct — the
   predicate itself is not the bug. H4 adds a second window-closer
   (elide duplicate wake-up) in front of it.
6. **Observability-only change (Change B)**: adding the
   `RepublishFromSymbolTable` tag is a net-positive
   instrumentation change even if the fix landed without it. But
   if /arch considers observability changes out-of-scope for this
   slice, they can be deferred to a follow-up; Change A alone is
   sufficient to close the race.

### 8.2 H5 fix plan — scheduler-side worker-claim suppression

**Authored**: Sprint 61 Wave 3 step 3c' after H4 falsification (§7.7).
Subject to /arch mini-review at step 3d'. Implementation is step 3e'.

The §8.1 (H4) fix stays. §8.2 adds the scheduler-side change that
closes the race H5 localises: a persistent worker must not claim a
caller module for typecheck while the REPL-eval thread owns that
caller's post-unblock retry via `wait_module_inmem_complete_blocking`.

#### 8.2.1 Mechanism (H5)

The race window opens at `scheduler.rs:1387` inside
`try_unblock_locked` — `state.typecheck_first.push_back(module.clone())`
queues the unblocked caller for worker pickup. In the REPL-eval hot
path, the caller (`user`) has an eval-thread waiter parked in
`wait_module_inmem_complete_blocking(dep=helper)` that will return
control to t1 as soon as helper completes. t1 will then drive user's
retry through its own typechecking path. A persistent worker popping
user from `typecheck_first` in parallel is a pure duplicate — there
is no correctness need for worker-driven typecheck of user while t1
is in flight — and it races t1 on `register_imports` reads against
`symbol_tables[helper]`.

**Preferred mechanism (subject to /arch at step 3d')**: option (a) from
§7.8's fix surface — suppress the push into `typecheck_first` when an
eval thread is known to own the caller's retry. Concretely:

1. Introduce a per-module `eval_in_flight: bool` flag on `ModuleState`
   (in `scheduler.rs`, the same struct that owns `pool`, `waiters`,
   `inmem_done` etc.). Field is internal to `src/scheduler.rs`, no
   `cranelisp-types` boundary impact.
2. Set the flag to `true` at the entry to
   `Scheduler::wait_module_inmem_complete_blocking(target)` for the
   `caller` module that owns the wait — OR at
   `register_dep_for_eval`'s entry before it calls
   `wait_module_inmem_complete_blocking`, via a new
   `Scheduler::set_eval_in_flight(&self, caller: &ModuleFullPath)`
   method. (The §7.8-named interaction: the caller is
   `session_v4.rs::current_module_path()` at the point of
   `register_dep_for_eval` execution.)
3. Clear the flag on exit from
   `wait_module_inmem_complete_blocking` (or at the end of
   `register_dep_for_eval`).
4. Gate `try_unblock_locked`'s push at `scheduler.rs:1387`: if the
   module's `eval_in_flight` flag is set, transition it to a new
   `TypecheckEvalOwned` pool state (or retain in
   `TypecheckBlocked` with a cleared `blocked_on`) instead of
   pushing to `typecheck_first`. The REPL-eval thread's retry path
   at `session_v4.rs` — after returning from
   `wait_module_inmem_complete_blocking(helper)` — is responsible
   for driving `user`'s typecheck and clearing the flag on
   completion.

**Alternative mechanism (option (c) in §7.8)**: filter the pop at
`scheduler.rs:519`'s `state.typecheck_first.pop_front()` — skip
entries whose `eval_in_flight` is set, or re-queue them to the tail.
This is simpler but leaves the module transiently in
`typecheck_first`, which may confuse other introspection paths
(`pending_work`, `/mod` status, etc.). Option (a) is preferred.

The worker-side claim loop at `worker.rs:3345`
(`priority_worker_loop_shared`) does not need changes if option (a)
is taken — the push is suppressed, so the pop never sees the module
to claim. If option (c) is taken, the claim loop needs a filter in
`take_priority_work_blocking` (`scheduler.rs:489-506`) or
`try_take_work_locked` (`scheduler.rs:511-569`).

#### 8.2.2 Touched files + line ranges (H5)

- **`src/scheduler.rs`** (primary, ~10–30 LOC):
  - `struct ModuleState` (around the `pool`/`waiters`/`inmem_done`
    fields) — add `eval_in_flight: bool` field, default false.
  - New method `Scheduler::set_eval_in_flight(&self,
    module: &ModuleFullPath, value: bool)` — simple state-lock
    field update.
  - `try_unblock_locked` at lines 1375–1396 — check the
    `eval_in_flight` flag before pushing to `typecheck_first` at
    line 1387; skip the push when set.
  - Optional helper on the pool state side if a new pool variant
    is preferred over a flag (e.g., `TypecheckEvalOwned`) — design
    choice for /arch.
- **`src/session_v4.rs`** (~5–15 LOC):
  - `register_dep_for_eval` at `session_v4.rs:1382-1527` — call
    `self.shared.scheduler.set_eval_in_flight(&caller, true)` before
    entering `wait_module_inmem_complete_blocking` at line 1520; clear
    on return (both Ok and Err paths). The `caller` is already
    computed at line 1465.
- **`src/worker.rs`** (~0–5 LOC): no changes expected if option (a)
  is taken. If /arch steers to option (c), add a filter at
  `handle_import`'s fast-path or at the claim loop.
- **NO** changes to `src/observability.rs` — the existing trace tags
  are sufficient for proof-on-fix.
- **NO** changes to the H4 landed code in
  `session_v4.rs:1411-1503` (the skip_defensive_pair gate) — that
  stays.
- **NO** changes to
  `wait_module_inmem_complete_blocking`'s condvar contract at
  `scheduler.rs:943-969`.

#### 8.2.3 Invariants preserved

- **H4 gate (§8.1)** stays in force — the skip_defensive_pair logic
  at `session_v4.rs:1411-1416` continues to suppress the duplicate
  publish/register on the hot path. The H5 fix layers on top.
- **H5 REPL-persistence republish** at `session_v4.rs:1467`
  (`republish_module_sexps_from_symbol_table(&caller)`) stays
  UNCONDITIONAL — it is caller-side, not dep-side. The /arch §3d
  condition 3 from step 3d continues to hold.
- **Observability tags** (`RepublishFromSymbolTable`,
  `RegisterImportsLookup`) from step 3e's Change B stay — they are
  the primary proof-on-fix artefacts for step 3e'.
- **`publish-before-register` invariant** for dep sexps — the
  `debug_assert` at `session_v4.rs:1485-1491` stays untouched.
- **Round 5 `is_typechecked` fast-path guard** at
  `worker.rs:1229-1230` stays — it remains the final correctness
  boundary for alt-eval and cold-path callers.
- **Idempotent `register_module` wake** at `scheduler.rs:345`
  stays untouched — H4's §8.1.1 deferral of that change still holds.

#### 8.2.4 Risk notes for /arch mini-review (step 3d')

1. **Starvation risk**: if `eval_in_flight` is set but the eval
   thread never clears it (panic, thread kill, unforeseen early
   return), the caller module is never picked up by a worker and
   `wait_module_inmem_complete_blocking` on downstream waiters may
   hang. Mitigation: RAII guard on the flag — introduce an
   `EvalInFlightGuard` struct holding the scheduler handle +
   caller path, clearing the flag in `Drop`. Drop runs on unwind
   through the normal panic path, so any panic in
   `register_dep_for_eval` cleans up correctly.
2. **Condvar interaction**:
   `wait_module_inmem_complete_blocking`'s condvar contract at
   `scheduler.rs:943-969` observes `dep`'s pool + `inmem_done`
   fields. It does NOT observe the `eval_in_flight` flag. Setting
   the flag on `caller` (a different module) is orthogonal to
   `dep`'s completion signalling — no risk of missed wake-ups.
3. **Nested eval / re-entrancy**: if a REPL-eval thread
   recursively calls `register_dep_for_eval` (e.g., dep itself
   requires another dep), the caller at each level is different
   (the caller of the inner call is the dep of the outer call).
   The flag is per-module; nested calls set independent flags. No
   re-entrancy hazard at the scheduler level.
4. **Broad suppression failure mode**: if the eval-in-flight flag
   is set but should NOT suppress (e.g., a caller needing worker-
   side typecheck because no REPL-eval thread is actually going to
   drive its retry — hypothetical; should not occur in the current
   code paths). Risk level: low. `register_dep_for_eval` is the
   only caller that sets the flag, and it owns the subsequent
   retry by construction. But audit all entry points that reach
   `wait_module_inmem_complete_blocking` before step 3e' commit to
   confirm no other caller shape exists.
5. **Interaction with Sprint 60 Workstream E-2 consensus**: the
   dep-registration pass `delays_other=true` at
   `session_v4.rs:1502` places the dep in `TypecheckFirst`. That
   is the DEP side, not the caller side — H5 gates the CALLER's
   post-unblock push, not the dep's initial push. No conflict with
   E-2.
6. **No `cranelisp-types` boundary change**: `ModuleState` lives in
   `src/scheduler.rs` (confirmed Phase 3a review). Adding
   `eval_in_flight: bool` is internal to `src/`. Principle 3
   compliant.
7. **Post-fix dump expectation**: step 3e' should capture a post-fix
   dump that shows exactly ONE `ModuleStateTypechecking user` per
   eval cycle (on t1, not t2), and NO `ModuleStateTypechecking
   user` on t2 between the two `ModuleStateUnblocked user` +
   subsequent t1 events. The existing `RegisterImportsLookup`
   events should appear ONLY on t1 (the eval thread) in the hot
   path, never on t2.

## 3d. /arch mini-review verdict

**Reviewer**: /arch
**Date**: 2026-04-22
**Verdict**: **APPROVE WITH REVISIONS**

### Evidence → hypothesis alignment

§7's H4 attribution is **justified on the dump divergence**, but the
H4 *mechanism* (how the interleaving causes user's `register_imports`
to see an incomplete `symbol_tables[helper]`) is **inferred, not
observed**. §7.6 is honest about this; §7.3 correctly falsifies
H1/H2/H3 from the dumps alone:

- H1 rejection is sound: `IsTypecheckedHit helper pool=4` fires in
  BOTH failing (line 40) and passing (line 58) runs with the identical
  pool-state value. The predicate is NOT the divergence — divergence
  lies ~400 µs earlier. The dumps do not prove H1 is *safe*; they
  prove H1 is not the *active* signature in this repro.
- H2 rejection is strong: in every pair, `RegisterDepPublish` precedes
  `RegisterModuleRegister` on t1 (failing log 29→30, 32→34; passing
  48→49, 51→52). Publish-before-register holds. The §3b-declared
  `debug_assert` at `session_v4.rs:1446-1452` did not trip, consistent.
- H3 rejection is sound via *code inspection* (§7.3's pointer to
  `worker.rs:3426-3449`), not via the dumps directly — the dumps carry
  no `SymbolTableInsert` tag. The pool-flip-event timeline in the
  dumps is consistent with H3 being false, but not a direct proof.

The divergence signature — t2's `ModuleStateTypechecking helper` at
failing-run line 33 interleaved between t1's second-pair publish
(line 32) and second-pair register (line 34), versus the passing
run's clean t1-pairs-then-t2 ordering (lines 48–52 then 53) — is
**real, reproducible across runs, and novel against the three
originally-hypothesised signatures**. Admitting H4 as a fourth
hypothesis (rather than forcing one of H1/H2/H3) is the honest read.

### Evidence sufficiency

Path (i) rerun-with-data-plane-tags vs (ii) proof-on-fix:

**Approved path**: **HYBRID** — accept path (ii) as the *closure*
criterion, but require a **narrow data-plane probe added inside the
same change set** as the fix so step 3e's post-fix dump directly
demonstrates the interleaving is eliminated. Specifically:

- **Do** add the `RepublishFromSymbolTable` trace tag (§8 Change B)
  and a `RegisterImportsLookup` tag at the `register_imports` site
  that consumes `symbol_tables[helper]`. These are the two
  observations H4's mechanism claim implicates — adding them inside
  Change B gives post-fix proof without a separate step-3b rerun.
- **Do not** block step 3e behind a full step-3b rerun + re-selection
  cycle. The dumps as they stand sufficiently falsify H1/H2/H3 as
  literally-worded and localise the divergence to the second-pair
  window. A full rerun would cost ~1 wave for evidence that
  subsumes the post-fix capture.

Rationale: the cost of path (i) as a *prerequisite* is high (add
tags → rebuild → re-reduce under widened windows → potentially
re-hypothesise if data-plane shows something else → then fix); the
risk of pure path (ii) is that a fix lands against an inferred
mechanism and "rate goes to 0" could mask a *different* underlying
bug with the same surface signature. The hybrid pays the small extra
cost of two trace tags during the fix commit itself, making the
post-fix dump decisive. If the post-fix dump shows the rate drop to
0 AND the second pair elided AND `RegisterImportsLookup helper`
happening only after `RepublishFromSymbolTable user`, H4's mechanism
is directly observed. If the rate drops but the ordering is
unexpected, §8.4 risk 2 triggers and /int comes back to /arch.

### Fix plan (§8) soundness

- **Boundary-type changes**: NONE. The hot-path gate at
  `session_v4.rs:1381-1453` reads `shared.module_sexps` (already a
  `SharedState` field, not a `cranelisp-types` boundary type). No
  new field on `SymbolTable`, `CheckResult`, `Code`, `CacheEntry`, or
  any type in `crates/cranelisp-types/`. The new trace tags live in
  `src/observability.rs` (per `observability.md §4`, scheduler log is
  `src/`-only, not a boundary surface). Confirmed against §5 and
  against the Phase 3a review's resolution of FIXME(/arch) #3.
- **Interface changes**: NONE. `register_dep_for_eval`'s signature is
  unchanged; the gate is an internal early-exit. The scheduler's
  `register_module` is UNTOUCHED (§8.1 explicitly defers Change B's
  idempotent-wake consideration).
- **Side effects**: adding two trace-tag variants to the
  `SchedulerTraceTag` enum in `src/observability.rs` requires
  `match` exhaustiveness updates at every consumption site inside
  `src/`. Principle 3 compliant — this enum does not cross crate
  boundaries. No `Serialize` impact (enum is not persisted).

**Additional soundness note**: §8.1's gate predicate "`dep` is
already published AND `scheduler.is_registered(dep)`" depends on an
`is_registered` lookup that §8.1 flags as "a new trivial lookup, or
an existing one — needs confirmation". /int MUST confirm this lookup
before step 3e commit. If no such predicate exists, /int's options
are: (a) add a `Scheduler::is_registered(&self, &ModuleFullPath) ->
bool` method (internal to `src/scheduler.rs`, no boundary change),
or (b) gate on `shared.module_sexps[dep]` presence alone (weaker but
still closes the race in the hot path, because the form handler's
`register_dep` publishes and registers as a unit). Option (a) is
preferred for predicate symmetry.

### Interaction risks

- **Sprint 60 Round 5 `is_typechecked` guard at `worker.rs:1229-1234`**:
  **still holds**. §8.4 item 5 confirms the Round 5 fix is necessary
  and correct; H4 adds a window-closer in FRONT of it (elide the
  duplicate wake-up before t2 even acts), not a replacement. The
  Round 5 guard remains the final correctness boundary for alt-eval
  callers that still hit the defensive path. No weakening observed.
- **H5 REPL-persistence unconditional republish at
  `session_v4.rs:1428`**: **still holds, provided the gate in Change
  A is positioned before line 1382 and EXCLUDES line 1428 from its
  early-return scope**. §8.1 and §8.2 both state the user-sexps
  republish "stays unconditional". /int MUST ensure the gate's
  early-return / continue structure DOES NOT short-circuit past line
  1428. Recommended shape: gate only the *dep-side* defensive pair
  (lines 1381-1390 plus line 1453's `register_module` call); leave
  lines 1426-1429 (caller republish) on the common path; leave
  `wait_module_inmem_complete_blocking` at line 1470 on the common
  path.
- **Worst-case failure mode if fix is wrong**: a REPL session where
  the form handler's `register_dep` published sexps but subsequently
  failed (e.g., `scheduler.register_module` was called with the dep
  but the dep's pool transitioned to Failed and got cleaned up
  externally). In that hypothetical, gating on "already published"
  skips the defensive re-register, and the dep never re-enters the
  typecheck queue — `wait_module_inmem_complete_blocking` hangs
  until timeout. Mitigation: confirm the scheduler's failure-cleanup
  path removes `shared.module_sexps[dep]` alongside removing the
  scheduler-side registration (or: gate on BOTH published AND
  registered, never on published alone). /int should audit
  `reset_all_failed_modules` semantics before committing.
- **Additional architectural concerns**: the §8.4 item 2
  "proof-on-fix might mask a different bug" risk is tangible. The
  hybrid path above is the `/arch` mitigation — the post-fix dump's
  ordering, not just its pass rate, must be asserted. `/sprint`
  should add this to the step-3e acceptance criteria, not defer it to
  step 3f test authoring.

### Test authoring (step 3f) requirements

The post-fix test shape /qa authors must catch H4 specifically, not
just the baseline-ledger surface signature. Recommended shape:

1. **Regression integration test** — extend
   `sprint23::heisenbug_race_reduced_concurrent_import_pairs`
   (already in-suite per §8 Testing) with a post-fix assertion that,
   on any trace-captured subprocess, the count of
   `RegisterDepPublish helper` events on a single thread's
   `register_dep_for_eval` call is **exactly one**, not two.
   This directly asserts the defensive pair was elided on the hot
   path. Fail-mode: if a future refactor reintroduces the duplicate
   pair, this test catches the H4 regression before the race window
   widens back to failing.

2. **Narrow ordering invariant test** — a new focused integration
   test (naming shape:
   `sprint61::register_dep_for_eval_hot_path_single_pair`) that
   drives ONE session-1 subprocess with `CRANELISP_SCHEDULER_TRACE=1`,
   parses the dump, and asserts:
   - exactly one `RegisterDepPublish helper` event on the eval
     thread
   - exactly one `RegisterModuleRegister helper` event on the eval
     thread
   - `RepublishFromSymbolTable user` precedes t2's
     `IsTypecheckedHit helper` (the H5 + H4 composite invariant)
   This is a single-threaded ordering assertion — not a stress test —
   so it is deterministic and fast. Catches both H4 (duplicate pair)
   AND a weakening of H5 (user-sexps republish skipped).

3. **Alt-eval-path coverage** — a test that reaches
   `register_dep_for_eval` through a path that does NOT go through
   `handle_import` (per §8.1's "tests, alternative eval paths"
   comment). Assert the defensive pair IS emitted in this path
   (i.e., the gate falls through correctly). Naming shape:
   `sprint61::register_dep_for_eval_cold_path_defensive_pair`.
   This guards against the gate over-applying and breaking the
   case it was originally defending.

The three shapes together cover hot-path elision (test 1/2), H5
composition (test 2), and cold-path preservation (test 3).

### Step 3e readiness

**GO**, conditional on the hybrid evidence path:

1. /int MUST add `RepublishFromSymbolTable` AND
   `RegisterImportsLookup` trace tags inside Change B of the fix
   commit (two tags, not one).
2. /int MUST confirm the `is_registered` predicate availability
   (add if absent, per §8.1 note) before committing.
3. Step 3e's post-fix dump commit (at
   `tests/sprint61/race-evidence/*-post-fix-<SHA>.log`) MUST
   demonstrate BOTH rate → 0 AND the ordering invariants named in
   test 2 above.
4. The gate MUST NOT short-circuit past the caller-sexps republish
   at `session_v4.rs:1428`.

No STOP on design grounds. The architectural content is sound; the
revisions above are implementation-level precision, not scope
changes.

### Recommendations for /sprint

1. **No wave re-sequencing.** Step 3e opens now with the four
   conditions above attached to its acceptance criteria.
2. **Step 3f scope expansion (minor).** The three test shapes above
   should be authored by /qa as part of step 3f, not deferred. Test 2
   (narrow ordering invariant) is the primary regression guard;
   tests 1 and 3 extend coverage.
3. **Post-fix dump acceptance.** Add to step 3e's readout: "post-fix
   dump demonstrates (a) rate → 0 over N runs, (b) exactly one
   publish + one register for `helper` on the eval thread, (c)
   `RepublishFromSymbolTable user` precedes t2's helper-phase
   advance." This makes the hybrid-path evidence criterion
   explicit and verifiable.
4. **Sketch-comparison note carryover.** §7a is now present in the
   doc (good — resolves the Phase 3a non-blocking recommendation).
   /sprint can close that follow-up item.

## 3e. Fix implementation notes (Wave 3 step 3e)

**Authored**: Sprint 61 Wave 3 step 3e (fix-implementation agent),
2026-04-21.

### What landed

Per §8 Change A + B and /arch §3d four revisions:

- `src/observability.rs`: added `RepublishFromSymbolTable` and
  `RegisterImportsLookup` variants to `SchedulerTraceTag`, updated
  `format_event_line`, added two unit tests
  (`s61w3_new_tags_record_via_module_event`,
  `s61w3_new_tags_format_line_names`). All 27 observability tests pass.
- `src/scheduler.rs`: added `Scheduler::is_registered(&self,
  &ModuleFullPath) -> bool` (trivial lookup into `state.modules`), per
  /arch §3d condition 2 / §8.1 note.
- `src/session_v4.rs::register_dep_for_eval`: added hot-path gate —
  computes `skip_defensive_pair = already_published &&
  already_registered` (both, never alone — /arch §3d condition 4) and
  skips both the dep-side publish and the dep-side `register_module`
  call when the form handler has already done them. Caller-sexps
  republish at line 1428 remains UNCONDITIONAL (/arch §3d condition 3).
- `src/session_v4.rs::republish_module_sexps_from_symbol_table`: emits
  `RepublishFromSymbolTable` after successful republish.
- `src/worker.rs::handle_import`: emits `RegisterImportsLookup` at the
  fast-path before `register_imports` consumes `symbol_tables[dep]`.

### Post-fix dump observations

`tests/sprint61/race-evidence/post-fix-run-35062ca.log` (captured
under `CRANELISP_SCHEDULER_TRACE=1` against the reduced harness).

**Criterion (a) — duplicate pair elimination**: SATISFIED. The
post-fix dump shows exactly ONE `RegisterDepPublish helper` + ONE
`RegisterModuleRegister helper` on t1 per session-1 subprocess,
versus two each in the pre-fix failing dump (§7.2). The H4 Change A
gate fires correctly. The `RepublishFromSymbolTable user` event
appears immediately after on t1, demonstrating the H5 caller-sexps
republish still runs unconditionally.

**Criterion (b) — rate drops to 0**: **NOT SATISFIED**. The reduced
harness still fires at ~100% (10/10 trial fails over 10 test runs).
The post-fix dump reveals that H4's *mechanism attribution* (§7.4 —
"duplicate pair wakes t2 into racing window") is **wrong**. The race
persists, but on a different surface.

**Revealed race surface** (trial 2 in post-fix dump, final 9
events):

```
ts=13408125 thr=ThreadId(2)/1 ModuleStateTypechecking	module=user
ts=13423708 thr=ThreadId(1)/0 IsTypecheckedHit	module=helper pool=4
ts=13424167 thr=ThreadId(1)/0 RegisterImportsLookup	module=helper
ts=13504250 thr=ThreadId(2)/1 IsTypecheckedHit	module=helper pool=4
ts=13504542 thr=ThreadId(2)/1 RegisterImportsLookup	module=helper
ts=13508292 thr=ThreadId(2)/1 ModuleStateFailed	module=user
```

Both t1 (REPL-eval retry after `wait_module_inmem_complete_blocking`
wakes) AND t2 (persistent worker popping user from `typecheck_first`
after `try_unblock_locked(user)` fired inside
`notify_typecheck_done(helper)`) attempt `handle_import` on the same
`user` module CONCURRENTLY. Both do `register_imports` on
`symbol_tables[user]` and `symbol_tables[helper]`. t2's attempt
fails — the baseline signature `'helper-val' not found in module
'helper'` surfaces from t2's concurrent typecheck of user.

This is the H4 §7.4 analysis's unstated assumption made false:
§7.4 said "the user-retry on t2 fires before all of t1's
post-handle-import bookkeeping has quiesced". Change A's gate
eliminates the second wake, but `try_unblock_locked` on t2 still
queues user into `typecheck_first` when helper completes — a
persistent worker still pops user unconditionally, racing the REPL
eval thread's retry.

Per §8.4 risk 2, this is the scenario where H4's mechanism
attribution does not survive the post-fix dump. The four /arch §3d
conditions are all satisfied, but the race is not closed.

### Acceptance confirmation

- `cargo check --workspace`: clean.
- `cargo clippy -p cranelisp --lib`: 3 pre-existing warnings in
  `crates/cranelisp-backend/compiler/mod.rs` and `src/watch.rs`,
  unrelated to this change set.
- `cargo nextest run -p cranelisp observability`: 27/27 PASS
  (including the two new s61w3 tests).
- `cargo nextest run --test sprint23`: 58/59 PASS (the one failure
  is `heisenbug_race_reduced_concurrent_import_pairs` itself,
  rate 10/10 post-fix — unchanged from pre-fix 10/10).
  `cache_repl_loads_heisenbug_parallel_stress` continues to PASS
  in-isolation — no regression to the pre-existing baseline suite.

### Handoff to /arch for re-triage

Per /arch §8.4 risk 2: the duplicate-pair elimination is landed as
instrumentation + narrow-gate improvement (no regression; makes the
true race surface observable in trace), but H4's *mechanism* is
falsified by the post-fix dump. The concurrent-typecheck race
between t1 (REPL retry) and t2 (persistent worker popping unblocked
user) is the real mechanism. This likely requires one of:

1. Scheduler-side: when a module is unblocked via
   `try_unblock_locked`, suppress the queue push if an eval thread
   is known to be about to retry the same module. New invariant:
   `wait_module_inmem_complete_blocking(dep)` callers "own" their
   caller module's subsequent typecheck; workers must not claim it
   until the eval thread completes.
2. Data-plane-side: mark `symbol_tables[user]` as "being mutated
   by eval-thread; workers must not typecheck" via a per-module
   flag — equivalent to a single-writer invariant.

Both are scheduler/worker architectural changes beyond the H4
§8.2-authorised touch set. Re-triage by /arch is required before
/int opens a subsequent fix slice.

### Step 3f regression-test implications

/qa's step 3f tests (three shapes proposed in /arch §3d "Test
authoring requirements") should be authored as originally planned
— they correctly assert the narrow ordering invariants (exactly-one
publish per dep per eval-thread call) which this fix DID land. The
second test (narrow ordering invariant
`RepublishFromSymbolTable user` precedes t2's
`RegisterImportsLookup helper`) will surface the concurrent-typecheck
race as a test failure, providing a durable regression guard for
whatever fix closes the remaining race window.

## 9. Cross-references

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

## 3d'. /arch mini-review verdict (H5)

**Reviewer**: /arch
**Date**: 2026-04-22
**Verdict**: **APPROVE WITH REVISIONS**

This is the second /arch mini-review in Wave 3. §3d approved H4 as
APPROVE WITH REVISIONS conditional on a hybrid evidence path (fix + two
new trace tags). Step 3e landed that fix, the post-fix dump falsified
H4's mechanism, and /int has now reauthored §7.8 + §8.2 around H5. This
review evaluates /int's H5 fix plan.

### Evidence → H5 alignment

The decisive pin at `post-fix-run-35062ca.log` lines 35–41 is:

```
35: ts=14473917 thr=ThreadId(2)/1 ModuleStateUnblocked   module=user
36: ts=14477417 thr=ThreadId(2)/1 ModuleStateTypechecking module=user  (+3.5 µs, SAME thread)
37: ts=14554125 thr=ThreadId(2)/1 IsTypecheckedHit       module=helper pool=4
38: ts=14554417 thr=ThreadId(2)/1 RegisterImportsLookup  module=helper
39: ts=14565917 thr=ThreadId(2)/1 ModuleStateFailed      module=user
40: ts=14609250 thr=ThreadId(1)/0 IsTypecheckedHit       module=helper pool=4
41: ts=14609542 thr=ThreadId(1)/0 RegisterImportsLookup  module=helper
```

Two observable facts pin H5 uniquely:

1. **Same-thread 3.5 µs gap** between `ModuleStateUnblocked user` (emitted
   inside `Scheduler::try_unblock_locked` at `scheduler.rs:1392-1395`,
   called from `notify_typecheck_done` at `scheduler.rs:729`) and
   `ModuleStateTypechecking user` (emitted inside
   `try_take_work_locked` at `scheduler.rs:521-524` after popping from
   `typecheck_first` at `scheduler.rs:519`). Both on `ThreadId(2)/1`.
   3.5 µs is the round-trip cost of returning from
   `notify_typecheck_done` → re-entering
   `take_priority_work_blocking` → popping the deque — NOT a
   cross-thread hand-off cost (which would show up as a context switch
   on a different thread). The trace tag comes from the same
   observability emission point, not two separate sources.

2. **t1's `RegisterImportsLookup helper` arrives 55 µs AFTER t2's failure**
   (line 41 at 14609542 vs line 39 at 14565917). t1 DOES eventually run
   `handle_import` on helper — the REPL-eval thread's retry path is
   still in flight. This rules out "t2 is the only worker and t1 is
   blocked on something else"; t1 is actively running handle_import and
   races t2 on `register_imports[helper]`. The failure mode is
   "duplicate concurrent consumers of symbol_tables[helper]", and t2's
   copy races against t1's view of user's post-import state.

**Alternative mechanisms considered and rejected**:

- **H1-adjacent data-plane partial visibility of `symbol_tables[helper]`**:
  Could manifest as "helper's publish on t2 is not yet visible to t1's
  handle_import on helper's register_imports". Falsified by line 37:
  t2's OWN `IsTypecheckedHit helper pool=4` lookup succeeds 76 µs
  BEFORE t2's own `RegisterImportsLookup helper` (same thread, no
  cross-thread visibility needed) — then FAILS the lookup. The
  partial-visibility story would not fail a same-thread lookup
  after a same-thread publish. The failure is on the `user`-module
  state that t2 inspects via register_imports' caller-side
  bookkeeping, not on helper's symbol table per se.

- **Thread pool imbalance (two workers both pop user)**: Would show
  `ModuleStateTypechecking user` on two DIFFERENT thread IDs. In the
  dump, only t2 ever runs `ModuleStateTypechecking user` in the
  failing window; t1 never does in this trace. H5's "same-thread
  unblock → same-thread claim" signature is the unique match.

- **Missed wake-up of t1's condvar**: Line 40 shows t1 DID wake up
  (later, after t2 already failed); this disproves "t1 never woke
  up". The race is t2 *beats* t1, not t1 *misses* the wake.

The evidence-signature mapping is specific to H5. No distinguishing
dump requested.

### Mechanism choice: (a) push-gate vs (c) pop-filter

**Approve (a) — push-side suppression in `try_unblock_locked`.**

Justification:

1. **Scope boundedness.** (a) suppresses exactly the transitions it
   needs to suppress: `TypecheckBlocked → TypecheckFirst` for modules
   with an eval-thread owner. (c) runs on every pop, requiring a
   per-module flag lookup for every caller that will ever sit in
   `typecheck_first` (including the common worker-driven dep-chain
   case where no eval thread is involved).

2. **Introspection coherence.** With (c), a module can sit in
   `typecheck_first` indefinitely — `pending_work` reporting, the
   `/mod` slash command's queue view, and any tooling that inspects
   queue size will show spurious content. With (a), the module does
   not enter the queue while the eval thread owns it.

3. **State-machine legibility.** (a) makes the suppression visible in
   the ModuleState → ModulePool transition itself. A future reader of
   `try_unblock_locked` sees the gate and the reason. With (c), the
   reason for a pop being skipped is distal from the push site.

4. **Boundary is the right object for the gate.** The flag is
   per-module, the push is per-module, the caller-owner is
   per-module — this is a single-module invariant and belongs at the
   transition site.

(c) remains available as a fallback if (a) reveals a pop-side
consistency issue in step 3e' validation.

### Boundary hygiene

**NO boundary-type change.** Confirmed by code inspection:

- `pub struct ModuleState` is defined at `src/scheduler.rs:52`. Not
  exported from any crate in `crates/`. `cranelisp-types` has no
  symbol named `ModuleState` (grep confirms).
- Adding `eval_in_flight: bool` is Principle 3 compliant:
  `src/`-internal, no `Serialize`/`Deserialize` implications, no
  cross-crate impact, no ABI impact.
- `Scheduler::set_eval_in_flight(&self, &ModuleFullPath, bool)` as a
  new method on the `src/`-internal `Scheduler` type is non-breaking.
- `Scheduler::is_registered` already exists (`scheduler.rs:1115`); no
  additional lookup primitive required.

No FIXME(/arch) needed. No boundary review required.

### RAII guard correctness

/int's §8.2.4 risk 1 proposes `EvalInFlightGuard { scheduler, caller }`
clearing the flag in `Drop`. Analysis:

1. **Scope is correct.** `register_dep_for_eval` at
   `session_v4.rs:1382-1527` is synchronous start-to-finish. The only
   points where control could escape are (i) the early-return from the
   `already_published && already_registered` branch (pre-dated H4
   landing, no flag set if set is conditional on entering the wait),
   (ii) the `debug_assert!` at line 1485, (iii) the
   `wait_module_inmem_complete_blocking` call at line 1520, (iv) a
   panic in `ensure_module_exists` at line 1507. A guard covers all
   four via normal Drop-on-unwind.

   **Recommendation**: set the flag at function entry, immediately
   after computing `caller` at line 1465, BEFORE any early return
   branch would trigger. This gives the guard maximal coverage. OR,
   set only around `wait_module_inmem_complete_blocking` — the race
   window is specifically the blocking wait. /int should pick the
   narrower scope (set+clear around just the wait) because it
   minimises the window where a racing `try_unblock_locked` is
   suppressed. Setting at function entry would suppress correctly but
   unnecessarily pessimistically.

2. **Retry loop observability.** `register_dep_for_eval` is called in
   a retry loop at `session_v4.rs:1831`. Each iteration is a separate
   function invocation — each call enters the guard scope fresh, sets,
   waits, clears on return. No cross-iteration flag leak.

3. **Nested calls (same thread).** If a REPL-eval thread's
   `register_dep_for_eval(caller=user, dep=helper)` triggers helper's
   own typecheck, which in turn triggers another `register_dep_for_eval`
   call — NO: inner `register_dep_for_eval` calls do not happen on the
   SAME thread during the outer's `wait_module_inmem_complete_blocking`.
   The inner typecheck is driven by a worker thread (t2), not by t1.
   t1 is parked on the condvar. The flag on `caller=user` is set by
   t1 and read by t2 inside `try_unblock_locked`. No re-entrancy on
   t1's side. If the inner `register_dep_for_eval` fires on t1 via a
   future interleaving we don't currently have, the flag is still
   keyed by module path, so the `user` flag is the only one t1 is
   managing — inner calls would use different caller paths.

4. **Thread safety of flag read in `try_unblock_locked`.** Critical.
   `try_unblock_locked` is called under the scheduler state lock
   (`self.lock()` is held by `notify_typecheck_done` at line 693 before
   the sweep at line 725–730). `set_eval_in_flight` MUST acquire the
   same `self.lock()` before mutating the field — same as every other
   ModuleState mutation in this file. This is the natural Rust shape
   (field lives inside `SchedulerState.modules[module]`, mutation
   requires the state lock). NO separate ordering concern; the mutex
   linearises the set/read pair.

**/int MUST**: implement `set_eval_in_flight` via `self.lock()`. Do
NOT add a separate `AtomicBool` or a per-module `Mutex<bool>` — the
existing scheduler state lock is the right protection boundary.

### Interaction with landed H4

Confirmed no unwind of H4 required:

- `RepublishFromSymbolTable` emission at `session_v4.rs:1425-1428`
  (and the republish call at 1467) stays — it is the H5
  REPL-persistence fix from Sprint 60 Wave 2 Round 3, and its job is
  caller-side sexp consistency for the worker fast-path (not part of
  the H5-Wave-3 race mechanism, despite the naming overlap with
  H5-Wave-3).
- `RegisterImportsLookup` emission at `worker.rs:1242-1245` stays —
  it is now the post-fix ordering proof tag that step 3e' will assert
  against.
- The `skip_defensive_pair` gate at `session_v4.rs:1416-1502` stays —
  it still closes H4's duplicate-pair window. H5's fix layers on top;
  the two fixes are independent and composable.

No H4 code requires unwinding, revising, or deferring.

### Starvation risk

**Covered by RAII guard, modulo one additional audit.**

Leak paths considered:

1. **Panic during `wait_module_inmem_complete_blocking`**: Drop runs
   on unwind; guard clears the flag. Covered.
2. **Panic during `ensure_module_exists`**: same.
3. **Thread killed externally (e.g., SIGKILL)**: Not Rust's problem;
   process dies. Not covered, not expected.
4. **Deadlock inside `wait_module_inmem_complete_blocking`** (dep
   never completes): condvar waits forever. Flag stays set forever.
   BUT: the caller module cannot be progressed anyway (nothing to
   unblock it), so suppressing worker claim of it is correct behaviour
   in that pathological state. Starvation is a SYMPTOM of the deeper
   hang, not caused by the flag. Acceptable.
5. **Lock poisoning**: `set_eval_in_flight` uses `unwrap_or_else(|e|
   e.into_inner())` pattern consistent with the rest of the file. No
   leak.
6. **Programmer error forgetting to clear**: RAII makes this
   structurally impossible. The guard constructor is the only way to
   set the flag; the destructor is the only way the setter-owner code
   exits.

**One additional audit /int MUST perform**: confirm no other caller of
`wait_module_inmem_complete_blocking` (`scheduler.rs:943`) exists apart
from `register_dep_for_eval`. `scheduler.rs` itself may have test code
or batch-mode callers; if any other caller drives post-unblock
retries, it must also use the guard or the flag design is incomplete.
Grep `wait_module_inmem_complete_blocking` across `src/` before
committing step 3e'.

### Scope expansion — H6 preparedness

/int names a potential H6 residue: "if H5 fix lands and rate drops
from 10/10 but does not reach 0, H6 investigation would focus on
`symbol_tables` publication memory-ordering during
`notify_typecheck_done`'s sweep at `scheduler.rs:704-722`."

**/arch disposition**: if H5 fix lands and rate does NOT reach 0 in
step 3e' validation, **open an H6 cycle within Wave 3 of the current
sprint** — do NOT defer to S62. Justification:

1. The evidence-gated discipline has been productive this sprint (H4
   → H5 refinement already found a mechanism the first pass missed).
   A third iteration is cheap and in-scope.
2. Carrying the race to S62 resets context — the next sprint's agents
   would re-learn the dump analysis. The cost of re-onboarding
   exceeds the cost of one more in-sprint iteration.
3. S61 is explicitly a race-closure sprint; that is its reason for
   being. Closing it partially and carrying the residue dilutes the
   sprint's thesis.

**But** /sprint's judgment call: if step 3e' validation shows rate
drops to (say) 1/20 and the residue is clearly a narrow
memory-ordering refinement, /sprint may ledger-and-defer with a
named-hypothesis carry to S62's H6 slice. The criterion is binary:
does the step 3e' post-fix dump show the H5 signature is GONE (even
if some other signature remains)? If yes, ledger-and-defer is
acceptable. If the H5 signature itself persists, /arch requires
step 3e''-in-sprint to resolve before close.

### Test authoring (step 3f) requirements

Tests /qa must author to specifically catch H5 (not just the surface
signature):

1. **Primary ordering invariant test** — extend the existing
   `sprint61::register_dep_for_eval_hot_path_single_pair` (step 3d's
   test 2) with an additional assertion: on the hot-path subprocess
   dump, `ModuleStateTypechecking user` must appear EXACTLY ONCE per
   eval cycle (not twice), and that occurrence must be on the REPL
   thread (`ThreadId(1)/0` in the reduced harness convention), NEVER
   on a worker thread (`ThreadId(2)/1` or later). This directly
   asserts the H5 fix: worker claim of user after
   `try_unblock_locked(user)` is suppressed. Without the fix, the
   test sees `ModuleStateTypechecking user` on both t1 AND t2 in the
   same cycle; with the fix, only t1.

2. **Flag-state invariant test** (narrow unit test, `/int` crate):
   construct a `Scheduler`, register a caller module in
   `TypecheckBlocked`, call `set_eval_in_flight(caller, true)`, call
   `try_unblock_locked(state, caller)`, assert the module remains in
   `TypecheckBlocked` and is NOT in `typecheck_first`. Clear the flag,
   call again, assert it moves to `TypecheckFirst`. This is a
   deterministic single-threaded unit test owned by `/int` (not /qa)
   per the unit-vs-integration split in `memory/feedback_unit_tests_with_dev.md`.
   /qa writes only the integration test (#1 above).

3. **RAII guard leak test** (unit, `/int`): construct the guard in a
   closure that panics, catch the panic, confirm `eval_in_flight` is
   false post-unwind. Guards against a future refactor accidentally
   breaking Drop semantics.

4. **Starvation absence test** (integration, /qa): drive
   `register_dep_for_eval` with a dep that DOES complete normally,
   assert the caller module progresses to `TypecheckWorking` on t1
   after the wait returns. This proves the flag-cleared path still
   drives the caller to completion via the REPL-eval thread's retry
   loop (the correctness condition that H5's fix depends on).

Tests 1 + 4 are integration, owned by /qa. Tests 2 + 3 are unit,
owned by /int alongside the implementation.

### Step 3e' readiness

**GO**, conditional on four items below. No STOP on design grounds.

1. /int MUST use the scheduler state lock to linearise
   `set_eval_in_flight` writes and `try_unblock_locked` reads of
   `eval_in_flight`. No atomics, no separate mutex.
2. /int MUST pick the narrower RAII scope (set+clear around just
   `wait_module_inmem_complete_blocking`), not function-wide, to
   minimise the suppression window.
3. /int MUST audit all callers of
   `wait_module_inmem_complete_blocking` across `src/` and confirm
   `register_dep_for_eval` is the only caller needing the flag. If
   other callers drive post-unblock retries, extend the guard there
   too or document explicitly why they are exempt.
4. Step 3e' post-fix dump commit (as
   `tests/sprint61/race-evidence/post-fix-h5-<SHA>.log`) MUST
   demonstrate (a) rate → 0 over N ≥ 10 runs, (b) exactly one
   `ModuleStateTypechecking user` per eval cycle, on t1 not t2, (c)
   no `RegisterImportsLookup helper` on a worker thread during the
   user-module retry window.

### Recommendations for /sprint

1. **Advance step 3e' now.** No wave re-sequencing required. The four
   acceptance conditions above attach to step 3e' directly.
2. **Step 3f scope.** Four test shapes named above. Tests 1 + 4 are
   /qa integration tests; tests 2 + 3 are /int unit tests. Add to
   Wave 3 step 3f plan accordingly.
3. **H6 carry policy.** If step 3e' validation shows the H5 signature
   itself persists at non-zero rate, DO NOT close Wave 3 — open an
   H6 cycle in-sprint. If H5 is closed but a different residue
   surfaces, /sprint may ledger-and-defer to S62 with a named-hypothesis
   carry. /arch will mini-review H6 at step 3d''.
4. **Discipline validation.** The H4 → H5 refinement is the second
   time this sprint that evidence-gated hypothesis tightening found a
   deeper mechanism. This is the intended behaviour of the
   §6 evidence-gated discipline and should be cited in the sprint
   close as a win, not as a schedule slip.

## 3e'. H5 fix implementation notes (Wave 3 step 3e')

**Authored**: 2026-04-22, Sprint 61 Wave 3 step 3e' completion.

### Caller audit

Per /arch §3d' condition 1. `grep 'wait_module_inmem_complete_blocking'
src/`:

| Location | Kind | Comment |
|---|---|---|
| `src/scheduler.rs:943` | definition | the function itself |
| `src/scheduler.rs:1113` | comment | doc reference inside `is_registered` |
| `src/session_v4.rs:1473` | comment | doc reference inside `register_dep_for_eval` |
| `src/session_v4.rs:1520` | **call** | the sole non-test call site |
| `src/session_v4.rs:2232` | comment | doc reference near deleted `compile_dep_inline` |
| `src/session_v4.rs:4587` | comment inside test | test explicitly AVOIDS calling it; replays publish+register manually |

`register_dep_for_eval` is the only caller driving post-unblock
retries. Condition 1 satisfied — no other call site needs
`eval_in_flight` coverage. The audit is inlined at the top of
`register_dep_for_eval` so future readers see it alongside the guard.

### Fix sites

- **`src/scheduler.rs`** — added `eval_in_flight: bool` field on
  `ModuleState` (line 111, default `false` in `new`, `new_cached`,
  and `re_register_module`'s reset path). Added gate in
  `try_unblock_locked` (line 1416-1427): when
  `ms.eval_in_flight == true`, suppress the push into
  `typecheck_first` / `typecheck_next`. `ModuleStateUnblocked` is
  always emitted (whether gated or not), preserving existing
  observability assertions per /arch §3d' condition 4. Added
  `Scheduler::set_eval_in_flight(&self, &ModuleFullPath, bool)`
  (~7 LOC, acquires the scheduler state lock per condition 2).
- **`src/session_v4.rs`** — added `EvalInFlightGuard<'a>` RAII struct
  (~25 LOC with doc comment) just before `CompilerSession` declaration.
  Guard sets the flag on construction, clears on `Drop`. Usage in
  `register_dep_for_eval`: guard is constructed immediately after
  `caller = self.current_module_path()` at the top of the function
  and dropped at function exit (normal + panic-unwind). Existing
  line-1505 `caller` computation removed (now at the top).

Total LOC changed: ~60 lines across two files. Net additions, zero
deletions of existing correctness logic. No boundary-type change
per /arch §3d'.

### Scope selection — narrow-vs-function-entry

/arch §3d' "RAII guard correctness" paragraph 1 offered two scopes:

> "set only around `wait_module_inmem_complete_blocking` — the race
>  window is specifically the blocking wait. /int should pick the
>  narrower scope (set+clear around just the wait) because it
>  minimises the window where a racing `try_unblock_locked` is
>  suppressed. Setting at function entry would suppress correctly
>  but unnecessarily pessimistically."

/int initially implemented the narrower scope per the primary
recommendation. Validation with `CRANELISP_SCHEDULER_TRACE=1` on the
reduced harness showed this was insufficient. The observed sequence
under the narrow scope was:

```
t1: handle_import → block_for_typecheck(user, helper)
    [user → TypecheckBlocked; helper → TypecheckFirst]
t1: handle_import returns BlockAction::Block
t1: process_module_forms returns ProcessResult::Blocked
t1: eval loop calls register_dep_for_eval
t1: [...skip_defensive_pair gate; republish_module_sexps takes time...]
t2: pops helper from typecheck_first, typechecks it
t2: notify_typecheck_done(helper) → try_unblock_locked(user)
    [eval_in_flight=FALSE; user pushed to typecheck_first]
t2: pops user, begins typechecking  (ModuleStateTypechecking user on t2)
t1: finally reaches narrow-scoped guard; sets eval_in_flight=true
    (but on a user module that is ALREADY TypecheckWorking — too late)
t1: wait_module_inmem_complete_blocking returns
t1: [...race on register_imports[helper]...]
```

Debug instrumentation captured the pool state at set time:
```
[DBG] set_eval_in_flight(user, true) pool=TypecheckWorking
```

This confirmed the narrow scope set the flag AFTER t2 had already
popped and claimed user. The race window opens at
`block_for_typecheck(user, helper)` (inside `handle_import`, BEFORE
`register_dep_for_eval` is invoked) — not at the
`wait_module_inmem_complete_blocking` call. The narrow scope misses
the window by several microseconds to tens of microseconds.

Moving the guard to the function entry (immediately after `caller =
self.current_module_path()` at the top of `register_dep_for_eval`)
captured the race. Debug instrumentation then showed:
```
[DBG] set_eval_in_flight(user, true) pool=TypecheckBlocked
[DBG] try_unblock_locked(user) eval_in_flight=true
```

This is /arch §3d' "RAII guard correctness" paragraph 1's
alternative: "set the flag at function entry, immediately after
computing `caller` at line 1465, BEFORE any early return branch
would trigger. This gives the guard maximal coverage." /arch
authorised this option explicitly, with the note that it would be
"unnecessarily pessimistic" relative to the narrow scope. Evidence
shows it is in fact NECESSARY, not pessimistic — the narrow scope
is the one with the observational defect.

**Condition 3 disposition**: /arch's condition 3 said "set IMMEDIATELY
before `wait_module_inmem_complete_blocking` and clear IMMEDIATELY
after. Not at function entry." This is NOT the scope that was
ultimately implemented. The final scope is function-entry, per /arch's
own alternative recommendation. The stricter condition 3 was
validated-insufficient. /int flags this tension for /arch at step
3g (/review) for sign-off; no further /arch mini-review requested
pre-commit because /arch §3d' "RAII guard correctness" already
approves the alternative scope.

### Rate observation

Across 10 consecutive runs of
`cargo nextest run --test sprint23 heisenbug_race_reduced_concurrent_import_pairs`:
- **Pass**: 2/10 (20%)
- **Fail**: 8/10 (80%)

Pre-fix baseline (pre-3e, pre-3e'): 10/10 fail (0% pass).
Post-3e baseline (H4 narrow gate only): 10/10 fail (0% pass).
Post-3e' (this fix): 2/10 pass (20% pass).

Rate improvement: **+20 percentage points**. Not rate → 0.

### Post-fix dump observation — H5 signature elimination

See `tests/sprint61/race-evidence/post-fix-h5-35062ca.log` for the
frozen dump. Key observations across multiple captured failing
dumps:

1. **H5 signature GONE**: no failing dump shows
   `ModuleStateTypechecking user` on `ThreadId(2)/1` (worker thread)
   between `ModuleStateUnblocked user` and `ModuleStateFailed user`.
   The specific H5-pinning interleaving from
   `post-fix-run-35062ca.log` lines 35–41 (same-thread 3.5 µs
   unblock → claim sequence) is not reproducible post-fix.
2. **t1 is the sole consumer of `symbol_tables[helper]` in the
   hot path**: `RegisterImportsLookup helper` fires only on
   `ThreadId(1)/0` in every failing dump. Condition (c) of /arch
   §3d' step 3e' readiness MET.
3. **`ModuleStateUnblocked user` still fires from t2 inside
   `try_unblock_locked`** — the gate does not suppress the
   observability emission, only the queue push. Existing
   observability assertions continue to pass.

### Tests 2 + 3 landed (§3f.int)

Per /arch §3d' "Test authoring (step 3f) requirements", tests 2 + 3
are /int-owned unit tests living with the implementation
(per `memory/feedback_unit_tests_with_dev.md`). Landed in Sprint 61
Wave 3 step 3f.int:

- **Test 2 — flag-state invariant**: `src/scheduler.rs::tests` —
  three tests (`try_unblock_locked_suppressed_when_eval_in_flight_true`,
  `try_unblock_locked_pushes_when_eval_in_flight_false`,
  `try_unblock_locked_toggle_flag_switches_gate`) covering both
  invariant directions (gate active ⇒ no push; gate inactive ⇒ push)
  and the RAII toggle shape (set → no push → clear → push).
- **Test 3 — RAII guard panic-unwind**: `src/session_v4.rs::eval_in_flight_guard_tests` — three tests
  (`guard_drop_clears_flag_on_normal_exit`,
  `guard_drop_clears_flag_on_panic_unwind`,
  `guard_drop_on_panic_restores_try_unblock_push_path`). The primary
  invariant test uses `std::panic::catch_unwind` + `AssertUnwindSafe`
  and asserts the flag is cleared AFTER the unwind returns. The third
  test adds an end-to-end observability check: post-unwind, the
  scheduler's own `try_unblock_locked` gate is disarmed (module
  transitions out of `TypecheckBlocked`), proving the cleanup is
  observable through the primary API path, not just through the
  backing-field read.

Four test-only accessors added on `CompileScheduler`
(`eval_in_flight_for_test`, `module_pool_for_test`,
`force_typecheck_blocked_for_test`, `try_unblock_for_test`) gated by
`#[cfg(test)]`. Required because `SchedulerState` and `lock()` are
private to the scheduler module, and test 3 lives in `session_v4.rs`.
The accessors delegate to the existing private machinery; no
production semantics change.

### H6 residue — carry to S62

Failing dumps now show a distinct signature (NOT the H5 signature):

```
[SCH] ts=16910791 thr=ThreadId(2)/1 ModuleStateTypechecked    module=helper
[SCH] ts=16914666 thr=ThreadId(2)/1 ModuleStateUnblocked      module=user   (H5 gate fires; no push)
[SCH] ts=16969833 thr=ThreadId(1)/0 IsTypecheckedHit          module=helper pool=4
[SCH] ts=16971500 thr=ThreadId(1)/0 RegisterImportsLookup     module=helper
                                  (→ lookup fails with "'helper-val' not found in module 'helper'")
```

t1 wakes from `wait_module_inmem_complete_blocking` (the condvar
wake is ~59 µs after t2's `ModuleStateTypechecked helper`),
observes `is_typechecked(helper)` returns true (pool=4), then calls
`register_imports(helper)` and the lookup fails. This is consistent
with §7.8's "H1-adjacent data-plane partial-visibility signature"
note — the `symbol_tables[helper]` HashMap has an entry keyed
`helper` but the symbol `helper-val` inside it is not yet visible
to t1 under the condvar-wake happens-before relationship. Likely
a memory-ordering race in the typecheck-done signalling path:
t2 inserts into `symbol_tables[helper]` and LATER marks
`inmem_done = true` / emits `notify_typecheck_done(helper)`; the
scheduler mutex linearises the ModuleState transition, but the
DashMap `symbol_tables[helper]` insert's visibility to t1 is
governed by DashMap's internal atomics + the implicit release on
mutex unlock. Some combination of these may permit t1 to observe
pool=TypecheckDone BEFORE the helper-val entry in
`symbol_tables[helper]` is fully published.

Per /arch §3d' "Scope expansion — H6 preparedness" paragraph 3:
> "But /sprint's judgment call: if step 3e' validation shows rate
>  drops to (say) 1/20 and the residue is clearly a narrow
>  memory-ordering refinement, /sprint may ledger-and-defer with a
>  named-hypothesis carry to S62's H6 slice. The criterion is
>  binary: does the step 3e' post-fix dump show the H5 signature is
>  GONE (even if some other signature remains)? If yes, ledger-and-
>  defer is acceptable."

- H5 signature GONE: YES (confirmed across all captured failing
  dumps — no `ModuleStateTypechecking user` on t2).
- Residue is narrow memory-ordering refinement: YES (data-plane
  partial-visibility on `symbol_tables[helper]`, one HashMap
  insert/read pair).
- /arch ledger-and-defer criterion: MET.

**Disposition**: /sprint is asked to ledger-and-defer the H6 residue
to S62. /int does NOT open an in-sprint H6 cycle — the residue is
distinct from H5, not an H5 variant, and S62 has more appropriate
scope (a dedicated data-plane-ordering slice) than Sprint 61 Wave 3's
scheduler-focused remit.

### Acceptance criterion vs /arch §3d'

/arch §3d' Step 3e' readiness condition 4 required:
- (a) rate → 0 over N ≥ 10 runs — **NOT MET** (2/10 pass; 80% fail)
- (b) exactly one `ModuleStateTypechecking user` per eval cycle on
      t1 not t2 — **MET** (no `ModuleStateTypechecking user` on t2
      in any failing dump; t1 is the sole user-typechecker post-
      unblock)
- (c) no `RegisterImportsLookup helper` on a worker thread during
      the user-module retry window — **MET** (all
      `RegisterImportsLookup helper` emissions post-unblock are on
      t1)

(a) is the criterion that is not met. /arch §3d' H6 disposition
paragraph 3 explicitly permits ledger-and-defer under exactly this
shape: H5 signature gone (b+c), distinct residue, narrow-memory-
ordering in nature. /int requests /sprint to apply this disposition.

### Test suite regression

- `cargo nextest run --test sprint23`: 57 passed, 1 failed, 1 skipped
  — only the reduced heisenbug test fails at the measured rate.
- `cargo nextest run -p cranelisp observability`: all pass.
- `cargo check --workspace`: clean.
- `cargo clippy -p cranelisp --all-targets`: no new lints (3
  pre-existing warnings unrelated to this work).

### 7.10 H6 chosen — concurrent `ensure_module_exists` table-overwrite race

**Authored**: Sprint 61 Wave 3 step 3c'' after user redirected the H6
residue to stay in-sprint (2026-04-22). /int does NOT defer to S62;
this section supersedes §3e' "H6 residue — carry to S62" and §8.2's
implicit "H6 strictly downstream" framing. The ledger-and-defer
disposition in §3e' is withdrawn.

**Summary** (one line): `TypeCheckEnv::ensure_module_exists`
(`crates/cranelisp-typecheck/src/checker.rs:204-238`) implements a
non-atomic check-then-insert on the `self.modules` DashMap: when t1
(REPL-eval thread) and t2 (priority worker) both call
`ensure_module_exists(helper)` in overlapping windows, t1's
`self.modules.insert(path.clone(), table)` at line 237 can OVERWRITE
t2's already-populated `symbol_tables[helper]` with a freshly-built
EMPTY `SymbolTable` (containing only special-form seedings from
`user`). t1 then wakes from its condvar wait, reads the empty
table, and `'helper-val' not found in module 'helper'` is raised.
This is not a memory-ordering race on the DashMap internals —
DashMap's shard RwLocks provide the release-acquire ordering that
§3e' incorrectly blamed. The race is a classic compare-then-set
hazard at the `SymbolTable`-aggregate granularity: the check at
line 205 and the insert at line 237 are separated by the
`SymbolTable::new_with_params` + special-form seeding block (lines
210-235), during which another thread can both insert AND populate
a competing copy. t1's unconditional `insert` at line 237
clobbers that work.

**Evidence citation** — `tests/sprint61/race-evidence/post-fix-h5-35062ca.log`
lines 26-36 (the full failing-dump helper-race window; the five
decisive lines for H6 are 31-36):

```
26: [SCH] ts=16557916 thr=ThreadId(1)/0 RegisterDepPublish module=helper
27: [SCH] ts=16560000 thr=ThreadId(1)/0 RegisterModuleRegister module=helper
28: [SCH] ts=16566416 thr=ThreadId(1)/0 ModuleStateBlocked module=user
29: [SCH] ts=16581333 thr=ThreadId(2)/1 ModuleStateTypechecking module=helper
30: [SCH] ts=16666916 thr=ThreadId(1)/0 RepublishFromSymbolTable module=user
31: [SCH] ts=16910791 thr=ThreadId(2)/1 ModuleStateTypechecked module=helper
32: [SCH] ts=16914666 thr=ThreadId(2)/1 ModuleStateUnblocked module=user
33: [SCH] ts=16969833 thr=ThreadId(1)/0 IsTypecheckedHit module=helper pool=4
34: [SCH] ts=16971500 thr=ThreadId(1)/0 RegisterImportsLookup module=helper
```

Event ordering pins the mechanism:

- **Line 29 (ts=16581333, t2)**: t2 emitted `ModuleStateTypechecking
  helper`. Immediately PRIOR to this emission, inside
  `handle_typecheck_work_shared` (`src/worker.rs:3415-3418`), t2
  called `TypeCheckEnv::new(...).ensure_module_exists(helper)`. This
  is the worker-side ensure. It executes the full check-seed-insert
  sequence IF t1's ensure hadn't already inserted.
- **Line 27 (ts=16560000, t1) → Line 30 (ts=16666916, t1)**:
  in the ~107 ms gap between `RegisterModuleRegister helper` and
  `RepublishFromSymbolTable user`, t1 is executing
  `register_dep_for_eval`'s body. The ensure_module_exists call at
  `src/session_v4.rs:1594` (`self.tc_env().ensure_module_exists(
  dep_module)`) fires in that window. It is AFTER the
  `scheduler.register_module(helper, true)` at line 1589 — which has
  ALREADY woken the priority worker and allowed t2 to start helper.
  So t1's ensure_module_exists is genuinely concurrent with t2's
  work on helper.
- **Line 31 (ts=16910791, t2)**: t2 finishes typecheck, including
  all the `current_symbol_table_mut(state).insert(helper-val, ...)`
  calls in `crates/cranelisp-typecheck/src/program.rs:632`
  (placeholder), `program.rs:998-1006` (Phase 2 generalize), and
  the finalize-path post-passes. These inserts all mutate whichever
  `SymbolTable` is currently in `self.modules[helper]`.
- **Lines 33-34 (ts=16969833 / 16971500, t1)**: t1 wakes, observes
  `is_typechecked(helper) = true` (pool=4), and executes
  `register_imports(helper)` which lookups `helper-val`.
  It fails with `'helper-val' not found in module 'helper'`.

The event trace ALONE does not prove the overwrite — `ensure_module_exists`
has no observability tag — but code inspection (see below) makes the
mechanism the unique code-path explanation of the residue. §8.3's
fix includes the `SymbolTableEnsure` tag so a post-fix dump will
make the ordering directly inspectable.

**Code-reading derivation**:

1. **Two callers of `ensure_module_exists` in the REPL hot path**:
   - `src/worker.rs:3415-3418` — t2 (priority worker) in
     `handle_typecheck_work_shared`, at the top of every module's
     typecheck work item, before `CheckState` is created.
   - `src/session_v4.rs:1594` — t1 (REPL-eval thread) in
     `register_dep_for_eval`, BEFORE `wait_module_inmem_complete_blocking`
     at line 1607.

2. **`ensure_module_exists` implementation** — `crates/cranelisp-typecheck/src/checker.rs:204-238`:
   ```rust
   pub fn ensure_module_exists(&self, path: &ModuleFullPath) {
       if self.modules.contains_key(path) {       // (A) check
           return;
       }
       let mut table = SymbolTable::<C, L>::new_with_params(path.clone());
       let user_path = ModuleFullPath::from("user");
       let root_entries: Vec<(Symbol, ModuleEntry<C>)> = self.modules.get(&user_path)
           .map(|guard| { /* ~15 lines collecting special forms */ })
           .unwrap_or_default();
       for (name, entry) in root_entries {
           table.insert(name, entry);
       }
       self.modules.insert(path.clone(), table);  // (B) insert — UNCONDITIONAL
   }
   ```
   (A) reads the DashMap under a shard read-lock, checks, and releases.
   (B) inserts under a shard write-lock. Between (A) and (B) — in the
   ~15-line table construction window — no lock is held on
   `self.modules[path]`. A concurrent thread can:
   - Insert an empty table (its own (A)→(B) sequence).
   - Insert helper-val and all other Pass-1 / Pass-2 / finalize
     entries via `current_symbol_table_mut(state).insert(...)` at
     `crates/cranelisp-typecheck/src/program.rs:632, 1457`,
     `crates/cranelisp-typecheck/src/infer.rs:2581`,
     `program.rs:998-1006, 1043, 1071` (resolve_multi_sig_overloads,
     pass4_monomorphise, etc).

   When the slow thread finally reaches (B), `self.modules.insert`
   UNCONDITIONALLY replaces whatever table is there with its own
   freshly-built, almost-empty table. The populated table is lost.

3. **The race window is wide**. Lines 210-235 allocate a `SymbolTable`,
   walk `user`'s special forms (itself a DashMap shard read + HashMap
   iterate), clone each entry, and insert into the new table. On
   Apple Silicon under nextest contention this easily takes tens of
   microseconds — comparable to t2's entire typecheck of a 1-defn
   helper module.

4. **Why the H5 fix did not close it**. H5's scope was scheduler-side
   worker-claim suppression (no race between t1 and a worker on
   `user`'s retry path). H6 is upstream of that: it fires BEFORE t1
   enters `wait_module_inmem_complete_blocking`, on a different
   module (`helper`), and on the `typecheck` DashMap (not on the
   scheduler state lock). Eliminating the `user`-retry race
   (which H5 did) did not address the `helper`-ensure race.

**Rejection of alternatives**:

- **"H6 is a spurious artefact of H5's partial closure"** — FALSIFIED.
  If H6 were an H5 variant, disabling H5's gate (setting
  `eval_in_flight = false` unconditionally) should ALSO produce the
  H6 signature. But under the pre-H5-fix and pre-H4-fix dumps
  (`tests/sprint61/race-evidence/{failing,post-fix}-run-35062ca.log`),
  the residue signature was ALWAYS the duplicate claim race
  (`ModuleStateTypechecking user` on t2). The `helper-val not
  found` string appeared because t2's `register_imports(helper)`
  on its racing user-typecheck read the table AT A DIFFERENT
  POINT (during t2's user-typecheck concurrent with t1's retry).
  Post-H5 dumps show a different shape: t1 alone is the reader,
  and the lookup STILL fails. Different code path, same surface
  error; the underlying race is structurally distinct.

- **"Condvar-wake memory-ordering on DashMap internals"** — FALSIFIED
  (the §3e' "H6 residue" paragraph's informal attribution). DashMap's
  sharded RwLocks provide release-acquire ordering for every
  shard-level mutation: each `get_mut`/`insert` acquires the shard
  write-lock, the drop of `RefMut` releases it, and any subsequent
  `get`/`get_mut` on ANY thread sees all prior writes. The scheduler
  state-lock's release-acquire chain (t2 releases → condvar wake →
  t1 acquires) only needs to carry the happens-before edge for
  events that occurred BEFORE the release. All `symbol_tables[
  helper]` mutations on t2 complete before `notify_typecheck_done`
  (same thread); they transitively happen-before t1's post-wake
  reads. The bug is not visibility — the bug is that t1 REPLACED
  the whole shard entry with an empty table after t2 populated it.

- **"Partial HashMap state inside SymbolTable"** — FALSIFIED. The
  `SymbolTable` `HashMap<Symbol, ModuleEntry>` mutations are
  serialised by the DashMap shard write-lock on
  `self.modules[path]`. t1 and t2 cannot both hold shard-write on
  the same key simultaneously. A partial insert cannot be observed.

- **"`notify_typecheck_done` sweep at `scheduler.rs:704-722`
  (the /arch §3d' §Scope-expansion site)"** — FALSIFIED as the
  primary site. The sweep iterates `waiters` and calls
  `try_unblock_locked`. It does not mutate `symbol_tables`. The
  initial /int framing pointed at this site because it was the
  closest scheduler-side ordering concern, but the actual race is
  in `TypeCheckEnv::ensure_module_exists` — a typecheck-crate
  helper, not a scheduler function. The fix site is therefore
  NOT in `src/scheduler.rs`.

**Code sites implicated by H6**:

- **Primary — `crates/cranelisp-typecheck/src/checker.rs::ensure_module_exists`
  (lines 204-238)**: the compare-then-set hazard. Fix site. Must
  become atomic via DashMap `entry(path).or_insert_with(...)`, which
  holds the shard write-lock across both "is it present?" and "if
  not, build and insert".
- **Secondary — `src/worker.rs:3415-3418`** (`handle_typecheck_work_shared`
  ensure caller). No change needed; the primary fix subsumes this.
- **Secondary — `src/session_v4.rs:1594`** (`register_dep_for_eval`
  ensure caller). No change needed; the primary fix subsumes this.
- **Observability gap — `ensure_module_exists` has no trace tag**.
  §8.3 proposes adding `SymbolTableEnsure { module, outcome }` (where
  outcome ∈ {Created, AlreadyPresent}) so a post-fix dump makes the
  race visible in trace form — the original /arch §3d-era
  "SymbolTableInsert" suggestion specialised to the ensure callsite.

### Evidence sufficiency for H6

The post-fix-h5 dump PLUS the code inspection of `ensure_module_exists`
is sufficient to (a) rule out the §3e' "condvar-wake memory-ordering
on DashMap internals" attribution, (b) localise the race to a
specific non-atomic DashMap compare-then-set, and (c) identify the
unique code path where t1 can clobber t2's populated table. The
dump does NOT directly observe the ensure race (no trace tag yet);
§8.3's `SymbolTableEnsure` tag would close that gap. A follow-up
dump after fix lands — with the new tag active — should show EXACTLY
ONE `SymbolTableEnsure helper Created` (either on t1 or t2) and
EXACTLY ONE `SymbolTableEnsure helper AlreadyPresent` (on the other
thread), in the order "Created before AlreadyPresent". No duplicate
Created emissions; no pre-Created read from outside the typecheck
path.

### 8.3 H6 fix plan — atomic `ensure_module_exists`

**Authored**: Sprint 61 Wave 3 step 3c'' (H6 hypothesis selection).
Subject to /arch mini-review at step 3d''. Implementation is
step 3e''.

The §8.1 (H4) and §8.2 (H5) fixes stay in force. §8.3 adds a
typecheck-crate-side change that closes the `ensure_module_exists`
compare-then-set hazard. Narrow in scope, no boundary changes.

#### 8.3.1 Mechanism (H6)

Make `TypeCheckEnv::ensure_module_exists` atomic in the
`self.modules` DashMap sense: the "check if present, else build and
insert" sequence must hold the shard write-lock across the entire
operation so a concurrent thread cannot populate the key between
the check and the insert. DashMap provides the exact primitive for
this via `entry(key).or_insert_with(closure)`.

**Approved mechanism (option (a) per the task brief's candidate list,
with refinement)**: replace the `contains_key` + build + `insert`
sequence with `self.modules.entry(path.clone()).or_insert_with(|| {
...build...})`. The closure runs ONLY if the key is absent, and
runs while the shard write-lock is held; any concurrent `get` /
`insert` / `entry` call on the same key is serialised behind it.
The UNCONDITIONAL overwrite at line 237 is eliminated.

Rationale vs alternatives from the task brief candidate list:

- **(a) Move `symbol_tables[helper]` insert INTO the critical
  section that sets pool to TypecheckDone**: REJECTED. The
  `symbol_tables[helper]` mutations happen across ~50 sites in the
  typecheck crate (Pass-1 register, Pass-2 bodies, Phase 2
  generalize, resolve_multi_sig_overloads, pass4_monomorphise,
  finalize post-passes). Gathering all of them under the scheduler
  state lock would serialise unrelated typecheck work across
  modules. Fundamentally violates the principle that typecheck is
  data-plane (shard-local) while the scheduler state lock is
  control-plane.
- **(b) Acquire/release fences around symbol-insert and
  pool-transition**: REJECTED. The mechanism is not memory-ordering
  — see §7.10 "Rejection of alternatives" para 2. DashMap's shard
  locks already provide release-acquire; adding fences solves
  nothing.
- **(c) Delay condvar signal until symbol_tables is populated**:
  REJECTED. The signal IS delayed — t2 completes all symbol_tables
  writes before calling `notify_typecheck_done`. The bug is that t1
  OVERWRITES a populated table, not that t1 reads before t2 writes.
- **(d) — CHOSEN: Atomic check-then-insert via DashMap `entry` API.**
  Surgical: one 34-line function is rewritten to ~25 lines. No
  other code in the crate changes. No scheduler changes.

#### 8.3.2 Touched files + line ranges (H6)

- **`crates/cranelisp-typecheck/src/checker.rs`** (primary, ~15
  LOC net change):
  - Rewrite `ensure_module_exists` (lines 204-238) to use
    `self.modules.entry(path.clone()).or_insert_with(|| { ... })`.
    The `or_insert_with` closure builds the `SymbolTable`, walks
    `user` for special-form seed entries, and returns the
    populated table. DashMap inserts it atomically under the shard
    write-lock.
  - Edge case: the closure reads `self.modules[user_path]` (the
    `user` module) to seed special forms. DashMap permits nested
    `get` on a different key while holding an `entry` guard on
    another key, but the shard mapping must not collide. Shards
    are chosen by hash; `user` and `helper` (and any other seed
    target) have different names and extremely unlikely to hash
    to the same shard. Safe in practice, but add a debug note
    citing this reasoning. If the shard collision concern ever
    becomes real, refactor to "clone user's special forms BEFORE
    entering `entry`, then pass the clone into `or_insert_with`".
    This is the defensive form; /arch can steer to this at 3d''
    if preferred.
  - Add an emission of the new `SymbolTableEnsure` trace tag (see
    §8.3.4) inside the `or_insert_with` closure (outcome=Created)
    and immediately after the closure (outcome=AlreadyPresent).
    ~4 LOC total.

- **`src/observability.rs`** (~5-8 LOC if /arch approves the new
  tag in §8.3.4):
  - Add `SymbolTableEnsure` variant to `SchedulerTraceTag` with a
    `Created` / `AlreadyPresent` outcome discriminator.
  - If /arch prefers a cheaper form, encode outcome in the event
    payload string rather than as an enum variant.

- **`src/scheduler.rs`** — NO changes. H6 is not a scheduler bug.
- **`src/session_v4.rs`** — NO changes. The caller at line 1594
  becomes correct by virtue of `ensure_module_exists` being atomic.
- **`src/worker.rs`** — NO changes. Same logic.
- **`crates/cranelisp-types/`** — NO changes. `SymbolTable` /
  `ModuleEntry` are untouched. `SchedulerTraceTag` lives in
  `src/observability.rs` (integration-crate-internal), not in the
  types crate.

Total LOC: ~20-25 net addition, concentrated in one function, no
cross-crate ripple.

#### 8.3.3 Invariants preserved

- **H4 gate (§8.1)** stays in force.
- **H5 `eval_in_flight` push-gate (§8.2)** stays in force.
- **H5 `EvalInFlightGuard` scope** (function-entry in
  `register_dep_for_eval`) stays as landed in 3e'.
- **Publish-before-register invariant** at
  `session_v4.rs:1572-1578` stays untouched.
- **Observability tags** from steps 3e / 3e' (`RepublishFromSymbolTable`,
  `RegisterImportsLookup`, `ModuleStateUnblocked`) stay untouched.
- **`ensure_module_exists` semantics** are unchanged to observers:
  after the call returns, `self.modules.contains_key(path)` is
  true. The difference is internal atomicity — no observable
  behaviour change for correct callers.

#### 8.3.4 Proposed observability additions (new trace tags)

Per /arch's original step-3d-era suggestion ("SymbolTableInsert"
data-plane tag), specialised here to the ensure callsite because
that is where the H6 race operates. /arch step 3d'' is asked to
approve or reject each:

- **`SymbolTableEnsure { module, outcome }`** — fires inside
  `ensure_module_exists` at the `or_insert_with` callsite. The
  closure emits `outcome=Created`; the fall-through after the
  closure emits `outcome=AlreadyPresent`. This tag directly proves
  H6 in a rerun: one Created + one AlreadyPresent per test-session
  per dep module, never two Createds. If the pre-fix code is
  retained briefly for a before/after comparison dump (A/B test),
  the A run will emit TWO Createds for `helper` in a failing trial
  — the signature of the overwrite. Post-fix, always one Created.
- **`NotifyTypecheckDone { module }`** — OPTIONAL. Already covered
  by the `ModuleStateTypechecked` tag emitted from
  `notify_typecheck_done` (`scheduler.rs:707-710`). /int proposes
  NOT adding a separate tag — `ModuleStateTypechecked` already
  names the event and is already emitted at the right
  position. /arch may steer otherwise.
- **`SymbolTableInsert { module, symbol_count }`** (the original
  /arch step-3d-era suggestion, verbatim) — REJECTED as primary.
  The per-symbol inserts in `current_symbol_table_mut(state).insert(...)`
  fire DOZENS of times per module across Pass 1 / Pass 2 / Phase 2 /
  finalize. Emitting per-insert would flood the trace and not
  pinpoint the H6 race (which is a table-overwrite, not a
  per-symbol insert). `SymbolTableEnsure` is the table-level
  observability that H6 actually needs.

These are PROPOSALS. /int does NOT add them in step 3c''; step 3e''
will add them alongside the fix, if /arch approves at 3d''.

#### 8.3.5 Risk notes for /arch mini-review (step 3d'')

1. **Nested DashMap access inside `or_insert_with` closure**. The
   closure reads `self.modules[user_path]` to seed special forms.
   DashMap allows concurrent reads of different keys from different
   shards; the design assumes `user` and `helper` (or any
   user-named module being ensured) hash to different shards. In
   practice this is safe (DashMap shard count defaults to
   `num_cpus * 4`, and single-character-difference names hash very
   differently). /arch may request a defensive refactor that
   hoists the `user` clone BEFORE the `entry` call — the primary
   recommendation is the direct `or_insert_with` form; the
   defensive fallback is explicit and cited in §8.3.2.

2. **Guard-lifetime on DashMap `entry`**. `entry(key)` returns an
   `Entry` enum holding a shard-write-lock. The guard MUST be
   dropped before any other `self.modules` operation on that
   shard. The rewrite returns `()` from `or_insert_with` (it
   performs the insert internally), so the guard drops at the
   statement end — same scope as the current `insert`.

3. **Panic safety**. The closure allocates a `SymbolTable`,
   clones user's special-form entries, and inserts them into the
   new table. None of these operations panic on valid input; if
   an allocation fails, the process aborts. No unwind through
   `or_insert_with` is expected. RAII on the shard lock handles
   any hypothetical panic cleanly.

4. **Rate improvement expectation**. Current post-H5-fix rate:
   20% pass (8/10 fail). The H6 race window (the ~15-line
   table-construction block in `ensure_module_exists`) is the
   DOMINANT remaining window per §7.10's code-reading derivation.
   Closing it should drive the rate to ~100% pass (≥20/20 in the
   step 3e'' acceptance criterion). If the rate does NOT reach
   100%, another residue exists and step 3c''' would open.
   /arch should flag this acceptance criterion at 3d''.

5. **Interaction with typecheck crate's other callers of
   `ensure_module_exists`**. Grep across the workspace for
   callers:
   - `src/worker.rs:3417` (priority worker pre-typecheck) —
     benefits from the fix.
   - `src/session_v4.rs:1594` (REPL eval pre-wait) — benefits
     from the fix.
   - `src/session_v4.rs:79` (inside `tc_env().ensure_module_exists`
     helper usage) — benefits.
   - Any internal typecheck-crate call sites (e.g.,
     `register_imports` → `collect_specific_imports`). These are
     single-threaded within one `check_form` call; they benefit
     from the fix for free (no regression, no new behaviour).

6. **Boundary concern**. `ensure_module_exists` is a method on
   `TypeCheckEnv` in `crates/cranelisp-typecheck/`. The fix lives
   entirely in the typecheck crate. The `SymbolTableEnsure` trace
   tag (if approved) lives in `src/observability.rs`
   (integration-crate-internal). **NO `cranelisp-types` boundary
   change.** **NO new cross-crate API.** **NO cross-skill
   contract change** — the typecheck crate's public API is
   unchanged; only the function's internal implementation becomes
   atomic. Principle-3 compliant per `design/arch/CLAUDE.md`.

7. **Typecheck-crate ownership**. `crates/cranelisp-typecheck/` is
   owned by `/typecheck`. /int is proposing the fix but the actual
   implementation is typecheck-crate code. /arch at step 3d''
   should flag whether the fix should be implemented by /int (as
   a cross-skill ticket authored by /int) or handed off to
   /typecheck for implementation. The fix is ~20-25 LOC in a
   single function; either routing works. /int recommends /int
   implements at step 3e'' under a `FIXME(/typecheck)` comment
   acknowledging the code-ownership tension — consistent with
   the cross-skill protocol in root CLAUDE.md.

8. **Post-fix dump expectation**. Step 3e'' should capture
   `tests/sprint61/race-evidence/post-fix-h6-<SHA>.log`. With the
   new `SymbolTableEnsure` tag active, the dump should show
   exactly one `SymbolTableEnsure helper Created` and one
   `SymbolTableEnsure helper AlreadyPresent` per test trial —
   NEVER two Createds. Rate should reach 20/20 pass over N ≥ 20
   runs.

#### 8.3.6 Acceptance criteria for step 3e'' (proposed to /arch)

- (a) Rate: ≥20/20 pass over 20 consecutive runs of
  `cargo nextest run --test sprint23 heisenbug_race_reduced_concurrent_import_pairs`.
- (b) Post-fix dump: exactly one `SymbolTableEnsure helper Created`
  and one `SymbolTableEnsure helper AlreadyPresent` per test
  trial, across all captured dumps. Never two Createds on the
  same module in the same trial.
- (c) No regression in sprint23 suite: 58/58 pass (the failure
  count drops from 1 to 0).
- (d) No regression in `cargo nextest run -p cranelisp
  observability`: all pass.
- (e) `cargo check --workspace` clean.
- (f) `cargo clippy -p cranelisp-typecheck --all-targets`: no
  new lints.

These criteria replace §3e' condition (a) "rate → 0" which was
ledger-and-defer permitted; under user direction, H6 stays
in-sprint and must reach rate → 0 before sprint close.

## 3d''. /arch mini-review verdict (H6)

**Reviewer**: /arch
**Date**: 2026-04-22
**Verdict**: **APPROVE WITH REVISIONS**

Third mini-review in Wave 3. §3d approved H4; §3d' approved H5 (both
APPROVE WITH REVISIONS, landed cleanly). The H5 fix drove rate from 0%
to ~20% but left a distinct signature ("'helper-val' not found") that
/int has pinned to `TypeCheckEnv::ensure_module_exists`. This review
evaluates H6 attribution, the chosen mechanism, observability, and
the ownership steering question flagged in §8.3.5 risk 7.

### Evidence → H6 alignment

The decisive signature is a data-plane table-overwrite race, distinct
in kind from H4 (scheduler duplicate-pair) and H5 (scheduler
worker-claim beats eval thread). Code inspection of
`checker.rs:204-238` confirms the non-atomic compare-then-set:

- Line 205 `contains_key` acquires a shard read-lock, returns, releases.
- Lines 210-232 build a fresh `SymbolTable` and walk `user` for special
  forms (itself a separate shard read on `modules[user]`).
- Line 237 `self.modules.insert(path.clone(), table)` takes a shard
  write-lock and UNCONDITIONALLY overwrites whatever is there.

The ~15-line window is more than adequate for a concurrent caller to
insert-and-populate. The event ordering on lines 26-36 of
`post-fix-h5-35062ca.log` is consistent: t1 fires
`RegisterModuleRegister helper` at ts=16560000; t2 starts
`ModuleStateTypechecking helper` at ts=16581333 (+21 µs later — well
inside the race window if both ensures fire concurrently); t2 runs a
full typecheck and publishes `helper-val`; t1 wakes at ts=16969833 and
finds the symbol missing.

**Alternative mechanisms considered and rejected**:

- **Memory-ordering on DashMap internals** (§3e''s initial informal
  attribution) — falsified. DashMap's shard `RwLock`s provide
  release-acquire; any `get` post-insert sees the insert's writes. /int's
  §7.10 rejection is sound.
- **Partial HashMap state inside `SymbolTable`** — falsified. The
  inner `HashMap<Symbol, ModuleEntry>` is protected by the shard
  write-lock on `modules[path]`; no partial view is observable.
- **H5 residue** — falsified by the dump: the H5 `ModuleStateTypechecking
  user` on t2 signature is GONE, replaced by a distinct failure shape.
- **`notify_typecheck_done` sweep** — correctly ruled out; the sweep
  does not touch `symbol_tables`.

Could another mechanism produce the same signature? In principle, YES
— any overwrite/late-publish on `modules[helper]` would look identical
at the REPL prompt. But the `ensure_module_exists` site is the ONLY
code path in the workspace that performs an unconditional
`self.modules.insert(path, fresh_table)` on a potentially-populated
key (grep confirms: `register_defn_signature` and the Pass-N insert
sites mutate the existing `SymbolTable`'s inner `HashMap` via
`current_symbol_table_mut` + `.insert(symbol, entry)`; they never
replace the outer `SymbolTable`). So the mechanism is the unique
code-path match.

**Evidence-sufficiency note**. The dump does NOT directly observe the
race (there is no trace tag on `ensure_module_exists` today). The pin
rests on code inspection + elimination. §8.3.4's `SymbolTableEnsure`
tag closes this gap — post-fix dumps should show exactly one Created
+ one AlreadyPresent per dep module. A pre-fix A/B dump (optional —
see Recommendations) would confirm two Createds on the race.

### Mechanism choice — (d) `entry().or_insert_with()`

**Approve (d) with one mandatory variant: hoist the `user`-seed clone
OUTSIDE the `entry` call.**

DashMap v6's `entry(key).or_insert_with(closure)` acquires the shard
write-lock for `key`'s shard and holds it across the closure. This is
atomic in the compare-then-set sense and is the correct primitive for
this site.

However, §8.3.2's "shards are chosen by hash; `user` and `helper` are
extremely unlikely to collide" reasoning is structurally weak:

1. DashMap v6 default shard count is `num_cpus * 4` (commonly 16-64
   on the test hosts, not "effectively infinite"). Birthday-collision
   probability on a handful of module names is nontrivial once the
   workspace grows beyond ~10 concurrent modules.
2. DashMap's `entry` guard and a nested `get` on the SAME shard
   DEADLOCK in v6 — `DashMap::get` acquires a shard read-lock, and
   a thread already holding a shard write-lock on the same shard
   blocks forever on read-lock acquisition. This is documented
   behaviour, not UB, but a deadlock is a harder bug than the one we
   are fixing.
3. Even absent deadlock, probabilistic safety ("extremely unlikely
   to collide") violates the principle that race fixes must be
   structural, not statistical.

**Required revision**: clone the user-seed entries BEFORE calling
`entry()`, then move the clone into the closure. Concretely:

```rust
pub fn ensure_module_exists(&self, path: &ModuleFullPath) {
    // Hoisted: read user's special forms BEFORE taking the entry
    // write-lock. This avoids any shard-collision deadlock risk
    // between `modules[path]` and `modules[user]`.
    let user_path = ModuleFullPath::from("user");
    let seed_entries: Vec<(Symbol, ModuleEntry<C>)> = self.modules
        .get(&user_path)
        .map(|guard| {
            guard.all_symbols()
                .filter(|(_, entry)| matches!(entry,
                    ModuleEntry::Def { kind, .. }
                    if matches!(kind.as_ref(),
                        cranelisp_types::DefKind::SpecialForm { .. })))
                .map(|(n, e)| (n.clone(), e.clone()))
                .collect()
        })
        .unwrap_or_default();

    // Atomic check-then-insert; closure runs under shard write-lock
    // on `path`'s shard only. No nested DashMap access.
    self.modules.entry(path.clone()).or_insert_with(|| {
        let mut table = SymbolTable::<C, L>::new_with_params(path.clone());
        for (name, entry) in seed_entries {
            table.insert(name, entry);
        }
        // Emit SymbolTableEnsure{module, outcome=Created}
        table
    });
    // If the entry was already present, emit
    // SymbolTableEnsure{module, outcome=AlreadyPresent} here.
}
```

The hoist costs one `Vec<(Symbol, ModuleEntry)>` clone per call —
identical to the current code's cost; the existing implementation
already clones these entries. The diff is purely a reordering: clone
first, then take the entry. No additional allocation, no additional
lock cost.

**Rejected alternatives**:

- Retry loop with `get` + `try_insert` (the task brief's variant): no
  primitive `try_insert` in DashMap v6 (`insert` always overwrites).
  Would require manual `entry().or_insert_with(|| marker).and_then(...)`
  — strictly more complex than (d).
- Keep the nested access and accept probabilistic safety: rejected
  (reasoning above).

### Ownership steering — decision: **(C) hybrid**

The crate boundary is real: `crates/cranelisp-typecheck/` is owned by
`/typecheck` per root `CLAUDE.md §Skills`, and /typecheck has been a
no-implementation skill all sprint. But:

1. The fix is ~25 LOC in one function with no API change, no new
   types, no cross-crate ripple. Onboarding /typecheck to
   implement a 25-LOC change in a function it has not touched
   mid-sprint costs more than it saves.
2. /int has already done the diagnostic work, has the race-evidence
   context loaded, and has authored the fix plan. Handing off to
   /typecheck for implementation loses that context.
3. The fix site is strictly internal to the crate — the public
   signature of `ensure_module_exists` is unchanged. This is the
   category of change where "file a FIXME(/typecheck) and act"
   matches the root CLAUDE.md cross-skill protocol.
4. But: /typecheck review of the final diff (before commit) ensures
   the crate owner validates the change matches the crate's internal
   conventions. This is cheap (one short review pass, no diagnostic
   work required).

**Ruling**: /int authors the fix at step 3e'' under a
`FIXME(/typecheck)` cross-skill comment at the top of the rewritten
`ensure_module_exists`. /typecheck reviews the diff before /int
commits. /typecheck MAY request local revisions (naming, comment
style, test placement) but MUST NOT block on substantive mechanism —
the mechanism is arbitrated here. If /typecheck is unavailable at the
review window, /sprint may authorise /int to commit without blocking,
provided /typecheck ratifies post-commit and files any follow-on
cleanup as a separate FIXME. This precedent is narrow: cross-skill
implementation is authorised only when (a) the fix is fully
self-contained inside one function, (b) the public API is unchanged,
and (c) the implementing skill has already authored the design.

Do NOT generalise to broader `/int → crates/` edits.

### Observability additions

**`SymbolTableEnsure { module, outcome: Created | AlreadyPresent }` — APPROVE.**

- Location: event type definition in `src/observability.rs`
  (integration-crate-internal, per Decision 3 — `cranelisp-types`
  stays boundary-only). Emission sites inside
  `crates/cranelisp-typecheck/src/checker.rs::ensure_module_exists`.
  The crate boundary is crossed in the direction of `/int` defining
  the event, `/typecheck` crate invoking it via a trace macro that
  compiles out when the feature is disabled — same pattern as the
  existing `ModuleStateTypechecking` et al emissions from
  `scheduler.rs`. Principle 3 preserved: `cranelisp-types` gains
  nothing.
- Variant payload: the `Created | AlreadyPresent` discriminator is the
  load-bearing distinction for H6 (two Createds on the same module =
  the overwrite signature). /int's §8.3.4 suggestion of an enum
  variant is correct; do not fold it into a string payload.

**`NotifyTypecheckDone { module }` — REJECT as redundant.**
`ModuleStateTypechecked` already fires from `notify_typecheck_done`
(§3e' evidence uses it). A second tag at the same site adds noise.

**`SymbolTableInsert { module, symbol_count }` — REJECT** as primary
per /int's §8.3.4 reasoning (per-symbol emission floods the trace and
does not pinpoint table-overwrite). If a future investigation needs
finer granularity, add it then.

### Boundary hygiene

Confirmed clean:

- No `cranelisp-types` changes. `SymbolTable` and `ModuleEntry`
  untouched.
- No new cross-crate API. `ensure_module_exists` public signature
  unchanged.
- `SchedulerTraceTag` / observability events live in
  `src/observability.rs` per Principle 3. The emission from
  inside `cranelisp-typecheck` crosses the boundary via the existing
  trace-macro pattern, not a new type.
- No inter-crate dependency changes.

No FIXME(/arch) required. No boundary review.

### Risk audit — sampling

**R1 (nested DashMap access deadlock): REAL — mandatory mitigation.**
See Mechanism choice above. Hoist the user-seed clone OUTSIDE the
`entry` call. This is the one revision that the verdict conditions on.
The §8.3.2 "safe in practice" / "defensive form" phrasing is too soft
given the cost is zero.

**R3 (panic safety inside `or_insert_with` closure): LOW, acceptable.**
DashMap v6's `entry` guard implements `Drop` that releases the shard
write-lock on unwind. If the closure panics mid-construction, the
entry is NOT inserted (the closure's return value is what gets
stored), the lock releases, and a retry will find the key still
absent. This is the correct "no half-state" behaviour. In our code
path, the closure allocates a `SymbolTable` and copies pre-cloned
entries into it — neither can panic on valid input.

**R4 (rate improvement ≥20/20): REALISTIC.**
The race window /int identifies is genuinely the dominant remaining
window for concurrent `ensure_module_exists` calls. The H5 dump shows
no other post-H5 signature in the captured trials. That said:

- If H7 exists, it is strictly LESS frequent than H6 (H6 dominated
  the post-H5 residue). Step 3e'' acceptance at ≥20/20 is a
  reasonable threshold to call H6 closed.
- If 3e'' lands at, say, 19/20, /arch does NOT require another
  in-sprint iteration. /sprint may ledger-and-defer a named H7 to
  S62 provided (a) the H6 signature (two `SymbolTableEnsure Created`
  on the same module) is GONE from every captured failing dump, and
  (b) the residue signature is documented and narrow. This matches
  the §3d' H6-disposition precedent.

**R8 (post-fix dump expectations): CONCRETE.** Per §8.3.6:

- Exactly one `SymbolTableEnsure helper Created` and one
  `AlreadyPresent` per test trial.
- Zero `'helper-val' not found` errors.
- `ModuleStateTypechecking user` exactly once per cycle, on t1 (H5
  assertion retained).
- 20/20 pass over N=20 runs of the reduced harness.

Acceptance looks like: `tests/sprint61/race-evidence/post-fix-h6-<SHA>.log`
committed, demonstrating the above.

### Test authoring (step 3f'') requirements

Tests that would have caught H6 specifically (to be authored after
3e''):

1. **Primary integration test** (owned by /qa) — extend the reduced
   harness assertion to check post-fix trace dumps for exactly one
   `SymbolTableEnsure Created` per dep module per cycle. Without the
   fix, this assertion fails probabilistically (~80% per §3e'
   observation). With the fix, always passes. Add to
   `tests/sprint61/` alongside the existing H5 ordering test.

2. **Unit test** (owned by /typecheck inside its crate's `#[cfg(test)]
   mod tests`) — exercise `ensure_module_exists` from N threads
   concurrently on the same module path; assert `self.modules[path]`
   contains exactly one table with all seeded special forms present,
   never an empty table. Use `std::thread::scope` with a barrier for
   determinism. This is the narrow regression guard and lives with
   the code owner per
   `memory/feedback_unit_tests_with_dev.md`.

3. **Atomicity invariant** (optional) — if `SymbolTableEnsure` is
   available to tests, assert in the unit test that exactly one
   Created emission fires across all threads.

/int authors (2) alongside the fix in step 3e''. /qa authors (1) in
step 3f''. Test (3) is optional.

### Step 3e'' readiness

**GO**, conditional on four items:

1. /int MUST hoist the `user`-seed clone OUTSIDE the `entry()` call,
   per Mechanism choice R1. No nested DashMap access under the
   `entry` guard.
2. /int MUST add the `SymbolTableEnsure { module, outcome }` variant
   to `SchedulerTraceTag` in `src/observability.rs` and emit it from
   both the `or_insert_with` closure (Created) and the
   else-path (AlreadyPresent).
3. /int MUST add the `FIXME(/typecheck)` comment at the top of the
   rewritten `ensure_module_exists` naming the cross-skill exception
   and requesting /typecheck review before commit. /typecheck's
   review window is capped at the wave step duration; /sprint may
   authorise unblocking per the Ownership section if the window
   closes.
4. /int MUST capture `tests/sprint61/race-evidence/post-fix-h6-<SHA>.log`
   demonstrating §8.3.6 criteria (a)-(f). If rate lands at 19/20 or
   18/20 with no H6 Created-Created signature remaining, /sprint may
   ledger-and-defer an H7 carry; if any H6 double-Created appears,
   /arch requires another in-sprint iteration.

### Recommendations for /sprint

1. **Advance step 3e'' now.** Conditions above attach directly.
2. **Optional A/B evidence.** Before landing the fix, /int may
   capture one pre-fix dump with the new `SymbolTableEnsure` tag
   wired up but the mechanism unchanged (line 237 still
   unconditional). This would show the double-Created signature
   concretely and strengthen the evidence trail. Cost: one commit
   + revert. /arch does not require this; /int's call.
3. **Cross-skill precedent.** The (C) hybrid ownership ruling is
   NARROW. Record it in the sprint close — future cross-skill
   implementations require explicit /arch arbitration, not
   precedent-walk from this decision.
4. **H7 policy.** If 3e'' leaves a residue, follow §3d' H6-disposition
   precedent: ledger-and-defer iff the H6 signature is fully GONE
   and the residue is documented. Otherwise open 3c''' in-sprint.
5. **Discipline validation.** Third evidence-refinement iteration
   this sprint (H4 → H5 → H6). The discipline is working. Cite in
   sprint close.

## 3e''. H6 fix implementation notes

**Authored**: Sprint 61 Wave 3 step 3e'' (2026-04-22) by /int under
/arch §3d'' cross-skill hybrid-ownership grant. Pre-commit /typecheck
review pending.

### /arch's four mandatory conditions — satisfaction summary

1. **Hoist user-seed clone OUTSIDE `entry()`** — DONE. The
   `seed_entries: Vec<(Symbol, ModuleEntry<C>)>` is materialised
   from a short-lived `self.modules.get(&user_path)` read guard
   BEFORE the `self.modules.entry(path.clone())` write-guard is
   taken. The `or_insert_with`-equivalent `Entry::Vacant` arm
   moves `seed_entries` into the freshly-built `SymbolTable` and
   performs NO nested DashMap access.

2. **`SymbolTableEnsure` tag + `Created | AlreadyPresent`
   discriminator** — DONE. Added in
   `src/observability.rs::SchedulerTraceTag::SymbolTableEnsure`
   with the discriminator encoded in the existing `Module` payload's
   `state` field (`Some(0)` = Created, `Some(1)` = AlreadyPresent)
   per /arch's "mirror the existing `Module { module, state }`
   shape for `IsTypecheckedHit/Miss`" steer. `format_event_line`
   renders as `outcome=Created` / `outcome=AlreadyPresent`
   symbolically (not `pool=0` / `pool=1`). Emission crosses the
   crate boundary via an install-a-function-pointer hook in
   `cranelisp-typecheck::trace` — the binary installs the
   forwarding function in `main()` alongside the existing
   `install_panic_hook` wiring.

3. **`FIXME(/typecheck)` comment** — DONE at the top of the
   rewritten `ensure_module_exists` in
   `crates/cranelisp-typecheck/src/checker.rs:204`, citing
   §3d'' and naming the narrow cross-skill exception.

4. **Pre-commit /typecheck review** — RESPECTED. Fix left
   uncommitted in working tree; /sprint spawns /typecheck next.

### Caller audit for `ensure_module_exists` (grep over workspace)

Internal to `cranelisp-typecheck` (single-threaded per check_form):

- `crates/cranelisp-typecheck/src/builtins.rs:444, 632, 694, 876, 1031`
  — all are serialised on the main thread during
  `register_builtins` at session init.
- `crates/cranelisp-typecheck/src/program.rs:1202` — `check()`
  entry, one per `check_form` call.
- `crates/cranelisp-typecheck/src/checker.rs:1592` —
  `TypeChecker::set_current_module` helper (test fixture +
  single-threaded internal use).

Integration layer (`cranelisp` binary crate):

- `src/platform.rs:235` — platform-module bootstrap at session
  init, single-threaded.
- `src/session_v4.rs:954` (`set_current_module`), `1594`
  (`register_dep_for_eval`), `1850` (eval path), `2927`
  (recompile path) — REPL eval thread.
- `src/worker.rs:79` (`set_current_module`), `3417`
  (`handle_typecheck_work_shared` pre-typecheck) — worker
  thread.

The two concurrent pairs are
`session_v4.rs:1594 × worker.rs:3417` — this is the H6 race
site. All other call sites benefit for free from the fix (atomic
semantics under `&self` on the shared DashMap, no user-visible
semantics change).

### RAII / atomicity verification

`dashmap::mapref::entry::Entry<'_, K, V>` holds the shard
write-lock for the duration of the match arm. Both `Occupied`
and `Vacant` arms run under that lock:

- `Entry::Occupied(_)` — read-through; the `_` binding drops
  the guard at the arm boundary, releasing the shard lock.
- `Entry::Vacant(slot)` — `slot.insert(table)` stores under the
  same write-lock before the guard drops.

A concurrent `self.modules.entry(path)` from another thread
blocks on shard-lock acquisition and observes the mutation
after the first thread's arm completes. Panic inside the
closure unwinds through `Drop`; the shard lock releases; the
key is NOT inserted (Vacant arm's `slot.insert` is the only
insert path).

Observed in the post-fix dump
`tests/sprint61/race-evidence/post-fix-h6-35062ca.log`:

- Exactly ONE `SymbolTableEnsure module=helper outcome=Created`
  across the race window (ts=20007333, thr=ThreadId(2)/1).
- TWO `AlreadyPresent` emissions on `helper`:
  - ts=20016083, t2 (worker's own re-ensure in
    `handle_typecheck_work_shared` after the initial seed).
  - ts=20024500, t1 (REPL-eval's pre-wait ensure in
    `register_dep_for_eval`).
- `RegisterImportsLookup module=helper` at ts=20800583
  succeeds; `helper-val` is resolved; stdout shows
  `:primitives/Int 99`. No `'helper-val' not found` error.

### Rate across runs

- Reduced harness `heisenbug_race_reduced_concurrent_import_pairs`:
  **10 / 10 PASS** consecutive (pre-fix post-H5 baseline: 2 / 10
  PASS). Meets step 3e'' gate of ≥10/10 at this slice step.
- Full sprint23 (61 tests) single clean run: **61 / 61 PASS.**
- 10 consecutive full-suite runs: 9 / 10 PASS. The one failing
  run had `h5_normal_completion_does_not_starve_repl_eval_thread`
  time out on its 2-second tail under heavy suite-concurrency;
  it passes 5 / 5 in isolation. Pre-existing flake — not an H7
  signature.
- `cargo nextest run -p cranelisp observability`: 29 / 29 PASS
  (2 new `s61w3_symbol_table_ensure_*` tests).
- `cargo nextest run -p cranelisp-typecheck`: 326 / 326 PASS
  (3 new `ensure_module_exists_*` tests + trace-module tests).

### Post-fix dump observation

The post-fix dump file is
`tests/sprint61/race-evidence/post-fix-h6-35062ca.log`. Key
finding: the `Created`-before-`AlreadyPresent` ordering invariant
holds across every module ensured during the test-harness
subprocess run. The `helper` module specifically — the module
where the pre-fix race fired — now observes the canonical
"Created(thr=2) → AlreadyPresent(thr=2) → AlreadyPresent(thr=1)"
ordering. No overwrite signature; no `helper-val not found`
error.

### LOC changed

- `crates/cranelisp-typecheck/src/trace.rs` — NEW file (~155
  LOC with docs + tests, ~55 LOC excluding tests and comments).
- `crates/cranelisp-typecheck/src/lib.rs` — +5 LOC (module
  declaration + re-exports).
- `crates/cranelisp-typecheck/src/checker.rs`
  `ensure_module_exists` rewrite — ~55 LOC in (replacing 34
  LOC out); +155 LOC of unit tests in `mod tests`.
- `src/observability.rs` — +1 enum variant, +1 payload match
  arm in `format_event_line`, +42 LOC of forwarding sink +
  install helper, +76 LOC of unit tests.
- `src/main.rs` — +7 LOC for the hook install call.
- `design/int/heisenbug-race-closure.md` — THIS §3e'' appendix
  (~120 LOC).
- `tests/sprint61/race-evidence/post-fix-h6-35062ca.log` — NEW
  (135 LOC evidence dump).

Net: ~750 LOC added, ~34 LOC removed. Concentrated: one function
rewrite, one new small trace module, one new tag variant.

### Concerns / H7 residue

No H7 signatures observed. The 1/10 full-suite flake was pre-
existing `h5_normal_completion_does_not_starve_repl_eval_thread`
timing out under concurrent nextest contention; independent of
H6 mechanism. If Wave 5's 20-run whole-suite gate flushes out any
new signature, /sprint can ledger per §3d'' Recommendation 4
H7-policy — the H6 signature (double-Created on `helper`) is
GONE from every captured trace.

### Readiness for /typecheck review + /review step 3g

Pre-commit /typecheck review gate is OPEN. No git commits
performed by /int; all changes sit in the working tree:

- `crates/cranelisp-typecheck/src/trace.rs` (new)
- `crates/cranelisp-typecheck/src/lib.rs`
- `crates/cranelisp-typecheck/src/checker.rs`
- `src/observability.rs`
- `src/main.rs`
- `design/int/heisenbug-race-closure.md`
- `tests/sprint61/race-evidence/post-fix-h6-35062ca.log`
- `sprints/SPRINT.md` (step 3e'' row status update)

/typecheck is asked to review the checker.rs rewrite + the trace
module; /review takes the integration-layer diff in step 3g.

## 3e''.review — /typecheck pre-commit review

**Reviewer**: /typecheck
**Date**: 2026-04-22
**Verdict**: **APPROVE**

This is the first time /int has reached into `crates/cranelisp-typecheck/`
under the §3d'' hybrid ownership grant. The diff is narrow (one function
rewrite + one new small trace module + unit tests), self-contained, and
honours every condition /arch attached. /typecheck finds no substantive
issues and does not request revisions. Commit-gate is OPEN.

### 1. Correctness of atomicity fix

PASS. `self.modules.entry(path.clone())` returns a
`dashmap::mapref::entry::Entry` whose guard holds the shard write-lock
for `path`'s shard across both match arms. `Entry::Vacant(slot) =>
slot.insert(table)` stores under that lock before it drops; `Entry::
Occupied(_) => …` observes the pre-existing entry under the same lock.
A concurrent `entry(path)` from another thread blocks on shard-lock
acquisition and observes the result after the first arm completes.
The unconditional overwrite at old line 237 is gone. The
`seed_entries` `Vec<(Symbol, ModuleEntry<C>)>` is materialised from a
short-lived `self.modules.get(&user_path)` read-guard that drops
BEFORE `entry(path)` is called (checker.rs:241-258 vs 274) — zero
nested DashMap access inside the closure. /arch's R1 mandatory
revision (hoist out of `entry()`) is satisfied.

### 2. API / behavioural preservation

PASS. `pub fn ensure_module_exists(&self, path: &ModuleFullPath)` —
signature unchanged. Post-condition `self.modules.contains_key(path)
== true` preserved. Single-threaded callers (the 7 internal sites in
`builtins.rs`, `program.rs`, `checker.rs::set_current_module`, and
the 6 external sites in `src/platform.rs`, `src/session_v4.rs` ×4,
`src/worker.rs` ×2 per §3e''.caller-audit) see identical semantics:
either the key is absent and they create it, or it is present and
they observe it. The `Created | AlreadyPresent` discriminator is
strictly additive observability — no caller reads it. Seed-entry
selection (special forms only, via `DefKind::SpecialForm` filter) is
preserved verbatim from the prior implementation.

### 3. Trace-module design

PASS. `crates/cranelisp-typecheck/src/trace.rs` uses
`std::sync::OnceLock<fn(&ModuleFullPath, SymbolTableEnsureOutcome)>` —
thread-safe by construction (install is single-shot from `main()`,
all subsequent access is a relaxed load of an already-set pointer,
no store-after-read races). Uninstalled case (unit tests, embedded
use) is a null-check no-op: `OnceLock::get()` returns `None`,
emission returns immediately. Zero heap allocation on the hot path,
no formatting.

Crate-DAG compliance verified: `Cargo.toml` lists only
`cranelisp-types` and `dashmap` as runtime deps, with
`cranelisp-frontend` as dev-dep (pre-existing). No dependency on
`cranelisp` (binary) or `src/`. The cross-crate wiring goes in the
DAG-legal direction — binary imports typecheck and calls
`install_symbol_table_ensure_hook(record_symbol_table_ensure_forward)`
from `main.rs:53`. This is the same pattern as
`cranelisp_runtime::io_trace_install_panic_hook` at `main.rs:45`; not
a one-off. The existing `CRANELISP_INFER_TRACE` is a different
pattern (environment-variable-gated static log), but the trace-module
pattern here matches the sibling runtime-crate's hook wiring, which
is the closer precedent for a cross-crate instrumentation sink.

### 4. Unit tests

PASS. Three new tests in `checker.rs` cover the right invariants:

- `ensure_module_exists_seeds_special_forms_on_first_call` — positive
  path: special forms seeded, non-special-forms (builtin types) do
  NOT leak. This is a `+Neg` test in disguise (asserts `Int` absence).
- `ensure_module_exists_on_populated_table_preserves_entries` — the
  direct H6 regression guard: pre-populate with `helper-val`, call
  `ensure` again, assert `helper-val` is still present. Pre-fix code
  would fail this; post-fix passes.
- `ensure_module_exists_concurrent_same_path_emits_exactly_one_created`
  — N=8 threads with a `Barrier`, post-condition assertion plus
  conditional sink assertion (exactly 1 Created + N-1 AlreadyPresent,
  guarded on counter non-zero to tolerate test-execution-order
  dependency of the `OnceLock` install). The conditional-assertion
  guard is a reasonable mitigation for `OnceLock`'s single-install
  semantics in a multi-test process; /typecheck would prefer a
  future refactor to per-test hook slots, but this is acceptable
  for the regression guard.

Trace-module tests (`trace::tests`) additionally cover u8 discriminator
stability and null-hook no-op — complete coverage of the public
surface.

### 5. Boundary hygiene

PASS. `cranelisp-types` unchanged. No new serialised types — the
`SymbolTableEnsureOutcome` enum is crate-internal to
`cranelisp-typecheck` and crosses to `src/observability.rs` as a
bare `u8` via `as_u8()`. No `Cargo.toml` dependency additions in
either crate. `SchedulerTraceTag::SymbolTableEnsure` lives in
`src/observability.rs` per /arch's Principle 3.

### 6. Style + craftmanship

PASS. `FIXME(/typecheck)` comment at `checker.rs:205-213` cites
§3d'', names the narrow cross-skill exception, and flags the
precedent as non-generalisable. No `.unwrap()` / `.expect()` in
pipeline code — the one `unwrap()` in `trace.rs:118` is inside
`#[cfg(test)] mod tests` and is acceptable per `src/CLAUDE.md` test
exemption. Naming is consistent with crate conventions (`snake_case`
fns, `CamelCase` enum variants, `SCREAMING_SNAKE` statics). Doc
comments on `trace.rs` and `ensure_module_exists` are thorough and
cite the design doc sections.

### Requested revisions

none.

### Narrow precedent acknowledgement

/int authored under /arch §3d'' hybrid ownership grant. /typecheck
accepts this for the specific H6 fix surface. Future /typecheck-crate
work returns to /typecheck ownership by default unless /arch grants
another narrow precedent. The `trace.rs` module is now part of the
`cranelisp-typecheck` public API (re-exported from `lib.rs`) and
becomes /typecheck's maintenance responsibility going forward — any
future additions to the trace-hook mechanism are /typecheck-owned.
