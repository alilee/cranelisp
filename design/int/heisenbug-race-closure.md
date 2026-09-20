# Heisenbug race closure — the S61 per-interleaving lineage

> **SUPERSEDED AS THE FIX STRATEGY (S93).** This is the **tactical lineage**
> (H4→H5→H6→H7): a treadmill of per-interleaving patches, each closing one
> window while the race resurfaced through the next. With `eval_in_flight`
> deleted (S78) and the ensure-a-module-table operation already atomic (H6),
> the race still fired ~5–10% under contention — evidence that the failure was
> **structural**, not a sequence of isolated micro-bugs. The live cure is the
> signature/body pre-pass barrier: **`design/int/signature-body-prepass.md`**
> (arch-blessed, `design/arch/bounded-contexts.md` §6 +
> `design/arch/sequences/concurrency-dependency-service.mmd`), and
> the in-call-stack cluster model in `design/int/int.md` §6.2 that
> removed the shared re-read surface entirely.

**Owner**: `design` (int). **Status**: reference lineage — evidence and
precedent, never current design intent. **Origin**: Sprint 61 Wave 3.

## How to read this record

Retained for three uses, in order of value:

1. **Precedent** — what a per-interleaving cure costs, and what evidence is
   required before one is believed. The next race-class investigation starts
   here and at `tests/plan/s109-attribution-index-feed-race.md`.
2. **Rationale for live instruments** — `SchedulerTraceTag::SymbolTableEnsure`
   and the typecheck-side trace hook follow the [instrument rationale](#834-the-instrument--symboltableensure)
   and [H6 ruling](#3d-arch-verdict-h6--retained-rulings); the
   regression guards in `crates/cranelisp-typecheck/src/checker/tests.rs` and
   `tests/repl_persist_race.rs` exist because of §8.3 and §3b.
3. **Falsification record** — three code-plausible hypotheses (H1–H3) and one
   evidence-backed one (H4) were all falsified by dumps before H5/H6 landed.

**Section numbers are pinned.** Live source comments, test plans and neighbour
designs cite `§3b`, `§7.7`, `§7.8`, `§7.10`, `§8.2`, `§8.3`, `§8.3.4`, `§3d'`
and `§3d''`. The gaps in the numbering are deliberate: the abandoned
investigation plans, per-step readiness notes and process narration those
numbers once carried were removed in the S122 consolidation (recoverable from
Git). Loci are named by symbol, not line, because line citations rot.

## 1. Problem

A REPL session that imports a helper module intermittently reported
`'helper-val' not found in module 'helper'` / `undefined variable: helper-val`
under parallel test pressure — a reader observing a module's scheduler state as
"typecheck done" and then failing to find symbols the writer had published (or
had had clobbered). Pre-reduction fire rate ~30% under full-suite pressure;
Sprint 60 Round 5 reduced but did not eliminate it.

Three hypotheses were framed from code reading — a too-permissive
`is_typechecked` predicate (H1), symbol publication outside the critical
section (H2), and pool-state transition before publication (H3). **All three
were falsified by the event dumps.** The mechanism was in neither the predicate
nor the publication ordering: it was *two orchestrators acting on the same
module*, then an *unconditional table overwrite*. This is the record's first
lesson — a hypothesis that merely explains the symptom is not evidence.

## 3b. The reduced repro

`heisenbug_race_reduced_concurrent_import_pairs` (now in
`tests/repl_persist_race.rs`) — 6 concurrent OS threads, each running 2
sequential `(session 1 → delete cache → session 2)` pairs, inside a 10-trial
loop that fast-fails on first reproduction. Fired ~86% per test run in ~1 s
wall-time against the pre-fix tree, with the baseline signature verbatim.

Two properties made it useful, and both are the transferable part:

- **It needed no production hooks.** The reduction was achieved by test-harness
  shape alone — no `#[cfg(test)]` seams were cut into the scheduler or worker.
- **It fast-fails.** A repro that reproduces in ~1 s and stops at the first hit
  is what makes `CRANELISP_SCHEDULER_TRACE=1` dump capture practical; a 30%
  full-suite flake is not an instrument.

The race is session-1-side: session 2 recompiles (its cache is deleted), so the
cache-hit path is not exercised by this shape.

## 3c. Evidence artefacts

Committed under `tests/sprint61/race-evidence/` — paired failing/passing
scheduler-trace dumps, merge-sorted across threads at dump time per
`design/int/observability.md`. They are the irreplaceable part of this record:
the prose below summarises them, and any re-reading of the lineage should
prefer the dumps.

## 7.7 H4 falsified by its own post-fix dump

H4 (a duplicate publish/register pair on the dep module opening a claim window)
was approved on evidence, landed, and **falsified by the post-fix dump**: the
duplicate pair was gone — the gate fired on the hot path — and the failure rate
was unchanged at 10/10 trials.

What the falsification bought: with the duplicate-pair noise removed, the true
interleaving became legible for the first time. H4's gate was correctness- and
observability-positive and stayed in the tree; its *mechanism attribution* was
wrong by one module and one scheduler phase.

**Lesson**: a fix that removes a real defect can leave the rate untouched. Rate
is the acceptance criterion; mechanism plausibility is not.

## 7.8 H5 — the worker claims the caller the eval thread already owns

Mechanism, from the dump: `notify_typecheck_done(helper)` invokes
`try_unblock_locked(user)`, which pushes `user` into the prioritised typecheck
queue. The *same* persistent worker that just completed `helper` pops `user`
~3.5 µs later and runs its import handling — while the REPL-eval thread is
still parked in `wait_module_inmem_complete_blocking(helper)` and will drive
`user`'s retry itself the moment it wakes (observed 132 ms later). Both threads
then read `symbol_tables[helper]`; the losing one reports the missing symbol.

The dump pins this directly: `ModuleStateUnblocked user` and
`ModuleStateTypechecking user` on the worker thread, then the worker's failing
lookup and `ModuleStateFailed user`, with the eval thread's own lookup arriving
55 µs after the failure.

**The invariant H5 names**: the REPL-eval thread is the authoritative driver of
its caller module's post-unblock retry. A worker-driven typecheck of that
module in parallel is a pure duplicate — no correctness need, only a race.

## 7.10 H6 — non-atomic ensure-module-exists overwrote a populated table

Mechanism: the ensure-a-module-symbol-table operation was a non-atomic
check-then-insert. Between the `contains_key` check and the unconditional
`insert`, it built a fresh `SymbolTable` and walked `user` for special-form
seed entries — a ~15-line window. When the eval thread and a worker both
ensured the same module, the eval thread's `insert` **overwrote the worker's
already-populated table with an empty one**. The reader then woke, found the
table present, and missed the symbol.

Two rejections inside H6 matter more than the fix:

- **Not memory ordering.** The shard `RwLock`s already supply release-acquire;
  the earlier informal "memory-ordering" attribution was falsified. This was a
  compare-then-set hazard at `SymbolTable`-aggregate granularity.
- **Uniquely attributable by code path.** The ensure site was the only place in
  the workspace that unconditionally replaced an outer `SymbolTable` on a
  possibly-populated key; every other write mutates the existing table's inner
  map. The dump alone could not observe the overwrite — there was no tag on the
  ensure site — so the pin rested on inspection plus elimination, and §8.3.4
  added the instrument that closes exactly that gap.

## 8.2 H5 cure — push-side suppression (landed S61, retired S78)

An `eval_in_flight` flag on the scheduler's per-module state, set by an RAII
guard around the eval thread's dep wait, gating the push into the prioritised
queue inside `try_unblock_locked`.

**Push-gate over pop-filter** (§3d' ruling): suppress at the transition rather
than filter at the pop, because the push site is where the per-module invariant
lives, the queue never holds a module nothing may claim (so queue introspection stays
truthful), and the reason for the suppression is visible to the next reader of
the transition.

**Status: retired.** S78's in-call-stack cluster model keeps a caller's
in-progress state on the eval thread's own stack frame, so no worker can
observe it and there is no race for the gate to suppress; `register_dep_for_eval`
records the deletion. What survives is the reader-side trace tag
(`RegisterImportsLookup`) that made the interleaving visible, and the ordering
invariant it witnesses.

**Live successor rule** — *every* dep-registration site registers with
`delays_other = true`; only a caller that is itself the whole-world waiter
registering its own entry module uses `false`. Canonical in
`design/int/int.md` §6.1.

## 8.3 H6 cure — atomic ensure, and its regression guard

The check-then-insert was replaced by a single atomic entry operation whose
closure runs only when the key is absent and runs under the shard write lock.
The unconditional overwrite is gone; observers see the same post-condition
(the module's table exists after the call), and the change was internal — no
public signature, no boundary, no `cranelisp-types` shape change.

**One mandatory revision from `/arch` (§3d''), and it is the reusable part**:
the `user`-seed clone is materialised from a short-lived read guard *before* the
write guard is taken. Nested access to another key while holding an entry guard
was rejected on principle — "different keys are almost certainly different
shards" is probabilistic safety, and the deterministic form cost nothing.

**Current locus**: the atomic operation and its `EnsureOutcome` now live in
`cranelisp_types::ensure_module_exists`; `cranelisp-typecheck`'s `TypeCheckEnv`
calls it and forwards the outcome to the trace hook. The regression guard is
the concurrent-ensure unit test in
`crates/cranelisp-typecheck/src/checker/tests.rs` — N threads ensuring one path
must leave exactly one table with its seeded special forms intact, never an
empty one.

### 8.3.4 The instrument — `SymbolTableEnsure`

A table-level tag with a `Created | AlreadyPresent` discriminator, emitted at
both arms of the ensure operation. Approved because it makes the H6 signature
directly falsifiable: **two `Created` on one module in one trial is the
overwrite; post-fix there is always exactly one `Created` and one
`AlreadyPresent` per dep module per cycle.**

Two alternatives were rejected, and the reasoning generalises:

- **A per-symbol `SymbolTableInsert` tag** — rejected. Dozens of emissions per
  module across the passes; it floods the trace and cannot discriminate a
  table-overwrite from ordinary publication. The instrument must sit at the
  granularity of the hazard.
- **A second tag at `notify_typecheck_done`** — rejected as redundant with the
  existing `ModuleStateTypechecked` emission at the same site.

The discriminator stayed an enum rather than a string payload because it is the
load-bearing distinction, not a label.

**Crate crossing**: `/int` defines the event in `src/observability.rs`;
`cranelisp-typecheck` emits through an install-a-function-pointer hook
(`cranelisp_typecheck::trace::install_symbol_table_ensure_hook`), installed by
the binary at startup. Typecheck does not depend on the binary crate, and the
cost with no sink installed is one relaxed load plus a null check. This is the
documented pattern for any future typecheck-side trace emission
(`design/typecheck/typecheck.md`).

## 3d'. `/arch` verdict (H5) — retained rulings

- **Push-gate over pop-filter**, for the four reasons in §8.2.
- **RAII, not paired calls.** The flag's only setter is the guard constructor
  and its only clearer is the destructor, which makes "forgot to clear"
  structurally impossible and covers unwind. The one pathological leak path — a
  dep that never completes — leaves the flag set, but suppressing worker claim
  of a module that cannot progress anyway is correct behaviour there; the
  starvation is a symptom of the hang, not caused by the gate.
- **Absence-of-starvation is its own test.** A guard whose failure mode is an
  infinite block needs a normal-completion test with a wall-clock ceiling, and
  the ceiling must be ≫ typical (set at ~30× observed worst case) so a
  contended machine is never mistaken for a leaked flag. Carried forward as
  `tests/repl_persist_race.rs::h5_normal_completion_liveness_yields_dep_value`.
- **Audit every caller of the primitive the guard wraps** before landing: a
  second caller driving post-unblock retries without the guard would make the
  design incomplete.

## 3d''. `/arch` verdict (H6) — retained rulings

- **Mechanism**: atomic entry operation, with the seed clone hoisted outside
  the write guard (mandatory, see §8.3).
- **Observability**: `SymbolTableEnsure` approved with the enum discriminator;
  the per-symbol and duplicate-site tags rejected (§8.3.4).
- **Ownership steering — hybrid, and narrow.** The design owner authored a
  ~25-LOC fix inside another crate's code, with the crate owner reviewing the
  diff before commit and permitted to require local revisions but not to
  re-arbitrate the mechanism. The precedent is explicitly limited to a change
  that is (a) self-contained in one function, (b) public-API-unchanged, and
  (c) designed by the implementing role. **Do not generalise it** to broader
  cross-surface edits; today's route for such a change is a filing to the
  owning role through `sprint`.
- **Test authoring**: (1) an integration assertion over the post-fix dump —
  exactly one `Created` per dep module per cycle, which fails probabilistically
  without the fix; (2) the narrow concurrent-ensure unit test beside the code it
  guards; (3) optionally, the same one-`Created` assertion from inside the unit
  test. (2) and (3) landed together as
  `crates/cranelisp-typecheck/src/checker/tests.rs::ensure_module_exists_concurrent_same_path_emits_exactly_one_created`.
- **Acceptance was rate-based**: 20/20 consecutive passes of the reduced repro,
  plus the dump signature — not "the suite is green".

## 9. What the lineage teaches

- **A per-interleaving cure predicts its own successor.** Three cures landed,
  each correct, each rate-improving, and the race survived all three until the
  shared re-read surface itself was removed (S78) and the phase ordering was
  made structural (S93). When the second cure in a family is needed, the
  question stops being "which window is open" and becomes "why is this state
  shared at all".
- **Evidence gating worked exactly once per hypothesis.** Every hypothesis that
  was pinned by code reading alone was wrong or mis-localised; every one pinned
  by a merge-sorted dump held. Where the dump could not observe the mechanism
  (H6), the fix shipped the instrument that would have.
- **The instrument must sit at the hazard's granularity**, and its signature
  must be a *count* a reader can falsify (two `Created`), not a narrative.

## Cross-references

- `design/int/signature-body-prepass.md` — the S93 structural cure that
  supersedes this whole approach.
- `design/int/int.md` §6.2 — the in-call-stack cluster model that
  removed the shared re-read surface these races lived on.
- `design/int/index-worker-isolation.md`, `design/int/prelude-table-write-isolation.md`
  — the isolation-by-construction successors in the same lineage.
- `design/int/observability.md` — the trace sinks and dump-time merge-sort.
- `design/typecheck/typecheck.md` — the typecheck-side trace hook as the
  crate's documented observability mechanism.
- `tests/plan/s109-attribution-index-feed-race.md` — `qa`'s reading of this
  treadmill as attribution precedent.
- `tests/sprint61/race-evidence/` — the dumps.
