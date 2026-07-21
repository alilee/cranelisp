---
number: 0604
target: /dev (src — S115 instrumented run; escalation path /dev(typecheck) per
  the trace, see the S114 re-attribution section)
re_scoped_from: /qa (S114 pre-W7 disposition, folding /review's 0698) ←
  /dev (S110 — per contract §4; see "S110 /dev disposition" below)
filed_by: /qa
filed_at: 2026-07-15
sprint_filed: 109
scheduled: S115 (early wave — front-load; 3-sprint carry, escalation flag for
  /sprint Phase 1)
refers_to: src/worker.rs::commit_staging_to_live (:439; `live.insert` :513 —
  the census-missed suspected writer) + src/imports.rs census block +
  check_terminal_closure/write_is_closure_valid (landed 58ac8e46 — predicate
  provably passes the live phantom) + design/int/prelude-table-write-isolation.md
  §2.2 (false premise + census + check shape — /design(int) correction rides
  the fixing wave); poison-consumer (CORRECT, do not touch) at
  src/imports.rs::insert_detecting_ambiguity ~L547-560.
status: open
---

# Phantom undeclared-PUBLIC `bit-and` entry in prelude's live table (S114: foreground writer, deterministic on this VM; formerly "index-feed write-race")

## /dev(src) S115 W2 change-set LANDED (2026-07-21 — the structural gate; retirement is /qa's call per the re-based plan)

The structural gate landed on its merits (writer-ID desired-not-required). What
landed:

- **Corrected predicate** (`src/imports.rs::write_is_closure_valid` +
  `check_terminal_closure`): provider-existence → **declared-export closure**
  keyed on the DESTINATION `D(M)`. `check_terminal_closure` no longer reads
  `symbol_tables`; its new param is `declared_exports: Option<&HashSet<Symbol>>`.
  Arms: own-def (non-`Import`) → Ok, NO map read; **intra-module self-alias**
  (`Import` whose `source.module == M`, e.g. a bare ctor alias
  `ZedC → prelude/Zed.ZedC` to the module's own canonical `Type.Ctor`) → Ok, NO
  D read (it is the module's own entry, §8.4 — this arm was ADDED after the first
  full-suite run false-fired 6 prelude/trait tests on legitimate self-aliases);
  cross-module public re-export → valid iff `name ∈ D(M)`; `D(M) == None`
  (unknown) → permit (never false-fire). The phantom `bit-and → primitives/bit-and`
  is cross-module (`primitives ≠ prelude`) with `bit-and ∉ D(prelude)` → rejected.
- **`SharedState.declared_exports: DashMap<ModuleFullPath, HashSet<Symbol>>`**
  (int-internal, unserialized, `prelude_fallback` model — no types/schema/
  public-api impact). Populated at the `install_exports` seam from the resolved
  export-spec names (foreground path threads `ctx.shared_state`; the background
  index path passes `None`, R13). SharedState field-count guard bumped 16→17.
- **`commit_staging_to_live` ROUTED** (the S114-missed census row): `D(module)`
  precomputed BEFORE the `get_mut` guard (a read of the SEPARATE map — deadlock
  hazard honored), each staged entry gated before `live.insert`; rejection
  propagates through the existing `Result`. Census table (`src/imports.rs`)
  updated with the `commit_staging_to_live` row.
- **MODULE_TRACE + diagnosed error** at the seam (self-identifies as an internal
  R7 breach naming module/name/source edge; `Span::SYNTHETIC`).
- **Falsified-comment rider**: the `prelude_write_is_closure_valid` "bit-and …
  absent from primitives" comment corrected (bit-and IS a bundled primitive; the
  legacy prelude-only rider stays a debug tripwire). The existing chokepoint unit
  test's fixture comment corrected in the same file.
- **Tests** (`src/imports/tests.rs` + `src/worker/tests.rs`): the synthesized
  provides-name-but-outside-declared-exports trigger (RED under provider-existence,
  GREEN under the correction — RED-on-revert demonstrated); false-fire fence
  (name ∈ D permits); unknown-D permit; and the `commit_staging_to_live` routing
  reject + permit pins. The two GREEN twins
  (`tests/spec_08_prelude_outer_scope.rs`) stay GREEN.
- **Behavioural**: deterministic recipe 0/30 fires vs real stdlib (no regression;
  no false-fire on the real prelude). ONE time-boxed load-amplified attempt: 0
  fires across 496 concurrent runs (60s) — quiet, abandoned without prejudice.

Retirement of this file is deferred to /qa per the re-based plan (writer
identification is desired, not required; the landed MODULE_TRACE + diagnosed
error name any future firing's seam).


## /qa S114 Phase-6b re-base (2026-07-20 — folds /stdlib FIXME 0713, now deleted; AMENDS the pre-W7 plan's step 1)

**The 25/25 determinism EVAPORATED at HEAD.** /stdlib (Phase 6a, FIXME 0713)
measured the deterministic recipe at HEAD `31101126` (debug binary rebuilt at
HEAD, this VM): **0 fires across 85 runs** (25 exact-recipe + 25 with-main +
30 exact-recipe; every run reaches the clean import, residual error only the
expected `entry module has no 'main' function`). The num.bits self-test is
stable 27/27 across 5 runs. The FIXME's own "preserve THIS record even if the
VM state drifts" instruction is now active: **the drift has occurred.** Fire
history is now: /sprint S109 16/16 → /testing S109 0/140 → /dev S110 0/~175 →
/dev S114-W5 25/25 → S114-6a **0/85**. The S114 carrier/settlement window is
the suspected perturbation (the same window shifted the ctor-as-value crash
[0712, verified fixed] and the 0694 load-flap) — but suppressed-by-timing vs
incidentally-fixed is UNDECIDABLE from quiet sweeps (that evidence class is
spent; ~320 cumulative no-fires before W5 already proved quiet runs prove
nothing).

**Re-based S115 plan (supersedes "a single instrumented run" in step 1
below — the one-run-names-it assumption no longer holds):**

1. **The structural gate lands ON ITS OWN MERITS, not gated on a firing.**
   /dev(src, narrow int): disposition the missed census row
   (`commit_staging_to_live`, src/worker.rs:439/:513 — route through the
   chokepoint or a named legal-skip with rationale), and land the corrected
   **declared-export-closure** predicate (provider-existence is structurally
   unable to catch the live defect) as an unconditional diagnosed error at
   the chokepoint, honoring the deadlock hazard (precompute the closure; no
   map read under the `get_mut` guard). `MODULE_TRACE` emission at the seam
   rides the same change-set — the instrumentation is the OBSERVABILITY
   deliverable (any future firing names its writer), not the ship gate.
2. **The guard rides a SYNTHESIZED trigger, not the dead recipe.** /testing:
   a unit test at the corrected predicate that INJECTS an out-of-closure
   public write at the chokepoint and asserts the diagnosed error
   (fail-on-revert by construction, interleaving-independent). The 25/25
   recipe demotes to a bounded behavioural sweep (≥25×, expect 0-fire — a
   no-regression check, NOT the acceptance gate).
3. **A load-amplified recipe attempt is bounded, not open-ended**: one
   time-boxed /testing attempt to re-induce the fire (suite-load
   concurrent-compile pressure alongside the recipe, per the 0694
   load-flap mechanism), abandoned without prejudice if quiet — the
   structural gate does not wait for it.
4. Acceptance re-based: census CLOSED including `commit_staging_to_live`;
   corrected predicate unconditional + unit-pinned (injected trigger); twin
   guards GREEN; /design(int) §2.2 correction + fixture-comment correction
   ride the wave. Writer identification is DESIRED (via the landed trace, if
   it ever fires again), no longer REQUIRED for this file to retire.

Disposition record: `tests/plan/s114-test-plan.md` §12 item 4.

## /qa S114 pre-W7 re-attribution (2026-07-20 — PLAN OF RECORD; folds /review FIXME 0698, now deleted)

**Supersedes the S114 Phase-3 section below.** The W5 change-set `58ac8e46`
(C3 chokepoint + census) produced MAJOR re-attribution evidence, previously
durable only in that commit message; scribed here per 0698 finding 1.

### The corrected model

1. **The old premise is FALSE.** This file's root-cause section below says
   "no stdlib module re-exports `bit-and`" as if no legitimate provider
   path existed — but `bit-and` IS a bundled primitive: a genuine provider
   (`primitives/bit-and`) exists. Consequence: **any provider-existence
   check passes the defect by construction.**
2. **The phantom is an UNDECLARED-PUBLIC entry**: a public
   `bit-and → primitives/bit-and` entry in prelude's LIVE table that is
   outside prelude's DECLARED export closure. **The correct check is
   declared-export closure, not provider-existence.** The landed
   `write_is_closure_valid` gate is therefore structurally unable to catch
   the live defect (disclosed in the W5 commit; 0698 finding 3).
3. **It bypasses all four routed src/ install seams** (install_exports,
   install_imports, insert_cluster, defmacro register — all verified
   routing through the chokepoint). **The W5 census MISSED
   `commit_staging_to_live`** (src/worker.rs:439; `live.insert` at :513) —
   the staging→live commit that writes every typecheck-staged entry
   (including public Defs) into the live table, and the very seam the
   evidence names as the suspected writer. Until that seam is dispositioned
   (route through the gate or a named legal-skip with rationale), the
   census cannot support its closure claim (0698 finding 2).
4. **THIS VM reproduces 25/25 deterministically.** Environment fingerprint:
   the S114 W5 /dev environment = the current project VM (aarch64 Linux,
   kernel 7.0.0-27-generic), debug build at `58ac8e46`-era HEAD, recipe =
   §"Deterministic repro recipe" below (`--run --no-cache` vs the workspace
   stdlib). Contrast history: /sprint S109 env 16/16; /testing S109 0/140;
   /dev S110 env 0/~175. The determinism is the single most valuable asset
   this defect has ever had — preserve THIS record even if the VM state
   drifts.

### Next investigative step (S115, front-loaded — a single run, not a hunt)

1. **/dev(src, narrow int)**: add `MODULE_TRACE` emission + the
   declared-export-closure check (diagnostic tier first) at
   `commit_staging_to_live`, dispositioning the missing census row
   (route-or-legal-skip); then run the deterministic recipe ONCE with
   `CRANELISP_MODULE_TRACE=1` — 25/25 determinism means one run names the
   writer of the phantom entry and its origin.
2. **Attribution fork, decided by the trace**: if the phantom entry arrives
   in staging via typecheck's staging population, the defect is
   **cross-crate** — attribution moves to /dev(typecheck) with the trace as
   the brief; if the write is session-side (src/), it stays /dev(src).
3. **Predicate correction lands with the fix**: provider-existence →
   declared-export closure. Forward hazard (0698): the
   `form_dispatch.rs::register_macro_in_module` gate call runs under a held
   `get_mut` guard and is safe ONLY because the current predicate does no
   map read for non-Import entries — a declared-export-closure check that
   reads the target module's own declared exports would DEADLOCK there
   (DashMap re-entrancy). Precompute/pass the export closure; no map read
   under the guard.
4. **Doc + fixture corrections ride the fixing wave**: /design(int)
   corrects `prelude-table-write-isolation.md` §2.2 (false premise,
   check-shape, census — add the staging-commit + defmacro-register rows);
   /testing corrects the counterfactual comment on
   `imports/tests.rs::check_terminal_closure_rejects_out_of_closure_public_write`
   ("primitives has NO bit-and" — mechanics valid, comment false).

### Amended acceptance (replaces the S114 §4 gate)

Census CLOSED including `commit_staging_to_live`; corrected
declared-export-closure predicate at the chokepoint (unconditional
diagnosed error, deadlock hazard honored); writer identified via the
deterministic recipe and fixed at its owning crate; the 25/25 recipe flips
to 0-fire ≥25× on THIS VM; twin guards GREEN; unit test at the corrected
predicate; /design(int) + fixture-comment corrections landed. Then this
file retires.

Disposition record: `tests/plan/s114-test-plan.md` §11 item 1.

---

## /qa S114 Phase-3 plan of record (2026-07-20 — SCHEDULED TO SHIP; user approved Phase 1)

**Supersedes the S113 observability-rider plan below as the plan of record.**
Full attack plan: `tests/plan/s114-test-plan.md` §4.2 (Track C). Summary:

1. **The ship gate is STRUCTURAL, not a flip** (still no stable RED — the
   sanctioned exception stands): /dev(src, narrow int surface) lands (a) a
   complete FOREGROUND writer census (`src/imports.rs` installers,
   `src/process_form/`, `src/worker.rs` — every seam that can insert a
   PUBLIC entry into a live module table routes through one chokepoint or
   carries a named legal-skip; seed = `prelude-import-convergence.md` §3.4),
   and (b) a **terminal-table freeze / export-closure gate at that ONE
   chokepoint**, promoting the S113 PS-R7 `debug_assert!` to an
   unconditional diagnosed error (trust-boundary tier) — isolation by
   construction per the S61→S93 precedent, no per-interleaving patch.
2. **Prime suspects to check first**: a prelude transparent-fallback hit
   MATERIALIZED as a public table entry under concurrency (§8.6.4's
   materialise-or-not is zero-weight only while never public); an
   import-direction write landing in the wrong table during the concurrent
   build of prelude's ~13-module re-export closure.
3. **Acceptance**: chokepoint unit test (fail-on-revert, METHOD §2.2);
   census table in the change-set; ≥25× recipe sweep vs real stdlib
   (`--run` + REPL — behavioural no-regression, not the guard); the two
   GREEN twins hold; /design(int) records the isolation contract.
   `concurrency_capacity` stays a SEPARATE defect (effect-concurrency
   track).
4. This file retires when the chokepoint + census + guards land; any
   interim firing names its seam via the promoted assert and narrows the
   fix.

## /qa S113 Phase-3 plan of record (2026-07-19 — observability rider, then evidence; SUPERSEDED by the S114 section above)

Standing state after the S111 P5-close hunt (`tests/plan/PLAN.md` §"Sprint
111" I.4, "0604 seam verdict"): ~320 cumulative no-fires across four
scheduling regimes; `CRANELISP_MODULE_TRACE` CANNOT locate the seam (the
foreground install path has zero trace instrumentation — the trace recipe
above is INOPERABLE for seam location); static narrowing exhausted (no
textual path to `prelude ← bit-and` in the enumerable writer set). Further
quiet-environment sweeps are spent evidence.

Plan (consumes the S113 W4 rider — arch revision 7, `safety-invariants.md`
R7/§6 task 4): (1) `/dev`(int) lands `debug_assert!` + `MODULE_TRACE` emit at
EVERY live-table insertion seam enforcing the prelude-export-closure
invariant, UNGATED by the W0 depth decision, unit-pinned at the assert seam;
(2) the deliverable is observability — the NEXT firing anywhere names its
seam instead of needing another hunt; (3) a bounded recipe re-sweep runs
ONLY in an environment with prior fires (the S109-era `/sprint` one, if
accessible); (4) the IR-1 lane + the two GREEN twins below stay must-hold.
This file stays open (the sanctioned no-stable-RED exception) and retires
when a named-seam firing yields the fix + its fail-on-revert sweep. Row:
`tests/plan/s113-test-plan.md` PS-R7.

## Why a FIXME despite the no-FIXME-with-failing-test rule

There is **no stable RED**: `/testing`'s reduction (`ea77dad8`) could not make
the WRITE trigger deterministic free-standing, and committing an intermittent
RED is its own defect. The two committed guards are GREEN twins pinning the
poles (see §Guards). This file is therefore the record + trigger; delete it
when the S110 fix + its fail-on-revert sweep land.

## The defect

Importing `stdlib/num/bits` intermittently fails:

```
dependency 'num.bits.test' failed: type error … ambiguous bare name 'bit-and'
— provided by distinct sources 'num.bits/bit-and' and 'primitives/bit-and'
```

Root cause (two `/testing` passes + `/sprint` verification + `/qa`
attribution, `tests/plan/s109-attribution-index-feed-race.md` — the full
record): the background stdlib file-index feed intermittently injects a
**phantom public `bit-and → primitives/bit-and` entry into the live `prelude`
module's symbol table**. `stdlib/prelude.cl` exports only
`[Int Bool Float String]`; no stdlib module re-exports `bit-and`. With the
phantom present, `num.bits.test`'s legitimate `(import [super [bit-and]])`
meets a second distinct terminal and the §8.6.5 peer-poison fires
**spec-correctly** — the poison logic is CORRECT; **the bug is the phantom
WRITE**, upstream. Blast radius: all 27 `num.bits` self-tests; `num.bits`
unimportable whenever it fires; any stdlib module of the same shape exposed.

**Fingerprint (concurrent mis-attribution, not deterministic logic):** only
`bit-and` leaks — never the identically-shaped `bit-or`/`bit-xor` wrappers in
the same module. **Scheduling-dependent:** 16/16 deterministic in the
`/sprint` environment; 0/140 in `/testing`'s earlier runs. Not cache
(`--no-cache` + cleared `.cranelisp-cache` still fires).

## Deterministic repro recipe (in the environment where it fires)

```bash
printf '(import [num.bits [bit-and]])\n(import [primitives [Int]])\n(defn use-it [:Int x] :Int (bit-and x 7))\n' > /tmp/di.cl \
  && CRANELISP_LIB=/home/alilee/cranelisp/stdlib \
     /home/alilee/cranelisp/target/debug/cranelisp --no-cache --run /tmp/di.cl
```

Trace the write with `CRANELISP_MODULE_TRACE=1`.

## Seam and suspected mechanism

`index_worker.rs::index_branch_c` typechecks candidate modules **through the
real import-installing path** (`cluster::process_cluster` — installs
`(import …)` decls + prelude env) **against the LIVE `symbol_tables`**, then
removes "the live residue" claiming R13 (SharedState maps byte-unchanged).
Mutate-live-then-undo, concurrent with user compiles and other workers, is the
defect surface: a concurrent index pass's import-direction write lands in the
wrong table (reaching `prelude`'s live table) or escapes the cleanup. R13 is
observed VIOLATED. The S61→S93 precedent
(`design/int/heisenbug-race-closure.md` → `signature-body-prepass.md`) says
per-interleaving patches treadmill; the durable cure is **isolation by
construction** — the indexer typechecks into staging/discard substrate, never
live — with `/design` (int) recording the contract.

## Guards (committed, `ea77dad8`, `tests/spec_08_prelude_outer_scope.rs`)

- `super_import_wrapper_over_specific_prelude_compiles_clean` — GREEN correct
  pole (specific-export prelude → clean compile, exit 8); goes RED if the
  phantom write ever turns deterministic in the reduced fixture.
- `super_import_wrapper_collides_when_prelude_globs_primitive_neg` — GREEN
  deterministic twin of the abused seam (glob prelude → poison is
  spec-correct; exact live error signature). Do NOT weaken the poison.

## Family (fold / verify / exclude)

- **FOLDED — #4 `/search` private-submodule leak residual:** `fff94fa7` fixed
  the search-time *surfacing* (subtree-visibility filter); the underlying
  index WRITE-race is THIS fixme — which is why #1 kept firing after
  `fff94fa7`. One fix closes both faces.
- **VERIFY-AFTER-FIX (candidate same-root, unverified):**
  `tests/concurrency_capacity.rs::same_token_capacity_n_blocking_admits_n_concurrent_nplus1_parks`
  pass/fail/pass in isolation (`/sprint`, S109). Different subsystem
  (token-capacity trampoline), same scheduling sensitivity. Re-run ≥25×
  after the isolation fix; if still flaking, it is its OWN defect — attribute
  separately, do not silently fold.
- **EXCLUDED (separate root):** `agent_flag_errors_on_non_agent_build`
  build-interleave (SPRINT.md §Findings) — nextest build-artifact infra race,
  not the index feed; carried with the 0605 gate work.
- **NOT folded into 0583** (S110 centrepiece): 0583 is a backend
  bounded-context violation (backend re-resolving); this is int-layer
  shared-state isolation (background feed writing the live substrate).
  Different crate, seam, cure. Thematically adjacent — `/sprint` may wave
  them together in S110 — but separate acceptance criteria.

## Acceptance (S110 fixing change-set)

1. Phantom write structurally impossible (indexer isolated from live tables);
   R13 true by construction; `/design` (int) doc records the contract.
2. **Fail-on-revert guard lands WITH the fix**: ≥25-iteration repetition sweep
   of the deterministic recipe against the full real stdlib (C1-e2e sweep
   precedent, PLAN §S109 C) — plus the unit test at the exact write seam per
  METHOD §2.2.
3. Twin guards stay GREEN; the `concurrency_capacity` verify step recorded.
4. `/testing` retro-tags the repro family `// defect:` (class TBD by `/qa` —
   candidate: new `shared-state-write-race` vocabulary entry; request it).

## S110 /dev disposition — the IN-MEMORY isolation LANDED, §3.3 DEFERRED, the recipe writer RE-SCOPES to foreground

`/dev` (int) narrow-deployed S110, `src/session_v4/index_worker.rs`.

### What landed (the IN-MEMORY isolation half of `index-worker-isolation.md` §3)

- **§3.2 prelude-fallback SNAPSHOTTED.** `checked_typecheck_module` clones
  `shared.prelude_fallback` into a function-local `private_prelude_fallback`; the
  index typecheck reads the private snapshot — no live `&shared.*` map is now
  threaded into any install/typecheck/register call (the §5 grep's map-threading
  half is total).
- **§3.1 stale docstrings REWRITTEN** (top-of-file note, `index_branch_c`,
  `checked_typecheck_module`) — the retired mutate-live-then-undo /
  `process_cluster` / "REMOVE the residue (R13)" framing is gone; the docs now
  describe the S91 private-substrate model accurately (and record the §3.3
  deferral inline).
- Unit test at the isolation seam:
  `index_typecheck_mutates_no_live_shared_state` (fail-on-revert — pins that the
  index typecheck mutates no live `symbol_tables` / `prelude_fallback`). Twin
  guards (`tests/spec_08_prelude_outer_scope.rs`) stay GREEN; baseline REDs
  unchanged.

### What did NOT land — §3.3 cache-channel severance DEFERRED (FIXME filed to /design)

The §3.3 severance (delete `write_index_meta`; stop `try_branch_b`'s
`record_source_hash`) is **NOT landed**, for two reasons surfaced during
implementation:

1. **It does not fix this defect** (the re-scope below): the writer is FOREGROUND,
   so severing the index feed's cache channel changes nothing for the recipe.
2. **It retires §25.5, which breaks three committed e2e pins** in
   `tests/search.rs` — `search_branch_c_stale_meta_typechecks_writes_meta`,
   `search_burndown_arms_at_repl_startup_neg_not_on_first_search`,
   `search_index_to_import_is_meta_cache_hit` (they assert branch (c) writes a
   `.meta` and the index→import cache-hit, per `agent.md §25.1/§25.5`). Retiring
   §25.5 must be a /design-coordinated wave (update `agent.md §25` + `/qa`
   updates those tests), not a unilateral /dev severance that reddens the
   baseline. Coordination FIXME **0626** filed `target: /design (int)`.

### Why the recipe RE-SCOPES to the foreground (contract §4, CONFIRMED)

The deterministic recipe is `--run --no-cache`. Under it the index feed is
**provably inert**, so severing its channels cannot change the recipe's outcome:

1. **`--run` never arms the index.** `arm_importable_index()` is called only from
   `main.rs`'s REPL arm (`main.rs:342`); `arm` is its sole worklist populator;
   `run_one_index_task` drains an empty worklist and returns `false`. So
   `index_one_module` / `index_branch_c` / `write_index_meta` are UNREACHABLE
   under `--run`. **Instrumentation confirms it: `index_one_module` fires 0×
   under `--run`, 39× under REPL** (a temporary `eprintln` at the branch entry,
   removed after measuring).
2. **`--no-cache` gates the cache channel independently.** `write_index_meta`
   and `try_branch_b`'s recorder both require `cache_dir = Some`, which is `None`
   under `--no-cache`.

Both hold in the recipe, so the `/sprint` 16/16 fires under `--run --no-cache`
did **not** involve the index feed. Even the one mode where the cache channel is
fully live (REPL **with** cache) cannot produce THIS phantom: the index writes
`num.bits.meta` (not `prelude`'s table), and `num.bits.test` is a PRIVATE
`(mod- test)` submodule that the feed drops from the worklist and never indexes,
so no index artifact ever touches the `num.bits.test` super-import resolution.

**Conclusion (per contract §4):** the residual writer of the phantom
`bit-and → primitives/bit-and` terminal is on the **FOREGROUND** concurrent-
compile path — the eval thread + priority/nice workers building `num.bits` +
`num.bits.test` + `prelude` + prelude's ~13 re-exported domain modules
concurrently — not the background index feed. Attribution moves off
int-isolation. **`/qa` re-attribution + a foreground repro are owed** (the write
is quiet in the `/dev` environment: 0 fires across ~175 iterations spanning
`--run --no-cache`, clean-cwd REPL `--no-cache`, and REPL-with-cache).

### Guard / verify notes

- The ≥25× recipe sweep against the real stdlib lands as behavioural
  verification: 0/30 `--run` + 0/30 REPL post-fix (== the pre-fix baseline —
  the recipe never engaged the index feed, so the isolation cannot regress it).
  It is **not** a fail-on-revert guard for the recipe defect (that guard must
  ride the eventual FOREGROUND fix, once `/qa`/`/testing` reduce a repro).
- **`concurrency_capacity::same_token_capacity_n_blocking_admits_n_concurrent_nplus1_parks`
  is its OWN defect (attribute separately).** Re-run ≥25× (+12× idle): it FAILS
  CONSISTENTLY (not intermittently) at ~151–156ms against a 150ms overlap
  threshold, in `--run` mode (index feed inert — cannot be perturbed by this
  change). This is a timing-threshold / effect-concurrency-overlap defect on the
  `/dev` VM, unrelated to the index-feed write-race and unaffected by this
  change-set. Owner: `/qa` triage (effect-concurrency track), NOT folded here.
