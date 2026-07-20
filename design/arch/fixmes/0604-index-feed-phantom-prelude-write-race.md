---
number: 0604
target: /qa
re_scoped_from: /dev (S110 — per contract §4; see "S110 /dev disposition" below)
filed_by: /qa
filed_at: 2026-07-15
sprint_filed: 109
scheduled: S110
refers_to: src/session_v4/index_worker.rs (branch (c) `index_branch_c` — the
  live-table typecheck + R13 undo discipline) + the import/prelude installer
  writers it drives (src/imports.rs); poison-consumer (CORRECT, do not touch)
  at src/imports.rs::insert_detecting_ambiguity ~L547-560. Narrow-deploy
  /dev to src/ (int); /design (int) records the isolation contract.
  RE-SCOPED S110: the recipe's residual writer is on the FOREGROUND concurrent-
  compile path (src/process_form/, src/imports.rs, src/worker.rs), NOT the
  index feed — the index feed is proven inert under the `--run` recipe. See the
  disposition section.
status: open
---

# Background stdlib index feed racily writes a phantom public binding into the live `prelude` table (family FIXME: the index-feed WRITE-race)

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
