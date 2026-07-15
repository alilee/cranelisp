---
number: 0604
target: /dev
filed_by: /qa
filed_at: 2026-07-15
sprint_filed: 109
scheduled: S110
refers_to: src/session_v4/index_worker.rs (branch (c) `index_branch_c` — the
  live-table typecheck + R13 undo discipline) + the import/prelude installer
  writers it drives (src/imports.rs); poison-consumer (CORRECT, do not touch)
  at src/imports.rs::insert_detecting_ambiguity ~L547-560. Narrow-deploy
  /dev to src/ (int); /design (int) records the isolation contract.
status: open
---

# Background stdlib index feed racily writes a phantom public binding into the live `prelude` table (family FIXME: the index-feed WRITE-race)

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
