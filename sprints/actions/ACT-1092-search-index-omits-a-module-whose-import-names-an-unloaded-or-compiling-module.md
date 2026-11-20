---
id: ACT-1092
title: The search index omits a valid module whose import names a module the session has not loaded, or is still compiling, and reports the index as complete
status: open
priority: required
from: qa
to: qa
sprint: 124
filed_at: 2026-11-20
refers_to:
  - repl/spec/17a-agent-language-awareness.md §17.19
  - repl/spec/17a-agent-language-awareness.md §17.19.5
  - design/int/index-worker-isolation.md
  - src/session_v4/index_worker.rs::checked_typecheck_module
  - sprints/actions/ACT-0952-complete-semantic-search-indexing.md
---

## Origin

`test`, committing REPRO-1090 (`f18652c6`), reported that some launches
printed `index: could not index m: … 'pf' not found in module 'p'`,
including launches that scored 51. `qa` took it in on 2026-11-20.

## Observation

`qa`, 2026-11-20, the debug binary built from `39db1bb1`, at the REPL with
no prelude, in scratch directories, on a 14-processor machine.

```clojure
;; p.cl
(import [primitives [Int add-i64]])
(defn pf [:Int n] n)

;; m.cl
(import [primitives [Int]])
(import [p [pf]])
(defn mf [:Int n] (pf n))

;; app.cl
(import [primitives [Int add-i64]])
```

**Face 1, every launch.** The session is `/search mf`, then `/search pf`.
With no cache, and with `--no-cache`, 4 of 4 launches print
`; no importable symbols matched` for `mf` and list `pf` in `p`. With
`CRANELISP_MODULE_TRACE=1` each prints
`index: could not index m: import install error: … unknown module 'p' in import`.

**Face 2, run-dependent.** REPRO-1090's fixture (six bulk modules of 200
definitions). The session is `(p/pf 1)`, `/search mf`. Fourteen directories
ran at once.

| Cache before the launch | Launches | `index:` note | `/search mf` lists nothing |
|---|---|---|---|
| Complete, then `p.o` removed, so `p` compiles in the launch | 420 | 115 | 115, the same launches |
| The same, with `(add-i64 1 1)` and a second `/search mf` | 210 | 49 | 49, in both searches |
| Complete, so `p` is restored (control) | 210 | 0 | 0 |
| Complete, then `p.o` removed, one launch at a time | 30 | 0 | 0 |
| `--no-cache` | 210 | 95 | 95 |
| `--no-cache`, one launch at a time | 40 | not read | 40 |

- The note in these launches reads `'pf' not found in module 'p'`.
- **The note in REPRO-1090 has no face.** With that cell's own turn, which
  loads `m`, 29 of 420 loaded launches printed the note and all 29 listed
  `mf` in `m` afterwards. The cell prints the note and does not decide on
  it.

## Classification: a defect against REPL §17.19 R10

The user ruled on 2026-11-20: "search returns what is reachable not what is
already imported". `spec` recorded it at `21101921`.

- [§17.19 R10](../../repl/spec/17a-agent-language-awareness.md#1719-importable-symbol-search--search--pillar-3-s90-re-pin)
  now reads: a reachable module MUST NOT be omitted merely because it or a
  dependency is not yet loaded or is still compiling in the session. Face 1
  is the *not yet loaded* clause and face 2 the *still compiling* clause.
- [§17.19.5](../../repl/spec/17a-agent-language-awareness.md#17195-robustness--searching-the-library-must-never-crash-the-repl-s90-re-pin)'s
  allowance that a failed attempt contributes no rows no longer covers
  either face: the text makes it subordinate to R10.
- **Severity: wrong value, no memory hazard.** The search prints
  `no importable symbols matched`, the complete-index answer, for a symbol
  the project defines. Importing the module still works.
- **Reach.** A project module that imports a sibling is the ordinary shape.
  Face 1 is every launch, so most of a multi-module project is absent from
  the index until its modules are loaded.
- **It predates S124** (*Age*, below) and is a nonconformance against a
  requirement recorded on 2026-11-20. `qa` first read §17.19.5 as allowing
  it; `spec` reports that reading was available on the earlier text.

Re-read by `qa` on 2026-11-20 with the debug binary built from `39db1bb1`,
source unchanged to `21101921`: face 1 as above in 4 of 4 launches. A
three-module chain (`t` imports `m`, `m` imports `p`, none loaded) lists
`pf` and neither `mf` nor `tf`, in 3 of 3 launches.

## Attribution: the binary's index feed

- **At the seam.** The note is the feed's own report from
  `index_branch_c`: the private import installation refused `m`'s import
  of `p`.
- **In source.** `checked_typecheck_module` resolves a module's imports
  from a copy of the live tables only. A module the session has not loaded
  is absent from the copy (face 1). A module registered and not yet
  published is copied as it stands, without its definitions (face 2).
  Neither is loaded or awaited, and the module is then marked indexed with
  no rows.
- **Control.** With `p` restored before the feed reaches `m`, 210 of 210
  launches list `mf`.
- **Not established.** Why a valid `.meta` for `m` does not serve the rows
  while `p` compiles; `qa` read the trace lines only. Why 115 of 210
  loaded `--no-cache` launches list `mf` and none of 40 unloaded ones do.
- **Age.** The private typecheck dates from S91 and the copy from S110.
  `qa` ran no earlier tree.

## Routing

- **`qa` holds this action** until the correction lands and its coverage is
  judged.
- **`test`:** T-SEARCH-REACH, the reproduction, allocated in the
  [S124 evidence delta §14.3](../../tests/plan/s124-evidence-delta.md#143-allocated-to-test).
- **`design`(int), then `dev`(`src/`):** the correction, carried on
  T-SEARCH-REACH unless the user schedules it (`sprints/SPRINT.md`, Notes).
  `design`(int) states how the feed resolves a module's imports without
  the session having loaded them, in
  [index-feed isolation](../../design/int/index-worker-isolation.md), and
  whether [ACT-0952](ACT-0952-complete-semantic-search-indexing.md)'s
  dependency discovery is that correction or a later one.
- **`dev`(`src/`), with the correction:** two module rows over
  `checked_typecheck_module`, stated in the delta §14.3. The second is the
  only evidence allocated for face 2.

## Completion evidence

- T-SEARCH-REACH is committed, observed RED on its row clauses, and passes
  on the corrected build.
- The two module rows pass, and the *registered, not yet published* row was
  seen to fail before the correction.
- The design states the feed's import resolution as built.
