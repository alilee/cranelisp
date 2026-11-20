---
id: ACT-1092
title: The search index omits a valid module whose import names a module the session has not loaded, or is still compiling, and reports the index as complete
status: open
priority: advisory
from: qa
to: design
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

## Classification: not a defect against the current text; an unrecorded limit

- [§17.19.5](../../repl/spec/17a-agent-language-awareness.md#17195-robustness--searching-the-library-must-never-crash-the-repl-s90-re-pin)
  lets a source-index attempt whose declaration processing fails contribute
  no rows, and lets the session say `could not index <module>`. The
  section's status line defers complete indexing to ACT-0952.
- R10 of §17.19 makes every `.cl` module on the project root reachable. A
  project module that imports a sibling is the ordinary shape, so the limit
  removes most of a multi-module project from the index until its modules
  are loaded.
- The search then prints `no importable symbols matched`, the complete-index
  answer, for a symbol the project defines.
- **Refuted as "not a defect" if** `spec` reads R10 as requiring a valid
  reachable module's rows whatever the session has loaded. That is a
  question for `spec` which blocks no test; current behaviour stands.

No memory is read or written that should not be. The face is a missing
search row.

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

## Request

`design`(int), with ACT-0952:

1. Record in [index-feed isolation](../../design/int/index-worker-isolation.md)
   that a module whose import names a module absent from, or unpublished
   in, the live tables is not indexed in that session, and that the search
   then reports a complete index.
2. State in ACT-0952 that its dependency discovery closes both faces, or
   say what does.

## Completion evidence

The design states the limit or its correction. If `spec` rules that R10
requires the rows, `qa` allocates a cell over face 1's three files:
`/search mf` lists `mf` in `m` once the index has settled, with `/search pf`
as its control.
