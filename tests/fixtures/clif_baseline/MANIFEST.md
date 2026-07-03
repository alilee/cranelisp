# L-B1 golden-CLIF corpus — MANIFEST

**Lane:** L-B1 (analysis-off differential oracle, byte-identical-off) —
`tests/plan/s100-ownership-verification.md` §3.1; corpus pins per the S102
/arch Q1 ruling (canonical home `design/arch/ownership-inference.md` §6.2).
**Owner:** `/qa` (corpus + this manifest); `/dev`(backend) executes the
capture (B0-be, `design/backend/ownership-codegen.md` §13.1) and commits the
golden dumps beside this file under `golden/`.

## Capture contract (binding on the B0-be capture change-set)

- **Mechanism:** `CRANELISP_CODEGEN_DUMP=*`, cold-cache `--run`, one
  invocation per corpus entry in an isolated tmpdir (no prelude file — every
  entry is self-importing). Script: `tests/scripts/clif_golden.sh`.
- **Frames** sorted by `module::symbol` (Hook H1 frame-atomic writes;
  harness-side sort is the default resolution unless the dump interleaves
  mid-function — qa plan §6 G-1).
- **Content byte-verbatim, NO canonicalization** — wrapper/slot identity is
  load-bearing (masking blinds the oracle to the 0483 class).
- **Determinism self-test:** double capture per entry, byte-identical,
  BEFORE any golden commit.
- **Config pins:** all perf toggles unset — `CRANELISP_NO_OWNERSHIP`,
  `CRANELISP_NO_LENIENT`, `CRANELISP_RC_STATS`, worker-count flags all
  absent; debug binary from a clean `cargo build`.
- **Green-only:** every entry runs green at capture time (verified at corpus
  authoring, 2026-07-03 — exit codes recorded below). Shapes under open
  failing-not-ignored guards are EXCLUDED — see `EXCLUSIONS.md`.
- **Extension ≠ re-baseline; scoped re-baseline only** for
  emission-affecting changes, delta attributed to the change's seam in the
  same commit (the `public-api.txt` discipline). Wholesale re-capture
  without attribution is forbidden.

## Entries

| # | Entry | Source fixture | Shape (mechanism surface) | Green witness (exit, 2026-07-03) | Capture SHA |
|---|---|---|---|---|---|
| 1 | 01_adt_construct_match | `corpus/01_adt_construct_match.cl` | ADT construct + match projections | 24 | *(pending B0-be)* |
| 2 | 02_closures_fn_as_value | `corpus/02_closures_fn_as_value.cl` | closures + same-module fn-as-value (1 instantiation) | 22 | *(pending B0-be)* |
| 3 | 03_auto_curry | `corpus/03_auto_curry.cl` | auto-curry partial application | 6 | *(pending B0-be)* |
| 4 | 04_vec_cow_loop | `corpus/04_vec_cow_loop.cl` | vec COW loop (push/set/get/len, direct calls) | 220 | *(pending B0-be)* |
| 5 | 05_string_externs | `corpus/05_string_externs.cl` | string externs (Decision-24 consuming; S5 sibling surface) | 6 | *(pending B0-be)* |
| 6 | 06_tco_loop | `corpus/06_tco_loop.cl` | TCO self-recursion (stack-slot back-edge surface) | 186 | *(pending B0-be)* |
| 7 | 07_trait_dispatch | `corpus/07_trait_dispatch.cl` | deftrait + impls + static dispatch | 8 | *(pending B0-be)* |
| 8 | 08_adt_in_vec_projection | `corpus/08_adt_in_vec_projection.cl` | ADT-in-Vec projection-read loop (I-G1 class) | 45 | *(pending B0-be)* |
| 9 | 09_parbind_launch | `corpus/09_parbind_launch.cl` | ParBind/LaunchContinue auto-spark D&C (R6 escape class) | 148 | *(pending B0-be)* |
| 10 | f1_machinery | `tests/fixtures/s99/f1_machinery.cl` | S99 F1 — spark machinery + shared-grid reads | s99_fixtures.rs guards | *(pending B0-be)* |
| 11 | f2_contention | `tests/fixtures/s99/f2_contention.cl` | S99 F2 — shared-Vec-of-ADTs copy contention | s99_fixtures.rs guards | *(pending B0-be)* |
| 12 | f3_inverted_search | `tests/fixtures/s99/f3_inverted_search.cl` | S99 F3 — inverted search | s99_fixtures.rs guards | *(pending B0-be)* |
| 13 | f4_sudoku | `tests/fixtures/s99/f4_sudoku.cl` | S99 F4 — copy-per-guess search | s99_fixtures.rs guards | *(pending B0-be)* |

The S99 entries (10–13) are referenced in place, not copied — their
parallel≡serial guards (`tests/s99_fixtures.rs`) are the green witness; the
capture runs them serially (`CRANELISP_NO_LENIENT=1` is NOT set — config
pins above apply; the dump is of compiled code, not execution order).

## Golden layout (written by the capture)

```
tests/fixtures/clif_baseline/golden/{entry}.clif   — sorted, byte-verbatim
```

The in-suite smoke (`tests/ownership_fences.rs::clif_golden_single_module_smoke`)
compares entry 06 (the smallest) against its golden on every canonical run —
RED until B0-be lands the capture; the full-corpus diff runs via
`tests/scripts/clif_golden.sh diff` at wave gates.
