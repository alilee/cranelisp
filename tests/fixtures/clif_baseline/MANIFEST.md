# L-B1 golden-CLIF corpus — MANIFEST

**Lane:** L-B1, the analysis-off differential oracle
([QA lane specification](../../plan/s100-ownership-verification.md#31-the-analysis-off-differential-oracle-backend-224-spine-62));
corpus rules from `design/arch/ownership-inference.md` §6.2 and the capture
substrate in `design/backend/ownership-codegen.md` §13.1.
**Owner:** `test` (corpus, goldens, this manifest and
`tests/scripts/clif_golden.sh`). An emission-affecting change-set carries its
own scoped re-baseline.

## Capture contract

- **Mechanism:** `CRANELISP_CODEGEN_DUMP=*`, cold-cache `--run --no-cache`,
  one invocation per corpus entry in an isolated tmpdir (no prelude file —
  every entry is self-importing). Script: `tests/scripts/clif_golden.sh`.
  `--no-cache` eliminates the nice-worker `.o` cache-write pass, so each
  symbol dumps exactly once (the JIT pass). A **duplicate frame is a hard
  error** (the cache pass leaked back in), never deduped.
- **Frames** are sorted by name; the dump channel is STDERR. **Zero frames
  extracted is a hard error** — an empty-versus-empty comparison is a false
  green.
- **Content byte-verbatim, NO canonicalization** — wrapper and slot identity
  are load-bearing; masking them blinds the oracle to wrapper-identity drift.
- **Determinism self-test:** double capture per entry, byte-identical, before
  any golden is written (`clif_golden.sh selftest`).
- **Config pins** — enforced by `env -u` in the script's `dump()` and by
  `env_remove` in the in-suite smoke; keep both in step with this list and
  with the [W0.b corpus](../clif_w0b/MANIFEST.md#capture-contract):
  all emission-affecting env unset — `CRANELISP_NO_OWNERSHIP`,
  `CRANELISP_NO_LENIENT`, `CRANELISP_CAPTURE_BORROW`,
  `CRANELISP_NONATOMIC_RC`, `CRANELISP_RC_STATS`, `CRANELISP_RC_DEC_CHECK`
  (each gates CLIF emission) and `CRANELISP_NO_IO_SCHEDULE` (the
  pre-typecheck bind-chain transform that shapes ParBind entries). The
  compile-time trace vars (`CRANELISP_RC_TRACE`, `CRANELISP_CODEGEN_TRACE`,
  `CRANELISP_GOT_TRACE`, `CRANELISP_MODULE_TRACE`,
  `CRANELISP_SCHEDULER_TRACE`, `CRANELISP_IO_TRACE`) are also cleared because
  they write to the dump channel. Runtime-only knobs
  (`CRANELISP_SPARK_BUDGET`, `CRANELISP_SATURATION_GATE`, `CRANELISP_DEGREE`)
  do not affect CLIF and are unpinned; the binary is the debug build.
- **Green-only:** every entry runs green at capture time. Shapes under an open
  failing-not-ignored guard are excluded and recorded in
  [EXCLUSIONS.md](EXCLUSIONS.md).
- **Extension ≠ re-baseline; scoped re-baseline only.** An emission-affecting
  change re-captures only the drifted entries and attributes every changed
  frame to the change's seam in its commit message. Wholesale re-capture
  without attribution is forbidden. The Git history of `golden/` holds each
  attributed re-baseline.

## Entries

`clif_golden.sh` `ENTRIES` must list exactly these.

| # | Entry | Source fixture | Shape (mechanism surface) | Exit at authoring |
|---|---|---|---|---|
| 1 | 01_adt_construct_match | `corpus/01_adt_construct_match.cl` | ADT construct + match projections | 24 |
| 2 | 02_closures_fn_as_value | `corpus/02_closures_fn_as_value.cl` | closures + same-module fn-as-value (1 instantiation) | 22 |
| 3 | 03_auto_curry | `corpus/03_auto_curry.cl` | auto-curry partial application | 6 |
| 4 | 04_vec_cow_loop | `corpus/04_vec_cow_loop.cl` | vec COW loop (push/set/get/len, direct calls) | 220 |
| 5 | 05_string_externs | `corpus/05_string_externs.cl` | string externs (consuming externs) | 6 |
| 6 | 06_tco_loop | `corpus/06_tco_loop.cl` | TCO self-recursion (stack-slot back-edge surface) | 186 |
| 7 | 07_trait_dispatch | `corpus/07_trait_dispatch.cl` | deftrait + impls + static dispatch | 8 |
| 8 | 08_adt_in_vec_projection | `corpus/08_adt_in_vec_projection.cl` | ADT-in-Vec projection-read loop | 45 |
| 9 | 09_parbind_launch | `corpus/09_parbind_launch.cl` | ParBind/LaunchContinue auto-spark divide-and-conquer | 148 |
| 10 | 10_nullary_arm_beside_boxed_arm | `corpus/10_nullary_arm_beside_boxed_arm.cl` | nullary/boxed match-result return seam beside an all-boxed control | 200 |
| 11 | f1_machinery | `tests/fixtures/s99/f1_machinery.cl` | spark machinery + shared-grid reads | `s99_fixtures.rs` guards |
| 12 | f2_contention | `tests/fixtures/s99/f2_contention.cl` | shared-Vec-of-ADTs copy contention | `s99_fixtures.rs` guards |
| 13 | f3_inverted_search | `tests/fixtures/s99/f3_inverted_search.cl` | inverted search | `s99_fixtures.rs` guards |
| 14 | f4_sudoku | `tests/fixtures/s99/f4_sudoku.cl` | copy-per-guess search | `s99_fixtures.rs` guards |

The S99 entries (11–14) are referenced in place, not copied; their
parallel≡serial guards (`tests/s99_fixtures.rs`) are the green witness. The
config pins above still apply — the dump is of compiled code, not execution
order.

**Known unsound golden frame.** `f4_sudoku` `user::Grid.cells` (a synthetic
accessor of a generic product) carries a shallower self-parameter release than
its type requires. The golden records current emission, not correctness;
FIXME 0903 owns the correction and its scoped re-baseline of that frame.

## Golden layout and runners

```
tests/fixtures/clif_baseline/golden/{entry}.clif   — sorted, byte-verbatim
```

- `tests/clif_golden_lane.rs::clif_golden_lane_no_drift` runs
  `clif_golden.sh diff` over every entry on each canonical run.
- `tests/ownership_fences.rs::clif_golden_single_module_smoke` compares entry
  06 in Rust, independently of the script.
- `clif_golden.sh capture` (re)writes goldens for a scoped re-baseline only.
