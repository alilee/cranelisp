# Wave 6 batch 1 — examples + exemplar audit

Per-test audit of the examples + exemplar cluster (4 files, 21 tests):

- `tests/examples.rs` (15 tests, 132 LOC)
- `tests/examples_run.rs` (1 test, 193 LOC)
- `tests/exemplar.rs` (3 tests, 78 LOC)
- `tests/exemplar_solver_correctness.rs` (2 tests, 302 LOC)

Author: `/qa` (audit-only dispatch, 2026-05-04). Methodology: per-test
review against the 17 e2e carry-forward files, with Wave 5.6 disposition
codes (COVERED / DUPLICATE-IN-LEGACY / GAP-COVER / REGRESSION-GUARD /
GAP-HARVEST). Same per-test framework as the sketch_port, ring0, ring1,
ring2 and e2e re-audits.

## Methodology recap

Per Wave 5.6 brief (already in force from Waves 5.5/5.6):

1. No exact 1:1 duplicates after `[Tested ...]` carry-forward exists.
2. Multi-angle on same spec property → PRESERVE.
3. Regression-named tests are presumptively discriminating — default
   to GAP-COVER (REGRESSION-GUARD) unless EXACT 1:1 duplicate is provable.
4. Spec-anchoring is the dedup criterion, not source-shape match.

**Cluster character.** All four files are *integration-tier in shape* —
two of them (`examples.rs`, `exemplar.rs`) call the legacy
`compile_and_run_simple`/`batch_run_file` helpers that go through the
Rust API; the other two (`examples_run.rs`, `exemplar_solver_correctness.rs`)
are subprocess-driven and align with the new harness.

**Carry-forward coverage of the cluster's *e2e* surface is essentially
zero.** No carry-forward file currently runs `examples/*.cl` or
`exemplar/*.cl` source — verified via `grep -l "examples/\|exemplar/\|sudoku\|solver"`
across the 17 carry-forward files (only two unrelated mentions: a
comment in `spec_08_modules.rs` and one in `repl_introspection.rs`).
Therefore the dispositions skew heavily to GAP-COVER and REGRESSION-GUARD.

The **examples are the user-surface acceptance criterion** for
"the documented examples actually work end-to-end" — this is the
shape `examples_run.rs` already asserts, and the per-example
`examples.rs` row-tests subset its assertion. They are presumptively
discriminating on the Wave 5.5/5.6 regression-guard rule because
each example is itself a defect-repro nucleus (recursion, ADTs,
closures, IO, parallelism, traits, vectors, lazy seqs, multi-clause
defmacro …) that has accreted across the project's ring deliveries.

The exemplar tests are even more discriminating: the
`exemplar_solver_correctness.rs` file carries Sprint 61 Slice 2's
two T-S2-{1,2} regression guards, both naming specific past defect
shapes (Layer-1 contract bug + Layer-3 inline-ADT-arg-wrapping-Vec
codegen bug). These are textbook REGRESSION-GUARD per the
Wave 5.5/5.6 directive.

## Summary

| Disposition | Count |
|---|---:|
| COVERED | 0 |
| DUPLICATE-IN-LEGACY | 0 |
| GAP-COVER | 21 (of which REGRESSION-GUARD: 21) |
| GAP-HARVEST | 0 |
| **Total** | **21** |

Every test in the cluster is GAP-COVER. **All 21 are also
REGRESSION-GUARD** under the Wave 5.5/5.6 rule:

- The 15 `examples.rs` tests + the `examples_run.rs` umbrella test
  exercise `examples/*.cl` programs. Each example is itself a
  curated defect-repro nucleus with a known expected-exit fingerprint
  authored as the user-facing acceptance criterion. Per the
  examples README rule (cited inline in `examples_run.rs:5-9`): a
  non-zero exit means all sub-tests passed, and each exit value is
  the sum of in-program sub-test pass counts. **The exit-code
  checksum is the regression-guard surface** — if compilation or
  codegen regresses for any sub-test, the example's exit drops to a
  smaller integer. Naming shape is `example_NN_<topic>` (e.g.,
  `example_05_recursion`, `example_15_traits`); the topic anchors
  the spec section, the NN anchors the file, and the expected sum
  is the discriminator.

- The 3 `exemplar.rs` tests are multi-module batch compilation
  smoke tests — `exemplar_batch_const_macro`,
  `exemplar_batch_cross_module_import`,
  `exemplar_batch_cross_module_adt`. Their *spec angle* (cross-module
  import + const macro + cross-module ADT) is largely covered by
  `spec_08_modules.rs` and `spec_09_macros.rs`, BUT the exemplar
  file's distinct contribution is asserting that the **multi-file
  on-disk batch** compilation pipeline works against TempDir-rooted
  source files (not just inline strings). That mode-of-operation
  shape is presently absent from the carry-forward universe.

- The 2 `exemplar_solver_correctness.rs` tests are explicit
  regression guards for two named defects (T-S2-1 Layer 1
  contract; T-S2-2 Layer 3 inline-ADT-arg-wrapping-Vec codegen bug),
  with the file headers documenting Sprint 61 Slice 5 Item I
  migration history. Highest-value REGRESSION-GUARD in the
  cluster — these capture compiler bugs whose shapes are not
  expressible in any carry-forward shape.

## Per-test classifications by file

### tests/examples.rs (15 tests)

All tests follow the same shape: `run_example("NN-<topic>.cl")` is
called, and the integer exit value is asserted against an expected
checksum. The file uses `compile_and_run_simple` (Rust-API integration
helper); the carry-forward target asserts the same end behaviour
through `Cranelisp::new().run("examples/NN-<topic>.cl")` against a
TempDir-rooted copy of the file (or `current_dir(examples_dir)` per
`examples_run.rs` precedent).

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 1 | `example_01_integers` | spec/04 §4.1.1 — Int literal arithmetic | running `examples/01-integers.cl` returns 69 | REGRESSION-GUARD | per-example exit-checksum guard; spec anchored §4.1.1. Carry to `examples.rs` (new) |
| 2 | `example_02_booleans` | spec/04 §4.1.3 — Bool literals + comparisons | `02-booleans.cl` returns 5 | REGRESSION-GUARD | per-example checksum; §4.1.3. Carry to `examples.rs` |
| 3 | `example_03_let_bindings` | spec/04 §4.3 — let expression | `03-let-bindings.cl` returns 97 | REGRESSION-GUARD | per-example checksum; §4.3. Carry to `examples.rs` |
| 4 | `example_04_functions` | spec/05 §5.1 — defn + application | `04-functions.cl` returns 135 | REGRESSION-GUARD | per-example checksum; §5.1. Carry to `examples.rs` |
| 5 | `example_05_recursion` | spec/12 §12.5 — TCO + recursion | `05-recursion.cl` returns 3635055 | REGRESSION-GUARD | per-example checksum; §12.5. Carry to `examples.rs`. **Note: `examples_run.rs` expects 111 from this file**, not 3635055 — a discrepancy worth surfacing (the `examples.rs` row-test was authored before the example file was reduced; cluster-mode dedupe must NOT collapse to either expected value without verifying which is current). |
| 6 | `example_06_enums` | spec/05 §5.2.3 — enum ADT | `06-enums.cl` returns 104 | REGRESSION-GUARD | per-example checksum; §5.2.3. Carry to `examples.rs` |
| 7 | `example_07_polymorphism` | spec/03 §3.3 — let-polymorphism | `07-polymorphism.cl` returns 119 | REGRESSION-GUARD | per-example checksum; §3.3. Carry to `examples.rs` |
| 8 | `example_08_floats` | spec/03 §3.1 — Float primitive | `08-floats.cl` returns 9 | REGRESSION-GUARD | per-example checksum; §3.1. Carry to `examples.rs` |
| 9 | `example_09_strings` | spec/03 §3.1 — String primitive ops | `09-strings.cl` returns 55 | REGRESSION-GUARD | per-example checksum; §3.1. Carry to `examples.rs` |
| 10 | `example_10_adts` | spec/05 §5.2 — ADT definitions | `10-adts.cl` returns 265 | REGRESSION-GUARD | per-example checksum; §5.2. **Note: `examples_run.rs` expects 9 — same discrepancy pattern as #5.** Carry to `examples.rs` |
| 11 | `example_11_destructuring` | spec/06 §6.2 — pattern kinds | `11-destructuring.cl` returns 69 | REGRESSION-GUARD | per-example checksum; §6.2. Carry to `examples.rs` |
| 12 | `example_12_closures` | spec/04 §4.5.1 — free var capture | `12-closures.cl` returns 263 | REGRESSION-GUARD | per-example checksum; §4.5.1. **Note: `examples_run.rs` expects 7 — discrepancy.** Carry to `examples.rs` |
| 13 | `example_13_higher_order` | spec/04 §4.6 — fn application + HOF | `13-higher-order.cl` returns 203 | REGRESSION-GUARD | per-example checksum; §4.6. Carry to `examples.rs` |
| 14 | `example_14_vecs` | spec/03 §3.2.4 — Vec ops | `14-vecs.cl` returns 541 | REGRESSION-GUARD | per-example checksum; §3.2.4. **Note: `examples_run.rs` expects 29 — discrepancy.** Carry to `examples.rs` |
| 15 | `example_15_traits` | spec/07 §7.1 — trait decl + dispatch | `15-traits.cl` returns 314 | REGRESSION-GUARD | per-example checksum; §7.1. **Note: `examples_run.rs` expects 58 — discrepancy.** Carry to `examples.rs` |

**Cross-file discrepancy flag.** Five examples (05, 10, 12, 14, 15)
have *different* expected exit values between `examples.rs` (which
uses `compile_and_run_simple` Rust API → returns `(main)`) and
`examples_run.rs` (which uses subprocess `--run` and checks process
exit code). The most likely explanation: the `examples/*.cl` source
files were edited after `examples.rs` was authored, and the
`compile_and_run_simple`-driven row-tests stayed green only because
their expected checksums were never updated; meanwhile
`examples_run.rs` was authored later and reflects the current source.
**This audit cannot resolve which value is correct** without running
both binaries, which is out of scope. Flagged for `/sprint` judgment
in §"Tests flagged for /sprint judgment" below.

### tests/examples_run.rs (1 test)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 16 | `every_example_file_runs_under_examples_prelude` | spec/10 §10 + tests/plan/ring4.md §G.20.6 — every example file runs under `--run` and exits with documented Int return | umbrella subprocess test: collects all `examples/*.cl`, asserts on-disk-vs-table parity, runs each via `--run`, accepts SIGTRAP/SIGPIPE artefacts for IO examples 21/24 | REGRESSION-GUARD | The 27-row `expected_exits` table is the authoritative ground truth; this file should be the canonical carry-forward (its shape matches the new harness already — subprocess-driven, signal-aware, on-disk parity check). Carry to `examples.rs` (new), absorbing the 15 row-tests in #1–#15 |

The `examples_run.rs` test is **strictly more comprehensive than
the 15 row-tests** in `examples.rs`:

- Covers all 27 examples (vs. 15 row-tests).
- Uses subprocess `--run`, matching the new harness shape.
- Asserts on-disk file set matches the table (catches added/renamed examples).
- Handles IO examples 21/24's stdin-closed SIGTRAP/SIGPIPE artefacts
  via `128 + signal` normalisation.
- Has detailed regression-history comments (Slice-4 RC fix, Wave-2
  H(4-1'') double-free, etc.).

**Recommendation: the carry-forward should adopt the `examples_run.rs`
shape, not the `examples.rs` shape.** Per-example assertions become
rows in a single table-driven test, with each row anchored to the
spec section the example demonstrates. This collapses 15 + 1 → 1 (or
preserves 1 umbrella + a small handful of "demonstrative" per-example
tests for the most regression-prone examples). Final shape is
`/sprint`'s call.

### tests/exemplar.rs (3 tests)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 17 | `exemplar_batch_const_macro` | spec/08 §8.2 — const macro works in batch files via prelude | TempDir multi-file batch: `(const SIZE 9)` + `(defn main [] SIZE)`; `batch_run_file` returns 9 | REGRESSION-GUARD | const macro inside batch-mode entry file; absorbed at the *spec* level by `spec_09_macros.rs` (const macro definition) + `spec_08_modules.rs` (batch entry compilation), but the **multi-file-batch-mode-pipeline** angle (TempDir on-disk source vs. inline-string REPL) is unique. Carry to `exemplar.rs` (new) using `Cranelisp::new().run(...)`. |
| 18 | `exemplar_batch_cross_module_import` | spec/08 §8.10.1 — cross-module import | TempDir 2-file batch: `util.cl` exports `helper`, `main.cl` imports + calls; result 42 | REGRESSION-GUARD | The cross-module import shape is covered by `spec_08_modules.rs::import_specific_name_compiles_and_runs` (which uses inline TempDir source via Cranelisp builder), but the legacy `batch_run_file` Rust-API shape is the discriminator. Per Phase 3 strategy, carry to `exemplar.rs` (new) with the Cranelisp builder shape — the integration-tier lift dies here. |
| 19 | `exemplar_batch_cross_module_adt` | spec/08 §8.10.1 — cross-module with ADT types | TempDir 2-file batch: `types.cl` defines `Color` enum + `color-val`, `main.cl` imports + calls; result 4 | REGRESSION-GUARD | Cross-module ADT is the distinct angle. `spec_08_modules.rs` covers cross-module *function* import; `spec_05_definitions.rs` + `spec_06_pattern_matching.rs` cover ADT + match in single-file shapes; the **cross-module ADT export-and-import** angle is e2e-observable but NOT directly carried in the existing universe. Carry to `exemplar.rs` (new). |

### tests/exemplar_solver_correctness.rs (2 tests)

Both tests carry **explicit regression-guard naming** (T-S2-1, T-S2-2)
with file headers documenting:

- Sprint 61 Slice 2 branch-(b) handoff defect-repro origin
- Sprint 61 Wave 5 Item I migration from `exemplar/` to `tests/`
  (per `memory/feedback_repro_handoff.md` discipline)
- Layer 1 (contract) vs Layer 3 (codegen) defect taxonomy

These are gold-standard REGRESSION-GUARDs per the Wave 5.5/5.6
directive. They MUST NOT be discarded.

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 20 | `eliminate_on_same_value_given_returns_none` (T-S2-1) | tests/plan/ring4.md §"Slice 2 branch-b outcome" T-S2-1 — `eliminate` on a `Given v` cell with same digit `v` MUST return `None` (contradiction contract) | TempDir + copies `exemplar/grid.cl`+`exemplar/solver.cl` + writes inline repro source; runs `--run`; asserts exit 0 (pass), 1 (contract violation), 2 (setup failure) | REGRESSION-GUARD | Layer-1 contract: solver.cl::eliminate must return None on contradiction. Highest-value preserve — this is named after a specific past defect. Carry to `exemplar.rs` or new `regression.rs`; **must continue to copy `exemplar/grid.cl`+`exemplar/solver.cl`** unless the test is rewritten as fully inline (see `/sprint` judgment §) |
| 21 | `inline_adt_arg_wrapping_vec_preserves_len` (T-S2-2) | tests/plan/ring4.md §"Slice 2 branch-b outcome" T-S2-2; design/backend/ring2-rc.md §5.5 — `borrowed_vars` rule | TempDir + fully-inline repro: `Box [0]` ADT, three call shapes (`direct-let`, `inline-arg`, `let-arg`), all three must print `len=1` | REGRESSION-GUARD | Layer-3 backend codegen: inline ADT constructor wrapping Vec, passed as fn argument, must NOT corrupt inner Vec length. Pre-fix this read len=0; HEAD reads len=1. **Self-contained — no exemplar/* dependency.** Carry to `regression.rs` (new) — this is a pure codegen regression guard, not exemplar-specific. |

## GAP-COVER candidates — recommended target files + new test names

For each, the recommendation is the carry-forward target file and a
proposed canonical test name. Final shape is `/sprint`'s call at
Wave 6 dispatch.

| # | Originating test | Target file | Proposed canonical name | Spec anchor | Notes |
|---:|---|---|---|---|---|
| 1 | `examples.rs::example_01_integers` (#1) | `examples.rs` (new) | `example_01_integers_returns_documented_sum` | spec/04 §4.1.1 | Use `Cranelisp::new().run("examples/01-integers.cl")` shape; assert exit 69 (per `examples_run.rs` table) |
| 2 | `examples.rs::example_02_booleans` (#2) | `examples.rs` (new) | `example_02_booleans_returns_documented_sum` | spec/04 §4.1.3 | exit 5 |
| 3 | `examples.rs::example_03_let_bindings` (#3) | `examples.rs` (new) | `example_03_let_bindings_returns_documented_sum` | spec/04 §4.3 | exit 97 |
| 4 | `examples.rs::example_04_functions` (#4) | `examples.rs` (new) | `example_04_functions_returns_documented_sum` | spec/05 §5.1 | exit 135 |
| 5 | `examples.rs::example_05_recursion` (#5) | `examples.rs` (new) | `example_05_recursion_returns_documented_sum` | spec/12 §12.5 | exit 111 (per `examples_run.rs`) — **flagged for /sprint judgment** |
| 6 | `examples.rs::example_06_enums` (#6) | `examples.rs` (new) | `example_06_enums_returns_documented_sum` | spec/05 §5.2.3 | exit 104 |
| 7 | `examples.rs::example_07_polymorphism` (#7) | `examples.rs` (new) | `example_07_polymorphism_returns_documented_sum` | spec/03 §3.3 | exit 119 |
| 8 | `examples.rs::example_08_floats` (#8) | `examples.rs` (new) | `example_08_floats_returns_documented_sum` | spec/03 §3.1 | exit 9 |
| 9 | `examples.rs::example_09_strings` (#9) | `examples.rs` (new) | `example_09_strings_returns_documented_sum` | spec/03 §3.1 | exit 55 |
| 10 | `examples.rs::example_10_adts` (#10) | `examples.rs` (new) | `example_10_adts_returns_documented_sum` | spec/05 §5.2 | exit 9 — **flagged** |
| 11 | `examples.rs::example_11_destructuring` (#11) | `examples.rs` (new) | `example_11_destructuring_returns_documented_sum` | spec/06 §6.2 | exit 69 |
| 12 | `examples.rs::example_12_closures` (#12) | `examples.rs` (new) | `example_12_closures_returns_documented_sum` | spec/04 §4.5.1 | exit 7 — **flagged** |
| 13 | `examples.rs::example_13_higher_order` (#13) | `examples.rs` (new) | `example_13_higher_order_returns_documented_sum` | spec/04 §4.6 | exit 203 |
| 14 | `examples.rs::example_14_vecs` (#14) | `examples.rs` (new) | `example_14_vecs_returns_documented_sum` | spec/03 §3.2.4 | exit 29 — **flagged** |
| 15 | `examples.rs::example_15_traits` (#15) | `examples.rs` (new) | `example_15_traits_returns_documented_sum` | spec/07 §7.1 | exit 58 — **flagged**; legacy carries `// IGNORED: constrained polymorphic` comment, unclear whether the example currently uses the constrained path |
| 16 | `examples_run.rs::every_example_file_runs_under_examples_prelude` | `examples.rs` (new) | `every_example_runs_with_documented_exit` (umbrella) | spec/10 §10 + spec/appendix-b-examples.md | Subprocess umbrella that loops the 27-entry `expected_exits` table; signal-aware (SIGTRAP=133, SIGPIPE=141 for IO 21/24); on-disk vs table parity guard |
| 17 | `exemplar.rs::exemplar_batch_const_macro` | `exemplar.rs` (new) | `batch_const_macro_in_main` | spec/08 §8.2 + spec/09 (const macro) | TempDir + `Cranelisp::new().run(...)` shape |
| 18 | `exemplar.rs::exemplar_batch_cross_module_import` | `exemplar.rs` (new) | `batch_cross_module_function_import` | spec/08 §8.10.1 | TempDir 2-file project; absorbs the integration-tier `batch_run_file` shape into the e2e harness |
| 19 | `exemplar.rs::exemplar_batch_cross_module_adt` | `exemplar.rs` (new) | `batch_cross_module_adt_export_and_pattern_match` | spec/08 §8.10.1 + spec/05 §5.2 + spec/06 §6.2 | The cross-module-ADT angle that's NOT in the carry-forward universe |
| 20 | `exemplar_solver_correctness.rs::eliminate_on_same_value_given_returns_none` | `exemplar.rs` or new `regression.rs` | `t_s2_1_eliminate_contract_on_given_returns_none` | tests/plan/ring4.md §"Slice 2 branch-b outcome" T-S2-1 | Layer-1 contract guard; preserve copy-from-exemplar setup OR rewrite fully inline (per /sprint) |
| 21 | `exemplar_solver_correctness.rs::inline_adt_arg_wrapping_vec_preserves_len` | new `regression.rs` (NOT `exemplar.rs`) | `t_s2_2_inline_adt_arg_wrapping_vec_preserves_len` | tests/plan/ring4.md §"Slice 2 branch-b outcome" T-S2-2; design/backend/ring2-rc.md §5.5 | **Self-contained codegen regression** — does NOT depend on exemplar/. Belongs in a regression-cohort file alongside the d{4,5,6} repros from sprint59*.rs. |

## Tests flagged for /sprint judgment

### A. The exit-value discrepancy across `examples.rs` and `examples_run.rs`

5 examples have different expected exit values between the two
files: 05 (3635055 vs 111), 10 (265 vs 9), 12 (263 vs 7), 14 (541 vs 29),
15 (314 vs 58).

**This is unresolvable in audit**. The carry-forward author needs to
either (a) run each example via `cargo run -- --run examples/NN-*.cl`
and observe the current exit, then update the carry-forward to that
value; or (b) consult the example file itself (the README rule says
`main` returns sum of sub-test pass counts, so reading the source
should reveal the intended sum). Recommendation: trust
`examples_run.rs`'s table — it's the more recent, more comprehensive,
subprocess-driven version, and was authored as the user-surface
acceptance criterion. The `examples.rs` row-test checksums likely
date from an earlier example revision and are stale.

### B. Cross-file recommendation: collapse 15+1 → 1 umbrella + spec-section parity rows

`examples.rs` (15 row-tests) is **strictly subsumed** by
`examples_run.rs` (1 umbrella that loops 27 entries via the
`expected_exits` table). Recommendation: carry forward only the
umbrella shape. If per-example test discoverability matters for
the spec-coverage auditing goal, the umbrella's table can be
restructured so each row is a separate `#[test]` via a macro
expansion — this is a presentation choice, not a substantive
coverage decision. The umbrella is the discriminator; per-example
rows add no new coverage.

The 12 examples that don't have row-tests in `examples.rs` (16-modules
is a subdir, 17–28 are not in the row-test list) are covered ONLY by
`examples_run.rs`. Dropping the umbrella in favour of just the 15
row-tests would silently lose coverage of examples 17–28 (display,
macros, threading, ADT-traits, hello-io, io-hello, io-sequence,
io-echo, curry, functor, lazy-seq, parallel) — exactly the
late-ring/feature-rich examples that are most regression-prone.

### C. Exemplar T-S2-1 setup: copies `exemplar/grid.cl`+`exemplar/solver.cl`

The Sprint 61 Slice 5 Item I migration moved the inline repro source
into the test file but kept the dependency on `exemplar/grid.cl` and
`exemplar/solver.cl` (copied to TempDir at test start). Per
`memory/feedback_repro_handoff.md`, "minimal repros live in tests/, not
exemplar/" — but the rule's spirit is that compiler regression guards
must NOT depend on `exemplar/` because exemplar/ is subject to
removal. The current T-S2-1 still has that dependency.

**Options for /sprint:**

1. **Status quo carry**: keep the copy-from-exemplar setup. Risk:
   if `/port` redesigns `grid.cl` or `solver.cl`, the regression
   guard breaks (and the breakage may be silent if the new shape
   still compiles but doesn't exercise the same Layer-1 contract).
2. **Inline rewrite**: rewrite the test to inline minimal grid +
   solver definitions sufficient to trigger the contract violation.
   This is more work but produces a self-contained guard
   matching `inline_adt_arg_wrapping_vec_preserves_len` (T-S2-2).
3. **Defer to a future port-coordination FIXME**: file a FIXME
   against `/port` to maintain test-touching APIs in `grid.cl`/
   `solver.cl` as a stable contract.

Recommendation: option (2) inline rewrite. The repro is small
(one cell with `(Given 5)`, call eliminate, check None). The
exemplar dependency is a debt that this sprint can pay off cheaply.

### D. Carry-forward target file naming

The natural target for #1–#16 is a new `tests/examples.rs`. **The
existing `tests/examples.rs` is a legacy file under audit.** Need
to confirm with `/sprint` whether (a) the legacy file is renamed
to `tests/legacy/examples.rs` first (matching the Wave 5 quarantine
discipline), then a fresh `tests/examples.rs` is authored; or
(b) the legacy file is overwritten in place with the new content.

Per Phase 2 "audit / port / reorganise / quarantine" workflow,
option (a) is the consistent shape — quarantine first, port to
new file, ledger entry. The new file's content is fundamentally
different (subprocess `Cranelisp::new()` vs. Rust-API
`compile_and_run_simple`) so it's a port, not an in-place rewrite.

Same applies to `tests/exemplar.rs` — quarantine first, port to a
new `tests/exemplar.rs` with `Cranelisp` builder shape.

`tests/examples_run.rs` and `tests/exemplar_solver_correctness.rs`
are ALREADY subprocess-driven — they could conceivably be folded
in-place into the new files, but the cleaner shape is still
quarantine-then-port to keep the audit discipline uniform.

### E. T-S2-2's target file (regression.rs vs exemplar.rs)

`inline_adt_arg_wrapping_vec_preserves_len` is **not exemplar-specific**
— it's a self-contained backend codegen regression guard that happens
to be named after Slice 2 because that's when the bug was discovered.
A future reader looking for "the canonical inline-ADT-wrapping-Vec
codegen regression test" should find it in a regression-cohort file,
not under `exemplar.rs`.

Recommendation: carry to a new `tests/regression.rs` (the file named
in PLAN.md §"Reorganisation strategy" — the defect-repro cohort
holding `sprint59_defects456_repro.rs`/`wave6_demo_repros.rs`/etc.
remnants). T-S2-1 (the Layer-1 contract) is more arguably exemplar-y
because it asserts a *contract on `solver.cl::eliminate`*, but if
option (2) inline-rewrite is taken, T-S2-1 also belongs in
`regression.rs`.

## Recommendations

1. **Adopt `examples_run.rs`'s shape as the canonical carry-forward.**
   The 15 `examples.rs` row-tests are subsumed; carry the
   subprocess-driven umbrella + the on-disk-vs-table parity guard +
   signal-aware exit normalisation. Resolves discrepancy A by trusting
   the more recent table.

2. **Quarantine all 4 source files first, then author new
   `tests/examples.rs`, `tests/exemplar.rs`, and `tests/regression.rs`
   under the e2e harness.** Matches Wave 5 discipline (quarantine
   before port). 4 harvest FIXMEs unnecessary because all 21 tests
   are e2e-observable (no GAP-HARVEST findings).

3. **Inline-rewrite T-S2-1** to remove the `exemplar/grid.cl`+`solver.cl`
   dependency. The repro is small enough that inlining is cheaper than
   the cross-skill stability debt.

4. **Place T-S2-2 in `regression.rs`, not `exemplar.rs`.** It's a
   codegen regression guard, not an exemplar correctness test.

5. **Per-example tests collapse to 1 umbrella + 0 explicit per-example
   tests** unless the spec-section discoverability requirement justifies
   restructuring. The 27-entry `expected_exits` table is the audit
   surface; per-row `#[test]` expansion can be added later if needed
   without changing coverage.

6. **No new defect FIXMEs surfaced by this audit.** All 21 tests are
   GAP-COVER REGRESSION-GUARD with no spec violations exposed during
   review. The 5-example exit-value discrepancy is a **stale-test**
   artefact (legacy `examples.rs` vs newer `examples_run.rs`), not a
   compiler defect.

## Cross-file pattern note

All 21 tests in this batch share a single carry-forward target shape:
**subprocess `--run` against `examples/*.cl` or `exemplar/*.cl`
source on disk, asserting exit code or stdout content.** This is the
shape the `Cranelisp` builder + `tests/helpers/e2e.rs` harness was
designed for. Two new files (`examples.rs`, `exemplar.rs`) plus a
contribution to `regression.rs` (T-S2-2 + optionally T-S2-1) cover
the full cluster.

The cluster is the most homogeneous batch encountered in the per-test
re-audits — 0 GAP-HARVEST, 0 COVERED, 21 REGRESSION-GUARD all sharing
one harness shape. The risk is concentration: if any single
harness-shape decision (TempDir-rooted vs `current_dir(examples_dir)`,
process exit vs `assert_stdout_contains`, etc.) needs revisiting,
it will affect the entire cluster's port. The recommendation for
`/sprint` is to settle the shape via examples_run.rs's umbrella
first, then port the rest in its image.
