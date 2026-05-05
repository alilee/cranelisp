# Wave 6 batch 3 — sprint59_cache_repro + sprint59_defects456_repro audit

Per-test audit of the Sprint 59 reduction-cluster files:

- `tests/sprint59_cache_repro.rs` (152 LOC, 2 tests)
- `tests/sprint59_defects456_repro.rs` (1766 LOC, 34 tests)

Total: **36 tests** across **2 files**.

Author: `/qa` (audit + carry-forward dispatch, 2026-05-05). Methodology:
per-test review against the existing e2e carry-forward universe, with
Wave 5.6 disposition codes (COVERED / DUPLICATE-IN-LEGACY / GAP-COVER /
REGRESSION-GUARD / GAP-HARVEST). Same per-test framework as the
sketch_port, ring0, ring1, ring2, e2e and Wave 6 batches 1–2 audits.

## Methodology recap

Per Wave 5.6 brief (in force from Waves 5.5/5.6):

1. No exact 1:1 duplicates after `[Tested ...]` carry-forward exists.
2. Multi-angle on same spec property → PRESERVE.
3. Regression-named tests are presumptively discriminating — default
   to GAP-COVER (REGRESSION-GUARD) unless EXACT 1:1 duplicate is provable.
4. Spec-anchoring is the dedup criterion, not source-shape match.

**Cluster character.** Both files are *Sprint 59 reduction* artefacts —
narrow regression guards authored as the tail of /qa's defect-reproduction
discipline (`memory/feedback_repros_join_suite.md`, root CLAUDE.md
§"Usability Findings and Defects"). Each test is a deliberate reduction
rung — "this small shape passes; this slightly larger shape fails" — that
narrows a defect surface for the owning compiler skill. The naming
convention is itself the regression-guard signal:

- `sprint59_cache_repro.rs::s59_cache_hit_*` — Sprint 59 Workstream A
  (cache-hit prelude-restoration bug). 2 tests.
- `sprint59_defects456_repro.rs::d45_*` — Defects 4 + 5 (`/run-tests`
  batched-dispatch crashes). 22 tests + 1 minimal RC underflow. 23 total.
- `sprint59_defects456_repro.rs::d6_*` — Defect 6 (exemplar solver
  segfault / stack-overflow on full grids). 11 tests.

Every test in `d45_*` and `d6_*` carries an inline `// FIXME(/backend)`
hypothesis. These are pre-Sprint 63 inline FIXMEs (predate the M7
methodology pivot) — they MUST migrate to numbered `design/arch/fixmes/`
files at harvest time, not at carry-forward time. The hypothesis content
is load-bearing for the regression cohort and is preserved verbatim in
the carry-forward.

**Carry-forward coverage of the cluster's surface is partial.** The
existing `tests/cache.rs::cache_repl_second_session_loads_prelude_from_cache`
(carry from `legacy/sprint23.rs::cache_repl_loads_on_startup`, Wave 6
batch 2 Part A) covers the *positive* prelude-restoration angle for the
TestStandard prelude, but the **minimum-viable plain-fn prelude** angle
and the **empty-prelude basic-eval** angle (the sprint59_cache_repro
reductions) have no carry-forward today. Likewise, `tests/regression.rs`
holds a single Wave 6 batch 1 carry (T-S2-2 inline-ADT-arg-wrapping-Vec)
but none of the d45/d6 reduction surface.

Therefore dispositions skew heavily to **GAP-COVER REGRESSION-GUARD**.

## Summary

| Disposition | Count |
|---|---:|
| COVERED | 0 |
| DUPLICATE-IN-LEGACY | 0 |
| GAP-COVER | 36 (of which REGRESSION-GUARD: 36) |
| GAP-HARVEST | 0 |
| **Total** | **36** |

Of the 36 REGRESSION-GUARDs:

- 2 named Sprint 59 Workstream A cache-restoration regression guards
  (`s59_cache_hit_*`)
- 22 d45 reduction rungs probing `/run-tests` batched-dispatch crash
  surface
- 1 d45 minimal-RC-underflow guard
- 11 d6 reduction rungs probing exemplar solver
  segfault/stack-overflow surface (4 of which currently FAIL — Defect 6
  remains open per ledger entries)

**Current pass/fail status against the binary at audit time:**

- `sprint59_cache_repro.rs`: 2/2 PASS
- `sprint59_defects456_repro.rs`: 30/34 PASS, 4 FAIL (Defect 6
  ledger entries — `d6_exemplar_propagate_only`,
  `d6_exemplar_propagate_single_pass`, `d6_exemplar_solve_all_dots`,
  `d6_exemplar_solve_minimal_puzzle_no_io`)

The 4 failing tests are confirmed-open Defect 6 regression surfaces per
`tests/plan/ledger.md §"Escaped carries — surfaced Sprint 61 Wave 3"`.
The carry-forward authoring MUST preserve them as failing-not-ignored
per `memory/feedback_failing_not_ignored.md` and the existing ledger
entries (which name the legacy file's test names — those entries will
re-target the carry-forward names at carry-forward time, OR the legacy
ledger references stay valid via the quarantined-source path until the
defect resolves).

A 5th historically-listed test (`d6_exemplar_eliminate_from_peers`) was
named in the Sprint 61 handoff brief but has been confirmed to PASS
consistently (ledger §note). It carries forward as REGRESSION-GUARD
PASSING.

## Per-test classifications

### File 1: tests/sprint59_cache_repro.rs (2 tests)

The file's docstring (lines 1–22) names the bug shape: REPL session 2
hits the cache for `prelude.{o,meta.json}` but does not rebind the
prelude's exported symbols, so a form referring to a prelude binding
fails with `undefined variable: …`. The two tests partition the
discrimination axis:

- (A) any prelude symbol → triggers; (B) empty prelude → does not
  trigger (cache-hit module-load path itself is OK; bug is symbol
  rebinding).

| # | Test name | LOC | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|---|
| 1 | `s59_cache_hit_plain_prelude_fn_not_restored` | 105–126 | repl/spec.md §15.2 + design/int/repl-lifecycle.md §4.2 — Cache Load on Startup/Reset; design/int/cache-prelude-restoration-repro.md | minimal prelude (`(defn f [] 42)`), session 2 cache hit must rebind `f` | GAP-COVER (REGRESSION-GUARD) | Named Sprint 59 Workstream A regression. **Distinct from `cache.rs::cache_repl_second_session_loads_prelude_from_cache`**: that test uses TestStandard prelude (operator + trait + ADT machinery — many bindings, complex). This test uses the **smallest possible prelude** — a single plain `defn`, no operators, no traits, no impls, no ADTs. The reduction angle is "if this fails, the bug is universal across binding types; if it passes, the bug is specific to operator/trait machinery." Carry to `cache.rs` as a sibling test. |
| 2 | `s59_cache_hit_empty_prelude_basic_eval_works` | 134–152 | repl/spec.md §15.2 + design/int/repl-lifecycle.md §4.2 — empty-prelude pathway | empty `;; empty\n` prelude; session 2 must still produce 42 from a literal expression | GAP-COVER (REGRESSION-GUARD) | The **negative-control** reduction — no symbols to rebind, only the cache-hit module-load pathway. If it fails, the bug is at the module-level not the symbol-rebinding level. Discriminates the bug shape. Carry to `cache.rs` as a sibling test. |

**Carry target:** Both tests carry to `tests/cache.rs` as REPL-mode
prelude-restoration regression guards, alongside the existing
`cache_repl_second_session_loads_prelude_from_cache`. Names stay
discriminative-prefixed (e.g.,
`cache_repl_minimal_plain_fn_prelude_restored_on_session_2` /
`cache_repl_empty_prelude_session_2_evaluates_literal`).

### File 2: tests/sprint59_defects456_repro.rs (34 tests)

The file's docstring (lines 1–24) names two defect clusters:

- **Defects 4+5**: `/run-tests` on a multi-test module crashes
  (SIGSEGV/SIGTRAP) — narrowed by progressively widening test bodies
  from trivial → str-concat → cross-module ADT → real exemplar shape.
- **Defect 6**: exemplar solver segfault, NOT a simple stack overflow
  — narrowed by progressively widening from Vec-of-Int-COW →
  Vec-of-ADT-COW → Grid wrapper → recursive solve → real exemplar
  source.

Subprocess-driven (`drive_repl` for REPL `/run-tests` crashes;
`run_file` for `--run` crashes). Crash detection via `assert_no_signal_crash`
(exit 139 SIGSEGV / 133 SIGTRAP / None signal-killed).

#### §A — d45 cluster: /run-tests batched dispatch (synthetic, single-file)

Tests #1–#5 + #14–#15 + #18 — synthetic single-file modules
under `/run-tests`.

| # | Test name | LOC | Spec property | Angle | Disposition |
|---:|---|---|---|---|---|
| 1 | `d45_baseline_trivial_run_tests_no_crash` | 174–200 | repl/spec.md §16.3 — /run-tests | trivial `(defn test-none-ok [] None)` | GAP-COVER (REGRESSION-GUARD) — baseline rung |
| 2 | `d45_single_str_concat_contains_run_tests_no_crash` | 205–230 | repl/spec.md §16.3 — single-test str-concat | one test body w/ `(contains? (str-concat ...) "world")` | GAP-COVER (REGRESSION-GUARD) — single-body rung |
| 3 | `d45_wrap_tag_html_verbatim_run_tests_no_crash` | 235–261 | repl/spec.md §16.3 — 5-deep nested str-concat | inlined `wrap-tag` from html.cl, single test, str-eq compare | GAP-COVER (REGRESSION-GUARD) — nested-str rung |
| 4 | `d45_multiple_tests_with_contains_run_tests_no_crash` | 265–288 | repl/spec.md §16.3 — multi-test batch dispatch | three tests sharing `(mk-str)` helper | GAP-COVER (REGRESSION-GUARD) — multi-test rung |
| 5 | `d45_form_shaped_body_run_tests_no_crash` | 292–310 | repl/spec.md §16.3 — let + str-eq + Option | minimal form-shape | GAP-COVER (REGRESSION-GUARD) — form rung |
| 14 | `d45_two_trivial_tests_run_tests_no_crash` | 754–765 | repl/spec.md §16.3 — 2 trivial tests | two no-op tests | GAP-COVER (REGRESSION-GUARD) — batch-size rung |
| 15 | `d45_ten_str_bodies_run_tests_no_crash` | 770–798 | repl/spec.md §16.3 — 10 str-concat tests | 10 tests w/ same `(mk)` helper | GAP-COVER (REGRESSION-GUARD) — 10-test batch rung |
| 18 | `d45_solution_cell_single_call_no_rc_underflow` | 1749–1766 | spec/12-runtime.md §12.3 — consuming convention RC balance | direct call to `solution-cell g g 0`, two consecutive invocations | GAP-COVER (REGRESSION-GUARD) — minimal RC-ABI shape; carries `// spec:` annotation already |

#### §B — d45 cluster: cross-module fixture probing

Tests #19–#23 + #6 — two-file synthetic modules, ADT export from `lib`.

| # | Test name | LOC | Angle | Disposition |
|---:|---|---|---|---|
| 19 | `d45_cross_module_adt_basic_no_crash` | 836–841 | minimum 2-file: lib exports Cell ADT, mymod uses ctor + match in test body | GAP-COVER (REGRESSION-GUARD) — cross-module-ADT-only rung |
| 20 | `d45_cross_module_import_but_no_use_no_crash` | 879–884 | imports Grid ADT but tests are pure-string | GAP-COVER (REGRESSION-GUARD) — import-without-use rung |
| 21 | `d45_cross_module_grid_build_in_test_no_crash` | 908–913 | one test builds (Grid (Vec Cell)) via cross-module ctor | GAP-COVER (REGRESSION-GUARD) — Grid-build rung |
| 22 | `d45_cross_module_html_like_batch_no_crash` | 988–993 | 4 tests: pure-string + Grid-build + page-derivation | GAP-COVER (REGRESSION-GUARD) — html-like-mix rung |
| 23 | `d45_cross_module_html_full_10_tests_no_crash` | 1122–1127 | 10-test synthetic batch closely matching html.cl shape | GAP-COVER (REGRESSION-GUARD) — full-batch synthetic rung |

#### §C — d45 cluster: real exemplar source probing

Tests #6–#7 + #24–#26 — copies the actual `exemplar/html.cl` (with
optional trimmed grid).

| # | Test name | LOC | Angle | Disposition |
|---:|---|---|---|---|
| 6 | `d45_real_exemplar_html_run_tests_no_crash` | 332–347 | real `exemplar/html.cl` via `/run-tests html` | GAP-COVER (REGRESSION-GUARD) — full-exemplar rung |
| 7 | `d45_real_exemplar_html_single_run_test_no_crash` | 359–370 | single `(run-test "html/test-wrap-tag")` (not /run-tests batch) | GAP-COVER (REGRESSION-GUARD) — single-vs-batch dispatch rung |
| 24 | `d45_real_html_with_trimmed_grid_no_crash` | 1171–1177 | real html.cl + trimmed grid.cl | GAP-COVER (REGRESSION-GUARD) — trimmed-grid rung |

#### §D — d45 cluster: html-source reduction ladder

Tests #25–#34 — progressive html-source strip (no css, solution-only,
1 test, 2 tests, 3 tests mixed, 2-arg solution, min v1, min v2).

| # | Test name | LOC | Angle | Disposition |
|---:|---|---|---|---|
| 25 | `d45_html_no_css_no_crash` | 1331–1337 | real html.cl minus css | GAP-COVER (REGRESSION-GUARD) — no-css rung |
| 26 | `d45_html_solution_tests_only_no_crash` | 1422–1428 | only 3 solution-page tests | GAP-COVER (REGRESSION-GUARD) — solution-only rung |
| 27 | `d45_html_one_test_no_crash` | 1470–1476 | one test, simplified solution-cell | GAP-COVER (REGRESSION-GUARD) — 1-test rung |
| 28 | `d45_html_two_tests_no_crash` | 1521–1527 | 2 tests sharing make-grid + page | GAP-COVER (REGRESSION-GUARD) — 2-test shared-helper rung |
| 29 | `d45_html_three_tests_mixed_no_crash` | 1589–1595 | 3 tests + second grid-build helper | GAP-COVER (REGRESSION-GUARD) — 2-grid-build-fns rung |
| 30 | `d45_html_two_arg_solution_no_crash` | 1655–1661 | 2-arg solution-cell (2 grid params) | GAP-COVER (REGRESSION-GUARD) — 2-arg-cell rung |
| 31 | `d45_html_min_v1_no_crash` | 1698–1704 | 1 test, 9-cell grid, flat str-concat | GAP-COVER (REGRESSION-GUARD) — 9-cell rung |
| 32 | `d45_html_min_v2_no_crash` | 1729–1735 | 1 test, 1-cell grid, no loop | GAP-COVER (REGRESSION-GUARD) — 1-cell rung |

#### §E — d6 cluster: synthetic Vec/ADT/Grid COW reductions

Tests #8–#11 — single-file `--run` reductions.

| # | Test name | LOC | Angle | Disposition | Status |
|---:|---|---|---|---|---|
| 8 | `d6_vec_cow_int_loop_does_not_segv` | 388–418 | Vec of Int + recursive vec-set loop, no ADT | GAP-COVER (REGRESSION-GUARD) — int-only rung | PASS |
| 9 | `d6_vec_cow_adt_loop_does_not_segv` | 423–455 | Vec of ADT (Cell) + COW loop, no Grid wrapper | GAP-COVER (REGRESSION-GUARD) — ADT-cells rung | PASS |
| 10 | `d6_grid_wrapper_cow_does_not_segv` | 461–501 | Grid (Vec Cell) wrapper + set-cell COW | GAP-COVER (REGRESSION-GUARD) — Grid-wrap rung | PASS |
| 11 | `d6_solve_recursive_adt_does_not_segv` | 507–553 | recursive solve-shape, depth=30, ADT match | GAP-COVER (REGRESSION-GUARD) — recursive-solve rung | PASS |

#### §F — d6 cluster: real-exemplar reductions (subset failing)

Tests #12–#13 + #16–#17 — copies real `exemplar/grid.cl` + `solver.cl`.

| # | Test name | LOC | Angle | Disposition | Status |
|---:|---|---|---|---|---|
| 12 | `d6_exemplar_solve_minimal_puzzle_no_io_does_not_segv` | 565–598 | full solve on 17-clue puzzle, no IO | GAP-COVER (REGRESSION-GUARD) — Sprint 61 W3 LEDGER ENTRY (FAILING) | **FAIL** (open Defect 6 ledger) |
| 13 | `d6_exemplar_propagate_only_does_not_segv` | 604–630 | single propagate call on 17-clue puzzle | GAP-COVER (REGRESSION-GUARD) — Sprint 61 W3 LEDGER ENTRY (FAILING) | **FAIL** (open Defect 6 ledger) |
| 16 | `d6_exemplar_solve_all_dots_does_not_segv` | 635–658 | solve on all-dots empty puzzle | GAP-COVER (REGRESSION-GUARD) — Sprint 61 W3 LEDGER ENTRY (FAILING) | **FAIL** (open Defect 6 ledger) |
| 17 | `d6_exemplar_propagate_single_pass_does_not_segv` | 667–689 | single propagate-pass-helper call | GAP-COVER (REGRESSION-GUARD) — Sprint 61 W3 LEDGER ENTRY (FAILING) | **FAIL** (open Defect 6 ledger) |

#### §G — d6 cluster: real-exemplar reductions (passing)

Tests #6–#7 + #14–#15 in d6 — real exemplar reductions that pass.

| # | Test name | LOC | Angle | Disposition | Status |
|---:|---|---|---|---|---|
| 14 | `d6_exemplar_eliminate_from_peers_does_not_segv` | 696–718 | one eliminate-from-peers call on cell 0 | GAP-COVER (REGRESSION-GUARD) — finest-grain reduction | PASS (per ledger §note 2026-04-22 SHA `35062ca` and re-verified at audit time 2026-05-05) |
| 15 | `d6_exemplar_make_grid_only_does_not_segv` | 722–741 | construct Grid via make-grid only | GAP-COVER (REGRESSION-GUARD) — pre-solver-init rung | PASS |

(Note: tests #14, #15 here in §G are the make_grid_only and
eliminate_from_peers tests at LOC 722 and 696 — they pass. I'm
keeping the audit-table numbering by file order; numbering is
incidental, the test names are what carry forward.)

## Total: 36 carry-forwards (2 from cache_repro + 34 from defects456_repro)

## Carry-forward target files

A single new home is appropriate for the d45 + d6 cluster: it is a
defect-repro cohort, exactly matching the existing `tests/regression.rs`
disposition (which already holds Wave 6 batch 1 T-S2-2). The d45/d6
reductions are:

- Self-contained codegen / RC / dispatch regression guards.
- Not spec-anchored to a user-observable spec property other than
  "the program does not crash" (the spec anchor is mostly
  `repl/spec.md §16.3` for d45 + `spec/12-runtime.md §12.5` for d6
  recursion + `tests/plan/ledger.md` Defect 6 entry for d6 specifically).
- Per `memory/feedback_repros_join_suite.md` discipline: regression
  guards committed to the suite for eternity.

The cache_repro tests, being prelude-restoration cache regression
guards, naturally extend `tests/cache.rs` (which already holds the
TestStandard-prelude variant of the same surface, carry from
`legacy/sprint23.rs::cache_repl_loads_on_startup`).

| Originating tests | Target file | Notes |
|---|---|---|
| #1, #2 (cache_repro) | extend `tests/cache.rs` | Sibling tests to `cache_repl_second_session_loads_prelude_from_cache` |
| #1–#34 (defects456_repro) | extend `tests/regression.rs` | Defect-repro cohort, matches T-S2-2 disposition |

## Tests flagged for /sprint judgment

### A. Defect 6 4-failing carry-forwards

The 4 currently-failing `d6_exemplar_*` tests (12, 13, 16, 17) are
Sprint 61 Wave 3 ledger entries with disposition
`exemplar-gap (owner=/port, underlying-owner=/backend)`. Per
`memory/feedback_failing_not_ignored.md` and existing ledger discipline,
they MUST land un-ignored. The carry-forward will fail-not-ignored, and
the existing ledger entries (which name the legacy test names) will
need a sibling mention for the carry-forward names — though the simpler
discipline is that the legacy ledger entries name the **legacy file's**
tests and will resolve when the underlying defect is fixed; the
carry-forward tests inherit the same ledger entry by reference.

Recommendation: file FIXME 0145 covering both quarantined files. Within
the FIXME, document that 4 tests carry forward as failing-not-ignored
guards for open Defect 6, with cross-references to the existing 4
ledger entries (lines 83–131 of `tests/plan/ledger.md`).

### B. Inline FIXMEs in legacy file

`sprint59_defects456_repro.rs` has **24 inline `// FIXME(/backend)`
markers** — one per d45/d6 test (except #18 `d45_solution_cell_single_call`
which carries a `// spec:` annotation). These are pre-Sprint 63 inline
FIXMEs (predate the M7 methodology pivot). Per Wave 6 batch 2 precedent
(FIXME 0144 §"Inline FIXMEs preserved in legacy/sprint23.rs"), the
established discipline is:

1. Preserve them inline in the quarantined source — **read-only** after
   quarantine.
2. Mark them as "verify during harvest" in the harvest FIXME.
3. Each surviving FIXME (post-harvest review) migrates to its own
   numbered `design/arch/fixmes/NNNN-*.md` per Sprint 63 M7 protocol;
   if all prove stale (e.g., the underlying defect is resolved and the
   reduction merely passes), delete the legacy file outright at
   harvest close.

The 24 hypothesis comments are load-bearing — they document
calibration: "if PASS, this rung passed and the next axis to probe is
X; if FAIL, the defect reduces to this minimum shape." Carry-forward
authoring will preserve the hypothesis content **inline in the
carry-forward source** so the regression-discrimination context is
not lost.

### C. The `fresh_dir` runs-tree pattern in sprint59_cache_repro.rs

Lines 37–55 of `tests/sprint59_cache_repro.rs` use a custom
`fresh_dir(label)` helper writing to
`tests/sprint59/.runs/{RUN_TS}/{n_label}/`. Per `tests/CLAUDE.md`
§"Fresh Temp Directory per Test", this is the permitted pattern as
long as `tests/sprint59/` is added to `.gitignore`. **Already done**:
the legacy file's `tests/sprint59/.runs/` tree is already gitignored
(by virtue of the `.runs/` general pattern), but the carry-forward will
use the new harness's `Cranelisp::new()` builder which manages its own
TempDir — no `tests/sprint59/.runs/` references survive.

### D. Carry-forward shape: the d6 4 failing cases

The 4 failing d6 tests use `copy_exemplar_tree(...)` (the file's
inline `copy_exemplar_tree` helper at LOC 61–81). The new harness has
`Cranelisp::new().fixture_tree(...)` for this — but `fixture_tree`
copies from `tests/fixtures/`, not from `exemplar/`. Two options:

1. Use `Cranelisp::new()`'s file/user/file methods to copy the
   exemplar source files individually into the per-test TempDir. This
   matches the harness's preferred pattern but requires a
   `read_to_string(project_root().join("exemplar/...")) ` at the
   carry-forward site, with a `// read-only on project_root` annotation
   per `tests/CLAUDE.md` §"Fresh Temp Directory per Test".
2. Add a `Cranelisp::fixture_tree_from_workspace(...)` method that
   copies from `project_root().join(<rel>)` (e.g., `"exemplar"`).
   This is a harness-feature request (file an `/qa` FIXME if needed).

Recommendation: option (1). Inline a small helper in `regression.rs`
(`copy_exemplar_into_tmp(out_subdir)`) that reads files via
`std::fs::read_to_string(project_root().join("exemplar").join(name))`
and writes them via the existing `Cranelisp::file()`. Same pattern
as `tests/exemplar.rs::t_s2_1_*` already uses (per Wave 6 batch 1).

### E. Fixture stability — exemplar/ source dependency

The 4 failing d6 tests + 2 passing d6 tests + 2 d45 tests (#6, #7) all
depend on `exemplar/grid.cl`, `exemplar/solver.cl`, and `exemplar/html.cl`.
Per `memory/feedback_repro_handoff.md`: "minimal repros live in tests/,
not exemplar/." The strict reading is that these tests should be
inline-rewritten, not copy-from-exemplar (to remove the cross-skill
stability risk if `/port` redesigns the exemplar).

However, the 4 failing tests are EXACTLY the Sprint 61 Wave 3 ledger
entries — they reproduce the open Defect 6 against the **real**
exemplar source. Inlining them would change their semantic — they
would no longer be the authoritative repro. The existing ledger
disposition relies on them reproducing against `exemplar/grid.cl` +
`solver.cl`.

Recommendation: keep the copy-from-exemplar shape for the d6 tests
(matches existing ledger semantics). Annotate each test with a comment
noting the cross-skill stability risk per
`memory/feedback_repro_handoff.md`, so a future audit can decide
whether to inline-rewrite once Defect 6 is fixed and the tests
become passing regression guards rather than open repros. This is the
same disposition Wave 6 batch 1 took for `t_s2_1` (with a different
recommendation — Wave 6 batch 1 inlined T-S2-1; Wave 6 batch 3 keeps
the d6 copy-from-exemplar shape because the repros are open, not
fixed).

## Recommendations

1. **Carry forward all 36 tests.** Zero DUPLICATE-IN-LEGACY, zero
   COVERED, zero GAP-HARVEST. Every test is a discrete reduction rung
   anchoring a specific historic defect surface.

2. **Two carry-forward targets**: extend `tests/cache.rs` (+2 tests)
   and extend `tests/regression.rs` (+34 tests). No new files.

3. **One harvest FIXME** (target `/backend`): 0145, covering both
   quarantined files. Both surfaces are squarely in `/backend`'s
   ownership — d45 cluster is RC/dispatch (run_test_by_name + batched
   /run-tests), d6 cluster is Vec/ADT COW + recursive match codegen,
   and the s59 cache cluster is prelude-symbol re-binding on cache
   load (in `/int`'s repl-lifecycle, but the underlying observable is
   a `/backend` cache-restoration defect already largely resolved per
   Sprint 59 Workstream A — the regression guards remain). Per Wave 6
   batch 2 precedent (one harvest FIXME for the whole quarantine
   batch), fold both files into a single FIXME named
   `0145-harvest-tests-legacy-sprint59-repros.md`.

4. **Preserve 4 failing d6 tests as failing-not-ignored.** They are
   Sprint 61 Wave 3 ledger entries naming Defect 6 as open. Per
   `memory/feedback_failing_not_ignored.md`, failing tests stay
   un-ignored as the durable record. The carry-forward names will
   either be referenced in updated ledger entries (cross-link
   carry-forward → legacy name) or (simpler) the existing ledger
   entries continue to name the legacy file's tests via the
   `tests/legacy/sprint59_defects456_repro.rs::*` path until the
   defect resolves.

5. **Preserve 24 inline `FIXME(/backend)` hypothesis comments** in the
   carry-forward source verbatim. The discrimination context is
   load-bearing for the regression cohort. The legacy file is
   read-only post-quarantine; harvest at FIXME 0145 close decides
   whether to migrate each to a numbered fixme file.

6. **Inline `copy_exemplar_into_tmp` helper** in `regression.rs` for
   d6 + d45 exemplar-dependent tests, matching `tests/exemplar.rs`'s
   approach. Use `// read-only on project_root` annotations on the
   `read_to_string` callsites.

## Methodology takeaway

Both files are **100% GAP-COVER REGRESSION-GUARD** (36/36):

| File | Tests | GAP-COVER | DUPLICATE | COVERED | Yield % |
|---|---:|---:|---:|---:|---:|
| `sprint59_cache_repro.rs` | 2 | 2 | 0 | 0 | **100%** |
| `sprint59_defects456_repro.rs` | 34 | 34 | 0 | 0 | **100%** |
| **Wave 6 batch 3 total** | **36** | **36** | **0** | **0** | **100%** |

Same structural reason as Wave 6 batch 2 (sprint23.rs at 97%): these
are Sprint 59-cohort defect-reduction work-product files. The defects
they reduce against (4, 5, 6, plus cache restoration) are
sprint-specific surfaces with no pre-existing carry-forward universe.
The dedup risk was zero by construction.

This validates the Wave 5.5/5.6 regression-guard rule operationally
for the third audit in a row: regression-named work-product files
exhaustively partition the carry-forward surface — they are
presumptively discriminating and the per-test review converges quickly
(the audit's per-test classification is essentially mechanical once
the cluster character is established).

The most consequential downstream work: **Defect 6 remains open** at
S64 close. The 4 failing carry-forwards will continue to fail until
`/backend` resolves the deep-recursion stack-overflow root cause in
JIT'd `propagate`/`solve` on 81-cell Vec-copying ADT traversal. The
regression cohort is the durable record.
