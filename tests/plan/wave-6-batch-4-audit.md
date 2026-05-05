# Wave 6 batch 4 — sprint60 trio audit

Per-test audit of three Sprint 60-cohort reduction files:

- `tests/sprint60_cache_build_marker.rs` (261 LOC, 3 tests)
- `tests/sprint60_reduction.rs` (721 LOC, 17 tests) — chunked review
- `tests/sprint60_run_tests_reduction.rs` (325 LOC, 5 tests)

Total: **25 tests** across **3 files**.

Author: `/qa` (audit + carry-forward dispatch, 2026-05-05). Methodology
identical to Wave 6 batches 1–3: per-test review against the existing
e2e carry-forward universe with disposition codes (COVERED /
DUPLICATE-IN-LEGACY / GAP-COVER / REGRESSION-GUARD / GAP-HARVEST),
spec-anchored dedup, regression-named tests treated as presumptively
discriminating per Wave 5.5/5.6 protocol.

## Cluster character

All three files are Sprint 60-cohort defect-reduction work-product files:

- `sprint60_cache_build_marker.rs` — Sprint 60 Workstream C (cache
  build-id invalidation). Subprocess-level integration coverage for the
  `build_id` field added to `.meta.json`. The header explicitly states
  unit-tier coverage already lives in
  `crates/cranelisp-backend/src/cache/serialize.rs` —
  this file is the e2e wrapper around the user-surface invariant
  ("tampering with the field forces a fresh build"). 3 tests.
- `sprint60_reduction.rs` — Sprint 60 Wave 1 + 2 cache-reuse and
  drop-glue reductions. Two reduction clusters: §A cache-reuse SIGSEGV
  (Step 1 baseline + 2.1–2.7 reductions + 3 controls = 11 tests; all
  PASS today); §B drop-glue / auto-curry double-free (Step 1 baseline +
  5 reductions/controls = 6 tests; all PASS today). 17 tests total.
- `sprint60_run_tests_reduction.rs` — Sprint 60 Wave 2 Round 3 reduction
  of `run_tests_batched_invocation_no_crash`. Persistence-collapse
  residue (REPL-eval'd import + empty `user.cl` produces "no parsed
  sexps" at shutdown). 4 named-`_failing` reductions + 1 named-
  `_passes_control`. 5 tests total.

Every test file's header and individual test docstrings carry inline
`// FIXME(/backend)` (or in the case of `sprint60_run_tests_reduction.rs`,
`// FIXME(/int) or FIXME(/backend)`) hypothesis comments. These are
pre-Sprint 63 inline FIXMEs (predate the M7 methodology pivot) that
must migrate to numbered `design/arch/fixmes/` files at harvest time
per Sprint 63 M7 protocol — the Wave 6 batch 2/3 precedent
(FIXMEs 0144 / 0145).

## Current pass/fail status against the binary at audit time

(2026-05-05, against `cargo build` of branch `main` at `c99cbab`):

- `sprint60_cache_build_marker.rs`: 3/3 PASS
- `sprint60_reduction.rs`: 17/17 PASS (the cache-reuse cluster's
  baseline crash and drop-glue cluster's baseline crash both pass on
  current binary — these reductions WERE the path that drove the
  Sprint 60 Workstream A single-GOT fix and the subsequent W2 R2 work
  that resolved the drop-glue defect)
- `sprint60_run_tests_reduction.rs`: 4/5 PASS, 1 FAIL — only test #3
  `s60_run_tests_reduction_3_quit_variant_failing` currently fails with
  the documented bug shape (the persistent worker pool aborts with
  `register_dep_for_eval MUST publish dep_sexps before calling
  scheduler.register_module`). Tests #1, #2, #4 named `_failing` PASS
  today (the bug appears resolved for those shapes); test #5 control
  PASSES.

The test #3 failure surface is the SAME persistence-collapse residue
the file's header documents (`module 'user' failed: ... no parsed
sexps`) — but the manifestation has shifted from the `Failed`/shutdown
path observed at sprint authorship to a `register_module` ordering
panic in the active code path. This IS a confirmed open defect
(failing-not-ignored).

## Methodology recap

Per Wave 5.6 brief (in force from Waves 5.5/5.6):

1. No exact 1:1 duplicates after `[Tested ...]` carry-forward exists.
2. Multi-angle on same spec property → PRESERVE.
3. Regression-named tests are presumptively discriminating — default
   to GAP-COVER (REGRESSION-GUARD) unless EXACT 1:1 duplicate is
   provable.
4. Spec-anchoring is the dedup criterion, not source-shape match.

## Summary

| Disposition | Count |
|---|---:|
| COVERED | 0 |
| DUPLICATE-IN-LEGACY | 0 |
| GAP-COVER | 25 (of which REGRESSION-GUARD: 25) |
| GAP-HARVEST | 0 |
| **Total** | **25** |

Same structural finding as Wave 6 batches 2 + 3: regression-named
work-product files exhaustively partition the carry-forward surface.
The dedup risk is zero by construction — every test is a deliberate
reduction rung against a specific historic defect surface, with no
pre-existing carry-forward universe to dedup against.

## Per-test classifications

### File 1: tests/sprint60_cache_build_marker.rs (3 tests)

The file's docstring (lines 1–13) explicitly notes that unit-tier
coverage for `build_id` serialise/deserialise lives in
`crates/cranelisp-backend/src/cache/serialize.rs` (`build_id_round_trip_succeeds`,
`stale_build_id_produces_build_id_mismatch`,
`missing_build_id_field_routes_cache_stale`). These three e2e tests
are user-surface wrappers proving the unit invariants surface
correctly through the binary. The trio partitions the discrimination
axis: (A) build_id is written; (B) tampered build_id is rejected and
restamped; (C) missing build_id (pre-Sprint-60 shape) is treated as
stale.

| # | Test name | LOC | Spec property | Angle | Disposition |
|---:|---|---|---|---|---|
| 1 | `cache_meta_carries_build_id_after_first_compile` | 137–167 | design/backend/module-caching.md §4 — Serialization Format (build_id round-trip via real binary) | first compile populates `build_id` non-empty + `schema_version` co-present | GAP-COVER (REGRESSION-GUARD) — write-side e2e wrapper around unit `build_id_round_trip_succeeds` |
| 2 | `cache_meta_with_stale_build_id_triggers_recompile` | 176–218 | design/backend/module-caching.md §6 — Cache Invalidation Strategy (build_id mismatch triggers recompile) | tamper meta.build_id with synthetic value; second compile must re-stamp original | GAP-COVER (REGRESSION-GUARD) — invalidation e2e wrapper around unit `stale_build_id_produces_build_id_mismatch` |
| 3 | `cache_meta_without_build_id_field_triggers_recompile` | 223–261 | design/backend/module-caching.md §6 — pre-Sprint-60 shape (missing field) treated as stale | strip build_id field; second compile must restore it | GAP-COVER (REGRESSION-GUARD) — schema-evolution e2e wrapper around unit `missing_build_id_field_routes_cache_stale` |

**Carry target:** All 3 tests carry to `tests/cache.rs` as siblings of
the existing `cache_*` tests. The file already covers cache hit/miss
+ invalidation extensively; build_id discrimination joins that surface.

### File 2: tests/sprint60_reduction.rs (17 tests) — chunked review

The file's docstring (lines 1–28) names the cluster character: cache-
reuse SIGSEGV reductions from the exemplar-shaped baseline down to a
5-LOC two-file minimum. Step 2.1–2.7 strip features one at a time;
each remaining-failing reduction is a regression guard. The Wave 2
Round 2 addendum (lines 416–460) adds drop-glue/auto-curry reduction
chain — Grid-wrapped Vec + double `cell-at` call → double-free.

#### Chunk A — cache-reuse cluster (lines 1–414, 11 tests + 3 controls)

Step 1: exemplar-shaped baseline.

| # | Test name | LOC | Angle | Disposition | Status |
|---:|---|---|---|---|---|
| 1 | `s60_cache_reuse_exemplar_shaped_no_crash` | 174–179 | Cell ADT + Grid wrapper + recursive helper; A.3b's uncommitted finding | GAP-COVER (REGRESSION-GUARD) — exemplar-shaped baseline | PASS |

Step 2: progressive reductions.

| # | Test name | LOC | Angle | Disposition | Status |
|---:|---|---|---|---|---|
| 2 | `s60_cache_reuse_no_cell_adt_no_crash` | 205–210 | strip Cell ADT; raw Ints in Vec | GAP-COVER (REGRESSION-GUARD) — Cell-not-load-bearing rung | PASS |
| 3 | `s60_cache_reuse_no_wrapper_adt_no_crash` | 224–229 | strip Grid wrapper; make-grid returns Vec | GAP-COVER (REGRESSION-GUARD) — wrapper-not-load-bearing rung | PASS |
| 4 | `s60_cache_reuse_non_recursive_helper_no_crash` | 241–246 | one-shot vec-push, no recursion | GAP-COVER (REGRESSION-GUARD) — recursion-not-load-bearing rung | PASS |
| 5 | `s60_cache_reuse_nullary_helper_no_crash` | 258–263 | nullary helper, no args | GAP-COVER (REGRESSION-GUARD) — arity-not-load-bearing rung | PASS |
| 6 | `s60_cache_reuse_empty_vec_helper_no_crash` | 275–280 | helper returns `[]`, no vec-push | GAP-COVER (REGRESSION-GUARD) — vec-push-not-load-bearing rung | PASS |
| 7 | `s60_cache_reuse_int_helper_no_heap_no_crash` | 294–299 | helper returns Int 42, NO HEAP | GAP-COVER (REGRESSION-GUARD) — heap-not-load-bearing rung; rules out RC | PASS |
| 8 | `s60_cache_reuse_minimal_5_loc_no_crash` | 354–359 | THE 5-LOC MINIMUM: int helper + cross-module wrapper, no `let` | GAP-COVER (REGRESSION-GUARD) — minimal crashing shape | PASS |

Step 3: negative controls.

| # | Test name | LOC | Angle | Disposition | Status |
|---:|---|---|---|---|---|
| 9 | `s60_control_single_file_no_crash` | 374–379 | single-file (no cross-module) | GAP-COVER (REGRESSION-GUARD) — pins cross-module-import as load-bearing | PASS |
| 10 | `s60_control_no_intra_module_call_no_crash` | 390–395 | no intra-module call in grid | GAP-COVER (REGRESSION-GUARD) — pins intra-module-call as load-bearing | PASS |
| 11 | `s60_control_direct_helper_call_no_crash` | 409–414 | direct call to helper, no wrapper | GAP-COVER (REGRESSION-GUARD) — pins imported-wrapper-calling-helper as load-bearing | PASS |

#### Chunk B — drop-glue cluster (lines 416–722, 6 tests)

Wave 2 Round 2: drop-glue / auto-curry double-free reductions.
10-trial cold-cache subprocess loop; 90% crash rate when bug active.

| # | Test name | LOC | Angle | Disposition | Status |
|---:|---|---|---|---|---|
| 12 | `s60_drop_glue_minimal_14_loc_no_crash` | 555–560 | 14-LOC minimal: Grid+Vec + double cell-at + walk fn | GAP-COVER (REGRESSION-GUARD) — drop-glue minimum baseline; carries `// spec: spec/12-runtime.md §12.4` annotation | PASS |
| 13 | `s60_drop_glue_one_cellat_call_passes` | 586–591 | single cell-at, no double-free | GAP-COVER (REGRESSION-GUARD) — pins TWO-call as load-bearing | PASS |
| 14 | `s60_drop_glue_inline_match_passes` | 616–622 | inline match instead of cell-at fn | GAP-COVER (REGRESSION-GUARD) — pins defn-call path (not match-on-Grid) | PASS |
| 15 | `s60_drop_glue_grid_vec_int_no_crash` | 655–658 | Grid (Vec Int) — Cell ADT not load-bearing variant | GAP-COVER (REGRESSION-GUARD) — DUPLICATE COVERAGE GUARD: identical source to #12 by design (header lines 651–653 explicitly preserve as a deletion-resistance double) | PASS |
| 16 | `s60_drop_glue_no_adt_wrapper_passes` | 680–685 | bare Vec, no Grid wrapper | GAP-COVER (REGRESSION-GUARD) — pins ADT-wrapper as load-bearing | PASS |
| 17 | `s60_drop_glue_no_intermediate_fn_passes` | 713–721 | inline both calls in main, no walk fn | GAP-COVER (REGRESSION-GUARD) — pins intermediate-fn-parameter-path as load-bearing | PASS |

#### Carry target

All 17 tests carry to `tests/regression.rs` as siblings of the d45/d6
cluster (Wave 6 batch 3). They are defect-repro regression guards
matching the file's existing disposition. **Note**: tests #12 and #15
are intentional duplicate coverage by the original author's
documented intent (line 651–653 of the legacy file: "committed as a
duplicate regression guard so that a well-intentioned 'simplify' edit
of the minimal test can't silently delete coverage. If one crashes,
both do.") — the carry-forward preserves both with the same comment
inline.

### File 3: tests/sprint60_run_tests_reduction.rs (5 tests)

The file's docstring (lines 1–82) names the cluster character:
persistence-collapse residue when REPL-eval'd `(import [tiny ...])`
runs against an empty entry `user.cl`. The original observation was
exit 1 with "no parsed sexps for module 'user'" at shutdown; the
audit-time observation has shifted (test #3 now panics in
`session_v4.rs:1572` with `register_dep_for_eval MUST publish
dep_sexps before calling scheduler.register_module`) — same root
cause class (entry-module sexp lifecycle inconsistency between REPL
import path and the persistent worker pool).

| # | Test name | LOC | Spec property | Angle | Disposition | Status |
|---:|---|---|---|---|---|---|
| 1 | `s60_run_tests_reduction_1_exemplar_batched_failing` | 166–200 | repl/spec.md §16.2.1 — `/run-tests` clean exit; design/int/repl-lifecycle.md (entry-module sexps) | exemplar /run-tests html with empty user.cl | GAP-COVER (REGRESSION-GUARD) — original cluster baseline | PASS today (bug shifted from this shape) |
| 2 | `s60_run_tests_reduction_2_repl_import_empty_user_failing` | 209–233 | (same anchor) — minimal 19-LOC repro of REPL-import-empty-user shape | one-defn module + REPL import + EOF | GAP-COVER (REGRESSION-GUARD) — minimum reduction | PASS today (bug shifted) |
| 3 | `s60_run_tests_reduction_3_quit_variant_failing` | 242–263 | (same anchor) — /quit variant rules out EOF-ordering | REPL-import + /quit | GAP-COVER (REGRESSION-GUARD) — **FAILING-NOT-IGNORED** open defect surface | **FAIL** — `register_dep_for_eval MUST publish dep_sexps` panic |
| 4 | `s60_run_tests_reduction_4_second_form_variant_failing` | 274–296 | (same anchor) — second-form variant rules out watcher-ordering | REPL-import + bare literal | GAP-COVER (REGRESSION-GUARD) | PASS today (bug shifted) |
| 5 | `s60_run_tests_reduction_5_import_in_file_passes_control` | 306–325 | (same anchor) — control: import in user.cl (not REPL-eval'd) | passing control | GAP-COVER (REGRESSION-GUARD) — pins REPL-eval-path as load-bearing | PASS |

**Carry target:** All 5 tests carry to `tests/regression.rs` as
siblings of the d45 `/run-tests` cluster (Wave 6 batch 3). The shape
is the same: subprocess-driven REPL with stdin pipe, exit-code +
stderr-tail assertion. Test #3 lands failing-not-ignored per
`memory/feedback_failing_not_ignored.md`.

## Tests flagged for /sprint judgment

### A. Test #3 (`s60_run_tests_reduction_3_quit_variant_failing`) — failing carry-forward

The single failing test is a confirmed open defect. The error
signature has shifted since sprint authorship (was: "no parsed sexps
for module 'user'" at shutdown; now: `register_dep_for_eval MUST
publish dep_sexps before calling scheduler.register_module` panic
during the active eval path) but the root-cause class is the same:
entry-module sexp-lifecycle inconsistency between REPL import and the
persistent worker pool.

Per `memory/feedback_failing_not_ignored.md` and the established
ledger discipline, the carry-forward lands un-ignored. The owning
skill is `/int` (REPL session lifecycle / `session_v4.rs`).

### B. Owning-skill alignment for the harvest FIXME

All three files map to the same harvest scope: `/backend` for the
cache-reuse + drop-glue codegen residues; `/int` for the REPL-eval
sexp-lifecycle residue in `sprint60_run_tests_reduction.rs`. The
established Wave 6 b2/b3 protocol is ONE harvest FIXME per quarantine
batch when owners align — but here ownership splits across two
skills (build-id + cache-reuse + drop-glue → /backend; REPL-eval
sexp-lifecycle → /int).

Recommendation: ONE harvest FIXME (0146) targeting **/backend**, with
a cross-reference in the FIXME body to `/int` for the
sprint60_run_tests_reduction.rs subset. The single failing test (#3)
is named explicitly as the open-defect carry-forward; the existing
FIXME 0142 (`int-repl-unclosed-paren-on-eof-silent`) is a related
but distinct REPL-eval defect and stays separate. The harvest FIXME
documents that the run_tests_reduction subset has /int as a
secondary owner — the canonical FIXME-target rule (one target) plus
the documented secondary owner matches the Wave 6 b3 `0145` pattern
(target /backend, secondary observation `/int repl-lifecycle`).

Alternative considered + rejected: file two FIXMEs (0146 /backend,
0147 /int). Rejected because the Wave 6 b2/b3 precedent is to fold
the entire batch's quarantine under one harvest FIXME unless the
subsets are entirely orthogonal — here the underlying surface
(cache-reuse semantics + module-lifecycle wiring) is unified enough
to share scope.

### C. Inline FIXMEs in legacy files

**sprint60_cache_build_marker.rs** — zero inline FIXMEs. The header
(lines 1–13) names the unit-tier counterpart explicitly.

**sprint60_reduction.rs** — **17 inline FIXME(/backend) markers**
across the file. Per Wave 6 b2/b3 protocol (FIXMEs 0144 / 0145), the
established discipline is to preserve them inline in the quarantined
source (read-only) and mark them as "verify during harvest" in the
harvest FIXME. Each surviving FIXME (post-harvest review) migrates to
its own numbered `design/arch/fixmes/NNNN-*.md` per Sprint 63 M7
protocol.

**sprint60_run_tests_reduction.rs** — **1 inline FIXME** in the file
header (line 80–81: `FIXME(/int) or FIXME(/backend)`). The four
`_failing` test names + 1 `_passes_control` carry the
discrimination context in their names.

### D. Existing FIXMEs already resolved by carry-forward

The cache-reuse cluster (#1–11) PASSES on the current binary. The
inline `FIXME(/backend)` hypotheses in those tests are now
"resolved by passing carry-forward" — when the carry-forward
regression.rs tests pass, the hypothesis was either (a) correct +
fixed or (b) a calibration that no longer applies. The harvest FIXME
0146 documents this disposition: 11 of the 17 inline FIXMEs in
sprint60_reduction.rs are resolved-by-passing; the remaining 6
(drop-glue cluster) are also passing today, so the entire file's
inline FIXME population is "verify-then-delete" at harvest, with
`/backend` in the position to confirm the verify step against current
codegen.

### E. spec/12-runtime.md §12.4 anchor

Test #12 (`s60_drop_glue_minimal_14_loc_no_crash`) is the only test
in the trio carrying a non-design-doc `// spec:` annotation:
`// spec: spec/12-runtime.md §12.4 — RC inc/dec must balance; drop
glue must not dec a captured value that the caller also dec's`. The
linter (`spec_link_check.py`) requires this anchor to exist in
`spec/12-runtime.md`. This will be verified before commit; if absent,
the carry-forward annotation drops the section number and uses
`(see header)` per the legacy file's intent.

## Recommendations

1. **Carry forward all 25 tests.** Zero DUPLICATE-IN-LEGACY, zero
   COVERED, zero GAP-HARVEST. Every test is a discrete reduction rung
   anchoring a specific historic defect surface — same structural
   finding as Wave 6 b2 (97%) and b3 (100%).

2. **Two carry-forward targets**: extend `tests/cache.rs` (+3 tests,
   build-id discrimination) and extend `tests/regression.rs` (+22
   tests, cache-reuse + drop-glue + REPL-eval clusters). No new
   files.

3. **One harvest FIXME 0146** (target `/backend`, secondary observer
   `/int` for the sprint60_run_tests_reduction subset), folding all
   three files into one quarantine wave per Wave 6 b2/b3 precedent.

4. **One failing-not-ignored carry-forward** for test #3 of
   sprint60_run_tests_reduction (`register_dep_for_eval` panic). The
   owning skill is `/int` (REPL session_v4 lifecycle wiring). Per
   `memory/feedback_failing_not_ignored.md` it lands un-ignored.

5. **Preserve inline FIXMEs** verbatim in the quarantine source
   (read-only post-quarantine). The harvest FIXME 0146 documents that
   most are "resolved by passing carry-forward" pending /backend
   verification at harvest time.

6. **Cache-reuse cluster's unique angle vs existing cache.rs**: the
   17 sprint60_reduction tests are about **two-run cache-reuse on
   cross-module + intra-module-call shape**, not about cache hit
   semantics in general. They overlap with `cache.rs::cache_*_hit_*`
   in mode (cache-warm `run_again()` pattern) but are discriminated by
   the *crashing-shape-reduction* angle the cache.rs tests do not
   cover. Carry to `regression.rs` (defect cohort), not `cache.rs`.

7. **Build-id tests' unique angle vs existing cache.rs**: cache.rs
   doesn't currently inspect `.meta.json` field contents — these 3
   tests add `build_id` field-level discrimination. They belong in
   `cache.rs`.

## Methodology takeaway

Wave 6 batch 4 is the FOURTH 100% GAP-COVER REGRESSION-GUARD batch
in a row in S64 W6 (b1: 21/21, b2: 59/61, b3: 36/36, b4: 25/25):

| File | Tests | GAP-COVER | DUPLICATE | COVERED | Yield % |
|---|---:|---:|---:|---:|---:|
| `sprint60_cache_build_marker.rs` | 3 | 3 | 0 | 0 | **100%** |
| `sprint60_reduction.rs` | 17 | 17 | 0 | 0 | **100%** |
| `sprint60_run_tests_reduction.rs` | 5 | 5 | 0 | 0 | **100%** |
| **Wave 6 batch 4 total** | **25** | **25** | **0** | **0** | **100%** |

The pattern is now well-validated: regression-named work-product
files exhaustively partition the carry-forward surface — they are
presumptively discriminating and the per-test review converges
quickly (audit's per-test classification is mechanical once the
cluster character is established).

The most consequential downstream finding: the bug-shape shift in
`s60_run_tests_reduction_3_quit_variant_failing` (now panicking on
`register_dep_for_eval` instead of "no parsed sexps") confirms that
keeping reduction rungs as failing-not-ignored guards captures
defect-class evolution, not just the original bug instance. The
carry-forward inherits this guard discipline.
