---
number: 0146
target: /backend
filed_by: /qa
filed_at: 2026-05-05
sprint_filed: 64
refers_to: tests/legacy/sprint60_cache_build_marker.rs, tests/legacy/sprint60_reduction.rs, tests/legacy/sprint60_run_tests_reduction.rs, tests/cache.rs, tests/regression.rs, tests/plan/wave-6-batch-4-audit.md, design/arch/fixmes/0142-int-repl-unclosed-paren-on-eof-silent.md
status: open
---

# Harvest tests/legacy/sprint60_{cache_build_marker,reduction,run_tests_reduction}.rs into /backend unit tests + review inline FIXMEs

## Issue

Sprint 64 Wave 6 batch 4 quarantined three Sprint 60-cohort
reduction-cohort files:

- `tests/sprint60_cache_build_marker.rs` (261 LOC, 3 tests, Sprint 60
  Workstream C cache `build_id` field round-trip + invalidation)
- `tests/sprint60_reduction.rs` (721 LOC, 17 tests, Sprint 60
  Workstream A cache-reuse SIGSEGV + W2 R2 drop-glue/auto-curry
  double-free reductions)
- `tests/sprint60_run_tests_reduction.rs` (325 LOC, 5 tests, Sprint 60
  W2 R3 REPL-eval persistence-collapse residue)

All 25 tests carry forward as REGRESSION-GUARDs across two existing
e2e files (no new files):

- `tests/cache.rs` (extended +3): `cache_meta_carries_build_id_after_first_compile`,
  `cache_meta_with_stale_build_id_triggers_recompile`,
  `cache_meta_without_build_id_field_triggers_recompile`. Siblings of
  the existing Sprint 59 Workstream A cache restoration regression
  guards (Wave 6 batch 3 carries) in the same file.
- `tests/regression.rs` (extended +22): all `s60_cache_reuse_*` (8) +
  `s60_control_*` (3) cache-reuse cluster + `s60_drop_glue_*` (6)
  drop-glue cluster + `s60_run_tests_reduction_*` (5) REPL-eval
  cluster. Defect-repro cohort siblings of the Wave 6 batch 1 T-S2-2
  + Wave 6 batch 3 d45/d6 clusters.

Total carry-forward: **25 tests across 2 files** (3 cache.rs + 22
regression.rs). On the binary at audit time (2026-05-05): **25/25 pass
in single-test isolation**, but the
`s60_run_tests_reduction_*` cluster is INTERMITTENTLY flaky — different
tests in the cluster fail across consecutive full-suite runs (a race
condition in the entry-module sexp-lifecycle wiring; the underlying
defect is REPL-eval'd imports against an empty entry user.cl). The
original shutdown-path symptom ("no parsed sexps for module 'user'")
has shifted to an active-path panic
(`register_dep_for_eval MUST publish dep_sexps before calling
scheduler.register_module` in `src/session_v4.rs:1572`) in the
failing rotation.

Per `memory/feedback_failing_not_ignored.md` and the
`memory/feedback_repros_join_suite.md` discipline, the regression
guards land un-ignored even given the flakiness — they capture defect-
class evolution, not just one bug instance.

## Owner alignment

The 3 sprint60_cache_build_marker tests + 17 sprint60_reduction tests
target `/backend` (cache invalidation + cache-reuse codegen + drop-glue
RC accounting). The 5 sprint60_run_tests_reduction tests target
**`/int` as secondary observer** (REPL session_v4 lifecycle wiring).
Per Wave 6 b2/b3 precedent (one harvest FIXME per quarantine batch
when owners align), this FIXME consolidates all three files under
`/backend` as primary, with the secondary `/int` observation called
out for the run_tests subset. Cross-reference: existing FIXME 0142
(`int-repl-unclosed-paren-on-eof-silent`) is a related but distinct
REPL-eval defect.

## Inline FIXMEs preserved in legacy/sprint60_reduction.rs

The legacy file preserves **10 inline `// FIXME(/backend)` markers**
documenting the discrimination calibration ("if PASS, the next axis
is X; if FAIL, the defect reduces to this minimum shape"):

- line 167: S60 Step 1 exemplar-shaped baseline (Cell ADT + Grid +
  recursive build-helper). Original A.3b finding.
- line 204: S60 reduction 2.1 — Cell ADT not load-bearing.
- line 223: S60 reduction 2.2 — Grid wrapper ADT not load-bearing.
- line 240: S60 reduction 2.3 — self-recursion not load-bearing.
- line 257: S60 reduction 2.4 — helper arity not load-bearing.
- line 274: S60 reduction 2.5 — vec-push not load-bearing.
- line 291: S60 reduction 2.6 — NO HEAP rules out RC entirely.
- line 321: S60 MINIMAL 5-LOC two-file cache-hit segfault. Hypothesis:
  cache-hit `make-grid`'s call to `build-helper` dispatches through a
  NULL/stale GOT slot. Root-cause area: `src/worker.rs::load_cached_module_via_linker`
  vs `design/backend/jit-object-convergence.md §4.3` GOT wholesale-swap.
- line 542: S60 Round 2 MINIMAL drop-glue 14-LOC. Hypothesis:
  `emit_consuming_caller_rc` for defn calls auto-curried despite both
  args present, OR closure env RC accounting for ADT-wrapped Vec
  captures.
- line 651: S60 Round 2 deletion-resistance double — committed as a
  duplicate of the minimal repro to prevent silent coverage deletion
  via "simplify" edits.

All 10 hypotheses are "resolved by passing carry-forward" at audit
time — the cache-reuse cluster's underlying defect was fixed by
Sprint 60 Workstream A's single-GOT fix, and the drop-glue cluster's
underlying defect was fixed post-S60 W2 R2. The carry-forwards in
`tests/regression.rs` ALL PASS. Per Sprint 63 M7 protocol, each FIXME
should be confirmed-resolved at harvest review time (verify the
hypothesis against current codegen, validate the fix is in place,
delete from the legacy file). When confirmed-resolved, the legacy
file may be deleted in full.

## Inline FIXMEs preserved in legacy/sprint60_run_tests_reduction.rs

The legacy file preserves **1 inline `// FIXME` marker** in the file
header (line 80–81): `FIXME(/int) or FIXME(/backend) — pick up from
defects-456-reduction.md §"Sprint 60 Wave 2 Round 3 — run-tests
batched reduction"`. The four `_failing` test names + 1
`_passes_control` carry the discrimination context in their names
without per-test FIXME markers. The file header documents the bug
shape: REPL-eval'd import + empty user.cl ⇒ shutdown-path module
failure. The audit-time observation is that the bug surface has
shifted to an active-path panic (`register_dep_for_eval` ordering
invariant violated). Same root-cause class — entry-module sexp-
lifecycle inconsistency between REPL import and the persistent
worker pool — but a different code path now exhibits it.

## Inline FIXMEs preserved in legacy/sprint60_cache_build_marker.rs

Zero inline FIXMEs. The file's docstring (lines 1–13) names the
unit-tier counterpart in `crates/cranelisp-backend/src/cache/serialize.rs`
(`build_id_round_trip_succeeds`, `stale_build_id_produces_build_id_mismatch`,
`missing_build_id_field_routes_cache_stale`).

## Proposed resolution

`/backend` reviews the quarantined files:

1. For each of the 25 carry-forward tests, verify it is e2e-equivalent
   to a `crates/cranelisp-backend/src/` `#[cfg(test)]` unit-tier test
   that asserts the same invariant at the Rust API level. Mapping:

   - The 3 build_id e2e tests already have unit counterparts named
     in the legacy file header. Verify the unit tests still cover the
     equivalent invariants.
   - The 11-test §A cache-reuse cluster maps to
     `crates/cranelisp-backend/src/cache.rs` cross-module + intra-module-call
     cache-hit pathways (the Sprint 60 W A single-GOT fix area).
   - The 6-test §B drop-glue cluster maps to
     `crates/cranelisp-backend/src/compiler/builtins.rs::compile_vec_op`
     + `compile_match` + closure-env RC emission for ADT-wrapped Vec
     captures (S60 W2 R2 fix area).
   - The 5-test sprint60_run_tests_reduction cluster maps to **`/int`'s
     `src/session_v4.rs::register_dep_for_eval`** (the panic site
     captured at audit time). Co-ownership; coordinate with `/int`
     before deleting the legacy file.

2. For each of the 10 inline `FIXME(/backend)` hypothesis comments in
   the legacy `sprint60_reduction.rs`, verify against the corresponding
   carry-forward test status. If the carry-forward passes (all 17 of
   17 do), the FIXME is "resolved by passing carry-forward" — annotate
   that in the harvest log and delete from the legacy. If any
   regression occurs, the FIXME documents an open defect — migrate to
   its own numbered `design/arch/fixmes/NNNN-*.md` per Sprint 63 M7
   protocol.

3. **Coordinate with `/int`** on the `sprint60_run_tests_reduction`
   subset. The 5 tests' underlying defect surface is in
   `src/session_v4.rs:1572` (the `register_dep_for_eval` invariant
   panic). When `/int` resolves the entry-module sexp-publication
   ordering, the 5 carry-forwards become passing regression guards
   without flakiness. The legacy file may then be deleted alongside
   the rest of this batch.

4. When all surface is harvested or proven stale, delete all three
   legacy files. Git history preserves provenance.

## Operational implication / Context

This is the **fourth 100%-GAP-COVER batch in a row** in Sprint 64
Wave 6 (b1: 21/21 = 100%; b2: 59/61 = 97%; b3: 36/36 = 100%; b4: 25/25
= 100%). Per `tests/plan/wave-6-batch-4-audit.md` §"Methodology
takeaway":

> The pattern is now well-validated: regression-named work-product
> files exhaustively partition the carry-forward surface — they are
> presumptively discriminating and the per-test review converges
> quickly.

The most consequential downstream finding from this batch: the
**bug-shape shift** observed in `s60_run_tests_reduction_3_quit_variant_failing`
(now panicking on `register_dep_for_eval` instead of the original
shutdown-path "no parsed sexps") confirms that keeping reduction
rungs as failing-not-ignored guards captures defect-class evolution,
not just one bug instance. The carry-forward inherits this
guard discipline — when the cluster flakes (which it does
intermittently in full-suite runs), it documents that the underlying
race in the entry-module sexp lifecycle is not yet resolved.

## Cross-references

- Audit document: `tests/plan/wave-6-batch-4-audit.md`
- Carry-forward sources:
  - `tests/cache.rs::cache_meta_carries_build_id_after_first_compile`
  - `tests/cache.rs::cache_meta_with_stale_build_id_triggers_recompile`
  - `tests/cache.rs::cache_meta_without_build_id_field_triggers_recompile`
  - `tests/regression.rs::s60_cache_reuse_*` (8 tests, lines after Wave 6 b3 d6)
  - `tests/regression.rs::s60_control_*` (3 tests)
  - `tests/regression.rs::s60_drop_glue_*` (6 tests)
  - `tests/regression.rs::s60_run_tests_reduction_*` (5 tests)
- Sibling carry-forwards from earlier batches:
  - `tests/cache.rs::cache_repl_minimal_plain_fn_prelude_restored_on_session_2`
    (Wave 6 b3 carry from `legacy/sprint59_cache_repro.rs`)
  - `tests/regression.rs::d45_*` + `d6_*` (Wave 6 b3 carries from
    `legacy/sprint59_defects456_repro.rs`)
  - `tests/regression.rs::t_s2_2_inline_adt_arg_wrapping_vec_preserves_len`
    (Wave 6 b1 carry)
- Related FIXMEs:
  - 0142 (`int-repl-unclosed-paren-on-eof-silent`) — distinct REPL-eval
    defect; co-located /int observation
  - 0145 (Wave 6 b3 harvest: sprint59 repros) — same /backend harvest
    scope, sibling
- Legacy unit-tier counterparts:
  - `crates/cranelisp-backend/src/cache/serialize.rs::build_id_round_trip_succeeds`
  - `crates/cranelisp-backend/src/cache/serialize.rs::stale_build_id_produces_build_id_mismatch`
  - `crates/cranelisp-backend/src/cache/serialize.rs::missing_build_id_field_routes_cache_stale`
- Source code areas:
  - `src/worker.rs::load_cached_module_via_linker` (cache-reuse cluster
    historic root cause)
  - `src/session_v4.rs::register_dep_for_eval` (run_tests cluster
    current panic site)
  - `crates/cranelisp-backend/src/compiler/builtins.rs::compile_vec_op`
    (drop-glue cluster historic root cause)
- Design-doc anchors:
  - `design/backend/jit-object-convergence.md §1.1` (cache-reuse
    invariant statement)
  - `design/backend/jit-object-convergence.md §4` (Decision-31
    carry-forward audit; convergence breach in cache-hit load path)
  - `design/backend/module-caching.md §4` (Serialization Format —
    build_id field)
  - `design/backend/module-caching.md §6` (Cache Invalidation Strategy
    — build_id mismatch path)
