---
number: 0145
target: /qa
filed_by: /qa
filed_at: 2026-05-05
sprint_filed: 64
refers_to: tests/legacy/sprint59_cache_repro.rs, tests/legacy/sprint59_defects456_repro.rs, tests/regression.rs, tests/cache.rs, tests/plan/wave-6-batch-3-audit.md, tests/plan/ledger.md
status: open
---

> **S81 W-C (carry-forward verified complete → RE-TARGET /qa for file deletion +
> inline-FIXME cleanup):** Both legacy files are 100%-GAP-COVER e2e
> reduction-cohort work-products with NO backend-crate-internal unit assertion to
> port — every test is a subprocess `--run`/REPL-stdin harness, and all 36 carry
> forward as active e2e regression guards (verified present on the current tree):
> - `tests/regression.rs`: `d45_*` (24 tests) + `d6_*` (10 tests) = 34.
> - `tests/cache.rs`: `cache_repl_minimal_plain_fn_prelude_restored_on_session_2`,
>   `cache_repl_empty_prelude_session_2_evaluates_literal` = 2.
>
> No genuinely-missing backend-internal assertion exists (the defect surfaces are
> RC/dispatch/codegen invariants, but the legacy tests observe them only through
> the binary, not through backend-crate-internal state). The 24 inline
> `FIXME(/backend)` hypothesis comments + the 4 open Defect-6 carry-forwards are
> tracked in the active `tests/regression.rs` + `tests/plan/ledger.md`, not in the
> quarantined file.
>
> **Disposition: RE-TARGET → /qa.** Owed work is the two legacy-file deletions +
> `tests/legacy/README.md` row removal + the inline-FIXME staleness review (per
> the FIXME body §"Proposed resolution" steps 2–4), all `/qa`'s prerogative over
> `tests/`.

# Harvest tests/legacy/sprint59_{cache,defects456}_repro.rs into /backend unit tests + review inline FIXMEs

## Issue

Sprint 64 Wave 6 batch 3 quarantined two Sprint 59 reduction-cohort files:

- `tests/sprint59_cache_repro.rs` (152 LOC, 2 tests, Sprint 59
  Workstream A cache-hit prelude-restoration regression guards)
- `tests/sprint59_defects456_repro.rs` (1766 LOC, 34 tests, Sprint 59
  Defects 4+5 `/run-tests` batched-dispatch crash reductions + Defect 6
  exemplar solver segfault reductions)

All 36 tests carry forward as REGRESSION-GUARDs across two existing
e2e files (no new files):

- `tests/cache.rs` (extended +2): `cache_repl_minimal_plain_fn_prelude_restored_on_session_2`,
  `cache_repl_empty_prelude_session_2_evaluates_literal` — sibling tests
  to `cache_repl_second_session_loads_prelude_from_cache` (carry from
  Wave 6 batch 2 Part A).
- `tests/regression.rs` (extended +34): all `d45_*` (22 + 1 RC underflow)
  and `d6_*` (11) reduction rungs preserved with their `// FIXME(/backend)`
  hypothesis comments verbatim. Six clusters: §A synthetic single-file,
  §B cross-module synthetic, §C real exemplar, §D html-source reduction
  ladder, §E synthetic Vec/ADT/Grid COW, §F+§G real exemplar (Defect 6).

Total carry-forward: **36 tests across 2 files** (2 cache.rs + 34
regression.rs). On the binary at audit time (2026-05-05): **32/36 pass,
4 fail-not-ignored** — the four are open Defect 6 ledger entries.

## Failing-not-ignored carry-forwards

Per `memory/feedback_failing_not_ignored.md` and the existing
`tests/plan/ledger.md §"Escaped carries — surfaced Sprint 61 Wave 3"`
entries (lines 83–131), four `d6_exemplar_*` carry-forwards land
failing:

- `tests/regression.rs::d6_exemplar_solve_minimal_puzzle_no_io_does_not_segv`
- `tests/regression.rs::d6_exemplar_propagate_only_does_not_segv`
- `tests/regression.rs::d6_exemplar_solve_all_dots_does_not_segv`
- `tests/regression.rs::d6_exemplar_propagate_single_pass_does_not_segv`

All four fail with the same shape: `thread 'main' has overflowed its
stack / fatal runtime error: stack overflow, aborting`, exit code None
(killed by signal). They reproduce against the real `exemplar/grid.cl`
+ `exemplar/solver.cl` + a small inline repro source.

The existing ledger entries name the **legacy file's** test names
(`tests/legacy/sprint59_defects456_repro.rs::d6_exemplar_*`); the
underlying defect surface is identical. When `/backend` resolves Defect
6 (deep-recursion stack overflow in JIT'd `propagate`/`solve` on
81-cell Vec-copying ADT traversal), both the legacy and carry-forward
names become passing regression guards. No ledger entry rewrite is
needed at this carry-forward time — the legacy entries continue to
name the legacy tests via the `tests/legacy/...` path.

A 5th historically-listed test (`d6_exemplar_eliminate_from_peers`)
was named in the Sprint 61 handoff brief as failing but has been
verified PASSING at audit time; it carries forward as
`tests/regression.rs::d6_exemplar_eliminate_from_peers_does_not_segv`
and PASSES on the current binary, matching the ledger §note.

## Inline FIXMEs preserved in legacy/sprint59_defects456_repro.rs

The legacy file preserves **24 inline `// FIXME(/backend)` markers** —
one per d45/d6 test (except `d45_solution_cell_single_call_no_rc_underflow`
which carries a `// spec: spec/12-runtime.md §12.3` annotation). These
are pre-Sprint 63 inline FIXMEs (predate the M7 methodology pivot).
The hypothesis content is load-bearing for the regression cohort —
each comment documents the calibration: "if PASS, the next axis is
X; if FAIL, the defect reduces to this minimum shape."

The hypothesis comments are **also preserved verbatim in the
carry-forward source** (`tests/regression.rs`) so the discrimination
context is not lost. Cross-reference: each carry-forward test carries
the `(carry: legacy/sprint59_defects456_repro::<name>)` provenance
comment, and the corresponding `// FIXME(/backend)` inline hypothesis
above the test in the carry-forward.

The legacy file's inline FIXMEs are line-anchored:

- 22 inline `FIXME(/backend)` on tests #1, #2, #3, #4, #5, #6, #7, #8,
  #9, #10, #11, #12, #13, #14, #15, #16, #17, #18, #19, #20, #21, #22,
  #23, #24 (total 24 — d45 cluster + d6 cluster)
- 1 `// spec:` annotation on `d45_solution_cell_single_call_no_rc_underflow`

Per Sprint 63 M7 protocol and Wave 6 batch 2 precedent (FIXME 0144),
each surviving FIXME (post-harvest review) should migrate to its own
numbered `design/arch/fixmes/NNNN-*.md` if the underlying issue
remains unresolved, or be deleted from the legacy file when
verification confirms staleness.

## Inline FIXMEs preserved in legacy/sprint59_cache_repro.rs

Zero inline FIXMEs. The file's docstring (lines 1–22) names the bug
shape and references `design/int/cache-prelude-restoration-repro.md`
as the diagnosis anchor. The 2 tests' headers are descriptive prose
only — no `FIXME(/...)` markers.

## Proposed resolution

`/backend` reviews the quarantined files:

1. For each of the 36 carry-forward tests, verify it is e2e-equivalent
   to a `crates/cranelisp-backend/src/` `#[cfg(test)]` unit-tier test
   that asserts the same RC/dispatch/codegen invariant at the Rust API
   level. The d45 cluster maps to the run-test dispatch loop (likely
   `crates/cranelisp-backend/src/...` containing `run_test_by_name`).
   The d6 cluster maps to Vec/ADT COW codegen (likely
   `crates/cranelisp-backend/src/compiler/builtins.rs::compile_vec_op`
   and `crates/cranelisp-backend/src/compiler/match_compiler.rs`).
   The cache cluster maps to `crates/cranelisp-backend/src/cache.rs`
   prelude-symbol-rebinding pathway (resolved Sprint 59 Workstream A,
   per the test header).

2. For each of the 24 inline `FIXME(/backend)` hypothesis comments in
   the legacy file, verify against the corresponding carry-forward
   test status. If the carry-forward passes, the FIXME is "resolved
   by passing carry-forward" — annotate that in the harvest log and
   delete from the legacy. If the carry-forward fails (the four
   d6_exemplar_* cases), the FIXME documents an open defect — migrate
   to its own numbered `design/arch/fixmes/NNNN-*.md` per Sprint 63
   M7 protocol, OR keep the inline FIXME until Defect 6 resolves and
   re-evaluate at that time.

3. **Defect 6 resolution closes 4 of the 24 inline FIXMEs in one
   commit** — the four corresponding carry-forwards become passing,
   their hypothesis comments are validated retrospectively, and the
   legacy file may be deleted in full.

4. When all surface is harvested or proven stale, delete
   `tests/legacy/sprint59_cache_repro.rs` and
   `tests/legacy/sprint59_defects456_repro.rs`. Git history preserves
   provenance.

## Operational implication / Context

This is the **third 100%-GAP-COVER batch in a row** in Sprint 64 Wave 6
(batch 1: 21/21 = 100%; batch 2: 59/61 = 97%; batch 3: 36/36 = 100%).
The pattern: regression-named work-product files exhaustively partition
the carry-forward surface — they are presumptively discriminating and
the per-test review converges quickly.

Per `tests/plan/wave-6-batch-3-audit.md` §"Methodology takeaway":

> Both files are 100% GAP-COVER REGRESSION-GUARD (36/36). Same
> structural reason as Wave 6 batch 2: these are Sprint 59-cohort
> defect-reduction work-product files. The defects they reduce against
> (4, 5, 6, plus cache restoration) are sprint-specific surfaces with
> no pre-existing carry-forward universe. The dedup risk was zero by
> construction.

The most consequential downstream work: **Defect 6 remains open** at
S64 close. The 4 failing carry-forwards in `tests/regression.rs` will
continue to fail until `/backend` resolves the deep-recursion
stack-overflow root cause. The regression cohort is the durable record.

## Cross-references

- Audit document: `tests/plan/wave-6-batch-3-audit.md`
- Existing ledger entries (4 open Defect 6 entries):
  `tests/plan/ledger.md` lines 83–131
- Carry-forward sources:
  - `tests/cache.rs::cache_repl_minimal_plain_fn_prelude_restored_on_session_2`
  - `tests/cache.rs::cache_repl_empty_prelude_session_2_evaluates_literal`
  - `tests/regression.rs::d45_*` (23 tests, lines after T-S2-2)
  - `tests/regression.rs::d6_*` (11 tests, lines after d45 cluster)
- Sibling tests in `tests/cache.rs`:
  `cache_repl_second_session_loads_prelude_from_cache` (carry from
  `legacy/sprint23.rs::cache_repl_loads_on_startup`, Wave 6 batch 2
  Part A)
- Diagnosis anchor for s59 cache cluster:
  `design/int/cache-prelude-restoration-repro.md` (referenced in legacy
  file header)
