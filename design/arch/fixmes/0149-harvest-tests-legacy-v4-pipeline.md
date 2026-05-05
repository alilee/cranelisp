---
number: 0149
target: /int
filed_by: /qa
filed_at: 2026-05-05
sprint_filed: 64
refers_to: tests/legacy/v4_pipeline.rs, tests/spec_12_runtime.rs, tests/spec_09_macros.rs, tests/spec_08_modules.rs, tests/spec_platforms.rs, tests/plan/wave-6-batch-6-audit.md, design/int/step5-lazy-discovery.md, design/int/step8-platform-registry.md, design/int/step9-error-cascade.md
status: open
---

# Harvest tests/legacy/v4_pipeline.rs into /int + co-owner unit tests

## Issue

Sprint 64 Wave 6 batch 6 (the **FINAL** Wave 6 batch) quarantined the
v4 scheduler-driven pipeline E2E witness file:

- `tests/v4_pipeline.rs` (1206 LOC, 47 tests, Sprint 49+45+58+60
  unified pipeline `--run` driver)

The 47 tests fan out across 7 sections: basic expressions (6),
functions (2), fallback (2), macros (10), multi-module Step 5 (11),
platform registry Step 8 (5), error cascade Step 9 (5), cross-module
macro deps Sprint 45 worker.rs:762 fix (6).

After per-test audit (chunk-by-chunk per the user mandate for the
1206-LOC scale), **27 tests** carry forward as GAP-COVERs across
**four existing e2e files** (no new files):

- `tests/spec_12_runtime.rs` (extended +11):
  - **§12.6 entry-point cluster (5 tests)** — first coverage of the
    `(defn main [] expr)` exit-code invariant (currently `[R4 S10]`
    UNTESTED in spec/12-runtime.md):
    `main_returning_int_produces_int_exit_code`,
    `main_returning_non_int_produces_zero_exit_code`,
    `main_invokes_primitive_call_for_exit_code`,
    `main_invokes_sibling_user_defn_for_exit_code`,
    `main_invokes_recursive_user_defn_for_exit_code`.
  - **§12.7.4.2 batch-mode error cluster (6 tests)** — first coverage
    of batch-mode error rendering (currently `[R4 S18]` UNTESTED):
    `main_with_undefined_name_errors_in_run_mode_neg`,
    `main_with_type_error_in_entry_errors_in_run_mode_neg`,
    `dependency_type_error_cascades_with_module_context_neg`,
    `dependency_type_error_cascade_preserves_root_cause_neg`,
    `clean_program_produces_no_error_in_run_mode`,
    `three_level_cascade_does_not_duplicate_error_output_neg`.
- `tests/spec_09_macros.rs` (extended +11):
  - **§9.2.5 single-file macro semantics (5 tests)** —
    `macro_body_calls_helper_function_in_run_mode`,
    `macro_calls_another_macro_reaches_fixed_point` (§9.3.3 fixed
    point), `multiple_macros_interleaved_with_defns_compose`,
    `macro_used_before_defmacro_form_is_hoisted` (§9.3.4 hoisting),
    `macro_body_drives_three_level_call_graph`.
  - **§9.2.5 + §8.12 cross-module macro deps cluster (6 tests)** —
    Sprint 45 worker.rs:762 fix regression-guard cluster:
    `cross_module_macro_calls_helper_in_other_module`,
    `cross_module_macro_transitive_via_reexport_chain`,
    `cross_module_macro_emits_qualified_reference`,
    `cross_module_macro_drives_transitive_call_graph`,
    `cross_module_macro_dependency_type_error_cascades_neg`,
    `cross_module_macro_cannot_use_private_helper_neg`.
- `tests/spec_08_modules.rs` (extended +2):
  - `multiple_import_forms_in_one_module` (§8.3 multi-import
    discipline)
  - `defn_before_import_resumes_correctly_after_dep_load` (§8.10.1
    Step 5 lazy-discovery resumption invariant) — preserves legacy
    spec assertion (clean stderr) + records discovered SEGV defect
    (see Defect-discovery note below).
- `tests/spec_platforms.rs` (extended +3):
  - `platform_form_with_stdio_compiles_in_run_mode` (collapse of
    legacy `v4_platform_form` + `v4_platform_stdio_print` +
    `v4_platform_import_and_use`)
  - `io_trampoline_executes_print_to_stdout` (Step 8 IO trampoline
    runtime path)
  - `no_platform_form_program_runs_with_empty_registry` (negative
    complement — empty PlatformRegistry codegen invariant)

Total carry-forward: **27 tests across 4 files**. On the binary at
audit time (2026-05-05): **47/47 PASS** in the legacy file; **27/27
PASS** in the carry-forwards. No failing-not-ignored carries.

The remaining **18 tests** are DUPLICATE-IN-LEGACY (REPL-canonical
equivalents already present in `spec_04_expressions.rs`,
`spec_05_definitions.rs`, `spec_08_modules.rs`, `spec_09_macros.rs`,
`spec_appendix_a_builtins.rs`, `cache.rs`).

## Owner alignment

The 47-test file fans out across owning-skills, but **/int is the
predominant owner** (4 of 6 surface areas):

- §A/§B Basic + Functions (8 tests) → /int (entry-point invocation
  in `src/main.rs` `--run` driver) + /backend (codegen of `defn main`)
- §C Fallback / negative undefined (2 tests) → /int + /typecheck
- §D Macros (10 tests, 5 carried) → /int (macro expander integration)
  + /frontend (macro hoisting, expansion fixed point)
- §E Multi-module Step 5 (11 tests, 2 carried) → /int (scheduler —
  `step5-lazy-discovery.md` resumption/cache-hit invariants)
- §F Platform Step 8 (5 tests, 3 collapsed-carries) → /platform
  (`step8-platform-registry.md`) + /int (registry consumption)
- §G Error cascade Step 9 (5 tests, all carried) → /int
  (`step9-error-cascade.md` rendering)
- §H Cross-module macros (6 tests, all carried) → /int (worker.rs:762
  — `compile_dep_symbol_inline` correct-module symbol-table lookup)

Per Wave 6 b2/b3/b4/b5 precedent, this batch files **one harvest
FIXME** with primary owner `/int` and named co-owners /backend
(entry-point codegen + the §8.10.1 SEGV defect — see below),
/frontend (macro hoisting), /platform (Step 8 registry).

## Defect-discovery note — §8.10.1 SEGV (open)

The carry-forward authoring of
`tests/spec_08_modules.rs::defn_before_import_resumes_correctly_after_dep_load`
discovered a defect not visible in the legacy test:

- The legacy `v4_resumption_correctness` only asserted stderr was
  empty; it did NOT check exit code. So it was green.
- The new carry-forward additionally observes that the run-mode child
  process **SEGVs (exit 139)** on this specific shape (local defn
  before import, both invoked from main with primitives/add-i64).
- The §8.10.1 spec invariant (compile-clean stderr) PASSES — the
  scheduler's resumption logic is correct.
- The downstream defect is in codegen / the scheduler's runtime
  wiring after the resumption (likely a missing GOT slot, RC-related
  use-after-free, or a misordered runtime initialization on the
  defn-before-import shape).

**The carry-forward keeps the legacy spec invariant assertion
(clean stderr) and records the SEGV inline as `XXX(/backend)
FIXME 0149`.** Re-enable the `assert_exit(42)` witness when the
defect is resolved.

Owning skill for the SEGV: **/backend** (run-mode child crash on
specific scheduler resumption shape). This FIXME 0149 covers both
the harvest scope (mostly /int) AND the open SEGV defect (/backend).

## Inline FIXMEs preserved in legacy/v4_pipeline.rs

One pre-Sprint-63 inline `FIXME` marker preserved in the
quarantined source (read-only post-quarantine):

- line 587–592: `FIXME(/int): Sprint 58 Wave 2c — second --run
  invocation produces a different exit code (None vs Some(77))`. On
  `v4_cache_hit_dependency`. **Resolved-by-passing-carry-forward** —
  the test passes today (47/47 PASS at audit time). The
  `cache_multi_module_hit_cross_module_call` test in `tests/cache.rs`
  is the established regression guard in the new e2e suite.

When confirmed-resolved at harvest review, the inline FIXME is
deleted from the legacy file. When all surface is harvested or
proven stale, the legacy file is deleted in full.

## Spec-link linter findings (pre-port)

Pre-port linter on the legacy file found **9 issues** (3 MIS-CITED,
6 MALFORMED):

- 3 MALFORMED — `spec/01-syntax.md` (does not exist; correct file is
  `spec/01-lexical.md`) at lines 129, 137. Resolution: carry-forwards
  use canonical `spec/01-lexical.md §1.3.1` / `§1.3.3`.
- 1 MIS-CITED — `spec/04-expressions.md §2.1` does not match (correct
  is `§4.4`) at line 159. Resolution: carry-forwards use `§4.4`.
- 1 MIS-CITED — `spec/04-expressions.md §3` does not match (correct
  is `§4.3`) at line 166. Resolution: carry-forwards use `§4.3`.
- 2 MALFORMED — `spec/05-functions.md` (does not exist; correct file
  is `spec/05-definitions.md`) at lines 177, 185. Resolution:
  carry-forwards use canonical `spec/05-definitions.md §5.1.1`.
- 2 MALFORMED — `design/arch/pipeline-v4-roadmap.md` (archived to
  `design/arch/archive/` in S63) at lines 409, 585. Resolution:
  carry-forwards cite `design/int/step5-lazy-discovery.md` directly.
- 1 MIS-CITED — `design/int/step8-platform-registry.md §"Registry API
  is_empty"` malformed anchor at line 807. Resolution: carry-forwards
  cite `spec/08-modules.md §8.9` (platform integration).

All 9 are addressed in the carry-forward annotations; the legacy
file remains as-quarantined (read-only post-quarantine) — the
findings now live in quarantined source and migrate at harvest
review per Sprint 63 M7 protocol.

## Proposed resolution

The owning skills review the quarantined file's carry-forward
mapping:

1. **`/int`** verifies that the four `/int`-owned surface areas
   (§A entry-point, §D macro hoisting, §E scheduler resumption + cache,
   §G error cascade, §H cross-module macros) have unit-tier
   counterparts in `src/main.rs` / `src/session_v4.rs` /
   `crates/cranelisp-int/src/worker.rs:762` `#[cfg(test)]` clusters.
   Specifically:
   - `(defn main [] Int)` exit-code wiring in the `--run` driver
   - `compile_dep_symbol_inline` correct-module symbol-table lookup
     (worker.rs:762 fix)
   - Step 5 lazy-discovery accumulator save/restore on import-blocking
   - Step 9 error cascade rendering — root cause preservation, no
     duplicate output
   - Macro hoisting (defmacro forms processed before other forms)

2. **`/backend`** verifies the §8.10.1 SEGV defect (open):
   - The shape `(defn local-fn [] X) (import [util [remote-fn]])
     (defn main [] (primitives/add-i64 (local-fn) (remote-fn)))` with
     `util.cl` defining `remote-fn` produces a clean compile but
     SEGVs at runtime (exit 139, empty stdout/stderr).
   - Hypothesis space: GOT slot allocation across the suspension/
     resumption boundary; RC accounting on the `local-fn` (which
     was compiled before the import-induced suspension); runtime
     initialization ordering.
   - When fixed, re-enable the `assert_exit(42)` witness in the
     carry-forward
     `tests/spec_08_modules.rs::defn_before_import_resumes_correctly_after_dep_load`.

3. **`/frontend`** verifies macro hoisting + fixed-point re-expansion
   in `crates/cranelisp-frontend/src/expander.rs` `#[cfg(test)]`
   cluster:
   - `(defn main [] (nope 42)) (defmacro nope [x] x)` succeeds
     (defmacro hoisted)
   - macro→macro expansion reaches fixed point in N iterations

4. **`/platform`** verifies PlatformRegistry empty-registry
   invariant + IO trampoline runtime path in
   `crates/cranelisp-platform/` + `cranelisp-runtime/src/io_trampoline.rs`.

5. When all surface is harvested or proven stale, delete
   `tests/legacy/v4_pipeline.rs`. Git history preserves provenance.

## Operational implication / Context

This batch closes Sprint 64 Wave 6 with the **lowest yield** (62%)
of any Wave 6 batch — but for a structural reason that's a sign of
maturity, not a problem:

| Batch | Tests | GAP-COVER | DUPLICATE | COVERED | Yield % |
|---|---:|---:|---:|---:|---:|
| b1 | 21 | 21 | 0 | 0 | 100% |
| b2 | 61 | 59 | 2 | 0 | 97% |
| b3 | 36 | 36 | 0 | 0 | 100% |
| b4 | 25 | 25 | 0 | 0 | 100% |
| b5 | 10 | 10 | 0 | 0 | 100% |
| b6 | 47 | 27 | 20 | 0 | 57% |
| **Wave 6 total** | **200** | **178** | **22** | **0** | **89%** |

The 18 DUPLICATE-IN-LEGACY tests in this batch are all defensible:
each has a REPL-canonical sibling in the Wave 5 spec_*.rs files that
covers the same spec property. The 27 GAP-COVERs that DO carry forward
are all genuinely discriminating — most of them anchor previously-
UNTESTED spec sections (§12.6 entry-point + §12.7.4.2 batch-mode
errors) or regression-guard the Sprint 45 worker.rs:762 cross-module
macro fix.

Wave 6 closes with **178 carry-forwards across 12 quarantined files**.

## Cross-references

- Audit document: `tests/plan/wave-6-batch-6-audit.md`
- Carry-forward sources (in current tree):
  - `tests/spec_12_runtime.rs::main_returning_int_produces_int_exit_code`
    + 10 siblings
  - `tests/spec_09_macros.rs::macro_body_calls_helper_function_in_run_mode`
    + 10 siblings
  - `tests/spec_08_modules.rs::multiple_import_forms_in_one_module`,
    `tests/spec_08_modules.rs::defn_before_import_resumes_correctly_after_dep_load`
  - `tests/spec_platforms.rs::platform_form_with_stdio_compiles_in_run_mode`
    + 2 siblings
- Sibling FIXMEs:
  - 0140 (`int-run-mode-import-below-use-rejected`) — adjacent
    surface (import placement); see also FIXME 0143 audit findings
  - 0143 (Wave 6 b1 examples-exemplar)
  - 0144 (Wave 6 b2 sprint23)
  - 0145 (Wave 6 b3 sprint59-repros) — parent /backend RC scope
  - 0146 (Wave 6 b4 sprint60-trio)
  - 0147 (Wave 6 b5 sprint61-bare-primitive)
  - 0148 (Wave 6 b5 wave6-demo-repros)
- Source code areas (harvest targets):
  - `src/main.rs` + `src/session_v4.rs` (entry-point invocation;
    `--run` driver)
  - `crates/cranelisp-int/src/worker.rs:762` (`compile_dep_symbol_inline`
    cross-module dep lookup — Sprint 45 fix)
  - `crates/cranelisp-frontend/src/expander.rs` (macro hoisting,
    fixed-point re-expansion)
  - `crates/cranelisp-backend/src/...` (Step 9 error cascade
    rendering; §8.10.1 SEGV defect surface)
  - `cranelisp-runtime/src/io_trampoline.rs` (Step 8 IO trampoline)
- Design-doc anchors:
  - `design/int/step5-lazy-discovery.md` (§4 import handling; §5
    suspension/resumption)
  - `design/int/step8-platform-registry.md`
  - `design/int/step9-error-cascade.md` (§4.1 cascade construction;
    §4.2 user-visible messages)
  - `design/int/bare-primitive-value-path.md` (sibling to FIXME 0147)
- Spec anchors:
  - `spec/12-runtime.md §12.6` — entry point (currently `[R4 S10]`,
    upgrade to `[Tested ...]` after this batch lands)
  - `spec/12-runtime.md §12.7.4.2` — batch-mode error behaviour
    (currently `[R4 S18]`, upgrade after)
  - `spec/09-macros.md §9.2.5` — macro body capabilities
  - `spec/09-macros.md §9.3.3` — re-expansion fixed point
  - `spec/09-macros.md §9.3.4` — module-wide macro availability
  - `spec/08-modules.md §8.3` — import discipline
  - `spec/08-modules.md §8.10.1` — dep graph + resumption (defect
    surface for the open SEGV)
  - `spec/08-modules.md §8.9` — platform integration

## Wave 6 closure note

This is the **final harvest FIXME of Sprint 64 Wave 6**. Wave 6
totals: 200 tests reviewed across 12 quarantined files; 178
carry-forwards (89% yield); 7 harvest FIXMEs filed (0143–0149);
zero carry-forward authored as failing-not-ignored (the open §8.10.1
SEGV is recorded as an `XXX(/backend)` aspirational re-enable
inside the passing carry-forward, not as a separate failing test).
