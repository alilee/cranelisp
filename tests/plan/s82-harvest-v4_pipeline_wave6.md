# S82 harvest disposition — v4_pipeline.rs + wave6_demo_repros.rs

- **Files:** `v4_pipeline.rs` (1273 LOC, 47), `wave6_demo_repros.rs` (528 LOC, 5)
- **FIXMEs:** 0149 (v4_pipeline), 0148 (wave6)
- **Prior audit:** none

## v4_pipeline.rs (47) — FIXME 0149

- **Owner:** `src/` with `cranelisp-backend`, `cranelisp-frontend`, `cranelisp-platform` co-owners.

ALL 47 COVERED. The v4-scheduler pipeline behaviour these tests exercise
is the language-semantics surface already validated by the canonical e2e
suite under `run_through_all_modes` (REPL/`--run`/`--link` parity) —
which directly confirms the `0134` partition finding that
`compile_both()`-style batch/REPL parity is e2e-covered, no int-unit
harvest warranted.

| Cluster | Count | Active coverage |
|---|---:|---|
| main exit-code + dependency type-error cascade (neg) | 11 | `tests/spec_12_runtime.rs` |
| macro body/cross-module/transitive/hoisting | 11 | `tests/spec_09_macros.rs` |
| import forms + defn-before-import resume | 2 | `tests/spec_08_modules.rs` |
| platform stdio compile + io-trampoline + empty-registry | 3 | `tests/spec_platforms.rs` |
| core primitives/if/let/import/macro/operator/cache/export/glob/platform duals | 20 | `spec_appendix_a_builtins.rs`, `spec_04_expressions.rs`, `spec_08_modules.rs`, `spec_09_macros.rs`, `spec_07_traits.rs`, `cache.rs`, `spec_platforms.rs` |

| Disposition | Count |
|---|---:|
| COVERED | 47 |
| GAP | 0 |
| OBSOLETE | 0 |

> Note (`0109` Wave D): the plan recommends running this audit against
> the decomposed session_v4/worker shape. Since all 47 are COVERED at
> the e2e language-semantics level (not against internal pipeline
> structure), the decomposition does not change the disposition — the
> behaviours are mode-parity properties, not internal-shape assertions.

## wave6_demo_repros.rs (5) — FIXME 0148

- **Owner:** `src/` with `cranelisp-backend`, stdlib, `/port` co-owners.

ALL 5 COVERED. These are demo-crash regression repros; each is carried
forward as an active regression guard.

| # | legacy fn | active test | defect |
|---:|---|---|---|
| 1 | `repl_dep_load_no_race_with_persistent_workers` | `tests/repl_persist_race.rs::repl_dep_load_no_race_with_persistent_workers` | Defect 1 (resolved) |
| 2 | `stdlib_seq_lazy_imports_resolve_nil_cons` | `tests/spec_08_modules.rs::null_import_module_resolves_all_names_via_explicit_imports` | Defect 2 (resolved-by-passing) |
| 3 | `display_defn_with_docstring_uses_dash_separator` | `tests/repl_introspection.rs::display_defn_with_docstring_uses_dash_separator` | Defect 3 (resolved) |
| 4 | `run_tests_batched_invocation_no_crash` | `tests/regression.rs::wave6_run_tests_batched_html_completes_without_crash` | Defects 4+5 (resolved-by-passing) |
| 5 | `exemplar_solver_does_not_stack_overflow_on_small_puzzle` | `tests/regression.rs::wave6_exemplar_solver_full_run_does_not_stack_overflow` | Defect 6 — **REGRESSION-GUARD, FAILING-NOT-IGNORED** (solver stack-overflow still open in /backend, folds into FIXME 0145) |

| Disposition | Count |
|---|---:|
| COVERED | 5 |
| GAP | 0 |
| OBSOLETE | 0 |

The Defect-6 guard is COVERED (the active `regression.rs` guard exists)
and is intentionally failing-not-ignored — it is NOT dropped; it flips
green when /backend lands the solver fix.

## Summary

- **v4_pipeline.rs: 47 tests: 47 covered / 0 gap / 0 obsolete**
- **wave6_demo_repros.rs: 5 tests: 5 covered / 0 gap / 0 obsolete** (1 reg-guard, active+failing)

## Exit checklist
- [x] (a) dispositioned; [ ] (b) no GAP to harvest; [ ] (c) deleted (Wave 2, after Defect 6 for wave6); [ ] (d) README rows; [ ] (e) FIXMEs 0149/0148 closed
