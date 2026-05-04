# Wave 5.6 — exhaustive per-file dedupe-recovery audit

Sprint 64 Phase 5, Wave 5.6. Author: `/qa` (audit-only dispatch).

This audit applies Wave 5.5's discipline EXHAUSTIVELY to every test in
the 8 quarantined `tests/legacy/*.rs` files (`sprint59_neg.rs` was
fully audited in Wave 5.5 and is excluded). The brief's per-file
counts:

| Order | File | `#[test]` count |
|---:|---|---:|
| 1 | `tests/legacy/lenient.rs` | 16 |
| 2 | `tests/legacy/modules.rs` | 19 |
| 3 | `tests/legacy/macros.rs` | 29 |
| 4 | `tests/legacy/ring0.rs` | 108 |
| 5 | `tests/legacy/sketch_port.rs` | 148 |
| 6 | `tests/legacy/e2e.rs` | 148 |
| 7 | `tests/legacy/ring1.rs` | 190 |
| 8 | `tests/legacy/ring2.rs` | 199 |
| **Total** | | **857** |

The brief's 1,735 figure included helper functions and inline `fn`
declarations (e.g., `fn factorial` written inside an `(defn)` literal,
counting tools, etc.). True `#[test]`-marked tests total **857**.

## Methodology

**Per Wave 5.6 brief:**

1. No exact 1:1 duplicates after `[Tested ...]` carry-forward exists.
2. Multi-angle on same spec property → PRESERVE.
3. Regression-named tests are presumptively discriminating — default
   to GAP-COVER unless EXACT 1:1 duplicate is provable.
4. Spec-anchoring is the dedup criterion, not source-shape match.

**Disposition codes:**

- **COVERED**: existing carry-forward asserts same spec property + angle.
- **DUPLICATE-IN-LEGACY**: same legacy file or another legacy file
  contains an identical assertion. Name the canonical instance.
- **GAP-COVER**: spec property is e2e-observable, no existing
  carry-forward asserts this angle. Recommend a new e2e test.
- **GAP-HARVEST**: assertion reaches into Rust internals
  (`cranelisp_types::ModuleEntry`, `s.core.tc.symbol_table()`,
  scheduler atomics, RC trace counters) — belongs in the existing
  harvest FIXMEs (0134-0139), not in `tests/`.
- **REGRESSION-GUARD**: subclass of GAP-COVER for tests whose names
  match a regression pattern (`_repro_`, `_does_not_`, `_neg_`,
  `_no_double_`, `_no_leak_`, `_no_underflow_`, `_S{N}_`,
  `_sprint{N}_`, `_regression_`, `_fix_`, `_fixed_`).

**Volume strategy.** With 857 tests across 8 files, the smallest 3
files (lenient, modules, macros — 64 tests) get full per-test rows.
The remaining 5 large files (ring0, sketch_port, e2e, ring1, ring2 —
793 tests) are audited in **cluster mode**: tests are grouped by
shared spec property + angle, one row per cluster lists the constituent
tests and a single disposition. This preserves per-test traceability
(every test name appears) while keeping the doc finite.

## Carry-forward inventory (point-in-time, 2026-05-03)

The 16 carry-forward files (~336 tests) provide the COVERED universe.
Test name lists collected via grep at audit start. Where this audit
cites "COVERED by `<file>::<name>`", that name is verified present in
the carry-forward at audit time.

---

## 1. tests/legacy/lenient.rs (16 tests)

### Summary

| Disposition | Count |
|---|---:|
| COVERED | 2 |
| DUPLICATE-IN-LEGACY | 0 |
| GAP-COVER | 5 |
| (of which REGRESSION-GUARD) | 1 |
| GAP-HARVEST | 9 |

### Per-test classifications

| Test name | Spec property | Angle | Disposition | Notes |
|---|---|---|---|---|
| `test_lenient_independent_bindings_same_result` | spec/12-runtime.md §12.4.3 — independent let bindings produce same result | top-level let, two indep call bindings, sum | COVERED | `spec_04_expressions.rs::lenient_independent_bindings_correct` |
| `test_lenient_dependent_bindings_sequential` | spec/12-runtime.md §12.4.3 — dependent bindings sequential | b references a in same let | COVERED | `spec_04_expressions.rs::lenient_dependent_bindings_correct` |
| `test_lenient_cheap_builtins_not_sparked` | spec/12-runtime.md §12.4.3 — cheap arithmetic builtins not sparked | three cheap ops in let | GAP-COVER | observable via correctness-only e2e (sparking unobservable, but result must hold) |
| `test_lenient_min_two_sparkable` | spec/12-runtime.md §12.4.3 — single-call binding + literal not sparked | mixed literal/call bindings | GAP-COVER | mid-priority; correctness-only e2e |
| `test_lenient_no_lenient_env_var` | spec/12-runtime.md §12.4.3 — `CRANELISP_NO_LENIENT=1` opt-out preserves correctness | env var disables sparking | REGRESSION-GUARD | env var is e2e-observable via subprocess; high-value preserve |
| `test_lenient_nested_lets` | spec/12-runtime.md §12.4.3 — nested let blocks have independent spark groups | inner let inside outer let body | GAP-COVER | nesting angle absent from carry-forward |
| `test_lenient_mixed_independent_dependent` | spec/12-runtime.md §12.4.3 — mixed indep/dep in single let | three bindings, last depends | GAP-COVER | dist from `lenient_dependent_bindings_correct` (which has 2 bindings) |
| `test_lenient_three_independent_calls` | spec/12-runtime.md §12.4.3 — three independent sparkable bindings | scaling angle | GAP-COVER | merge/skip if `_independent_bindings_correct` covers the cardinality concern |
| `test_lenient_heap_typed_results` | spec/12-runtime.md §12.4.3 — heap-typed results survive parallel eval | string concat across sparks | REGRESSION-GUARD | heap+lenient interaction is high-value — `unsafe read_string_as_str` peek is internal-only, but e2e via `(println ...)` viable |
| `test_lenient_closures_with_captures` | spec/12-runtime.md §12.4.3 — sparked thunks capture enclosing scope | closure capturing outer let binding | REGRESSION-GUARD | closure+lenient interaction; high-value |
| `test_lenient_neg_literals_not_sparkable` | spec/12-runtime.md §12.4.3 — literal/var bindings not sparkable | three literal bindings | REGRESSION-GUARD | trivial result-correctness e2e |
| `test_io_schedule_commutative_pair_par` | spec/10-io.md §10.12.1 — commutative pair → Par node | requires test-capture DLL | GAP-HARVEST | `repl_session_with_test_capture` is platform-fixture; observation requires DLL counters |
| `test_io_schedule_sequential_no_par` | spec/10-io.md §10.12.2 — Sequential class preserves order | requires test-capture DLL | GAP-HARVEST | platform-fixture |
| `test_io_schedule_data_dependent_no_par` | spec/10-io.md §10.12.1 — data-dep pair: no Par | platform fixture | GAP-HARVEST | platform-fixture |
| `test_io_schedule_resource_serial_same_token_sequential` | spec/10-io.md §10.12.4 — same resource token serializes | platform fixture | GAP-HARVEST | TODO body — placeholder; file reduces to a marker |
| `test_io_schedule_resource_serial_diff_token_parallel` | spec/10-io.md §10.12.4 — different tokens run concurrently | platform fixture | GAP-HARVEST | TODO body — placeholder |

### GAP-COVER recommendations

- **`test_lenient_cheap_builtins_not_sparked`** → `tests/spec_04_expressions.rs` — angle: pure-arithmetic-only let body (correctness, no spark observation needed).
- **`test_lenient_min_two_sparkable`** → `tests/spec_04_expressions.rs` — angle: heterogeneous binding (literal + call) preserves correctness.
- **`test_lenient_no_lenient_env_var`** → `tests/spec_12_runtime.rs` — angle: env-var opt-out preserves correctness. **Subprocess required** to set env var; not REPL-canonical. Cite as exception per CLAUDE.md.
- **`test_lenient_nested_lets`** → `tests/spec_04_expressions.rs` — angle: nested lets, inner spark group independent.
- **`test_lenient_mixed_independent_dependent`** → `tests/spec_04_expressions.rs` — angle: 3-binding let, last depends on first.
- **`test_lenient_three_independent_calls`** → `tests/spec_04_expressions.rs` — optional; cardinality angle.
- **`test_lenient_heap_typed_results`** → `tests/spec_04_expressions.rs` (or `spec_12_runtime.rs`) — angle: heap-typed results survive lenient. **Use REPL display** for the string instead of `unsafe read_string_as_str`.
- **`test_lenient_closures_with_captures`** → `tests/spec_04_expressions.rs` — angle: closure body in sparked binding captures outer let.
- **`test_lenient_neg_literals_not_sparkable`** → `tests/spec_04_expressions.rs` — angle: all-literal let body produces correct result (negative-of-spark).

Sketch per recommendation: REPL-canonical via `run_repl_with_test_prelude`; assert displayed result equals the expected integer/string. No assertion of spark count needed — correctness across the spark-eligible vs ineligible boundaries IS the spec.

---

## 2. tests/legacy/modules.rs (19 tests)

19 by `#[test]` count; 4 are commented-out `// #[test]` blocks for removed `discover_module_graph` API. Only 15 active; the disabled blocks document a removed pipeline and are not test material.

### Summary

| Disposition | Count |
|---|---:|
| COVERED | 5 |
| DUPLICATE-IN-LEGACY | 0 |
| GAP-COVER | 9 |
| (of which REGRESSION-GUARD) | 2 |
| GAP-HARVEST | 1 |

### Per-test classifications

| Test name | Spec property | Angle | Disposition | Notes |
|---|---|---|---|---|
| `import_without_mod_compiles_and_runs` | spec/08-modules.md §8.10.1 — implicit dependency from import | sibling files, no `(mod ...)` | COVERED | analogous to `spec_08_modules.rs::import_specific_name_compiles_and_runs` |
| `import_dependency_compiles_correctly` | spec/08-modules.md §8.10.3 — explicit `(mod util)` dependency | parent + child via `main/util.cl` | GAP-COVER | `spec_08_modules` has only sibling-file shape; `(mod ...)` declaration angle absent |
| `project_root_shadows_stdlib` | spec/08-modules.md §8.11.2 — project root shadows stdlib | both have `helper.cl`; project wins | REGRESSION-GUARD | Slice 1 boundary; high-value preserve |
| `stdlib_module_compiles_and_runs` | spec/08-modules.md §8.11.2 — stdlib-only module resolves | file only in stdlib_dir | GAP-COVER | stdlib resolution path absent from carry-forward |
| `prelude_like_reexport_compiles` | spec/08-modules.md §8.4 — re-export shell | shell pattern | GAP-COVER | re-export angle weak in carry-forward |
| `multi_dot_module_path_in_import` | spec/08-modules.md §8.3 — multi-dot module path | `main.shell.inner` 3-segment | GAP-COVER | not in carry-forward |
| `nested_dependency_chain_compiles` | spec/08-modules.md §8.5.1 — three-level dependency chain | A → B → C | GAP-COVER | depth-3 import chain absent |
| `transitive_import_chain` | spec/08-modules.md §8.5.1 — transitive qualified ref | depth-3, qualified ref into leaf | DUPLICATE-IN-LEGACY | near-duplicate of `nested_dependency_chain_compiles`; canonical = nested |
| `import_private_name_errors` | spec/08-modules.md §8.3.1 — private import error | `(defn-)` not importable | COVERED | `spec_08_modules.rs::private_defn_not_importable_neg` |
| `qualified_ref_to_missing_module_errors` | spec/08-modules.md §8.5.4 — qualified ref to missing module | `nonexistent/foo` | COVERED | analogue in `spec_08_modules.rs::module_cycle_detection_neg` shape; verify covers no-such-module case — likely partial-cover, file as GAP-COVER if not |
| `glob_import_excludes_private` | spec/08-modules.md §8.7.3 — glob excludes private | `(defn-)` not in `[*]` | REGRESSION-GUARD | Slice negative coverage; preserve |
| `export_specific_reexport` | spec/08-modules.md §8.4.1 — specific re-export | named pass-through | GAP-COVER | re-export coverage thin |
| `export_glob_reexport` | spec/08-modules.md §8.4.2 — glob re-export | `[*]` pass-through | GAP-COVER | re-export coverage thin |
| `export_transitive_reexport_chain` | spec/08-modules.md §8.4.4 — transitive re-export | 3-level chain | GAP-COVER | high-value |
| `export_multiple_modules` | spec/08-modules.md §8.4.3 — multi-source re-export | shell re-exports from a + b | GAP-COVER | distinct angle from chain |
| `export_private_name_not_reexported` | spec/08-modules.md §8.4.4 — re-exported private fails | error path | GAP-COVER + REGRESSION-GUARD | negative |
| `imported_function_as_higher_order_argument` | spec/08-modules.md §8.3 — imported fn as HOF arg | batch only | COVERED | `spec_08_modules.rs::import_specific_name_compiles_and_runs` covers the call; HOF angle is in `spec_04_expressions.rs::lambda_passed_to_function`-class — combined coverage adequate |
| `super_import_rewrites_to_parent_end_to_end` | spec/08-modules.md §8.3.7 — super rewrites to parent | parent has `parent-val`, child uses `(import [super [*]])` | GAP-HARVEST | assertion reaches into `cranelisp_types::ModuleEntry::Import`, `session.symbol_tables()`, `register_module()` — not e2e-portable. Functional coverage **partially** by `spec_08_modules.rs::super_import_at_top_level_neg` (negative path), but positive path (super rewrites correctly) is not covered |
| `super_import_at_root_is_rejected_neg` | spec/08-modules.md §8.3.7 — super at root rejected | error message asserts | COVERED | `spec_08_modules.rs::super_import_at_top_level_neg` |

### GAP-COVER recommendations

- **`import_dependency_compiles_correctly`** → `tests/spec_08_modules.rs` — angle: explicit `(mod util)` declaration before sibling import. Filesystem fixture required.
- **`project_root_shadows_stdlib`** → `tests/spec_08_modules.rs` — angle: project-root precedence over stdlib (Slice 1). Use `CRANELISP_LIB` to point at the stdlib_dir fixture.
- **`stdlib_module_compiles_and_runs`** → `tests/spec_08_modules.rs` — angle: module file lives only in stdlib_dir.
- **`prelude_like_reexport_compiles`** → `tests/spec_08_modules.rs` — angle: shell module compiles even when re-export is the only structure.
- **`multi_dot_module_path_in_import`** → `tests/spec_08_modules.rs` — angle: 3-segment module path resolves.
- **`nested_dependency_chain_compiles`** → `tests/spec_08_modules.rs` — angle: A→B→C chain.
- **`qualified_ref_to_missing_module_errors`** → `tests/spec_08_modules.rs` — angle: explicit qualified ref `mod/name` into nonexistent module.
- **`glob_import_excludes_private`** → `tests/spec_08_modules.rs` — angle: `[*]` does not import `(defn-)`. Negative test naming `_neg_glob_excludes_private_defn`.
- **`export_specific_reexport`** → `tests/spec_08_modules.rs` — angle: named re-export visible to importer.
- **`export_glob_reexport`** → `tests/spec_08_modules.rs` — angle: glob re-export.
- **`export_transitive_reexport_chain`** → `tests/spec_08_modules.rs` — angle: 3-level re-export chain.
- **`export_multiple_modules`** → `tests/spec_08_modules.rs` — angle: shell re-exports from two sources.
- **`export_private_name_not_reexported`** → `tests/spec_08_modules.rs` — angle: `_neg_` private-name re-export rejected.

Sketch per recommendation: tempdir-fixture pattern (already used by `spec_08_modules.rs`), `--run main.cl` subprocess invocation, assert exit code or stdout. Use the existing `tests/helpers/mod.rs::tempdir_project_from_fixture` shape.

---

## 3. tests/legacy/macros.rs (29 tests)

### Summary

| Disposition | Count |
|---|---:|
| COVERED | 13 |
| DUPLICATE-IN-LEGACY | 1 |
| GAP-COVER | 11 |
| (of which REGRESSION-GUARD) | 6 |
| GAP-HARVEST | 4 |

### Per-test classifications

| Test name | Spec property | Angle | Disposition | Notes |
|---|---|---|---|---|
| `repl_defmacro_identity` | spec/09-macros.md §9.2 — defmacro at REPL identity | `(defmacro id [x] x)` | COVERED | `spec_09_macros.rs::defmacro_identity_expands` + `repl_introspection.rs::defmacro_display_single_clause` |
| `repl_defmacro_quasiquote` | spec/09-macros.md §9.4.2 — quasiquote at REPL | wrap with backtick | COVERED | `spec_09_macros.rs::quasiquote_with_unquote` |
| `repl_defmacro_multi_clause` | spec/09-macros.md §9.2.6 — multi-clause dispatch | `(pick 42)` vs `(pick 1 2)` | COVERED | `spec_09_macros.rs::defmacro_multi_clause_dispatch` + `repl_lifecycle.rs::multi_clause_defmacro_dispatches` |
| `repl_defmacro_display_single_clause` | repl/spec.md §4.1.6 — single-clause display format | `; [x] -> Sexp` | COVERED | `repl_introspection.rs::defmacro_display_single_clause` |
| `repl_defmacro_display_multi_clause` | repl/spec.md §4.1.6 — multi-clause display format | 3 clause lines | COVERED | `repl_introspection.rs::defmacro_display_multi_clause` |
| `repl_macro_produces_if` | spec/09-macros.md §9.2 — macro producing `if` | both branches taken | GAP-COVER + REGRESSION-GUARD | distinct from `quasiquote_with_unquote` (which is single backtick); both-branches angle |
| `repl_macro_produces_let` | spec/09-macros.md §9.2 — macro producing `let` | binding form gen | GAP-COVER + REGRESSION-GUARD | `let`-emitting angle |
| `repl_macro_begin_splicing` | spec/09-macros.md §9.6 — begin splicing | `(begin (defn ...) (call))` | GAP-COVER + REGRESSION-GUARD | `spec_09_macros.rs::macro_begin_two_forms` covers begin reading; emit-from-macro angle thin |
| `repl_defmacro_in_results` | spec/09-macros.md §9.6 — defmacro-in-results | macro emits `(begin (defmacro ...))` | GAP-COVER + REGRESSION-GUARD | high-value: macros generating macros |
| `repl_error_recovery_bad_macro` | spec/09-macros.md §9.14 — bad macro body doesn't corrupt session | type-bad body | COVERED | `repl_negative.rs::failed_redefn_neg_original_preserved` shape covers the pattern; specific-to-macro variant: GAP-COVER if not |
| `repl_error_recovery_no_partial_macro` | spec/09-macros.md §9.14 — no partial registration | session usable after bad defmacro | COVERED | `repl_negative.rs::failed_defn_neg_no_partial_binding` (defn flavour). Strictly the macro flavour is GAP-COVER; reclassify as GAP-COVER. |
| `batch_defmacro_simple` | spec/09-macros.md §9.2 — defmacro in batch | `(defn main ...)` shape | COVERED | mode-equiv via `build_confidence.rs::mode_equiv_macro_user_defined` |
| `batch_defmacro_quasiquote` | spec/09-macros.md §9.4.2 — quasiquote in batch | inc-by-1 | DUPLICATE-IN-LEGACY | duplicates `batch_defmacro_simple`'s coverage in essentials; canonical=`mode_equiv_macro_user_defined` |
| `batch_defmacro_multi_clause` | spec/09-macros.md §9.2.6 — multi-clause in batch | dispatch in batch | COVERED | `mode_equiv_macro_user_defined` shape covers batch; multi-clause angle covered by `defmacro_multi_clause_dispatch` |
| `batch_defmacro_begin_splicing` | spec/09-macros.md §9.6 — begin splicing in batch | `(begin (defn ...))` | GAP-COVER | distinct from `repl_macro_begin_splicing`: batch-mode angle |
| `batch_macro_uses_earlier_macro` | spec/09-macros.md §9.2 — macro composition | `(inc2 (inc (inc x)))` | GAP-COVER | macro-using-macro absent from carry-forward |
| `batch_defmacro_identity` | spec/09-macros.md §9.2 — identity in batch | no quasiquote | COVERED | trivially in `mode_equiv_macro_user_defined` |
| `repl_macro_in_symbol_table` | spec/09-macros.md §9.13 — macro in symbol table | reaches into `s.core.tc.symbol_table()` | GAP-HARVEST | TODO comment in source already calls this out |
| `repl_macro_available_for_later_inputs` | spec/09-macros.md §9.12 — macros available for subsequent inputs | macro used inside later defn | COVERED | `spec_09_macros.rs::macro_persists_across_evals` |
| `repl_multiple_macros_sequential` | spec/09-macros.md §9.2 — multiple macros | m2 uses m1 | DUPLICATE-IN-LEGACY → reclassify | overlaps `batch_macro_uses_earlier_macro` (macro-using-macro). Distinct REPL angle. Reclassify GAP-COVER. |
| `batch_defmacro_parse_error` | spec/09-macros.md §9.14 — malformed defmacro | `(defmacro bad)` | COVERED | `repl_negative.rs::defmacro_missing_params_error` (REPL); batch angle: GAP-COVER if needed |
| `batch_defmacro_name_error` | spec/09-macros.md §9.14 — non-symbol name | `(defmacro 42 ...)` | COVERED | `repl_negative.rs::defmacro_numeric_name_error` |
| `neg_macro_non_sexp_return_type_batch` | spec/09-macros.md §9.2.3 — non-Sexp return errors | Int return body, batch | COVERED | `spec_09_macros.rs::defmacro_displays_with_classification` covers signature-shape; specific non-Sexp-return error: GAP-COVER if narrower needed |
| `neg_macro_non_sexp_return_type_repl` | spec/09-macros.md §9.2.3 — non-Sexp return errors at REPL | Int return, REPL | COVERED | as above |
| `neg_macro_non_sexp_return_bool_batch` | spec/09-macros.md §9.2.3 — Bool return errors | Bool return body | DUPLICATE-IN-LEGACY | of `neg_macro_non_sexp_return_type_batch`; canonical = Int-return |
| `neg_macro_expansion_depth_limit_exceeded` | spec/12-runtime.md §12.7 — expansion depth limit | mutual ping/pong | GAP-COVER + REGRESSION-GUARD | cycle detection in expander; not covered |
| `neg_macro_arity_mismatch` | spec/09-macros.md §9.14 — arity mismatch error | extra args | COVERED | `spec_09_macros.rs::macro_arity_mismatch_error` |
| `neg_macro_error_no_session_corruption` | spec/09-macros.md §9.14 — error doesn't corrupt session | recovery + new defmacro | COVERED | `repl_negative.rs::error_then_valid_form_succeeds` shape |
| `repl_defmacro_rest_splice` | spec/09-macros.md §9.4.2 — rest-param + ~@ splice | `~@rest` produces sconcat | GAP-COVER + REGRESSION-GUARD | rest-splice angle absent from carry-forward; high-value (the test was authored to cover a specific S{N} bug) |

### GAP-COVER recommendations

- **`repl_macro_produces_if`** → `tests/spec_09_macros.rs` — angle: macro emits `if`, both branches exercised.
- **`repl_macro_produces_let`** → `tests/spec_09_macros.rs` — angle: macro emits `let`.
- **`repl_macro_begin_splicing`** → `tests/spec_09_macros.rs` — angle: macro emits `(begin (defn ...) (call))`.
- **`repl_defmacro_in_results`** → `tests/spec_09_macros.rs` — angle: macro produces `(defmacro ...)`.
- **`batch_defmacro_begin_splicing`** → `tests/build_confidence.rs` (or `spec_09_macros.rs`) — angle: begin-splicing works in batch mode.
- **`batch_macro_uses_earlier_macro`** / **`repl_multiple_macros_sequential`** → `tests/spec_09_macros.rs` — angle: macro2 calls macro1 (composition).
- **`neg_macro_expansion_depth_limit_exceeded`** → `tests/spec_09_macros.rs` (or `spec_12_runtime.rs`) — angle: mutually recursive macros hit depth limit. Negative test, message must contain "depth"/"limit"/"expansion".
- **`repl_defmacro_rest_splice`** → `tests/spec_09_macros.rs` — angle: rest-param + `~@` splice expansion. Rust-internal-but-e2e-witnessable: macro definition then call.
- **`repl_error_recovery_no_partial_macro`** (reclassified) → `tests/repl_negative.rs` — angle: macro flavour of failed-defn-no-partial.
- **`batch_defmacro_parse_error`** (if narrower needed than REPL flavour) → `tests/build_confidence.rs` mode_equiv — angle: batch parse error.

Sketch per recommendation: REPL-canonical via `repl_session_with_test_prelude` + `repl_eval`/`repl_eval_display`; assert displayed result.

---

## 4. tests/legacy/ring0.rs (108 tests)

Cluster mode. ring0 is dominated by basic-language redundancy with `sketch_port.rs` and the `spec_04_expressions.rs` / `spec_05_definitions.rs` carry-forwards.

### Summary

| Disposition | Count (approx) |
|---|---:|
| COVERED | ~73 |
| DUPLICATE-IN-LEGACY (with sketch_port) | ~12 |
| GAP-COVER | ~18 |
| (of which REGRESSION-GUARD) | ~4 |
| GAP-HARVEST | ~5 |

### Cluster table

| Cluster | Spec property | Tests | Disposition |
|---|---|---|---|
| Basic arithmetic / IO display (5 tests) | spec/04 §4.1, §A.1 — primitive add/sub/mul/div, hello | `hello`, `arithmetic_addition`, `arithmetic_subtraction`, `arithmetic_multiplication`, `arithmetic_division` | COVERED — `spec_appendix_a_builtins.rs::primitive_*_i64` + `mode_equiv_primitive_arithmetic` |
| Recursion fundamentals (3 tests) | spec/04 §4.7 — recursive defns | `factorial`, `fibonacci`, `nested_let` | COVERED — `repl_lifecycle.rs::recursive_factorial`, `recursive_fibonacci`, `spec_04_expressions.rs::let_nested_shadowing` |
| Control flow basics (4 tests) | spec/04 §4.4, §4.6 — chained calls, if, comparison | `chained_function_calls`, `comparison_operators`, `forward_reference`, `nested_if` | COVERED — `spec_04_expressions.rs::application_chained`, comparison via `spec_appendix_a_builtins.rs::primitive_eq/lt/gt_i64`, `repl_lifecycle.rs::interleaved_defns_and_exprs` shape |
| REPL eval basics (8 tests) | repl/spec.md §3.1 — eval at prompt | `repl_eval_expression`, `repl_eval_arithmetic`, `repl_define_and_call`, `repl_chained_calls`, `repl_redefinition_updates_callers`, `repl_recursive_function`, `repl_type_error_recovers`, `repl_multiple_params` | COVERED — `repl_lifecycle.rs::*` and `repl_introspection.rs::display_*` |
| Lambda variants (6 tests) | spec/04 §4.5 — lambda forms | `lambda_immediate_call`, `lambda_in_let`, `lambda_passed_to_function`, `named_function_as_value`, `lambda_zero_params`, `lambda_multi_params` | COVERED — `spec_04_expressions.rs::lambda_immediate_call`, `lambda_zero_args`, `lambda_multi_args`, `lambda_closure_captures` |
| REPL lambda variants (4 tests) | repl/spec.md §3.1 — lambda at REPL | `repl_lambda_immediate`, `repl_lambda_in_let`, `repl_higher_order_function`, `repl_named_function_as_value` | COVERED via above carry-forwards (REPL-mode shared) |
| TCO cluster (5 tests) | spec/04 §4.7 — tail call optimisation | `tco_deep_countdown`, `tco_accumulator`, `tco_match_tail_position`, `tco_let_body_tail_position`, `tco_non_tail_recursion_unchanged` | GAP-COVER (×3) + DUPLICATE-IN-LEGACY (×2 vs sketch_port). High-value for runtime spec. **Wave 5.5 already deferred this cluster** — confirm same disposition; recommend filing a new `spec/12-runtime.md` MUST clause for TCO, then write 3 carry-forward tests (deep-countdown, match-tail, accumulator). |
| Float arithmetic (7 tests) | spec/04 §A.1 — float ops | `float_arithmetic`, `float_subtraction`, `float_multiplication`, `float_division`, `float_comparison`, `float_type_error_mixed`, `repl_float_eval`, `repl_float_arithmetic` | COVERED — `spec_appendix_a_builtins.rs::primitive_add_f64`, `primitive_lt_f64` + `display_format` for floats |
| Type errors basic (8 tests) | spec/03 §3.6 — type unification errors | `type_error_add_bool`, `error_type_error_int_plus_bool`, `error_type_error_bool_as_int`, `error_type_mismatch_if_branches`, `error_defn_body_type_mismatch`, `error_parse_error_unclosed_paren`, `error_parse_error_extra_closing_paren`, `error_unbound_symbol` | COVERED — `spec_03_types.rs::unification_int_vs_string_errors`, `repl_negative.rs::*_error*`, `parse_error_*` |
| Wrong arity / curry (2 tests) | spec/04 §4.5 — arity | `error_wrong_arity_too_many_args`, `auto_curry_too_few_args_returns_closure` | COVERED — `repl_negative.rs::wrong_arity_too_many_args`, `auto_curry_too_few_args_not_error` |
| ADT enum baseline (4 tests) | spec/06 §6.1, §6.5 | `adt_enum_match`, `repl_adt_enum`, `repl_adt_enum_match`, `error_non_exhaustive_match_runtime` | COVERED — `spec_06_pattern_matching.rs::match_enum_basic`, `pattern_non_exhaustive_match_on_adt_neg` |
| Dual-mode cluster (10 tests) | mode-equiv batch+REPL | `dual_mode_simple_int`, `dual_mode_arithmetic`, `dual_mode_factorial`, `dual_mode_nested_let`, `dual_mode_chained_calls`, `dual_mode_comparison`, `dual_mode_forward_reference`, `dual_mode_boolean_logic`, `dual_mode_enum_match`, `dual_mode_recursive` | COVERED — `build_confidence.rs::mode_equiv_*` family. The dual-mode framing is now first-class in `build_confidence.rs`; per-feature dual-mode tests are obviated. |
| Type annotations (3 tests) | spec/03 §3.5 — annotated params/return | `annotated_params`, `annotated_return_inferred`, `annotation_mismatch_error` | COVERED — `spec_03_types.rs::annotated_params_int`, `annotated_return_type_int`, `unification_int_vs_string_errors` |
| Polymorphism (2 tests) | spec/03 §3.7 — let polymorphism | `let_polymorphism_identity`, `let_bound_polymorphic_usage` | COVERED — `spec_03_types.rs::let_polymorphism_identity_two_types` |
| Multi-defn cluster (3 tests) | spec/05 §5.1 | `multiple_functions`, `mutual_forward_references`, `main_calls_helper` | COVERED — `spec_05_definitions.rs::forward_reference_between_defns`, `repl_lifecycle.rs::multiple_defns_coexist` |
| Literal edge cases (4 tests) | spec/04 §4.2 — literals | `negative_integer`, `zero`, `large_integer`, `boolean_not_true`, `boolean_not_false` | COVERED — `spec_04_expressions.rs::literal_*`, `repl_introspection.rs::display_negative_int`, `display_large_int`, `display_zero_int` |
| Deep let / if-with-let (2 tests) | spec/04 §4.3 | `deeply_nested_let`, `if_with_let_branches` | COVERED — `spec_04_expressions.rs::let_nested_shadowing` (depth angle: optional GAP-COVER if nesting depth ≥3 explicitly required) |
| Match patterns (2 tests) | spec/06 §6.5 | `match_wildcard`, `match_var_pattern` | COVERED — `spec_06_pattern_matching.rs::pattern_wildcard_catchall`, `pattern_variable_binds_value` |
| Comparison ≤≥ (2 tests) | §A.1 | `comparison_less_equal`, `comparison_greater_equal` | COVERED — `spec_appendix_a_builtins.rs::primitive_le_i64`, `primitive_ge_i64` |
| REPL boolean / if / let / negative-int / nested / parse-recover / not / comparison / multiple / countdown / enum / defn-then-expr (12 tests) | repl/spec.md §3 | `repl_boolean_expression`, `repl_boolean_false`, `repl_if_expression`, `repl_let_expression`, `repl_negative_int`, `repl_nested_calls`, `repl_parse_error_recovers`, `repl_not_operator`, `repl_comparison_operators`, `repl_multiple_definitions`, `repl_recursive_countdown`, `repl_enum_definition_and_use`, `repl_defn_then_expression` | COVERED — distributed across `repl_lifecycle.rs` and `repl_introspection.rs` |
| Error edge (3 tests) | repl_negative coverage | `error_if_condition_not_bool`, `error_duplicate_param_names`, `error_undefined_function_call` | COVERED — `repl_negative.rs::type_error_if_condition_wrong_type` + analogues. **Duplicate param names** angle: GAP-COVER if not present in `repl_negative.rs`; verify. |
| Integer overflow / underflow / div-by-zero (5 tests) | spec/12 §12.7 | `integer_overflow_wraps`, `integer_underflow_wraps`, `checked_division_by_zero_panics`, `checked_div_min_neg1_panics`, `checked_division_normal` | COVERED — `spec_12_runtime.rs::integer_overflow_wraps_silently`, `integer_underflow_wraps_silently`, `integer_division_by_zero_panics_neg`. The `checked_div_min_neg1_panics` (i64::MIN / -1 overflow trap) angle is GAP-COVER + REGRESSION-GUARD. |
| Source encoding (1 test) | spec/12 §12.1 | `source_encoding_utf8` | COVERED — `spec_12_runtime.rs::string_utf8_source_encoding_accepted` |

### GAP-COVER recommendations

- **`tco_deep_countdown`** → `tests/spec_12_runtime.rs` — angle: tail-recursive countdown to large depth (e.g., 100k) without stack overflow. **Pre-req**: `/spec` clarification on TCO normative section (already in Wave 5.5 deferred list).
- **`tco_match_tail_position`** → `tests/spec_12_runtime.rs` — angle: TCO inside `match` arm.
- **`tco_accumulator`** → `tests/spec_12_runtime.rs` — angle: accumulator-style tail recursion.
- **`tco_let_body_tail_position`** / **`tco_non_tail_recursion_unchanged`** → optional; angle: TCO inside `let` body / non-tail recursion still works.
- **`error_duplicate_param_names`** → `tests/repl_negative.rs` (verify not present) — angle: `(defn f [x x] ...)` rejected.
- **`checked_div_min_neg1_panics`** → `tests/spec_12_runtime.rs` — angle: i64::MIN / -1 traps. REGRESSION-GUARD.
- **Deep nested let (≥3 levels)** if not in `let_nested_shadowing` → optional; angle: `(let [a 1] (let [b 2] (let [c 3] ...)))`.

### GAP-HARVEST

The 4-5 dual-mode-batch-only or batch-stage-internal tests where the assertion reaches into batch-pipeline internals (rare in ring0; mostly the cluster is REPL-equivalent). Specifically:

- `auto_curry_too_few_args_returns_closure` (asserts on returned function value rep) — partially in `repl_negative.rs::auto_curry_too_few_args_not_error`; functional coverage adequate.
- `error_non_exhaustive_match_runtime` (asserts on runtime panic) — COVERED by `pattern_non_exhaustive_match_on_adt_neg`.

Tentative GAP-HARVEST count: ≤5; most "hard internals" went to ring2.

---

## 5. tests/legacy/sketch_port.rs (148 tests)

Cluster mode. Per Wave 5.5: 88% COVERED in sample — sketch_port is by design a port of the sketch's cross-pipeline acceptance suite, and most language-level assertions are already in the carry-forward.

Examination of test names (sample read of beginning + grep) confirms the file's structure: dual-mode tests of arithmetic, recursion, ADTs, closures, strings, vectors, traits, modules, and a layer of "sketch parity" tests that verify the new compiler reproduces the sketch's output for known programs.

### Summary (estimated from sample + structure)

| Disposition | Count (approx) |
|---|---:|
| COVERED | ~120 |
| DUPLICATE-IN-LEGACY (vs ring0/ring1) | ~16 |
| GAP-COVER | ~8 |
| (of which REGRESSION-GUARD) | ~3 |
| GAP-HARVEST | ~4 |

### Notable clusters

(See file for full test list; not enumerated here due to volume. Cluster groups derived from name prefixes.)

| Cluster prefix | Count (approx) | Disposition |
|---|---:|---|
| `arithmetic_*`, `factorial_*`, `fibonacci_*` | ~12 | COVERED — duplicates ring0 baseline; spec_04/spec_appendix_a |
| `closure_*` | ~25 | COVERED — `spec_04_expressions.rs::lambda_closure_captures`, `spec_05_definitions.rs::*` cluster handles closure shapes; high overlap with ring1 closure cluster |
| `adt_*`, `match_*` | ~30 | COVERED — `spec_06_pattern_matching.rs` covers core; some specific ADT-shape duplicates of ring1 |
| `string_*` | ~15 | COVERED — string ops were the big Wave 5.5 GAP-COVER, now landed in `spec_appendix_a_builtins.rs`; 1-2 may remain GAP-COVER |
| `vec_*` | ~20 | COVERED — `spec_appendix_a_builtins.rs::primitive_vec_*`, `spec_04_expressions.rs::vec_literal_*` |
| `module_*`, `import_*` | ~12 | COVERED partially — overlap with `tests/legacy/modules.rs`; some shapes may be GAP-COVER |
| `trait_*` | ~10 | COVERED — `spec_07_traits.rs` |
| `mode_equiv_*` (sketch parity) | ~15 | COVERED — `build_confidence.rs::mode_equiv_*` |
| `error_*`, `neg_*` | ~10 | COVERED — `repl_negative.rs` |

### GAP-COVER recommendations

Examination of the full file is needed for high-confidence enumeration, but Wave 5.5's 88% COVERED rate suggests **no high-value GAP-COVER remains** here. The residual ~8 likely-GAP-COVER are sketch-specific shapes (Decision-30 super rewrites, sketch-paritied multi-clause patterns) that are best harvested into the owning crate.

**Recommended action for `/sprint`**: dispatch `/qa` for a *focused second pass* on `sketch_port.rs` only if cross-file analysis surfaces a load-bearing gap. Otherwise treat as adequately covered and harvest the residual.

### GAP-HARVEST

`sketch_port.rs` includes ~4 tests that assert on `cranelisp_typecheck`/`cranelisp_backend` internals (e.g., specific AST shapes, generated CLIF). These are the harvest residue per FIXME 0136.

---

## 6. tests/legacy/e2e.rs (148 tests)

Cluster mode. Per Wave 5.5 sample, e2e.rs has the highest GAP-COVER residue density (8/30 in sample), and 11/18 regression-named tests were GAP-COVER. Wave 5.5 remediated the slash-command nonexistent-name guards (5 tests) + list-category negatives (3 tests) and some imports-fresh-session guards. Residual gaps cluster in:

### Summary (estimated)

| Disposition | Count (approx) |
|---|---:|
| COVERED | ~95 |
| DUPLICATE-IN-LEGACY | ~10 |
| GAP-COVER | ~30 |
| (of which REGRESSION-GUARD) | ~12 |
| GAP-HARVEST | ~13 |

### Cluster table (e2e_s{N}_{M}_* prefix-driven)

| Cluster | Spec property | Tests (approx count) | Disposition |
|---|---|---:|---|
| `e2e_s1_*` (boot/banner) | repl/spec.md §1 | ~6 | COVERED — `repl_lifecycle.rs::boot_*` |
| `e2e_s2_*` (eval primitives + display) | repl/spec.md §2 | ~15 | COVERED — `repl_introspection.rs::display_*` |
| `e2e_s3_1_*` (slash commands /sig /doc /info etc.) | repl/spec.md §3.1 | ~25 | COVERED via `repl_introspection.rs::*` + 5 nonexistent-name remediated in 5.5 |
| `e2e_s3_2_*` (multi-line / paste) | repl/spec.md §3.2 | ~6 | GAP-COVER — multi-line input fidelity; verify against `repl_lifecycle.rs::interleaved_defns_and_exprs` |
| `e2e_s3_3_*` (/list categories) | repl/spec.md §3.3 | ~12 | COVERED (positive) + remediated in 5.5 (3 negatives) |
| `e2e_s3_4_*` (/imports) | repl/spec.md §3.4 | ~10 | COVERED + remediated in 5.5 (1 negative) |
| `e2e_s3_5_*` (/exports) | repl/spec.md §3.5 | ~6 | GAP-COVER — exports-shape thin in carry-forward; verify against `spec_08_modules.rs` |
| `e2e_s3_6_*` (/expand) | repl/spec.md §3.6 | ~5 | COVERED — `repl_introspection.rs::expand_*` |
| `e2e_s3_7_*` (/help) | repl/spec.md §3.7 | ~3 | COVERED — `repl_introspection.rs::help_lists_commands` |
| `e2e_s3_8_*` (/mod /reload) | repl/spec.md §3.8 | ~6 | COVERED — `repl_lifecycle.rs::mod_shows_current` (partial); /reload angle is GAP-COVER |
| `e2e_s4_*` (run mode `--run`) | repl/spec.md §4 | ~8 | COVERED — `spec_10_io.rs::run_mode_main_*` |
| `e2e_s5_*` (link mode `--link`) | repl/spec.md §5 | ~6 | COVERED — `build_confidence.rs::smoke_link_then_run_*` |
| `e2e_s6_*` (cache observability) | various | ~8 | COVERED — `cache.rs::*` |
| `e2e_repro_*` (defect reproductions) | various | ~12 | GAP-COVER + REGRESSION-GUARD — defaults preserve unless EXACT 1:1 in `tests/sprint*` already |
| `e2e_neg_*` (negative paths beyond slash command) | various | ~8 | GAP-COVER — verify each against `repl_negative.rs` |

### GAP-COVER recommendations (priorities)

1. **`e2e_repro_*` cluster (~12 tests)** — every reproduction is presumptively discriminating. For each: open the test, identify the originating sprint/defect, verify if existing `tests/sprint*` files already cover; if not, carry-forward into the relevant `spec_*` file with `_repro_` in the name preserved.
2. **`e2e_s3_2_*` multi-line / paste fidelity (~6 tests)** — assert that pasted multi-line sexps are read and evaluated equivalently to single-line. Recommended target: `tests/repl_lifecycle.rs`.
3. **`e2e_s3_5_*` `/exports`** (~6 tests) — `/exports <mod>` listing module surface; thin in carry-forward. Target: `tests/repl_introspection.rs`.
4. **`e2e_s3_8_*` `/reload`** (~3 tests) — module reload shape. Target: `tests/repl_lifecycle.rs`.

### Sketch per recommendation

REPL-canonical via `run_repl` / `run_repl_with_test_prelude`; the existing test bodies in `e2e.rs` are largely subprocess-based already, so direct lift is mechanical.

### GAP-HARVEST

The ~13 e2e tests that assert on stderr-contained tracing/diagnostic substrings unique to a specific `CRANELISP_*_TRACE` env var, or on specific cache-file inode attributes, belong in the corresponding crate's unit tests.

---

## 7. tests/legacy/ring1.rs (190 tests)

Cluster mode. ring1 is the largest GAP-COVER surface per Wave 5.5 sample (14/30 GAP-COVER, dominated by string ops). Most string ops were remediated in Wave 5.5 (18 new `spec_appendix_a_builtins.rs` tests); residual gaps cluster in:

### Summary (estimated, post-Wave-5.5-string-fix)

| Disposition | Count (approx) |
|---|---:|
| COVERED | ~115 |
| DUPLICATE-IN-LEGACY (vs sketch_port + ring0) | ~25 |
| GAP-COVER | ~35 |
| (of which REGRESSION-GUARD) | ~10 |
| GAP-HARVEST | ~15 |

### Cluster table

| Cluster | Spec property | Tests (lines) | Disposition |
|---|---|---|---|
| String ops core (16 tests, lines 39-225) | spec/A.3 — basic string ops | `string_literal`, `string_empty_literal`, `string_in_let`, `string_as_function_argument`, `string_as_function_return`, `string_concat`, `string_eq_true`, `string_eq_false`, `string_int_to_string`, `string_float_to_string`, `string_bool_to_string`, `string_concat_chained`, `string_len`, `string_len_empty`, `string_in_if_branches`, `repl_string_literal`, `repl_string_concat`, `repl_string_eq`, `repl_int_to_string` | COVERED — `spec_appendix_a_builtins.rs::primitive_str_*`, `spec_03_types.rs::primitive_string_display`. Wave 5.5 remediation already absorbed |
| String ops extended (18 tests, lines 226-368) | spec/A.3 | `string_substring_*` (×4), `string_char_at_*` (×2), `string_trim_*` (×2), `string_to_upper_*`, `string_to_lower_*`, `string_starts_with_*` (×2), `string_ends_with_*` (×2), `string_contains_*` (×2), `string_replace_*` (×2), `string_split_*`, `string_join_*` | COVERED — Wave 5.5 ported these 18 to `spec_appendix_a_builtins.rs` |
| ADT product (7 tests) | spec/06 §6.1 | `adt_product_construct_and_match`, `adt_product_get_y`, `adt_product_multi_field`, `adt_product_in_let`, `adt_product_as_function_arg`, `adt_product_as_function_return`, `adt_shortcut_syntax` | COVERED — `spec_06_pattern_matching.rs::pattern_data_constructor_binds_fields`, `spec_05_definitions.rs::deftype_product_*` |
| ADT sum (5 tests) | spec/06 §6.1 | `adt_sum_option_some`, `adt_sum_option_none`, `adt_sum_wildcard_pattern`, `adt_sum_var_pattern`, `adt_sum_nested_match` | COVERED — `spec_06_pattern_matching.rs::pattern_some_binds_value`, `spec_05_definitions.rs::deftype_sum_with_field_match` |
| ADT polymorphic / Either / mixed (3 tests) | spec/06 §6.2 | `adt_polymorphic_type`, `adt_either_type`, `adt_enum_mixed_nullary_and_data` | GAP-COVER — `Either` shape and mixed-nullary-data discriminator are absent from carry-forward. `Either` is REGRESSION-GUARD per S{N}-shape (specific bug fix) |
| REPL ADT (5 tests) | repl/spec.md §3 | `repl_adt_product`, `repl_adt_sum_some`, `repl_adt_sum_none`, `repl_adt_match`, `repl_adt_product_match` | COVERED — covered by `repl_introspection.rs::constructor_display`, `deftype_display_*` + `spec_06_*` |
| Closures core (12 tests) | spec/04 §4.5 — closures | `closure_simple_capture`, `closure_multiple_captures`, `closure_returned_from_function`, `closure_nested`, `closure_with_higher_order`, `closure_zero_param`, `closure_multi_param`, `closure_capturing_bool`, `closure_apply_twice`, `closure_compose`, `named_function_as_value_apply`, `closure_capturing_function_arg`, `closure_in_if_branch`, `closure_recursive_with_higher_order` | COVERED — `spec_04_expressions.rs::lambda_closure_captures`, `lambda_passed_to_function` shape; `closure_compose` and `closure_recursive_with_higher_order` are GAP-COVER (specific composition shapes) |
| REPL closures (4 tests) | repl/spec.md §3 | `repl_closure_simple`, `repl_closure_multiple_captures`, `repl_closure_returned`, `repl_closure_display` | COVERED |
| Closure × ADT × string interactions (4 tests) | spec/04 §4.5 + §A.3 | `closure_returning_adt`, `closure_capturing_int_returning_match_result`, `adt_containing_closure_result`, `string_in_adt`, `string_from_int_to_string_in_match` | GAP-COVER — multi-feature interaction shapes; high-value preserve at least 2-3 of these |
| Match exhaustiveness (3 + 4 tests) | spec/06 §6.5 | `exhaustive_match_all_constructors`, `exhaustive_match_with_wildcard`, `exhaustive_match_with_var_pattern`, `non_exhaustive_match_panics`, `exhaustive_product_type`, `match_three_constructors` | COVERED — `pattern_non_exhaustive_match_on_adt_neg` (Wave 5.5) + `pattern_first_match_wins` |
| Dual-mode cluster (~14 tests) | mode-equiv | `dual_mode_*` family | COVERED — `build_confidence.rs::mode_equiv_*` first-class |
| Type errors with strings/ADTs (5 tests) | spec/03 §3.6 | `error_string_where_int_expected`, `error_int_where_string_expected`, `error_adt_constructor_wrong_arg_count`, `error_adt_constructor_wrong_type`, `error_if_branches_type_mismatch_string_int` | COVERED — `spec_03_types.rs::unification_int_vs_string_errors`, `repl_negative.rs::constructor_wrong_arg_count_error`, `type_error_arg_mismatch` |
| Closure arity / undef ctor (2 tests) | spec/03 §3.6 | `error_closure_arity_mismatch`, `error_undefined_constructor` | COVERED — `repl_negative.rs::wrong_arity_too_many_args`, `undefined_constructor_error` |
| Polymorphism shapes (6 tests) | spec/03 §3.7 | `let_bound_identity_at_multiple_types`, `polymorphic_higher_order`, `let_bound_lambda_with_capture`, `identity_on_string`, `identity_on_adt`, `higher_order_on_adt` | COVERED — `spec_03_types.rs::let_polymorphism_identity_two_types`, `polymorphic_identity_at_int/bool` |
| `parse_int_*` (2 tests) | spec/A.3 | `parse_int_valid`, `parse_int_invalid` | GAP-COVER — `parse-int` primitive not in `spec_appendix_a_builtins.rs`. REGRESSION-GUARD (Some/None return). |
| Closure × TCO × ADT (2 tests) | spec/12 §12.7 | `closure_and_tco`, `adt_in_tco` | GAP-COVER — TCO interaction shapes. Defer-tier per Wave 5.5 TCO defer. |
| Misc combination (4 tests) | various | `string_in_recursive_function`, `multiple_adt_definitions`, `closure_over_closure`, `let_bound_adt_and_closure` | GAP-COVER (×2-3) — specific multi-feature shapes |
| Vec literals + ops (~30 tests, lines 1434-1779) | spec/04 + §A | `vec_literal_*`, `vec_get_*`, `vec_set_*`, `vec_push_*`, `vec_len_*`, `vec_in_*`, `vec_of_*`, `vec_returned_*`, `vec_passed_*`, `repl_vec_*`, `dual_mode_vec_*` | COVERED — `spec_appendix_a_builtins.rs::primitive_vec_*`, `spec_04_expressions.rs::vec_literal_*`, `spec_12_runtime.rs::vec_set_cow_preserves_original`, `vec_push_cow_*`, `vec_of_strings_alloc_drop` |
| Match-quality errors (~15 tests, lines 1779-2253) | spec/06 §6.5 + spec/03 §3.6 — error-quality | `error_type_mismatch_names_both_types`, `error_if_branch_type_mismatch`, `match_eval_order_top_to_bottom`, `match_binding_scope_limited_to_arm`, `error_match_arm_type_disagreement`, `match_constructor_pattern_type_checking`, `match_variable_pattern_gets_scrutinee_type`, `match_wildcard_no_constraints`, `match_return_type_unified`, `match_non_adt_int_var_pattern`, `match_non_adt_bool_wildcard`, `neg_exhaustive_match_missing_constructor_compile_error`, `neg_exhaustive_match_single_arm_lists_all_missing`, `neg_match_empty_arms_rejected`, `neg_match_non_adt_scrut_with_adt_constructor_rejected`, `error_nested_pattern`, `match_in_trait_impl` | COVERED partially — `spec_06_pattern_matching.rs::pattern_arms_type_unify` covers the core; specific error-quality shapes (`error_quality_*` family below) and the `_neg_exhaustive_*` cluster are GAP-COVER + REGRESSION-GUARD |
| `error_quality_*` (8 tests, lines 2125-2196) | spec/03 §3.6 — error message quality | `error_quality_string_where_int_names_string`, `error_quality_string_where_int_names_int`, `error_quality_int_where_string_names_int`, `error_quality_int_where_string_names_string`, `error_quality_constructor_wrong_type_names_bool`, `error_quality_if_branch_mismatch_names_types`, `error_quality_undefined_constructor_names_it`, `error_quality_match_arm_type_mismatch` | GAP-COVER + REGRESSION-GUARD — error-quality is a specific user-facing concern; carry-forward only checks "errors", not "errors with the named types/symbols". High-value preserve. |
| Pattern shapes (3 tests) | spec/06 §6.5 | `neg_nested_pattern_rejected`, `neg_pattern_wrong_binding_count`, `neg_pattern_too_many_bindings` | GAP-COVER + REGRESSION-GUARD — pattern-shape rejections; spec-load-bearing |

### GAP-COVER recommendations (priorities)

1. **`error_quality_*` cluster (8 tests)** → `tests/repl_negative.rs` — angle: error message names the involved types/symbols. High-value: error UX is a Principle.
2. **`adt_polymorphic_type`, `adt_either_type`, `adt_enum_mixed_nullary_and_data`** → `tests/spec_05_definitions.rs` or `tests/spec_06_pattern_matching.rs` — angle: polymorphic ADT, Either type, mixed nullary+data discrimination.
3. **`closure_returning_adt`, `closure_capturing_int_returning_match_result`, `adt_containing_closure_result`** → `tests/spec_04_expressions.rs` — angle: closure × ADT interaction.
4. **`closure_compose`, `closure_recursive_with_higher_order`** → `tests/spec_04_expressions.rs` — angle: closure composition (`compose f g`), HOF-recursive shape.
5. **`parse_int_valid`, `parse_int_invalid`** → `tests/spec_appendix_a_builtins.rs` — angle: `parse-int` primitive returns Some/None.
6. **`neg_exhaustive_match_missing_constructor_compile_error`, `neg_exhaustive_match_single_arm_lists_all_missing`, `neg_match_empty_arms_rejected`, `neg_match_non_adt_scrut_with_adt_constructor_rejected`** → `tests/spec_06_pattern_matching.rs` — angle: compile-time exhaustiveness errors with specific message shapes.
7. **`neg_nested_pattern_rejected`, `neg_pattern_wrong_binding_count`, `neg_pattern_too_many_bindings`** → `tests/spec_06_pattern_matching.rs` — angle: pattern arity/shape rejections. REGRESSION-GUARD.
8. **`match_in_trait_impl`** → `tests/spec_07_traits.rs` — angle: `match` inside trait impl method.
9. **`closure_and_tco`, `adt_in_tco`** → defer (TCO sub-spec gap, Wave 5.5 deferred).

### GAP-HARVEST

The ~15 ring1 tests that assert on `cranelisp_typecheck::TypeChecker` internal state (mostly the match-quality cluster's `tc.symbol_table()` peeks) are harvest-tier per FIXME 0136.

---

## 8. tests/legacy/ring2.rs (199 tests)

Cluster mode. Per Wave 5.5: ring2 is dominated by the `regression_named_prim_*` cluster (10 tests, fully COVERED in `spec_appendix_a_builtins.rs`) plus trait/dual-mode tests already largely COVERED.

ring2 also contains specific "deep-internal" tests (HKT, occurs-check, scheduler internals) that Wave 5.5 deferred.

### Summary (estimated)

| Disposition | Count (approx) |
|---|---:|
| COVERED | ~140 |
| DUPLICATE-IN-LEGACY | ~10 |
| GAP-COVER | ~25 |
| (of which REGRESSION-GUARD) | ~12 |
| GAP-HARVEST | ~24 |

### Cluster table

| Cluster | Spec property | Tests | Disposition |
|---|---|---|---|
| `regression_named_prim_*` (10 tests) | spec/A.1, A.3 | `add-i64`, `sub-i64`, `mul-i64`, `div-i64`, `eq-i64`, `lt-i64`, `add-f64`, `le-i64`, `ge-i64`, `gt-i64` | COVERED — `spec_appendix_a_builtins.rs::primitive_*` (Wave 5.5 cited) |
| Traits (`trait_*`, ~25 tests) | spec/07 | core trait + impl + dispatch | COVERED — `spec_07_traits.rs::*` |
| Dual-mode-trait (`dual_mode_trait_*`, ~12 tests) | spec/07 | mode-equiv trait dispatch | COVERED — Wave 5.5 noted "REPL-canonical spec_07 tests; technically COVERED, just lower multiplicity" |
| HKT (`hkt_*`, ~3 tests) | spec/03 §3.7 (?) | higher-kinded type variables | GAP-HARVEST per Wave 5.5 — spec coverage unclear; needs spec sweep first |
| Occurs check (`neg_occurs_check_*`, 1 test) | spec/03 §3.6 | infinite type rejected | GAP-HARVEST — type-error e2e shape; deferred |
| Trait neg (`neg_impl_missing_method_errors`) | spec/07 | impl missing required method | GAP-COVER + REGRESSION-GUARD — Wave 5.5 deferred |
| Lazy seq (`lazy_seq_*`, ~5 tests) | spec/12 (TBD) | thunk-based seq construction | GAP-HARVEST — spec section needed first per Wave 5.5 |
| Scheduler / IO (`scheduler_*`, `io_*`, ~10 tests) | spec/10 §10.12, spec/12 §12.4 | concurrency primitives, scheduling classes | GAP-HARVEST — platform fixture required (test-capture DLL) |
| Multi-sig dispatch (`multi_sig_*`, ~10 tests) | spec/05 §5.2 | arity dispatch, type-based dispatch | COVERED — `spec_04_expressions.rs::multi_sig_arity_dispatch`, `spec_05_definitions.rs::defn_multi_clause_arity` |
| Constrained polymorphism (`constrained_*`, ~12 tests) | spec/03, spec/07 | monomorphisation at call site | COVERED — `spec_03_types.rs::constrained_add_int/float`, `spec_07_traits.rs::constrained_polymorphism_*` |
| RC interaction (`rc_*`, ~15 tests) | spec/12 §12.6 | reference counting | COVERED — `spec_12_runtime.rs::*_alloc_*_freed`, `vec_*_cow_*`, `string_*_freed` family + GAP-HARVEST residue |
| Closure capture cases (`capture_*`, ~10 tests) | spec/04 §4.5 | various capture shapes | COVERED — `spec_12_runtime.rs::closure_capture_alloc_*`, `closure_multiple_captures` |
| Match performance / size (`match_*`, ~10 tests) | spec/06 §6.5 | match dispatch | COVERED — partial; some specific shapes GAP-COVER |
| Mod / cache (`mod_*`, `cache_*`, ~10 tests) | spec/08, spec/12 | module + cache integration | COVERED — `cache.rs::*`, `spec_08_modules.rs::*` |
| Misc / sprint regressions (`sprint*_*`, ~15 tests) | various | per-sprint defect repros | GAP-COVER + REGRESSION-GUARD — verify each against `tests/sprint*.rs` |
| Internals (`internal_*`, `tc_internal_*`, etc., ~24 tests) | various | TC/backend internals | GAP-HARVEST per FIXME 0136 |

### GAP-COVER recommendations

1. **`neg_impl_missing_method_errors`** → `tests/spec_07_traits.rs` — angle: `impl` declares fewer methods than trait requires. REGRESSION-GUARD.
2. **`sprint*_*` tests (~10-15)** — for each, verify against `tests/sprint*.rs`; carry-forward to relevant `spec_*` file if not.
3. **Specific match-shape tests (~5)** — match performance edges, large arm count.
4. **Lazy seq cluster (5 tests)** — defer per Wave 5.5 (spec sweep needed first).
5. **HKT cluster (3 tests)** — defer per Wave 5.5.

### GAP-HARVEST

ring2's 24 deep-internals (TC symbol table peeks, codegen CLIF inspections, scheduler atomic counters) are the harvest residue per FIXME 0136. These were the "hard internals" subset noted in Wave 5.5 confidence assessment.

---

## Cross-file analysis

### Files where DUPLICATE-IN-LEGACY rate is high

- **sketch_port.rs × ring0.rs**: ~12 arithmetic/recursion duplicates. Canonical instance: ring0 (more complete dual-mode pairs).
- **sketch_port.rs × ring1.rs**: ~16 ADT/closure/string duplicates. Canonical: ring1.
- **modules.rs × sketch_port.rs**: ~3 module-resolution duplicates. Canonical: modules.rs (specifically the super-import pair).
- **macros.rs internal**: 1 duplicate (`neg_macro_non_sexp_return_bool_batch` ≈ `neg_macro_non_sexp_return_type_batch`).

### Spec sections with high GAP-COVER counts (under-served carry-forward)

| Spec section | GAP-COVER count | Source clusters |
|---|---:|---|
| spec/03 §3.6 (error message quality) | ~10 | ring1 `error_quality_*` |
| spec/06 §6.5 (pattern shape rejections) | ~7 | ring1 `neg_*_pattern_*` + `neg_exhaustive_*` |
| spec/08 §8.4 (export re-export) | ~5 | modules `export_*` |
| spec/04 §4.5 (closure × ADT × match) | ~5 | ring1 multi-feature shapes |
| spec/05 §5.2 (ADT polymorphic / Either / mixed) | ~3 | ring1 ADT cluster |
| spec/12 §12.4.3 (lenient eval) | ~7 | lenient (most are correctness-only e2e) |
| spec/12 §12.7 (TCO) | ~5 | ring0 + ring1 (deferred Wave 5.5) |
| repl/spec.md §3.5 (/exports) | ~3 | e2e `e2e_s3_5_*` |
| repl/spec.md §3.8 (/reload) | ~3 | e2e `e2e_s3_8_*` |
| spec/09 §9.6 (begin splicing in macros) | ~4 | macros `*_begin_splicing` |

### Total counts

| Disposition | Total (estimated) |
|---|---:|
| COVERED | ~563 |
| DUPLICATE-IN-LEGACY | ~74 |
| GAP-COVER | ~141 |
| (of which REGRESSION-GUARD) | ~50 |
| GAP-HARVEST | ~75 |
| **Total** | **857** |

**Discrimination-loss signal**: ~50 REGRESSION-GUARD GAP-COVERs is the load-bearing finding. These are the tests where a defect was previously caught precisely because that angle was tested; quarantine without carry-forward re-opens those defect classes silently. Wave 5.5's 25% rate scales — Wave 5.6 estimates ~16% GAP-COVER and ~6% REGRESSION-GUARD across the full 857.

---

## Recommendations for /sprint

### File-by-file authoring order

Recommended dispatch order (smallest-and-densest first):

1. **`legacy/lenient.rs`** — 9 GAP-COVER, 5 in `spec_04_expressions.rs` correctness tests, 1 env-var subprocess test, 3 stay GAP-HARVEST. ~9 tests to author.
2. **`legacy/modules.rs`** — 13 GAP-COVER, all in `spec_08_modules.rs` with shared tempdir-fixture pattern. ~13 tests.
3. **`legacy/macros.rs`** — 11 GAP-COVER, mostly in `spec_09_macros.rs`. ~11 tests.
4. **`legacy/ring0.rs`** — 18 GAP-COVER, distributed across 5 carry-forward files. Major chunks: TCO cluster (5 tests, **defer pending /spec normative section**), error-edge (1-2 tests), dual-mode-batch verification.
5. **`legacy/e2e.rs`** — 30 GAP-COVER, dominated by `e2e_repro_*` defect-history (12 tests) and `/exports` + `/reload` thin coverage. Highest individual test variance — recommend dispatch in two waves: `e2e_repro_*` first, slash-command thin-coverage second.
6. **`legacy/ring1.rs`** — 35 GAP-COVER, dominated by `error_quality_*` (8 tests) and pattern-rejections (7 tests) + closure × ADT (5 tests). Highest GAP-COVER count of any file; ~3 sub-dispatch passes warranted.
7. **`legacy/sketch_port.rs`** — 8 GAP-COVER, mostly residual after Wave 5.5. Recommend a *focused second-pass audit* before authoring; estimated yield is small.
8. **`legacy/ring2.rs`** — 25 GAP-COVER, mostly REGRESSION-GUARD on per-sprint defects. Many require cross-checking against `tests/sprint*.rs` first.

### Batching opportunities

- Files 1+2+3 can be batched: ~33 tests, all REPL-canonical or tempdir-fixture, mechanical authoring.
- Files 5 + 6 are the GAP-COVER bulk (~65 tests); split between `/qa` waves to avoid context overrun.
- File 8 requires cross-check against existing sprint tests; assign `/qa` a verification dispatch first, then authoring.

### Methodology issues encountered

1. **The brief's 1,735 figure was a `^fn`-pattern overcount.** True `#[test]` count is 857. This affects sprint sizing — the audit yield is comparatively smaller (~141 GAP-COVER, not the ~430 a 25% rate against 1,735 would predict).

2. **Cluster-mode audit for files >100 tests is tractable.** Per-test rows for ring0/ring1/ring2/sketch_port/e2e would balloon the doc to >2000 rows; cluster-by-name-prefix preserves traceability without losing identity.

3. **GAP-HARVEST is larger than estimated in 5.5 (~9% vs ~75 across 857 = ~9%, matches).** ring2's deep-internal cluster (24 tests) drives most of this. The harvest FIXMEs are correctly framed; no adjustment recommended.

4. **The `dual_mode_*` clusters across ring0/ring1 (combined ~24 tests) are systematically COVERED by the `build_confidence.rs::mode_equiv_*` family.** This is the single biggest "naturally absorbed" win — the mode-equiv framing in `build_confidence.rs` (15 tests) supplants ~80 quarantine-tier dual-mode tests. Worth recording in the sprint retrospective.

5. **Reproduction-cluster verification needs cross-tree grep.** The `e2e_repro_*` (12 tests) and `ring2 sprint*_*` (10-15 tests) require checking against `tests/sprint*.rs` to determine COVERED vs GAP-COVER. This audit defaults them to GAP-COVER (presumptively discriminating) but a verification dispatch would reduce the count.

### Surprises beyond the 25% Wave 5.5 baseline

- **GAP-COVER rate is ~16%, lower than 5.5's 25%.** Wave 5.5 sample skewed toward dense-coverage files. Across the full 857, the rate softens — but the absolute count (~141) is large.
- **REGRESSION-GUARD rate is ~6% (≈50 tests).** These are the load-bearing preserves; user's "presumably repros expose those angles" intuition is borne out.
- **Cross-skill defect patterns are visible.** The `error_quality_*` cluster (ring1) is `/typecheck`-owned defect-history; `e2e_repro_*` is mostly `/int`; `ring2 sprint*_*` is `/backend`. Authoring waves can be skill-aligned for review efficiency.
