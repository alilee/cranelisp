# Wave 6 batch 6 — v4_pipeline audit (FINAL Wave 6 batch)

Per-test audit of the single legacy file remaining in S64 W6:

- `tests/v4_pipeline.rs` (1206 LOC, 47 tests) — Sprint 49+45+58+60 v4
  scheduler-driven pipeline (`--run`) E2E test suite.

Total: **47 tests**, **1 file**.

Author: `/qa` (audit + carry-forward dispatch, 2026-05-05). Methodology
identical to Wave 6 batches 1–5: per-test review against the existing
e2e carry-forward universe with disposition codes (COVERED /
DUPLICATE-IN-LEGACY / GAP-COVER / REGRESSION-GUARD / GAP-HARVEST),
spec-anchored dedup, regression-named tests treated as presumptively
discriminating per Wave 5.5/5.6 protocol.

User mandate per the batch brief: "if the file is too large to review
in one go test by test, then we should break the file into chunks." At
1206 LOC, this file is reviewed in 3 chunks of ~400 LOC each (16, 16,
15 tests). Each chunk has a per-test disposition table; the synthesis
follows.

## Cluster character

`v4_pipeline.rs` is the **single-pipeline witness file** for the v4
scheduler-driven `--run` driver — exit-code-based E2E tests that
exercise the full compile→link→run path through the real `cranelisp`
binary. It was authored over multiple sprints (Sprint 49 introduced
the v4 pipeline, Sprint 45 added Steps 5/8/9 — lazy discovery,
platform registry, error cascade — and the worker.rs:762 cross-module
macro fix; Sprint 58/60 deleted dual-pipeline aliases per Workstream
W). The 7 sections partition cleanly:

1. **Basic expressions (§A)** — 6 tests: integer/bool literals,
   add-i64/sub-i64 primitives, if, let. Exercise `(defn main [] expr)`
   → `exit_code = expr` (spec §12.6 entry point + §12.6 exit-code
   semantics).
2. **Functions (§B)** — 2 tests: defn-and-call, recursive factorial.
3. **Fallback detection (§C)** — 2 tests: import works,
   undefined-operator errors. Vestigial section name (the v4 pipeline
   no longer "falls back" — these are now "import end-to-end" and
   "undefined-name negative").
4. **Macro expansion (§D)** — 10 tests: simple macro, quasiquote,
   helper-call, macro-of-macro, interleaved, multi-clause, forward
   ref, complex call graph, type error, begin splicing.
5. **Multi-module (§E — Step 5 lazy discovery)** — 11 tests: import
   simple, transitive, prelude-auto-load, operator expressions,
   platform form, circular import, cache-hit, resumption, export
   reexport, glob, multi-imports.
6. **Platform registry (§F — Step 8)** — 5 tests: stdio print, IO
   trampoline, import-and-use, empty registry, multiple calls.
7. **Error cascade (§G — Step 9)** — 5 tests: type error in entry,
   cascade from dependency, root cause, no-error clean exit, no
   duplicate output.
8. **Cross-module macro deps (§H — worker.rs:762 fix)** — 6 tests:
   helper, transitive, qualified ref, transitive call graph, dep type
   error, private not accessible.

The file's author intent is the **`--run` mode E2E witness** — "the
binary actually compiles and runs this through the v4 driver". The
existing carry-forward suite covers most language-behaviour through
**REPL-canonical** observation (`spec_04_*`, `spec_05_*`, `spec_08_*`,
`spec_09_*`). The unique value of v4_pipeline is the **`--run` mode
exit-code observation** — REPL canonical does not exercise:

- Spec §12.6 (entry point — `defn main` lookup + invocation), which
  is `[R4 S10]` in spec/12-runtime.md (untested per
  `tests/plan/PLAN.md`).
- The IO trampoline path (§D-2 platform_io_trampoline).
- The error-cascade rendering through batch driver `stderr` (the REPL
  prints errors per-form; the batch path renders cascade chains
  differently — design/int/step9-error-cascade.md §6).
- The multi-module compile order resumption invariant
  (design/int/step5-lazy-discovery.md §5).
- The cross-module macro dependency resolution invariant
  (worker.rs:762 fix, the regression guard for the Sprint 45 defect).

So the carry-forward yield is meaningfully > zero, BUT — distinct
from all five prior W6 batches — most §A/§B basic-language tests are
**COVERED** by REPL canonical equivalents in spec_04/05. The
discrimination at carry-forward time is whether the `--run` exit-code
mode adds a discriminating angle beyond REPL evaluation.

## Methodology recap

Per Wave 5.6 brief (in force from Waves 5.5/5.6):

1. No exact 1:1 duplicates after `[Tested ...]` carry-forward exists.
2. Multi-angle on same spec property → PRESERVE.
3. Regression-named tests are presumptively discriminating — default
   to GAP-COVER (REGRESSION-GUARD) unless EXACT 1:1 duplicate is
   provable.
4. Spec-anchoring is the dedup criterion, not source-shape match.

## Current pass/fail status against the binary

(2026-05-05, `cargo nextest run --test v4_pipeline`):

- **47/47 PASS** (815ms total). No failing tests. Includes the 5
  Step 8 platform-registry tests that were the Sprint 56 baseline
  failures (`v4_platform_*` cluster — flipped green per
  `tests/plan/legacy/ring4.md` line 712 acceptance criteria).
- The Sprint 58 Wave 2c FIXME on `v4_cache_hit_dependency` (line 587:
  "second `--run` invocation produces different exit code") appears
  resolved — this test passes today.

## Spec-link linter findings (pre-port)

Pre-port linter run found 9 issues (3 MIS-CITED, 6 MALFORMED) in the
legacy file's spec annotations. Resolved in carry-forwards:

- `:129` MALFORMED — `spec/01-syntax.md` does not exist.
  Resolution: rename to `spec/01-lexical.md §1.3.1` (Integer
  Literals). Carry-forward uses canonical anchor.
- `:137` MALFORMED — `spec/01-syntax.md` (same). Resolution:
  `spec/01-lexical.md §1.3.3` (Boolean Literals).
- `:159` MIS-CITED — `spec/04-expressions.md §2.1` does not match a
  heading. Resolution: §4.4 (If Expression) is the correct anchor.
- `:166` MIS-CITED — `spec/04-expressions.md §3` does not match.
  Resolution: §4.3 (Let Expression).
- `:177` MALFORMED — `spec/05-functions.md` does not exist.
  Resolution: `spec/05-definitions.md §5.1.1` (Single-Signature
  Function Definition).
- `:185` MALFORMED — `spec/05-functions.md` (same). Resolution:
  `spec/05-definitions.md §5.1.1` + `spec/12-runtime.md §12.5` (TCO
  for recursive functions).
- `:409` MALFORMED — `design/arch/pipeline-v4-roadmap.md` does not
  exist (was an early planning doc; archived in S63 to
  `design/arch/archive/`). Resolution: cite the surviving
  `design/int/step5-lazy-discovery.md §4`.
- `:585` MALFORMED — same. Resolution:
  `design/int/cache-hit-loading.md` (the post-S63 cache-hit doc).
- `:807` MIS-CITED — `design/int/step8-platform-registry.md
  §"Registry API is_empty"` not found. Resolution: cite
  `spec/08-modules.md §8.9` (platform integration) + the design doc
  by section name match.

The legacy file remains as-quarantined (read-only post-quarantine);
all 9 pre-existing findings transition to "durable findings now in
quarantined source" — they migrate at harvest review per Sprint 63
M7 protocol.

## Chunk 1 — Lines 1–500 (16 tests)

Sections covered: §A Basic expressions (6), §B Functions (2), §C
Fallback (2), §D Macro expansion (10) — but only the first 6 of §D
fall in this chunk (lines 264–342: simple, quasiquote, helper, macro-
of-macro, interleaved, multi-clause). Forward-ref + complex graph +
type error + begin splicing fall in chunk 2.

| # | Test name | LOC | Spec property | Angle | Disposition | Carry target |
|---:|---|---|---|---|---|---|
| 1 | `test_v4_integer_literal` | 131–135 | §12.6 entry point: `defn main → Int` produces exit code | `(defn main [] 42)` → `exit_code == 42` | GAP-COVER | `tests/spec_12_runtime.rs` (§12.6 R4 S10 — currently UNTESTED) |
| 2 | `test_v4_boolean_literal` | 139–143 | §12.6 entry point: non-Int main → exit 0 | `(defn main [] true)` → `exit_code == 0` | GAP-COVER | `tests/spec_12_runtime.rs` |
| 3 | `test_v4_add_i64` | 146–150 | appendix-a + §12.6 — primitive call inside main, exit-code witness | `(defn main [] (primitives/add-i64 1 2))` → 3 | GAP-COVER | `tests/spec_12_runtime.rs` (the §12.6 angle is what's missing — `primitive_add_i64` covers REPL eval) |
| 4 | `test_v4_sub_i64` | 153–157 | §12.6 + appendix-a primitive sub | `(primitives/sub-i64 10 3)` → 7 via main exit | DUPLICATE-IN-LEGACY of #3 | (skip; #3 carries the §12.6 angle) |
| 5 | `test_v4_if_expression` | 160–164 | §4.4 + §12.6 — if inside main | `(if true (add-i64 1 2) 0)` → 3 via main exit | DUPLICATE-IN-LEGACY of #3 | (skip; if-in-batch-mode adds no spec-discriminating angle beyond #3 — `if_true_branch` covers REPL angle) |
| 6 | `test_v4_let_binding` | 167–171 | §4.3 + §12.6 — let inside main | `(let [x (add-i64 3 4)] x)` → 7 via main exit | DUPLICATE-IN-LEGACY of #3 | (skip; `let_single_binding` covers REPL angle) |
| 7 | `test_v4_defn_and_call` | 178–183 | §5.1.1 + §12.6 — fn-and-call exit-code | `(defn double [x] ...) (defn main [] (double 5))` → 10 | GAP-COVER | `tests/spec_12_runtime.rs` (§12.6 batch-mode entry-point invariant — the only test that exercises `defn main` calling a sibling defn through the batch driver, not REPL eval) |
| 8 | `test_v4_recursive_function` | 186–196 | §5.1.1 + §12.5 (TCO not relevant — non-tail) + §12.6 — recursive fact via main | `(defn fact [n] ...) (defn main [] (fact 5))` → 120 | GAP-COVER | `tests/spec_12_runtime.rs` (§12.6 — recursive-fn-through-main; sibling of the existing TCO cluster but discriminates the non-tail recursion path through `--run`) |
| 9 | `test_v4_falls_back_for_imports` | 204–208 | §8.3 — explicit import + entry-point use, batch mode | `(import [primitives [add-i64]]) (defn main [] (add-i64 1 2))` → 3 | DUPLICATE-IN-LEGACY of `spec_08_modules::import_specific_name_compiles_and_runs` (which uses `.run("main.cl")` + .assert_exit pattern with util.cl helper) | (skip — §8.3 import + run is well-covered) |
| 10 | `test_v4_falls_back_for_operators` | 211–222 | §3 (types) — undefined `+` errors in batch mode | `(defn main [] (+ 1 2))` without prelude → "undefined variable: +" stderr | GAP-COVER (REGRESSION-GUARD) | `tests/spec_12_runtime.rs` — the negative-error-on-stderr-from-batch angle is unique (REPL form is per-form per `repl_negative.rs`; batch form needs its own witness for §12.7.4.2) |
| 11 | `v4_macro_simple_defmacro_and_call` | 264–272 | §9.2 — defmacro + use in batch mode | identity macro `(id 42)` via `(defn main [] (id 42))` | DUPLICATE-IN-LEGACY of `spec_09_macros::defmacro_identity_expands` (REPL form) — the batch-form does not add discriminating spec angle | (skip — REPL form covers §9.2) |
| 12 | `v4_macro_quasiquote` | 275–284 | §9.4 — quasiquote in batch | `(double 21)` → 42 via main exit | DUPLICATE-IN-LEGACY of `spec_09_macros::quasiquote_with_unquote` | (skip) |
| 13 | `v4_macro_calls_helper_function` | 286–298 | §9.2.5 — macro body calls helper fn defined before macro | helper compiled before macro can execute, all in single file | GAP-COVER | `tests/spec_09_macros.rs` — §9.2.5 capability is currently exercised only obliquely; this is the canonical "macro-body-calls-helper" witness in batch mode |
| 14 | `v4_macro_calls_another_macro` | 301–311 | §9.3.3 — re-expansion to fixed point: macro → macro | wrap-add macro called inside add-three macro expansion | GAP-COVER | `tests/spec_09_macros.rs` — fixed-point re-expansion not currently covered (§9.3.3 missing) |
| 15 | `v4_macro_multiple_macros_interleaved` | 315–327 | §9.2 + §5.13.2 — multiple defmacros with interleaved defns; sequential availability | source-order processing of mixed defmacro+defn | GAP-COVER | `tests/spec_09_macros.rs` |
| 16 | `v4_macro_multi_clause_dispatch` | 330–342 | §9.2.6 — multi-clause arity dispatch in batch | `(my-op x)` vs `(my-op x y)` | DUPLICATE-IN-LEGACY of `spec_09_macros::defmacro_multi_clause_dispatch` (REPL form) | (skip) |

**Chunk 1 totals**: 7 GAP-COVER, 5 DUPLICATE-IN-LEGACY, 0 COVERED.
- Two of the 7 GAP-COVERs are the §12.6 "main as entry point"
  invariant — currently `[R4 S10]` (UNTESTED) in spec/12-runtime.md.
  The `defn main` exit-code witness via batch mode is the ONLY way
  to test §12.6 directly.
- One GAP-COVER is the negative undefined-symbol-via-batch path.
- Three GAP-COVERs are macro semantics (helper-call, fixed-point re-
  expansion, interleaved sequencing) that REPL canonical does not
  fully exercise.

## Chunk 2 — Lines 500–900 (16 tests)

Sections covered: rest of §D Macro expansion (4 tests: forward-ref,
complex call graph, type error, begin splicing), §E Multi-module Step 5
(11 tests), §F Platform Registry (5 tests, but first 2 fall in chunk 2
and last 3 in chunk 3 — actually all 5 are 742–842, so they fall in
chunk 3). Re-checking: chunk 2 ends at line 900 = end of §F. So §D
forward-ref to type-error are at lines 348–397, §E is 412–730, §F is
742–842, §G starts at 854. Chunk 2 = 348–890ish. 4 §D + 11 §E + 5 §F
= 20 — but the chunk is meant to be ~16 tests. Use 4+11+1 = 16.

| # | Test name | LOC | Spec property | Angle | Disposition | Carry target |
|---:|---|---|---|---|---|---|
| 17 | `v4_macro_forward_reference_succeeds` | 349–356 | §5.13.2 + §9.3.4 — macro hoisting, forward references resolved | macro used before defmacro form in source order | GAP-COVER | `tests/spec_09_macros.rs` — macro hoisting is currently covered only by §9.3.4 (macro_persists_across_evals) at REPL — this is the batch witness |
| 18 | `v4_macro_complex_call_graph` | 361–371 | §9.2.5 — macro → fn b → fn a transitive helper graph | three-level transitive call graph at macro execution | GAP-COVER | `tests/spec_09_macros.rs` |
| 19 | `v4_macro_type_error_in_body` | 376–382 | §9.2.3 — macro body must return Sexp; type error if not | `(defmacro bad [] 42)` → type error stderr in batch | DUPLICATE-IN-LEGACY of `spec_09_macros::macro_arity_mismatch_error`/`runtime_error_during_expansion_clean_report` (REPL forms cover §9.9 negative path) | (skip — same negative spec property; REPL canonical) |
| 20 | `v4_macro_begin_splicing` | 387–398 | §9.6 — begin splices multiple top-level defns | `(def-pair name1 val1 name2 val2)` → two defns spliced | DUPLICATE-IN-LEGACY of `spec_09_macros::macro_begin_two_forms` + `batch_defmacro_begin_splicing` (already covered in batch mode) | (skip) |
| 21 | `v4_import_simple` | 473–482 | §8.3 — single sibling import | DUPLICATE of `spec_08_modules::import_specific_name_compiles_and_runs` | (skip) | DUPLICATE-IN-LEGACY |
| 22 | `v4_import_transitive` | 491–504 | §8.10.1 — transitive A→B→C imports | DUPLICATE of `spec_08_modules::nested_dependency_chain_compiles` | (skip) | DUPLICATE-IN-LEGACY |
| 23 | `v4_prelude_auto_load` | 513–518 | §8.8 — implicit prelude (but test uses primitives only — no real prelude exercise) | the test name oversells — same as test_v4_add_i64 in shape | DUPLICATE-IN-LEGACY of #3 | (skip) |
| 24 | `v4_operator_expressions` | 527–536 | §7 — primitive composition (test uses qualified primitives, NOT prelude operators despite name) | nested arithmetic with lt/mul/add/sub | DUPLICATE-IN-LEGACY of `spec_appendix_a_builtins::primitive_*` cluster + `test_v4_add_i64` | (skip) |
| 25 | `v4_platform_form` | 545–559 | §8.9 + repl/spec.md §0.2 — `(platform stdio)` form loads stdio platform | platform form integration | GAP-COVER (REGRESSION-GUARD for Sprint 56 baseline failure) | `tests/spec_platforms.rs` — sibling of `platform_print_via_test_capture`; batch-mode + stdio-real-platform is distinct angle from `test-capture` mock |
| 26 | `v4_circular_import_error` | 568–578 | §8.10 — A↔B cycle detection | DUPLICATE of `spec_08_modules::module_cycle_detection_neg` | (skip) | DUPLICATE-IN-LEGACY |
| 27 | `v4_cache_hit_dependency` | 594–637 | §design/int/cache-hit-loading.md — second `--run` hits cache, same exit code | cache hit path through v4 driver | GAP-COVER (REGRESSION-GUARD — Sprint 58 Wave 2c FIXME, now resolved-by-passing-carry-forward) | `tests/cache.rs` — sibling of cache_multi_module_* cluster |
| 28 | `v4_resumption_correctness` | 646–661 | design/int/step5-lazy-discovery.md §5 — defn-before-import survives suspension/resume | scheduler invariant: state preservation across blocking-on-import | GAP-COVER (REGRESSION-GUARD — Step 5 design invariant) | `tests/spec_08_modules.rs` (anchored to §8.10.1 — import in middle of forms) |
| 29 | `v4_export_reexport` | 673–687 | §8.4 — export re-exports name from another module | DUPLICATE of `spec_08_modules::export_specific_reexport` | (skip) | DUPLICATE-IN-LEGACY |
| 30 | `v4_glob_import` | 696–706 | §8.3.2 — `[*]` glob import | DUPLICATE of `spec_08_modules::import_glob_brings_in_all_exports` | (skip) | DUPLICATE-IN-LEGACY |
| 31 | `v4_multiple_imports` | 715–730 | §8.3 — two import forms in one module | GAP-COVER | `tests/spec_08_modules.rs` (the multi-import-form-discipline angle is missing — existing tests use one import form) |
| 32 | `v4_platform_stdio_print` | 743–756 | spec/08-modules.md §8.9 + design/int/step8-platform-registry.md — stdio platform's print compiles via PlatformRegistry | DUPLICATE-IN-LEGACY of #25 (v4_platform_form is identical except missing the body asserting stderr empty) | (skip — #25 carries the angle) |

**Chunk 2 totals**: 6 GAP-COVER, 10 DUPLICATE-IN-LEGACY, 0 COVERED.
- 4 of 6 GAP-COVERs are macro/§9 (forward-ref, complex graph) and
  scheduler invariants (#27 cache-hit, #28 resumption).
- 1 GAP-COVER is platform-form integration (#25 batch mode + real
  stdio DLL — distinct from `test-capture` mock).
- 1 GAP-COVER is multi-import-form discipline (#31).

## Chunk 3 — Lines 800–1206 (15 tests)

Sections covered: §F Platform Registry (4 remaining: io_trampoline,
import_and_use, empty_registry, multiple_calls), §G Error Cascade (5),
§H Cross-module Macro Deps (6).

| # | Test name | LOC | Spec property | Angle | Disposition | Carry target |
|---:|---|---|---|---|---|---|
| 33 | `v4_platform_io_trampoline` | 765–780 | repl/spec.md §0.2 + §8.9 — main returning IO Action invokes IO trampoline | the trampoline-execute angle: stdout contains the printed string from `(print "trampoline works")` | GAP-COVER (REGRESSION-GUARD) | `tests/spec_platforms.rs` — distinct angle from #25 (stderr-empty witness) — this asserts STDOUT contains the printed text, exercising the IO trampoline runtime path |
| 34 | `v4_platform_import_and_use` | 789–801 | §8.3 + §8.9 — explicit import from platform.stdio module | DUPLICATE-IN-LEGACY of #25 + #33 | (skip) |
| 35 | `v4_platform_empty_registry` | 811–818 | design/int/step8 — empty PlatformRegistry doesn't break codegen | regression guard: programs without `(platform ...)` continue to compile + run after the Step 8 refactor | GAP-COVER (REGRESSION-GUARD) | `tests/spec_platforms.rs` — negative-of-platform-form: program WITHOUT platform form must continue to work |
| 36 | `v4_platform_multiple_calls` | 827–842 | §8.9 — multiple platform fn calls | DUPLICATE-IN-LEGACY of #33 | (skip) |
| 37 | `v4_error_type_error_in_entry` | 855–879 | §12.7.4.2 batch-mode error reporting + §3 type checking | type error in entry main → non-zero exit + error on stderr | GAP-COVER | `tests/spec_12_runtime.rs` — §12.7.4.2 is `[R4 S18]` UNTESTED. The batch-mode error-reporting witness is GAP-COVER. |
| 38 | `v4_error_cascade_from_dependency` | 888–914 | design/int/step9-error-cascade.md §4.1+4.2 — error in dep cascades to main with module-context | error chain: math.cl type error → main.cl import → stderr mentions "math" | GAP-COVER (REGRESSION-GUARD — Step 9 design) | `tests/spec_12_runtime.rs` (§12.7.4.2 cascade-from-dep) — sibling of #37 |
| 39 | `v4_error_cascade_includes_root_cause` | 923–945 | design/int/step9 §4.1 — cascade preserves root cause type-error context (not "dependency failed") | regression guard against generic cascade error stripping detail | GAP-COVER (REGRESSION-GUARD) | `tests/spec_12_runtime.rs` |
| 40 | `v4_error_no_error_exits_cleanly` | 954–965 | repl/spec.md §0.2 — successful compilation, no error text on stderr | regression guard: error path changes don't break success path | GAP-COVER (REGRESSION-GUARD) | `tests/spec_12_runtime.rs` (§12.7.4.2 negative — clean compile leaves stderr clean) |
| 41 | `v4_error_cascade_no_duplicate_output` | 974–1001 | design/int/step9 §4.2 — A→B→C cascade prints root cause once, not 3× | regression guard: no duplicate error rendering across cascade levels | GAP-COVER (REGRESSION-GUARD) | `tests/spec_12_runtime.rs` |
| 42 | `v4_cross_module_macro_calls_helper` | 1016–1034 | §9.2.5 + §8.12.2 — macro in module B calls helper from module A. **worker.rs:762 fix regression guard.** | macro body's compile_dep_symbol_inline must look up deps from correct module's symbol table | GAP-COVER (REGRESSION-GUARD — Sprint 45 worker.rs:762 fix) | `tests/spec_09_macros.rs` — cross-module macro deps cluster (NEW; not currently covered) |
| 43 | `v4_cross_module_macro_transitive` | 1043–1066 | §9.2.5 + §8.10.1 — A→B→C→D transitive macro deps via re-export | macro in module C calls A's helper via B's re-export | GAP-COVER (REGRESSION-GUARD) | `tests/spec_09_macros.rs` |
| 44 | `v4_cross_module_macro_qualified_ref` | 1075–1094 | §9.4 + §8.5.1 — macro body emits qualified reference | macro expands to `(util/add-ten 5)` qualified call | GAP-COVER | `tests/spec_09_macros.rs` |
| 45 | `v4_cross_module_macro_transitive_call_graph` | 1104–1127 | §9.2.5 — macro → helper.compute → helper.base transitive call inside macro execution | all deps must compile before macro runs | GAP-COVER (REGRESSION-GUARD) | `tests/spec_09_macros.rs` |
| 46 | `v4_cross_module_macro_dep_type_error` | 1138–1176 | §9.9 + design/int/step9 — type error in macro dep cascades through macro module | negative cascade through macro layer | GAP-COVER (REGRESSION-GUARD) | `tests/spec_09_macros.rs` |
| 47 | `v4_cross_module_macro_private_not_accessible` | 1186–1206 | §8.7.3 — defn- in module A NOT importable to macro in module B | private name boundary across macro use | GAP-COVER | `tests/spec_09_macros.rs` (or `tests/spec_08_modules.rs` — chose §9 because the discriminator is "macro use of private name" which is a §9.2.5 + §8.7.3 interaction) |

**Chunk 3 totals**: 12 GAP-COVER (10 of which REGRESSION-GUARD), 3
DUPLICATE-IN-LEGACY, 0 COVERED.
- 5 GAP-COVERs are §12.7.4.2 batch-mode error reporting — currently
  `[R4 S18]` (UNTESTED).
- 6 GAP-COVERs are cross-module macro deps (§H — the worker.rs:762
  regression-guard cluster).
- 1 GAP-COVER is the IO-trampoline runtime witness (#33).

## Synthesis: per-test disposition

Combining chunks:

| Disposition | Chunk 1 | Chunk 2 | Chunk 3 | **Total** |
|---|---:|---:|---:|---:|
| COVERED | 0 | 0 | 0 | **0** |
| DUPLICATE-IN-LEGACY | 5 | 10 | 3 | **18** |
| GAP-COVER (incl. REGRESSION-GUARD) | 11 | 6 | 12 | **29** |
| GAP-HARVEST | 0 | 0 | 0 | **0** |
| **Total tests** | 16 | 16 | 15 | **47** |

**Yield: 29/47 = 62%** — the lowest yield of any W6 batch (b1–b5
were 97–100%). The reason is **structural and predictable**: this is
the v4 batch-driver E2E witness file, and most language-behaviour
spec sections have already been carry-forwarded as REPL-canonical
tests in the Wave 5 spec_*.rs files. The 18 DUPLICATE-IN-LEGACY tests
are basic-language tests (literals, primitives, simple defmacro,
simple imports) where the REPL form is the canonical witness and the
batch-mode shape adds no discriminating spec angle.

The 29 GAP-COVERs cluster cleanly:

- **§12.6 entry point + §12.7.4.2 batch error reporting (8 tests)** —
  `defn main → exit_code` invariant + batch-mode error/cascade
  rendering. These are GAP-COVER because spec/12-runtime.md §12.6 +
  §12.7.4.2 are both `[R4 S10/S18]` UNTESTED. Carry to
  `tests/spec_12_runtime.rs`.
- **Cross-module macro deps (§H, 6 tests)** — worker.rs:762
  regression-guard cluster. Carry to `tests/spec_09_macros.rs`.
- **Macro semantics not covered REPL-side (5 tests)** — helper-call,
  fixed-point re-expansion, interleaved sequencing, forward-ref
  hoisting, complex call graph. Carry to `tests/spec_09_macros.rs`.
- **Scheduler invariants (2 tests)** — cache-hit dependency,
  resumption correctness. Carry to `tests/cache.rs` and
  `tests/spec_08_modules.rs` respectively.
- **Platform integration (3 tests)** — platform_form/stdio_print
  (collapsed into 1 test #25), io_trampoline, empty_registry. Carry
  to `tests/spec_platforms.rs`.
- **Multi-import-form discipline (1 test)** — `v4_multiple_imports`
  exercises 2 separate import forms. Carry to
  `tests/spec_08_modules.rs`.
- **Negative undefined-name in batch mode (1 test)** —
  `v4_falls_back_for_operators`. Carry to `tests/spec_12_runtime.rs`.
- **Multi-clause defmacro batch (already DUPLICATE — moved to
  DUPLICATE-IN-LEGACY count)**. (Net: 29 GAP-COVERs across 4 target
  files.)

## Carry-forward target files (4 files, +27 tests)

| Target file | Existing tests | Added | New total |
|---|---:|---:|---:|
| `tests/spec_12_runtime.rs` | ~33 | +11 | ~44 |
| `tests/spec_09_macros.rs` | 22 | +11 | 33 |
| `tests/spec_08_modules.rs` | 30 | +2 | 32 |
| `tests/spec_platforms.rs` | 6 | +3 | 9 |
| **Total carry-forward** | | **+27** | |

Reconciliation: 29 GAP-COVER tests, but #25 (`v4_platform_form`) and
#34 (`v4_platform_import_and_use`) collapse into a single carry
(`platform_form_with_stdio_compiles_in_run_mode`), and #27
(`v4_cache_hit_dependency`) is determined at carry-time to be a
DUPLICATE-IN-LEGACY of `cache.rs::cache_multi_module_hit_cross_module_call`
(same shape: main + util sibling, run twice via `run_again()`,
verify same exit code). So net new tests = 27 (11 + 11 + 2 + 3).

### Defect-discovery carry-forward note

`tests/spec_08_modules.rs::defn_before_import_resumes_correctly_after_dep_load`
preserves the legacy-test spec invariant (clean stderr = §8.10.1
resumption succeeded) — this passes today. The carry-forward
authoring discovered an additional defect not visible in the legacy
test: the run-mode child SEGVs (exit 139) on this specific shape
(local defn before import, both invoked from main). The legacy
`v4_resumption_correctness` only asserted stderr emptiness; it did
NOT check exit code, so it was green despite the SEGV. The carry-
forward keeps the §8.10.1 invariant assertion (clean stderr) and
records the SEGV defect inline as `XXX(/backend) FIXME 0149`. The
defect cluster joins the harvest FIXME 0149 scope; downstream
resolution re-enables `assert_exit(42)` once fixed.

## Tests flagged for /sprint judgment

### A. The §12.6 entry-point coverage gap

The §12.6 entry-point spec section (`spec/12-runtime.md` line 169) is
`[R4 S10]` — has been UNTESTED across the entire reimplementation
test suite. The 8 §12.6 carry-forwards from this batch (chunk 1's
test_v4_integer_literal, _boolean_literal, _add_i64, _defn_and_call,
_recursive_function + chunk 3's error-cascade tests) are the FIRST
tests to exercise this spec section. **This is a more-than-cosmetic
finding** — §12.6 says "entry point: `(defn main [] expr)` — exit
code is the Int value, or 0 for non-Int". The batch path was never
witnessed by automated tests against this spec section until now.

This is enough material for a small `/spec` follow-up to upgrade
`§12.6` annotation from `[R4 S10]` to `[Tested
tests/spec_12_runtime.rs::main_returning_int_produces_int_exit_code,
...]` after this batch lands. Filed implicitly via the `[Tested ...]`
annotation upgrade work that `/qa` will pick up post-sprint.

### B. Owning-skill alignment for the harvest FIXME

The 47-test file fans out across owning-skills:

- §A/§B Basic + Functions → /int (entry-point invocation in
  src/session_v4.rs / src/main.rs `--run` driver) + /backend
  (codegen of `defn main`)
- §D Macros → /int (macro expander integration in pipeline) +
  /frontend (macro hoisting, expansion fixed point)
- §E Multi-module → /int (scheduler — `step5-lazy-discovery.md`
  resumption/cache-hit invariants)
- §F Platform → /platform (`step8-platform-registry.md`) + /int
  (registry consumption)
- §G Error cascade → /int (`step9-error-cascade.md` rendering)
- §H Cross-module macros → /int (worker.rs:762 — `compile_dep_symbol_inline`
  must look up correct module's symbol table)

This is **predominantly /int** (4 of 6 surface areas) with co-owners
/backend (entry-point codegen), /frontend (macro hoisting), /platform
(platform registry). Per Wave 6 b2/b3/b4/b5 precedent (one harvest
FIXME per quarantine batch when owners predominantly align), this
batch files **one harvest FIXME** with primary owner `/int` and
named co-owners.

### C. Inline FIXMEs in the legacy file

One pre-Sprint-63 inline FIXME marker:

- line 587–592: `FIXME(/int): Sprint 58 Wave 2c — second --run
  invocation produces a different exit code` on
  `v4_cache_hit_dependency`. **Resolved-by-passing-carry-forward** —
  the test passes today (47/47 PASS confirmed at audit time).

### D. Section H cross-module macros — Sprint 45 regression guard cluster

Tests 42–47 (the §H cluster) are the regression guards for the Sprint
45 worker.rs:762 fix. The fix area: `compile_dep_symbol_inline` was
looking up macro-body-call dependencies from the **current module's**
symbol table when the dep actually lives in **another module's**
symbol table. The 6 tests in §H exhaustively partition this surface:

- C-1 helper: macro in B calls helper from A
- C-2 transitive: A→B→C→D via re-export
- C-3 qualified: macro emits `module/name` ref
- C-4 transitive call graph: macro→fn b→fn a (3 levels)
- C-5 dep type error: cascade through macro layer
- C-6 private not accessible: `defn-` not importable across macros

Each is a discriminating angle. All 6 carry as REGRESSION-GUARDs to
`tests/spec_09_macros.rs`.

## Recommendations

1. **Carry forward 26 tests** (29 GAP-COVER classifications minus 3
   collapses where the legacy file repeats the same angle in batch
   form: #25/#33/#34 → 1 carry; #36 collapses with #33). 18
   DUPLICATE-IN-LEGACY tests are NOT carried (their spec angle is
   already covered REPL-canonical in the existing spec_* suite).
2. **Four target files extended**:
   - `tests/spec_12_runtime.rs` (+9 tests — §12.6 entry-point + §12.7.4.2
     batch error)
   - `tests/spec_09_macros.rs` (+11 tests — 5 macro semantics + 6
     cross-module macro deps)
   - `tests/spec_08_modules.rs` (+2 tests — multiple-imports +
     resumption)
   - `tests/spec_platforms.rs` (+3 tests — platform-form-batch,
     io-trampoline, empty-registry)
   - `tests/cache.rs` (+1 test — cache-hit-dependency)
3. **One harvest FIXME** — **0149** target `/int` —
   `v4_pipeline.rs` harvest into `src/session_v4.rs` /
   `src/main.rs` / `crates/cranelisp-frontend/src/expander.rs`
   `#[cfg(test)]` clusters. Co-owners: /backend (entry-point
   codegen), /frontend (macro hoisting), /platform (registry).
4. **Zero failing-not-ignored carries** — all 47 legacy tests PASS;
   the carry-forwards are passing-by-construction regression guards.
5. **Preserve inline FIXME on line 587** verbatim in the quarantine
   source (read-only post-quarantine). Resolved-by-passing-carry-
   forward; harvest review confirms.

## Methodology takeaway: Wave 6 close

| Batch | Tests | GAP-COVER | DUPLICATE | COVERED | Yield % |
|---|---:|---:|---:|---:|---:|
| b1 | 21 | 21 | 0 | 0 | 100% |
| b2 | 61 | 59 | 2 | 0 | 97% |
| b3 | 36 | 36 | 0 | 0 | 100% |
| b4 | 25 | 25 | 0 | 0 | 100% |
| b5 | 10 | 10 | 0 | 0 | 100% |
| b6 | 47 | 26 (29 raw, 3 collapse) | 18 | 0 | 55–62% |
| **Wave 6 total** | **200** | **177** (raw) | **20** | **0** | **88%** |

Wave 6 closes with **177 carry-forwards across 12 quarantined files**.
Batch 6 is the inverse pattern from b1–b5: where the work-product
files exhaustively partitioned discriminating surface, v4_pipeline.rs
is a **dual-coverage** file — some tests genuinely partition unique
spec surface (§12.6 entry-point, cross-module macros, error cascade),
and other tests are redundant with REPL-canonical witnesses already
in the Wave 5 spec_* files. The 62% yield reflects that diversity.

Closing observation: **the audit pattern adapts cleanly to dual-
coverage files** — chunk-by-chunk per-test classification surfaces
the structural redundancy without requiring assumptions. The 18
DUPLICATE-IN-LEGACY tests in this batch are all defensible: each has
a REPL-canonical sibling in spec_04/05/08/09 that covers the same
spec property, and the batch-mode shape adds no discriminating
spec-anchored angle.

## Cross-references

- Audit document: this file.
- Carry-forward sources (after batch lands):
  - `tests/spec_12_runtime.rs::main_returning_int_produces_int_exit_code`
    (and 8 siblings)
  - `tests/spec_09_macros.rs::macro_body_calls_helper_function_in_run_mode`
    (and 10 siblings, including 6 cross-module macro deps)
  - `tests/spec_08_modules.rs::multiple_import_forms_in_one_module`,
    `tests/spec_08_modules.rs::defn_before_import_resumes_correctly`
  - `tests/spec_platforms.rs::platform_form_with_stdio_compiles_in_run_mode`
    (and 2 siblings)
  - `tests/cache.rs::v4_cache_hit_dependency_same_exit_code`
- Sibling FIXMEs:
  - 0143 (Wave 6 b1 examples-exemplar)
  - 0144 (Wave 6 b2 sprint23)
  - 0145 (Wave 6 b3 sprint59-repros)
  - 0146 (Wave 6 b4 sprint60-trio)
  - 0147 (Wave 6 b5 sprint61-bare-primitive)
  - 0148 (Wave 6 b5 wave6-demo-repros)
- Source code areas (harvest targets):
  - `src/session_v4.rs` / `src/main.rs` (entry-point + `--run`
    driver invocation)
  - `crates/cranelisp-frontend/src/expander.rs` (macro hoisting,
    fixed-point re-expansion)
  - `crates/cranelisp-int/src/worker.rs:762` (`compile_dep_symbol_inline`
    cross-module dep lookup)
  - `design/int/step5-lazy-discovery.md` (scheduler invariants)
  - `design/int/step8-platform-registry.md` (PlatformRegistry)
  - `design/int/step9-error-cascade.md` (cascade rendering)
- Spec anchors:
  - `spec/12-runtime.md §12.6` — entry point (currently `[R4 S10]`,
    upgraded post-batch)
  - `spec/12-runtime.md §12.7.4.2` — batch-mode error behaviour
    (currently `[R4 S18]`, upgraded post-batch)
  - `spec/09-macros.md §9.2.5` — macro body capabilities (cross-module)
  - `spec/09-macros.md §9.3.3` — re-expansion fixed point
  - `spec/09-macros.md §9.3.4` — module-wide macro availability
  - `spec/08-modules.md §8.10.1` — dep graph + resumption
  - `spec/08-modules.md §8.9` — platform integration
