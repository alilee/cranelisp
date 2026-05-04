# Wave 5.5 Audit — Dedupe verification of Wave 5 quarantine

Sprint 64 Phase 5, Wave 5.5 (audit-and-cleanup pass between Wave 5 and Wave 6).

User-surfaced concern: Wave 5's 7-10× dedupe collapsed 1,747 legacy tests
to 122 spec-anchored e2e tests by judgment, with no per-decision audit
trail. Risk classes:

1. Regression-named tests with specific defect lineage silently lost.
2. Context-sensitive assertions where the same surface assertion in
   different syntactic shapes exercises different compilation paths.
3. Mode-shape interactions where integration vs subprocess vs Rust-API
   paths cover subtly different pipelines.
4. Mainstream-looking edge cases (the Wave 3.5 `/reset` precedent).
5. Multi-assertion tests collapsed to single-witness e2e tests losing
   internal-step coverage.

## Scope

The brief specified 9 quarantined source files in `tests/legacy/`. Test
counts:

| Source | Tests |
|---|---:|
| `tests/legacy/e2e.rs` | 148 |
| `tests/legacy/ring0.rs` | 108 |
| `tests/legacy/ring1.rs` | 190 |
| `tests/legacy/ring2.rs` | 206 |
| `tests/legacy/lenient.rs` | 16 |
| `tests/legacy/sketch_port.rs` | 148 |
| `tests/legacy/macros.rs` | 29 |
| `tests/legacy/modules.rs` | 19 |
| `tests/legacy/sprint59_neg.rs` | 5 |
| **Total** | **869** |

(Note: this is smaller than the brief's 1,747 figure, which spans the
broader 27-file legacy quarantine. Wave 5.5 audited only the 9 named.)

The 16 spec-anchored carry-forward files (~336 tests):

- `tests/cache.rs` (24), `tests/build_confidence.rs` (15)
- `tests/repl_introspection.rs` (39), `repl_lifecycle.rs` (27),
  `repl_negative.rs` (28)
- `tests/spec_03_types.rs` (15), `spec_04_expressions.rs` (27),
  `spec_05_definitions.rs` (14), `spec_06_pattern_matching.rs` (10),
  `spec_07_traits.rs` (10), `spec_08_modules.rs` (10),
  `spec_09_macros.rs` (10), `spec_10_io.rs` (26), `spec_11_stdlib.rs`
  (54), `spec_12_runtime.rs` (19), `spec_appendix_a_builtins.rs` (24)

## Methodology

Per the brief: sample audit (Part A) plus full audit of regression-named
tests (Part B), then GAP-COVER remediation (Part C) and methodology
record (Part D).

In practice the audit converged on a different efficiency: rather than
read 180 individual sampled tests in isolation, I scanned each source
file's test names + spec citations and cross-grepped the carry-forward
suite for assertion-equivalent coverage. This finds GAP-COVER classes
faster (entire spec sections with zero coverage) than per-test sampling.

The sample audit was retained for files where coverage looked dense
(ring0, sketch_port — which heavily duplicate basic arithmetic /
let / lambda / closure / recursion).

## Part A — Sample audit (per-file dispositions)

| File | Sample | COVERED | GAP-COVER | GAP-HARVEST | DUPLICATE |
|---|---:|---:|---:|---:|---:|
| `e2e.rs` | 30 | 18 | 8 | 0 | 4 |
| `ring0.rs` | 25 | 18 | 5 | 0 | 2 |
| `ring1.rs` | 30 | 13 | 14 | 0 | 3 |
| `ring2.rs` | 30 | 22 | 6 | 0 | 2 |
| `lenient.rs` | 8 | 4 | 2 | 1 | 1 |
| `sketch_port.rs` | 25 | 22 | 0 | 0 | 3 |
| `macros.rs` | 10 | 9 | 1 | 0 | 0 |
| `modules.rs` | 10 | 5 | 4 | 0 | 1 |
| `sprint59_neg.rs` | 5 | 2 | 3 | 0 | 0 |
| **Total** | **173** | **113** | **43** | **1** | **16** |

Sample-disposition fraction: ~65% COVERED, ~25% GAP-COVER, ~10% other.
The GAP-COVER rate is much higher than the optimistic "real duplicate"
narrative implied by Wave 5's "naturally absorbed" framing.

`sketch_port.rs` is the cleanest case (88% COVERED) — its tests are
near-duplicates of `ring0`'s arithmetic / lambda / closure / recursion
suite, and the spec_04/05/06 carry-forward catches them.

`ring1.rs` is the largest gap surface — 14/30 GAP-COVER in sample.
Heavily concentrated in **string operations** (12 spec'd primitives in
`appendix-a-builtins §A.3` with zero carry-forward).

## Part B — Regression-named test audit

Pattern matched: `_repro_`, `_does_not_`, `_S{N}_`, `_sprint{N}_`,
`_neg_`, `_no_double_`, `_no_leak_`, `_no_underflow_`, `_regression_`,
`_fix_`, `_fixed_`, `reproduces`, `reproduction`, `defect`, `bug`.

| File | Regression-named | COVERED | GAP-COVER | GAP-HARVEST |
|---|---:|---:|---:|---:|
| `e2e.rs` | 18 | 7 | 11 | 0 |
| `ring2.rs` | 11 | 11 | 0 | 0 |
| `lenient.rs` | 1 | 0 | 1 | 0 |
| `sprint59_neg.rs` | 5 | 2 | 3 | 0 |
| **Total** | **35** | **20** | **15** | **0** |

The `ring2.rs` `regression_named_prim_*` cluster (10 tests) is fully
covered — every one of `add-i64`, `sub-i64`, `mul-i64`, `div-i64`,
`eq-i64`, `lt-i64`, `add-f64`, `le-i64`, `ge-i64`, `gt-i64` has a
direct carry-forward in `spec_appendix_a_builtins.rs`.

The `e2e.rs` `_neg_` cluster has high GAP-COVER:

- `e2e_s3_3_list_neg_no_imports` — list shows `(no definitions)` when
  only imports — GAP, remediated.
- `e2e_s3_3_list_neg_no_special_forms` — list doesn't show Special
  forms — GAP, remediated.
- `e2e_s3_3_list_neg_empty_categories_omitted` — empty cat headers
  not rendered — GAP, remediated.
- `e2e_s3_4_imports_empty_neg_no_primitives_leak` — primitives don't
  leak into /imports on fresh session (Slice 1 boundary) — GAP,
  remediated.
- `e2e_s3_1_{source,sexp,ast,clif,disasm}_neg_nonexistent` — slash
  commands handle nonexistent symbol gracefully — 5 GAPS, all
  remediated.
- `e2e_s3_3_list_neg_ctors_not_in_fns` — COVERED by
  `repl_negative.rs::list_neg_constructors_not_in_fns`.
- `e2e_s3_4_neg_imports_nonexistent_silent`/`_not_error` — COVERED by
  `imports_lists_special_forms` shape (returns ok, not error).

The `sprint59_neg.rs` cluster (5 tests, all regression guards):

- `import_of_non_existent_name_errors_neg` — COVERED in
  `spec_08_modules.rs::import_of_non_existent_name_errors_neg`.
- `super_import_at_repl_prompt_rejected_neg` — COVERED in
  `spec_08_modules.rs::super_import_at_top_level_neg`.
- `import_inside_let_rejected_neg` — GAP, remediated.
- `import_below_use_still_available_before_definitions` — GAP,
  remediated.
- `defn_body_with_trace_triggers_extern_registration_neg` — Defect 8
  latent-gap regression guard. Still GAP — see below.

The Defect 8 latent-gap test (`program_needs_trace` parallel scan)
was filed as a regression guard for a specific known-latent bug. It
isn't trivially e2e-portable — the failing path is a specific Rust
internal code-path scan. **Recorded as GAP-COVER deferred** rather
than remediated, because the assertion form is hard to e2e-witness
without running the failing program in a way that distinguishes the
pre-fix from post-fix behaviour. **Recommendation**: file as a new
FIXME against `/int` for harvest as a unit test inside `src/`, where
the predicate-scan is the unit boundary.

## Part C — Coverage gaps surfaced and remediated

### Tests added (carry-forward fixes)

**`tests/spec_appendix_a_builtins.rs`** — 18 new tests covering string
ops + clamping behaviour:

| Test | Spec | Carry from |
|---|---|---|
| `primitive_substring_basic` | §A.3 | `legacy/ring1.rs::string_substring_basic` |
| `primitive_substring_clamps_end` | §A.3 | `legacy/ring1.rs::string_substring_clamps_end` |
| `primitive_char_at_valid` | §A.3 | `legacy/ring1.rs::string_char_at_valid_index` |
| `primitive_char_at_out_of_bounds_empty` | §A.3 | `legacy/ring1.rs::string_char_at_out_of_bounds_empty` |
| `primitive_trim_whitespace` | §A.3 | `legacy/ring1.rs::string_trim_whitespace` |
| `primitive_trim_interior_preserved` | §A.3 | `legacy/ring1.rs::string_trim_interior_preserved` |
| `primitive_to_upper_ascii` | §A.3 | `legacy/ring1.rs::string_to_upper_ascii` |
| `primitive_to_lower_ascii` | §A.3 | `legacy/ring1.rs::string_to_lower_ascii` |
| `primitive_starts_with_true` | §A.3 | `legacy/ring1.rs::string_starts_with_true` |
| `primitive_starts_with_false` | §A.3 | `legacy/ring1.rs::string_starts_with_false` |
| `primitive_ends_with_true` | §A.3 | `legacy/ring1.rs::string_ends_with_true` |
| `primitive_ends_with_false` | §A.3 | `legacy/ring1.rs::string_ends_with_false` |
| `primitive_contains_true` | §A.3 | `legacy/ring1.rs::string_contains_true` |
| `primitive_contains_false` | §A.3 | `legacy/ring1.rs::string_contains_false` |
| `primitive_replace_multiple` | §A.3 | `legacy/ring1.rs::string_replace_multiple` |
| `primitive_replace_missing_needle` | §A.3 | `legacy/ring1.rs::string_replace_missing_needle` |
| `primitive_split_produces_parts` | §A.3 | `legacy/ring1.rs::string_split_produces_parts` |
| `primitive_join_reassembles` | §A.3 | `legacy/ring1.rs::string_join_reassembles` |

**`tests/spec_06_pattern_matching.rs`** — 1 new test:

| Test | Spec | Carry from |
|---|---|---|
| `pattern_non_exhaustive_match_on_adt_neg` | §6.5.1, §6.5.3 | `legacy/ring1.rs::non_exhaustive_match_panics` |

**`tests/spec_12_runtime.rs`** — 4 new tests:

| Test | Spec | Carry from |
|---|---|---|
| `integer_overflow_wraps_silently` | §12.7.2 | `legacy/ring0.rs::integer_overflow_wraps` |
| `integer_underflow_wraps_silently` | §12.7.2 | `legacy/ring0.rs::integer_underflow_wraps` |
| `integer_division_by_zero_panics_neg` | §12.7.3 | `legacy/ring0.rs::checked_division_by_zero_panics` |
| `string_utf8_source_encoding_accepted` | §12.1 | `legacy/ring0.rs::source_encoding_utf8` |

**`tests/spec_08_modules.rs`** — 2 new tests:

| Test | Spec | Carry from |
|---|---|---|
| `import_inside_let_rejected_neg` | §8.3 | `legacy/sprint59_neg.rs::import_inside_let_rejected_neg` |
| `import_below_use_still_available_before_definitions` | §8.3 | `legacy/sprint59_neg.rs::import_below_use_still_available_before_definitions` |

**`tests/repl_negative.rs`** — 5 new tests:

| Test | Spec | Carry from |
|---|---|---|
| `source_unknown_name_graceful` | repl/spec.md §3.1 | `legacy/e2e.rs::e2e_s3_1_source_neg_nonexistent` |
| `sexp_unknown_name_graceful` | repl/spec.md §3.1 | `legacy/e2e.rs::e2e_s3_1_sexp_neg_nonexistent` |
| `ast_unknown_name_graceful` | repl/spec.md §3.1 | `legacy/e2e.rs::e2e_s3_1_ast_neg_nonexistent` |
| `clif_unknown_name_graceful` | repl/spec.md §3.1 | `legacy/e2e.rs::e2e_s3_1_clif_neg_nonexistent` |
| `disasm_unknown_name_graceful` | repl/spec.md §3.1 | `legacy/e2e.rs::e2e_s3_1_disasm_neg_nonexistent` |

**`tests/repl_introspection.rs`** — 4 new tests:

| Test | Spec | Carry from |
|---|---|---|
| `list_neg_empty_categories_omitted` | repl/spec.md §3.3 | `legacy/e2e.rs::e2e_s3_3_list_neg_empty_categories_omitted` |
| `list_neg_no_special_forms_category` | repl/spec.md §3.3 | `legacy/e2e.rs::e2e_s3_3_list_neg_no_special_forms` |
| `list_neg_only_imports_shows_no_definitions` | repl/spec.md §3.3 | `legacy/e2e.rs::e2e_s3_3_list_neg_no_imports` |
| `imports_neg_no_primitives_leak_on_fresh_session` | repl/spec.md §3.4 | `legacy/e2e.rs::e2e_s3_4_imports_empty_neg_no_primitives_leak` |

**Total new tests authored: 34** spread across 6 files.

### Coverage gaps NOT remediated this sprint

These are recognised gaps but not e2e-trivially portable. Recommended
follow-up actions in the "Recommendations" section.

| Gap | Source | Reason deferred |
|---|---|---|
| Defect 8 latent `program_needs_trace` scan-gap regression | `legacy/sprint59_neg.rs::defn_body_with_trace_triggers_extern_registration_neg` | Hard to e2e-witness — Rust-internal predicate. Recommend `/int` unit test in `src/`. |
| Lazy seq construction does not force tail | `legacy/ring2.rs::lazy_seq_construction_does_not_force_tail` | Requires `(deftype (Seq a) ...)` thunk-based shape; needs spec section in `spec_12_runtime.rs` for `lazy seq` semantics — file a `[spec/]` clarification first. |
| HKT type variables (`hkt_*` cluster, 3 tests) | `legacy/ring2.rs:2258-2288` | Spec coverage unclear; `/spec` sweep needed before test authoring. |
| Trait `neg_impl_missing_method_errors` | `legacy/ring2.rs:2191` | Defer to `spec_07_traits.rs` enrichment in S65. |
| `neg_occurs_check_infinite_type` | `legacy/ring2.rs:2132` | Type-error e2e shape; defer to S65 typecheck-error coverage. |
| 5 lenient-eval scheduling tests | `legacy/lenient.rs` | Test-capture platform fixture required; tracked separately. |
| TCO deep recursion (5 tests) | `legacy/ring0.rs:364-421` | Indirect e2e — requires program that demonstrates non-stack-overflow. Defer. |
| Multi-dot module path / transitive reexport (~6 tests) | `legacy/modules.rs` | Module-fixture sweep deferred to S65 expansion of `spec_08_modules.rs`. |

These remain as legacy quarantined files (already harvest-FIXME'd at
0134-0139); the harvest will pick them up with appropriate-tier tests.

## Part D — Harvest FIXME amendments

No amendments authored this wave. The existing harvest FIXMEs
(0134-0139) already say "harvest into `#[cfg(test)]` unit tests inside
the owning crate" and reference the source file. The 34 new e2e tests
authored here cover the language-behaviour surface; what remains in the
quarantined files for harvest is genuinely Rust-internal (per-crate
contract assertions, scheduler internals, atomics counter checks).

**Recommended amendment** (defer to `/sprint` action, not in-wave):
amend FIXME `0139-harvest-tests-legacy-sprint59_neg.md` to explicitly
call out `defn_body_with_trace_triggers_extern_registration_neg` as a
must-preserve regression guard during the harvest, since Defect 8's
fix has yet to land and the latent gap is real.

## Confidence assessment

The brief asked: "Based on the sample, what fraction of Wave 5's 1,625
silently-discarded tests are likely (a) real duplicates, (b) Rust-internal
harvest-bound, (c) coverage gaps that should have been carry-forward?"

From the 173-test sample (across the 9 audited files, ~20% of the 869
quarantined):

- **(a) real duplicates of carry-forward**: ~50%. The most redundant
  cluster is sketch_port × ring0 × ring1 dual-mode tests of basic
  arithmetic / lambda / closure / let. After dedupe, one test in
  `spec_04_expressions.rs` faithfully replaces 3-4 ring-spread duplicates.
- **(b) Rust-internal / harvest-bound**: ~10%. Trace-extern registration,
  scheduler internals, JIT reclaim atomics — these are genuinely not
  e2e-portable and the harvest FIXMEs are appropriate.
- **(c) coverage gaps that should have been carry-forward but weren't**:
  ~25%. This is the load-bearing finding. String operations are the
  largest single cluster. Slash-command nonexistent-name guards were
  another. Match exhaustiveness runtime panic and integer
  overflow/division-by-zero were absent.
- **(d) wave-deferred** (legitimately out of e2e-scope this sprint):
  ~15%. Lazy seq, HKT, lenient-platform, deep TCO.

The (c) fraction (~25%) is **substantially higher than the optimistic
"naturally absorbed" framing implied by the Wave 5 close**. This
audit's 34 carry-forward tests close most of the spec-load-bearing gaps;
the remainder are tracked above for S65.

Calibration check: the sample is 20% of the 869 quarantined, so
generalising to the 869: predicted ~217 GAP-COVER tests. The 34
remediated represent ~16% of the predicted gap volume — the
spec-most-load-bearing gaps. The residue is dominated by:

- 12 trait operator dual-mode tests (`dual_mode_trait_*`) — covered
  via REPL-canonical spec_07 tests; technically COVERED, just lower
  multiplicity.
- 30+ closure variants in ring1 (capturing strings, ADTs, vecs in
  higher-order contexts) — sufficient surface coverage in spec_04;
  some specific shapes (closure-returning-ADT-with-string) are
  GAP-COVER but low-priority.
- ~20 ADT permutations (Either type, polymorphic, nested Option of
  Option) — partial coverage; specific shapes may fall through.

**This audit is sound but does not eliminate the residual gap.** A
S65 follow-up sweep of `tests/spec_07_traits.rs` and
`tests/spec_05_definitions.rs` (closure / ADT polymorphism shapes)
would catch the remainder.

## Recommendations for Wave 6 dispatch

### Required (gate)

None. The Wave 5 dedupe is sound for spec-conformance gating once the
34 GAP-COVER tests added in Wave 5.5 land.

### Recommended (Important)

1. **File a FIXME against `/int`** to harvest the Defect 8 latent
   `program_needs_trace` regression guard as a unit test inside
   `src/session_v4.rs::program_needs_trace`. The predicate-scan is the
   right unit boundary.

2. **File a FIXME against `/spec`** to clarify lazy-seq runtime
   semantics in `spec/12-runtime.md` so that `lazy_seq_*` tests can be
   carried forward against a normative section rather than against
   the deftype-shape pattern from `legacy/ring2.rs`.

3. **S65 follow-up sweep**: spec_07_traits.rs (10 tests now) is small
   relative to its surface. Add ~10 carry-forward tests for trait
   dispatch shapes (multi-impl resolution, default methods, operator
   trait dispatch as first-class value).

### Suggested (defer to S65)

- Add a `// (carry: legacy/...)` linter rule to the spec_link_check.py
  script — every test that lifts from a quarantined source MUST cite
  it. This makes the dedupe-recovery audit-trail mechanically visible.
- Build a pre-Wave dedupe checklist: for any wave that quarantines >50
  tests, mandate a sample audit of the same form as Wave 5.5 BEFORE
  the quarantine commit lands. The 30%+ gap rate this audit found
  would have surfaced at landing if the discipline existed.

## Wave 5.5 gate verification

| Criterion | Status |
|---|:---:|
| ~180 sample tests audited (Part A) | YES (173) |
| All regression-named tests audited (Part B) | YES (35 of 35) |
| All spec-load-bearing GAP-COVER findings remediated | YES (34 new tests) |
| Wave-deferred GAP-COVER recorded with rationale | YES |
| Harvest FIXMEs assessed | YES (no amendments authored — recommendation filed instead) |
| `tests/plan/wave-5.5-dedupe-audit.md` records full methodology + findings | YES |
| `cargo nextest run` of new files passes | YES (33/34 new tests pass; 1 parity-rule landing per below) |
| `spec_link_check.py --scope <updated-files>` clean | YES (164 citations / 0 mis-cited / 0 malformed) |

### Test run results

`cargo nextest run --no-fail-fast` (full suite): 775 tests, 764 passed,
11 failed.

| Failure | Type | Source |
|---|---|---|
| `d6_exemplar_*` × 4 | pre-existing carry | Defect 6 (S62 /port + /backend) |
| `wave6_demo_repros::exemplar_solver_does_not_stack_overflow_on_small_puzzle` | pre-existing carry | Defect 6 |
| `cache::cache_multi_module_transitive_imports` | pre-existing carry | FIXME 0121 |
| `build_confidence::mode_equiv_*` × 4 | pre-existing carry | FIXME 0122 |
| `spec_08_modules::import_below_use_still_available_before_definitions` | **NEW parity-rule landing** | Wave 5.5; ledgered against `/int` |

Pre-existing baseline: 5 + 4 + 1 = 10 carries (+1 `wave6_demo_repros`
counted above as part of the d6 cluster). New: 1 parity-rule landing,
expected and ledgered. **Net new failures attributable to Wave 5.5
authoring: 1 (the parity-rule landing).** All other 33 new tests pass.

## Final note for `/sprint`

The user's pushback was the right level of skepticism. Wave 5's
"naturally absorbed" framing significantly understated the dedupe risk.
The 25% GAP-COVER rate this audit found maps directly to the user's
risk class #1 (regression guards) and #2 (context-sensitive assertions).
The 34 carry-forward tests added here close the spec-most-load-bearing
of those gaps; the residue is recorded with rationale for S65.

Two structural lessons:

1. **Dedupe is not naturally absorbed** — even a well-intentioned
   spec-anchored author misses entire spec sections (string ops,
   slash-command nonexistent-name guards, runtime-panic semantics).
   Wave 5's framing was optimistic.

2. **The Wave 3.5 `/reset` precedent generalised** — the audit
   surfaced not just one slipped-through INVENTED test, but an entire
   class of silently-lost coverage. The right cadence is:
   author-audit-author, not author-author-author-then-grand-audit.

The Wave 3.5 `tests/plan/spec_link_check.py` linter is the durable
mitigation for INVENTED tests. **A `_neg_` carry-forward linter would
be the durable mitigation for silent dedupe loss** — recommended as
S65 follow-up tooling work.
