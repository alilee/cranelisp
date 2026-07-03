# L-B1 golden-CLIF corpus — EXCLUSIONS

**Green-only construction** (S102 /arch Q1 ruling; `design/arch/
ownership-inference.md` §6.2; `tests/plan/s100-ownership-verification.md`
§3.1): every shape under an open failing-not-ignored guard at capture time is
excluded. **Each entry names the guard whose flip triggers extension** — when
the fix lands, `/qa` EXTENDS the corpus with the newly-green shape in the fix
change-set (existing golden entries untouched) and strikes the entry here.
This list is what makes the capture non-blocking on the Block-A defect wave.

| Excluded shape | Guard(s) (failing-not-ignored) | Extension trigger |
|---|---|---|
| Vec-trio op as a value at ≥2 instantiations of one HOF | `tests/vec_query_value_use.rs::vec_get_as_value_two_instantiations_of_one_hof_repl`, `…_run_mode`, `…vec_get_and_vec_push_as_values_through_one_hof_run_mode` (FIXME 0483) | 0483 fix (Block B3.1) — add a two-instantiation HOF module |
| Vec-trio op as a value (any position) — conservatively excluded wholesale while the 0483/0474 seam rework is in flight | 0483 guards above + `tests/vec_cow_value_use_leak.rs` ×3 (FIXME 0474; leak-class, green OUTPUT but the seam is mid-rework) | B3.1 seam rework lands — add single-instantiation value-use module(s) with the reworked wrappers |
| FQ call of a generic fn | `tests/generic_value_use_mono.rs::generic_fn_fq_call_monomorphises_like_bare_call` (FIXME 0488 sig a) | 0488(a) fix — add an FQ-generic-call module |
| Imported generic in value position | `…::imported_generic_in_value_position_monomorphises` (0488 sig b) | 0488(b) fix — add an imported-generic-value module |
| Composition over a fold-bodied imported generic | `…::composition_over_fold_bodied_imported_generic_monomorphises` (0488 sig c) | 0488(c) fix — add the composition module |
| Definition-over-explicit-import shadow order shapes | `tests/spec_08_modules.rs::import_used_then_shadowed_by_defn_is_rejected_error`, `…::import_shadowed_by_defn_before_first_call_is_rejected_error` (FIXME 0484, §8.6.4 rejection polarity) | 0484 fix (Block A5) — name-resolution precedence is emission-affecting for green programs, so this extension may instead ride a scoped re-baseline if any corpus entry's resolution changes |

Notes:

- The 0474 leaking shapes are *green programs* (correct output, unbalanced
  RC) and per `design/backend/ownership-codegen.md` §13.1 MAY join the
  corpus; they are held out here anyway because B3.1 reworks exactly their
  wrapper emission — adding them pre-rework would guarantee an immediate
  re-baseline with no oracle value. Add them WITH the B3.1 extension.
- Display/persistence/introspection/diagnostic defects (0485/0486/0487/
  0489/0490/0491/0492/0493, D1–D3, trap-format) have **no capture
  interaction** (the §6.2 classifier) and are not excluded shapes — their
  fixes never touch these dumps.
