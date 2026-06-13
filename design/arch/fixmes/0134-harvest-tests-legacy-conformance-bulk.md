---
number: 0134
target: /int
filed_by: /qa
filed_at: 2026-05-04
sprint_filed: 64
refers_to: tests/legacy/e2e.rs, tests/legacy/ring0.rs, tests/legacy/ring1.rs, tests/legacy/ring2.rs
status: open
int_reviewed_by: /dev int (S81 W-E)
---

## S81 W-E /dev int review — CARRIED (int slice is lowest-priority + e2e-covered; bulk is /typecheck + /backend)

This is the XL conformance harvest (~1300 source tests across 4 files). Per the
FIXME's own "Operational implication" sequencing, the int slice is explicitly
**lowest priority** ("most pipeline tests have e2e analogues already"), and the
harvest partition assigns:
- AST/type-shape + inference + `assert_type_error` → **/typecheck**
  (`crates/cranelisp-typecheck/src/`) — the largest share.
- `assert_rc_balanced` + closure/Vec-COW codegen → **/backend**
  (`crates/cranelisp-backend/src/`).
- int's named slice is only the `compile_both()` batch/REPL **parity**
  invariant — which is an **e2e** property (run the same source through `--run`
  and the REPL and assert mode-equivalence), and is already exercised by the
  canonical e2e suite's `run_through_all_modes` discipline
  (`tests/CLAUDE.md` §Test Standards) across the `spec_*.rs` files.

**Disposition this wave:** no int unit harvest is warranted — the int slice is
parity-shaped (e2e, /qa-owned) and already covered; the actionable bulk is
/typecheck + /backend. Left **OPEN**, `target: /int` retained only as the
multi-skill coordination anchor (the FIXME body explicitly splits sub-tasks
per-crate). No narrowing discarded: the int slice was assessed as e2e-covered,
not skipped. The /typecheck + /backend harvests + the eventual /qa file deletion
remain the open work.

---

# Harvest tests/legacy/{e2e,ring0,ring1,ring2}.rs into per-crate unit tests

## Issue

The Sprint 64 Wave 5 test-port quarantined four large legacy conformance
files:

- `tests/legacy/e2e.rs` (2701 LOC, 309 tests) — original integration-tier
  e2e suite. Heavy use of `compile_and_run_simple()`, `compile_and_run()`,
  `compile_and_run_with_macros()`, inline `NUM_TRAIT_PRELUDE` etc.
  constants. Many tests already in subprocess shape but coupled to legacy
  helpers.
- `tests/legacy/ring0.rs` (1135 LOC, 216 tests) — Ring 0 conformance:
  core expressions, arithmetic, primitives, let, if, lambda, application.
- `tests/legacy/ring1.rs` (2253 LOC, 380 tests) — Ring 1 conformance:
  strings, ADTs with fields, closures, vec ops, IO.
- `tests/legacy/ring2.rs` (2484 LOC, 405 tests) — Ring 2 conformance:
  traits, operator dispatch, constrained polymorphism, modules, ADT
  trait impls.

All four files use `tests/helpers/mod.rs::{ReplSession, compile_and_run_*,
repl_session*, assert_type_error, assert_parse_error, assert_rc_balanced}`
— the integration-tier surface that Phase 3 (S65) will delete. Their
language-conformance assertions have been carried forward as REPL-canonical
e2e tests in:

- `tests/spec_03_types.rs` — type system surface
- `tests/spec_04_expressions.rs` — special forms / lenient eval
- `tests/spec_05_definitions.rs` — defn / deftype / deftrait / impl
- `tests/spec_06_pattern_matching.rs` — match patterns
- `tests/spec_07_traits.rs` — trait dispatch + operator-as-method
- `tests/spec_08_modules.rs` — module discovery + import / visibility
- `tests/spec_09_macros.rs` — defmacro + quasiquote
- `tests/spec_appendix_a_builtins.rs` — primitive functions

The carry-forward is spec-anchored — one e2e test per spec assertion. The
duplication across e2e.rs / ring0.rs / ring1.rs / ring2.rs (the same
assertion appearing in 2-4 source files) collapsed naturally as the new
suite is authored against the spec, not the source-file shape.

## Proposed resolution

Per the two-tier strategy (`memory/project_test_strategy.md`), the
remaining Rust-internal observations belong inside the owning crate as
`#[cfg(test)]` unit tests. Suggested partition:

### `crates/cranelisp-typecheck/src/`

- AST-shape regression tests using `cranelisp_frontend::parse +
  build_program` per `tests/CLAUDE.md §"Isolating Cross-Crate Failures"`.
- Type-inference assertions that go beyond REPL-observable surface
  (specific type-variable shapes, constraint-set composition).
- `assert_type_error(src, msg)` callsites — translate to direct
  `tc.check()` invocations.
- Multi-sig dispatch resolution — the symbol-table inspection currently
  done via `ReplSession::show_entry()`.

### `crates/cranelisp-backend/src/`

- `assert_rc_balanced(src)` callsites — translate into RC counter
  inspection adjacent to alloc/dec emission code. The `CRANELISP_RC_TRACE`
  parsing in tests/helpers/mod.rs is integration-tier; the `#[cfg(test)]`
  form can read counters directly.
- Closure-capture codegen invariants beyond e2e observability.
- Vec COW edge cases that need Cranelift IR inspection (use `CRANELISP_CODEGEN_TRACE`
  pattern but at unit-test layer).

### `src/` (binary crate, post-FIXME 0109 decomposition)

- Pipeline orchestration tests — multi-form REPL sessions where the
  Rust-API form is materially clearer than subprocess piping.
- `compile_both()` (batch / REPL parity) — the same source compiled both
  ways with `// spec:` annotated parity invariant.

### Use existing patterns

- `cranelisp_frontend::parse` + `build_program` for AST input — do NOT
  hand-construct AST.
- `tempfile::TempDir` per test for any file-system fixtures.
- `// spec:` annotations on each translated test naming the spec section.
- Per-test naming preserved where possible to allow git blame to trace
  the harvested assertion back to the original.

## Operational implication / Context

This is the largest single harvest commitment from S64 — ~1300 source
tests across 4 files. The harvest does not need to be a single sprint:
each crate's harvest is independent. Suggested sequencing:

1. **`/typecheck`** — AST/type-shape assertions; lowest churn.
2. **`/backend`** — RC + codegen assertions; depends on FIXME 0109
   landing first if the harvest also wants to reshape `Code{ptr}` access.
3. **`/int`** — pipeline tests; lowest priority because most pipeline
   tests have e2e analogues already.

When a file is fully harvested (its assertions translated, no longer
load-bearing in the legacy archive), delete the file and remove its row
from `tests/legacy/README.md`. Until then, the file is inert (not
compiled by Cargo's auto-discovery, which only scans `tests/*.rs` at the
top level).

The four-file consolidation under one FIXME reflects the shared
multi-skill ownership; resolving skills can split sub-tasks per-skill at
their own discretion when the harvest sprint(s) plan.

## Wave 5.6 reclassification notes (2026-05-04)

The Wave 5.6 file 8 ring2.rs per-test re-audit
(`tests/plan/wave-5.6-ring2-reaudit.md`) reclassified three previously
GAP-HARVEST-marked HKT tests from cluster FF (lines 2258-2302) as
**GAP-COVER**, not harvest:

- `hkt_type_variable_in_trait` (#187) — landed as
  `tests/spec_07_traits.rs::hkt_deftrait_declaration_with_type_constructor_parameter_succeeds`.
- `hkt_trait_declaration` (#188) — landed as
  `tests/spec_07_traits.rs::hkt_functor_impl_on_option_dispatches_via_match`.
- `hkt_impl_bare_constructor` (#189) — landed as
  `tests/spec_07_traits.rs::hkt_impl_targets_bare_type_constructor_not_applied_form`.

Rationale: per-test review confirms the spec anchors are explicit
(`spec/03-types.md §3.7`, `spec/07-traits.md §7.2`,
`spec/05-definitions.md §5.4.4`) and the assertions are e2e-observable
through numeric output. The Wave 5.5 cluster-mode tag of GAP-HARVEST
under "spec coverage unclear" was over-conservative.

The chunk-4 GAP-HARVEST cluster that REMAINS in this FIXME's harvest
scope:

- `neg_hkt_impl_primitive_type_rejected` (#182) — defer per Wave 5.5
  disposition (error-stability concern: implementation may not produce
  a stable error message for impl-on-primitive rejection).
- `lazy_seq_take_from_infinite` (#190) — defer (lazy `Seq` semantics
  spec authority pending; spec/12 §12.4.2 references the property but
  `(Seq a)` is not normatively defined).
- `lazy_seq_construction_does_not_force_tail` (#191) — same as #190.

All other ring2.rs GAP-COVER findings have landed as carry-forward
e2e tests (chunks 1-4) and no longer need harvest treatment from this
FIXME's perspective. The tests/legacy/ring2.rs source remains for
unit-tier harvest by `/typecheck`/`/backend`/`/int` per the original
sub-task plan.
