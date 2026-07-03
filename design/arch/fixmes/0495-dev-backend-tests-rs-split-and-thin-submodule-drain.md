---
number: 0495
target: /dev
filed_by: /qa
filed_at: 2026-07-03
sprint_filed: 101
refers_to: crates/cranelisp-backend/src/tests.rs, sprints/METHOD.md §2.2 "Implementation-strategy unit scenarios", design/arch/fixmes/0494-arch-facade-unit-test-organization-convention.md, tests/plan/coverage-audit-s101.md §3.2
status: open
---

# Backend: split the flat crate-root `tests.rs` along submodule lines + drain the named thin strategy submodules

**Crate**: cranelisp-backend (`/dev` narrow).

## Issue

The S101 coverage audit (`tests/plan/coverage-audit-s101.md` §3.2) confirms the
backend as the priority unit-tier drain target:

1. **The named anti-pattern exhibit** (METHOD §2.2, FIXME 0494): a flat 5,861-line
   crate-root `tests.rs` holding 76 tests over 32,548 LOC of well-composed
   submodules — per-submodule coverage is unattributable by construction.
2. **~5,000 LOC of compiler strategy with zero dedicated per-submodule tests**:
   `compiler/rc_emission.rs` (788 LOC / 2 inline tests — the worst
   coverage-to-strategy ratio in the codebase), `compiler/control_flow/fn_as_value.rs`
   (960 / ~7 happy-only — the 0483/0474 crash-and-leak seam),
   `compiler/match_codegen.rs` (588 / 0), `compiler/control_flow/let_if.rs`
   (472 / 0 — branch RC), `compiler/control_flow/lambda.rs` (538 / 0),
   `compiler/control_flow/dependent_spark.rs` (433 / 0), `compiler/resolution.rs`
   (426 / 0), `compiler/context.rs` (275 / 0), `primitives_inline.rs`
   (612 / 11, all `_happy`-named).
3. **Strategy-matrix cells named by S101 defects and still untested at unit
   grain**: the runtime rc>1 COW copy branch (0474's leak branch — sibling
   rc-tests pin only the compile-time consuming-inc decision table); the
   per-instantiation wrapper matrix in `fn_as_value.rs` (0483's SIGBUS axis);
   GOT exhaustion/freeze/trap-patch (`got.rs` self-documents allocation as
   UNCHECKED; the W4 exhaustion guard has no direct unit pin).

## Proposed resolution

1. **Split `tests.rs`** by moving each attributable bucket next to the submodule
   it exercises (`foo/tests.rs` or `#[cfg(test)] mod tests` sibling), per METHOD
   §2.2 / 0494. Audit-provided bucket map: vec_codegen 20+, got 6–20,
   lib/module-assembly 6–20, resolution/apply 6–20, fn_as_value ~5, trap stub 3,
   fn_compiler 3, extern_call 2, lambda/launch 3, literals/match 2, jit ~3.
   Pure relocation first; no behaviour change.
2. **Drain the thin submodules** per the §2.2 taxonomy {complexity, edge,
   negative}, prioritized: rc_emission → fn_as_value (instantiation-count +
   rc-branch matrices) → got (exhaustion/freeze/trap-patch) → let_if branch RC →
   match_codegen shape matrix → resolution/primitives_inline curry arms.

## Progress — S102 CS-B3.0 (partial relocation; step 1 only)

**Relocated (green):** the fully self-contained `compile_trap_stub` trio
(`trap_stub_raises_provenance_message_and_returns_sentinel`,
`trap_stub_is_callable_at_nonzero_arity`, `trap_stub_raises_on_every_invocation`)
moved from the flat crate-root `src/tests.rs` into a `#[cfg(test)] mod
trap_stub_tests` beside `compile_trap_stub` in `src/lib.rs` (Principle 23). Pure
relocation, zero behaviour change. These depend only on `compile_trap_stub` + the
intrinsics panic slot, so no shared-harness plumbing was needed.

**Remainder (still in `src/tests.rs`, 73 tests):** the remaining buckets
(vec_codegen ~30, lib/module-assembly + got `decision_23_*` + `sprint56_*` +
`decision_36_*`, resolution/apply, fn_as_value value-use trio + curry,
extern_call, lambda/launch, literals/match, jit) all consume the ~600-line
shared harness at the top of `tests.rs` — `TestCheckResult` + `empty_check` +
`enrich_defn_from_side_maps` + the compile-and-run drivers +
`empty_tables`/`empty_aliases`/`make_def_entry_slot`/`vec_elem_for_test`/
`vec_len_for_test`/`run_vec_query_value_consumer`. **The gating sub-task is
extracting that harness into a crate-visible `#[cfg(test)] mod test_support`
(items → `pub(crate)`) that submodule test homes `use`.** That extraction is a
focused, higher-risk change-set of its own (it rewrites every test's helper
imports) and was deliberately NOT bundled with the golden-oracle-witness
change-set (B1-be) to keep the tree green and the empty-diff witness clean. It
should ride its own B3.0-continuation change-set before the B3.1 seam-drain
(step 2, which adds new scenario tests and needs the homes in place).

Status stays **open** — step-1 relocation is partially drained; step 2 (thin-
submodule scenario drain) is untouched (B3.1+ per `design/backend/
ownership-codegen.md` §13.2, not this wave).

## Operational implication / Context

Sequencing: rides increment I's first backend change-sets — increment I lands on
exactly these seams (fn_as_value/COW rework per backend §12.7, 0476 DefKind cure),
so the drain is the same-wave test half, not a separate sprint. The 22 intentional
REDs (0474/0483 guards among them) flip green against this work; the unit scenarios
prevent the *next* adjacent cell from escaping.
