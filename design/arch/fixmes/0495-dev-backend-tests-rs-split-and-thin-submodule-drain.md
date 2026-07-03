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

## Operational implication / Context

Sequencing: rides increment I's first backend change-sets — increment I lands on
exactly these seams (fn_as_value/COW rework per backend §12.7, 0476 DefKind cure),
so the drain is the same-wave test half, not a separate sprint. The 22 intentional
REDs (0474/0483 guards among them) flip green against this work; the unit scenarios
prevent the *next* adjacent cell from escaping.
