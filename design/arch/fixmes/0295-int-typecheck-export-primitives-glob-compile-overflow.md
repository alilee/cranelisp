---
number: 0295
target: /typecheck
filed_by: /review
filed_at: 2026-06-08
sprint_filed: 76
refers_to: cranelisp-types::types::apply (crates/cranelisp-types/src/types.rs cyclic-subst non-termination, per FIXME 0279), src/bootstrap.rs (Wave-4b primitives seeds: Pair/Result/discover-tests/catch-runtime-error), src/worker.rs::resolve_extern_target, tests/fixtures/preludes/primitives-only.cl, design/arch/fixmes/0279-qa-io-monad-compiler-stack-overflow.md
status: open
---

# `(export [primitives [*]])` compile-time stack overflow — Wave-4b NEW trigger of the 0279 cyclic-subst family (GATE BLOCKER)

## Issue — REGRESSION (bisection-proven, S76 Wave 3+4 gate review)

A module doing `(export [primitives [*]])` (the test prelude
`tests/fixtures/preludes/primitives-only.cl`) overflows the stack at COMPILE time
in int's `priority-worker-0`. After that prelude loads, ANY expression (even
`(add-i64 2 3)`, even empty input) overflows during prelude compile.

**Bisection (single-threaded, the true per-test verdict):**
- `9fe857c` (pre-Wave-4a): `(bind (Pure 77) …)` → `:primitives/Int 77` ✓
- `9491ccc` (Wave 4a — ferry + IVar widening + PrimitiveExtern): ✓ (ferry CLEARED as cause)
- `bcd45df` (Wave 4b partial — int facade settle): **stack overflow** ✗
- `eea4c3b` (HEAD): **stack overflow** ✗

Five `spec_10_io::bind_*` tests that PASS at 9fe857c FAIL at HEAD
(`bind_identity_continuation`, `bind_pure_to_pure_plus_one`,
`bind_polymorphic_inference`, `repl_bind_pure_lambda_no_double_free`,
`run_mode_main_returns_bind_exit_code`). This is NOT pre-existing baseline — the
0288/0292 agents' "in-flight baseline" attribution is refuted by the bisection.

**Exact trigger:** `(export [primitives [*]])` (re-export glob), NOT
`(import [primitives [*]])`. Introduced by bcd45df's new primitives seeds
(`Pair`/`Result` polymorphic ADTs, `discover-tests` as `DefKind::PrimitiveExtern`
with an import edge, `catch-runtime-error`) + `resolve_extern_target`'s
import-edge-following.

**Root:** the same `cranelisp_types::types::apply` cyclic / occurs-check-violating
substitution non-termination already documented in FIXME 0279 (cross-module
polymorphic monomorphisation). The new polymorphic primitives seeds, re-exported
through the glob, newly exercise it. **0279's fix should clear BOTH this regression
AND the pre-existing d6/wave6 overflow cluster** — one root.

## Proposed resolution

Fix the cyclic-subst non-termination at its root (per 0279's triage: occurs-check
/ cycle-guard in `apply` or in the subst composition during cross-module scheme
instantiation). Verify the `(export [primitives [*]])` prelude compiles and the 5
bind tests + the 0279 minimal repro go green. If a narrower int-side seeding change
(avoid the cyclic import edge / non-polymorphic seed shape) defuses the trigger
without the full root fix, that is an acceptable in-sprint stopgap ONLY if it does
not mask 0279 — prefer the root fix.

## Operational implication / Context

**GATE BLOCKER for S76 Wave 4c** — it breaks the test prelude, red-lining a swathe
of the e2e suite; the ledger must NOT record the 5 bind regressions as baseline.
Supersedes/absorbs 0279 (same root; 0279 stays as the minimal-repro record + the
d6/wave6 corollary). User decision pending: in-sprint fix vs explicit deferral.
