---
number: 0349
target: /typecheck
filed_by: /dev
filed_at: 2026-06-14
sprint_filed: 82
refers_to: design/arch/fixmes/0348-int-got-slot-reassigned-across-dual-compile-breaks-forward-ref-call.md, crates/cranelisp-typecheck/src/program.rs (mono-variant creation under forward-reference ordering), tests/spec_04_expressions.rs::polymorphic_accumulator_fold_does_not_over_unify (the 0344 e2e), src/worker.rs (commit_staging_to_live — slot allocation, now stable)
status: open
---

# 0348 re-attribution (int investigation): the 0344 fold wrong-value is TYPECHECK monomorphisation, NOT int GOT-slot allocation

## Issue (S82 Wave 2 /dev int finding)

0348 attributed the `(reduce add-i64 0 [1 2 3])` → exit 0 (should be 6)
defect to an **int GOT-slot reassignment** (`reduce.got_slot` changing 2→0
between the entry module's two `compile_to_module` passes). The int-side
investigation does **not** confirm a slot-reassignment bug. With the
`commit_staging_to_live` deterministic commit-order sort in place (keyed on
the staged got_slot — `src/worker.rs`), GOT slots are **stable and
identity-preserving** across the build, and the CLIF main bakes the **correct**
slot in both orderings. The remaining wrong value has a different cause.

### Evidence — slots are stable; the trigger is whether a mono variant is CREATED

Instrumenting `commit_staging_to_live` for the forward-reference (broken)
ordering:

```
[commit] module=fold name=reduce       staged=Some(0) live=0
[commit] module=fold name=reduce-loop  staged=Some(1) live=1
[commit] module=fold name=main         staged=Some(2) live=2
```

Slots are source-order stable (reduce@0, reduce-loop@1, main@2) — committed
**once**, not reassigned. CLIF (`CRANELISP_CODEGEN_DUMP=fold`):

- **BROKEN (reduce defined first):** `main` bakes `iadd_imm gv0, 0` (slot 0 =
  `reduce`, the polymorphic template) via `call_indirect sig3` (3-arg). There
  is **NO `reduce$Int+Vec` mono variant in the table at all.** Calling the
  un-monomorphised polymorphic `reduce` returns the initial accumulator (0).
- **WORKING (reduce-loop defined first):** the table contains
  `reduce-loop@0, reduce@1, main@2, reduce$Int+Vec@3` — a **mono variant
  exists**, and `main` bakes `iadd_imm gv0, 24` (slot 3 = `reduce$Int+Vec`).
  Returns 6.

So the difference between the two orderings is **not** which slot `main` bakes
(it bakes the right slot for whatever it resolved to) — it is **whether
typecheck creates `reduce$Int+Vec` and redirects `main`'s call to it**. Under
the forward-reference ordering the mono variant is never created, so `main`
calls the polymorphic template, which is itself miscompiled / returns the
initial accumulator. The `collect`/`(Vec a)` sibling is NOT required — bare
forward-reference ordering alone toggles mono-variant creation.

The 0348 backend evidence (`reduce@0, reduce-loop@2, main@1` etc.) was a
SNAPSHOT of pre-commit-sort non-determinism; the deterministic commit sort
(0348 int work, landed) removed the permutation. The residual failure is not a
slot bug.

## Proposed resolution

Owning surface: **/typecheck** (monomorphisation). The fix must make
`reduce$Int+Vec` creation + the `main` call-site redirect **insensitive to the
forward-reference definition order** — i.e. a generalized polymorphic fn used
at a concrete instantiation gets a mono variant created regardless of whether
the fn is defined before or after the helper it forward-references. Either
that, OR the polymorphic (non-monomorphised) higher-order recursive `reduce`
body must itself compile to a correct fold (today the polymorphic template
returns the initial accumulator when called directly — that is the deeper
correctness gap, possibly /backend).

The int GOT-slot allocation is **already stable** — `commit_staging_to_live`
sorts the staging→live drain by staged slot, guarded by a unit test
(`src/worker.rs::worker::tests::commit_staging_preserves_source_order_slots_into_empty_live`).
No further int slot work is warranted for this defect.

## Operational implication / Context

- The 0344 e2e (`tests/spec_04_expressions.rs::polymorphic_accumulator_fold_does_not_over_unify`)
  stays RED — it is a known failing guard, carried forward to the
  /typecheck (mono-variant-under-forward-ref) resolver, NOT int.
- 0348's int half (deterministic commit-order slot allocation) is DONE and
  guarded; this FIXME records the boundary finding so 0348 can be re-pointed /
  closed against the typecheck cause rather than re-spawning int slot work.
- `/dev (int)` cannot edit typecheck or backend — this is the cross-crate
  handoff brief per `tests/CLAUDE.md §"Isolating Cross-Crate Failures"`
  Step 4 (unit-stable at the int seam, e2e still red ⇒ cause is upstream).
