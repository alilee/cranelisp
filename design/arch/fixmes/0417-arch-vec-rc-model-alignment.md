---
number: 0417
target: /arch
filed_by: /arch
filed_at: 2026-06-20
sprint_filed: 87
refers_to: crates/cranelisp-backend/src/compiler/vec_codegen.rs:254,371,404-456,481 (vec-set/vec-push codegen + emit_vec_set_copy_temp_compensation), crates/cranelisp-intrinsics/src/vec_runtime.rs:188,220,238 (vec_set_copy / vec_push_copy), audits/cranelisp-backend-s87.md F3, audits/cranelisp-intrinsics-s87.md NEW-2, audits/cranelisp-primitives-s87.md MED-2, exemplar/CLAUDE.md §"Known Issues" DEF-2
status: open
---

# vec-set / vec-push consuming-inc RC-model alignment (paired backend + intrinsics; PAIRED-OR-UAF)

## Issue

The S87 Stage-B audit confirmed, from **both** sides, the S86 `vec_set_copy`
RC-asymmetry seed (backend F3 + intrinsics NEW-2; primitives MED-2 is a third
witness). The *decision* is uniform — both `vec-push` and `vec-set` share the
single `element_consuming_inc` predicate (`vec_codegen.rs:1467`) and the
inc-iff-heap-typed-Var rule. But the **emission strategy diverges**:

- **vec-push & generic args:** emit the consuming inc **in codegen, up-front**;
  `vec_push_copy` (`vec_runtime.rs:238`) does **NOT** inc the appended `val`.
- **vec-set:** the COW copy path relies on `vec_set_copy` (`vec_runtime.rs:220`)
  inc'ing `val` **unconditionally** at runtime, then **compensates** the
  temporary's over-inc with a codegen dec (`emit_vec_set_copy_temp_compensation`,
  `vec_codegen.rs:404-456`).

One conceptual operation ("store a heap element into a Vec, gaining a ref iff it
is a live Var") is implemented with **opposite divisions of labor**. Both are
correct today (suite green; inc + dec net out) — this is a **Principle-7
single-source-of-truth / Decision-24 uniformity** gap, not a live defect. But it
is the same RC-convention family as the active **DEF-2 `conj` heap-ADT
corruption** defect (Vec element-write consuming-inc discipline not single-sourced
across crates), and `str_split`/`str_join` (primitives MED-2) hand-roll a third
Vec-element-write path.

## Proposed resolution

Make vec-set match vec-push (the fully-symmetric design):

1. Hoist the consuming inc up-front in `compile_vec_set` (gated by
   `element_consuming_inc`, like vec-push).
2. **Stop** `vec_set_copy` inc'ing `val` — drop the `call_elem_fn(elem_inc_fn,
   val)` at `vec_runtime.rs:220` (`elem_inc_fn` for *retained* elements is
   unchanged; only the new-`val` inc is dropped).
3. **Delete** `emit_vec_set_copy_temp_compensation` (`vec_codegen.rs:404-456`).

This removes a runtime branch, a codegen helper, and the only labor-split
divergence in the RC convention. **PAIRED-OR-UAF:** changing the runtime inc
without removing the backend compensation (or vice-versa) is a use-after-free
regression of FIXME 0296. The two crates land **together** with a unit test on
each side (intrinsics: `vec_set_copy` no longer inc's `val`; backend: vec-set copy
path inc's a Var, transfers a temporary, no compensation).

`/arch` dispatches the paired `/dev backend` + `/dev intrinsics` change as one
change-set; do NOT split. Consider co-scheduling the **DEF-2 `conj` repro fix**
(same root cause) and re-routing primitives' `str_split`/`str_join` through a
`vec_runtime` element-store accessor in the same RC-convention pass.

## Operational implication / Context

- **Stage-B backlog item B2 (theme T2), ranked #1 by leverage×hazard.** Synthesis
  recommendation (`audits/s87-findings.md §3`): **lean must-fix-before-Phase-H**,
  paired with the DEF-2 `conj` defect, because fixing the Vec-element RC convention
  once before Phase H is cheaper than fixing it twice after.
- Cross-references the `vec_set_copy` seed in SPRINT.md "S86 hot-spot seeds".
