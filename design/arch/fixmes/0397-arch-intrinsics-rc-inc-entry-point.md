---
number: 0397
target: /arch
filed_by: /dev
filed_at: 2026-06-17
sprint_filed: 84
refers_to: crates/cranelisp-intrinsics/src/rc.rs, crates/cranelisp-primitives/src/marshal.rs (shallow_rc_inc), crates/cranelisp-primitives/src/string.rs (string_identity), audits/primitives-2026-06-14.md (MED-1)
status: open
---

# Add a blessed RC-inc entry point to `cranelisp_intrinsics::rc` (+ settle the atomicity policy)

## Issue

FIXME 0368 (HIGH-1) single-sourced the heap-layout offsets in
`cranelisp-primitives::marshal` from `HeapHeader` — landed. Its sibling
finding **MED-1** (unify the RC-inc path on `cranelisp_intrinsics::rc`)
**cannot be resolved inside `cranelisp-primitives`** because the blessed `rc`
module has **no public RC-inc function**:

- `cranelisp_intrinsics::rc` exposes `consume_shallow` (atomic *dec* +
  conditional free), `rc_trace`, and `rc_underflow_check` — but **no `rc_inc`**.
- Every RC-inc site therefore open-codes its own `fetch_add` (or non-atomic
  `+= 1`): `marshal.rs::shallow_rc_inc` (non-atomic), `string.rs::string_identity`
  (atomic `fetch_add(Release)`), and several intrinsics-internal sites
  (`trace.rs::rc_inc_if_heap` SeqCst, `drop.rs` Release, `ivar.rs` SeqCst).
- **Two+ atomicity disciplines coexist** with no single owner. Under live
  lenient-eval sparks (`ivar_spark` → `rayon::spawn`), a non-atomic inc on a
  value shared across a fork-join boundary is a latent data race.

`cranelisp-primitives` (`/dev` scope) consumes the intrinsics RC surface; it
cannot add the entry point. This is the `/arch`-routed half the 0368 brief
anticipated ("If the RC atomicity policy needs an architectural ruling, file a
sub-FIXME `target: /arch`").

## Proposed resolution (for `/arch` to rule)

1. Add a blessed public RC-inc entry to `cranelisp_intrinsics::rc` — e.g.
   `pub fn rc_inc(ptr: i64)` (atomic `fetch_add`, nullary-tag-skipping,
   `rc_trace("inc", …)`, mirroring `consume_shallow`'s shape). One owner for
   the RC-inc half, as `consume_shallow` already is for the dec half.
2. Settle the **atomicity policy** against the live spark model: the backend
   emits inline `atomic_rmw` for inc/dec, `string_identity` uses
   `fetch_add(Release)`, `trace`/`ivar` use SeqCst — name the required ordering
   for the extern-Rust RC-inc path and document it on the new fn (cross-ref
   Principle 7 + the runtime RC model / NFR C.4.1).
3. Once the entry exists, re-deploy `/dev` on `cranelisp-primitives` to route
   `marshal.rs::shallow_rc_inc` + `string.rs::string_identity` through it,
   deleting the open-coded pointer arithmetic (closes MED-1).

## Context

0368 HIGH-1 (offsets) is delivered and committed in S84; MED-1 carries here.
`marshal.rs::shallow_rc_inc` now derives its RC offset from
`HeapHeader::RC_OFFSET` and carries an inline NOTE pointing at this FIXME +
documenting why the non-atomic inc is sound *today* (no spark forks an
`sconcat`/`quote-sexp` callee mid-flight — both run on the calling thread), so
the divergence is a tracked hazard, not a present bug. The unification is a
clean dedup blocked only on the missing intrinsics entry point.
