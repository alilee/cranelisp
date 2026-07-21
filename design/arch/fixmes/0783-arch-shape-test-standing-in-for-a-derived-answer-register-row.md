---
number: 0783
target: /arch
filed_by: /dev
filed_at: 2026-07-21
sprint_filed: 115
refers_to: design/arch/safety-invariants.md §4 (invariant register) +
  design/arch/fixmes/0776 (the seam × obligation register row) — the class
  "a syntactic node-kind test standing in for the derived answer" has now
  produced four memory-safety defects in one sprint and has no register row
status: open
---

# Register row: "a syntactic node-kind test standing in for the derived answer" (4 instances, S115)

## Issue

The instrumentation question for FIXME 0781 (S115 W4c) answers **(b) — an
instrument existed and was blind**, and the reason it was blind is a *class*
fact that belongs in the register, not in one crate's conventions file.

The four S115 instances, all in `cranelisp-backend`, all live defects:

| # | FIXME | The shape test | Standing in for |
|---|---|---|---|
| 1 | 0693 | `matches!(callee_name, "vec-set" \| "vec-push")` | the COW-site identity (the resolution carrier) |
| 2 | 0752 | the same spelling test, two surviving sites, one FEEDING the "consolidated" gate | same |
| 3 | 0749 | an ad-hoc `matches!` list of "fresh" kinds at the `protect_return_value` site | `is_fresh_construction` |
| 4 | 0781 | `matches!(e, MonoExpr::Var { .. })` at **five** ownership gates in two seams | the value's provenance |

The blindness is precise and worth recording: instance 3's cure — making
`is_fresh_construction`'s match **exhaustive** — is a real standing instrument
and it works, but it guards ONE copy of the answer. The class is "a SECOND copy
of the answer exists elsewhere, phrased as a shape test", and an exhaustiveness
obligation on the canonical predicate is structurally incapable of seeing that
second copy. Every fix in this family has been "delete the second copy"; nothing
prevents a third from being written.

This is the same shape as 0776's seam × obligation register row (an operation
performed at N non-equivalent seams, each able to silently omit an obligation
its siblings discharge) — here the omitted obligation is *consult the derived
answer* — so it may fold into that row rather than becoming its own.

## What was landed in-crate (the cheap half)

`crates/cranelisp-backend/src/rc_ownership_fence_tests.rs` — a structural fence
asserting that no `matches!` in the RC-decision file set
(`vec_codegen.rs`, `match_codegen.rs`, `rc_emission.rs`, `capture_rc.rs`) tests
a `MonoExpr` node's KIND ALONE (`MonoExpr::Kind { .. }`, every field discarded).
Field-keeping tests are deliberately not fenced (asking which BINDING a node is
is a real question); `apply.rs` is deliberately excluded (its bare kind test
selects a codegen mode, not an ownership verdict) with the reason recorded.

**Detection proof (measured, METHOD §2.2):** reverting any one of the five 0781
gates to its pre-fix form flips the fence RED, reporting one violation per
reverted gate by `file:line`; verified for `vec_codegen::emit_vec_drop_if_temporary`
and both `match_codegen` gates. A false-fire control pins that it ignores
comments (every fixed site quotes the old pattern) and field-keeping tests.

## Proposed resolution

For `/arch`:

1. **A register row** in `safety-invariants.md` §4 for the class, with the four
   instances as its calibration, status `gated (in-crate, backend only)` and the
   fence cited as its detection proof (per 0768's bar).
2. **Decide the scope question the in-crate fence cannot**: the fence is a
   backend lint over a hand-named file set. The class is not backend-specific —
   the same move is available anywhere a derived analysis result exists and a
   node/entry/name is in hand (typecheck's ownership walk, int's display
   resolution). Whether the obligation is stated once architecturally (a
   Principle-25 corollary: *a narrowing consults the derived answer, never the
   shape it happens to hold*) or left as per-crate fences is `/arch`'s call.
3. **Record what the fence is BLIND to** (0768's per-row blind-spot note): it
   sees only `matches!` — not an `if let`, not a `match` arm, not a shape test
   written over a different type that a `MonoExpr` was projected into; and it
   sees only the four named files.

## Context

- FIXME 0781 — the fourth instance; the fix routed all five gates onto one
  three-point provenance lattice read at two thresholds.
- FIXME 0776 (`target: /arch`) — the seam × obligation register row this may
  fold into.
- FIXME 0768 (`target: /arch`) — register statuses require a cited detection
  proof; this row ships with one.
- `crates/cranelisp-backend/CLAUDE.md` §"RC-emission gates that are ONE
  predicate, not per-site syntax".
