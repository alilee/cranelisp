---
number: 0775
target: /dev
filed_by: /review
filed_at: 2026-07-21
sprint_filed: 115
refers_to: crates/cranelisp-typecheck/src/program/mono_collect.rs:778-783 —
  `resolve_auto_curry` is a convenience wrapper hard-coding
  `AutoCurryDrain::Final`, so a new drain seam silently opts OUT of the
  deferral discipline
status: open
---

# The auto-curry settlement discipline defaults to `Final` — the polarity that can strand a carrier

## Severity

**Important** (P18 — enforce invariants structurally).

## Issue

The S115 W4 `'='` producer fix introduces a real settlement discipline:

```rust
pub(crate) fn resolve_auto_curry(&self, state: &mut CheckState) {
    self.resolve_auto_curry_with(state, AutoCurryDrain::Final)
}
```

`AutoCurryDrain::Final` is the polarity that says *"this seam is settled; no
entry is held back"*. Its own doc comment states the drain "runs at SIX seams,
and they are not equivalent" — and then makes the non-deferring one the default
reachable under the short, obvious name. A seam added later calls
`resolve_auto_curry` because that is what the function is called, and thereby
asserts settlement it has not established. The failure mode is silent: an
unresolved trait-operator curry takes the `Final`-unresolved fallback
(`ApplyRef::ViaCallee`), which is only diagnosed one crate away, as the
backend's located producer-contradiction.

This is the shape Principle 18 exists to prevent: the safe answer should be the
one you get by default, or there should be no default at all.

The seam classification is also carried only in prose. Today's mapping —
`body.rs:88`, `body.rs:441` → `Deferrable`; `impl_check.rs:762`,
`impl_check.rs:1024`, `monomorphise.rs:856`, `finalize.rs:607` → `Final` — is
justified in a doc comment ("recheck-scoped seams, whose resolution maps and
module scope are swapped"), with nothing structural holding a new site to it.

## Proposed resolution

Delete the defaulting wrapper: make `drain: AutoCurryDrain` a **required**
parameter at every call site (rename `resolve_auto_curry_with` →
`resolve_auto_curry`). Six call sites is a small, one-time edit, and it forces
each new seam's author to answer "is this seam settled?" at the point where they
alone can answer it.

Optional second step, if the seam set grows again: give the discipline a name
per seam rather than a boolean-shaped enum (see FIXME 0776, `target: /arch`, on
the settlement-seam class).

## Context

- `design/backend/s115-carrier-and-rc-sweep.md` §1.3 — the boundary rule this
  discipline enforces ("never transport a trait-method-decl FQ as a dispatch
  carrier").
- The fix itself is sound and verified: `(defn g [x] (= x))` /
  `(defn main [] (Pure (if ((g 3) 3) 5 0)))` is the GOT-terminal error at
  `d4efdf08~1` and exits 5 at `d4efdf08`; the drain is idempotent (both
  `deferred_auto_curry` and `pending_auto_curry` are `mem::take`n, so a second
  run is a no-op); the multi-sig-return-feeding-the-operand and
  curry-inside-a-multi-sig-clause shapes both probe clean. This FIXME is about
  the discipline's *enforcement*, not its correctness.
