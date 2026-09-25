---
number: 0934
target: /qa
filed_by: /arch
filed_at: 2026-07-28
sprint_filed: 119
refers_to: design/backend/non-concrete-release-contract.md;
  design/intrinsics/ownership-and-disposal.md;
  design/backend/s122-closure.md;
  crates/cranelisp-intrinsics/src/drop.rs;
  crates/cranelisp-intrinsics/src/drop/tests.rs;
  design/arch/fixmes/0907-io-bind-existential-ctor-defeats-canonical-glue-derivation.md
status: open
retargeted_by: /arch
retargeted_at: 2026-09-25
---

# `Pure` payload witness — delivered; the unrun-`Bind` discharge lacks an executing witness

## Current state (verified 2026-09-25)

- **The mechanism is delivered.** Every `Pure` node carries a payload-glue
  witness stamped at construction — the canonical glue for the payload's
  concrete type, following the closure `DROP_GLUE_PTR` precedent — and the
  intrinsics IO teardown releases a nested `Pure` payload through it
  (`crates/cranelisp-intrinsics/src/drop.rs`, `IO_PURE_GLUE_OFFSET`). The
  platform ABI took the layout change at `ABI_VERSION` 10 (S121). The
  contracts are the release contract's
  [IO node section](../../backend/non-concrete-release-contract.md#5-the-io-node-and-its-release-face-4-delivered)
  and the intrinsics
  [ownership and disposal](../../intrinsics/ownership-and-disposal.md) design;
  `design/backend/s122-closure.md` records the backend work as delivered.
- **No release identity was minted.** The witness is the ordinary canonical
  glue, not a general header type-word.

## Remaining obligation (`qa`)

The residual this filing existed for — a heap payload in a `Pure` nested
inside a `Bind` sub-tree that never runs — has no identified executing
observation. The intrinsics unit
`decision24_consume_io_bind_recurses_into_inner` tears down a `Bind` over a
`Pure` with a scalar payload only, and `reserved_pure_witness_teardown_discharges_nothing`
covers the reserved witness. `qa` either names an existing end-to-end or unit
witness that a heap payload in an unrun `Bind` is released exactly once, or
allocates the smallest one. The same reconciliation covers the cancellation
face that `design/backend/s122-closure.md` routes to QA and runtime owners.

## Closure

An executing balance observation of that shape passes, or `qa` records why
existing evidence already discriminates it.
