---
number: 0461
target: /design
filed_by: /dev
filed_at: 2026-06-28
sprint_filed: 95
refers_to: design/platform/platform-dlls.md §"CLIO constructors", design/platform/platform.md §"Constants"
status: open
---

# Platform design docs predate the slice-3 capacity carrier (and the ABI-v4 fn-name field)

## Issue

The S95 Wave-2 capacity carrier landed in `cranelisp-platform`:

- new constructor `CLIO::effect_on_resource_with_capacity(token, capacity, f)`
  (additive sibling of `effect_on_resource`, which now lowers to
  `…_with_capacity(token, 1, f)`);
- new ungated const `IO_EFFECT_CAPACITY_OFFSET = 32` (the `IO_TAG_EFFECT` node
  payload widens 32 → 40, append-only);
- a new blocking test leaf `platforms/pool-demo` (`pool-read`/`pool-write`/`pool-log`,
  all declaring `(token, capacity)` via the new constructor).

The canonical design record for all of this is **current**: `io-trampoline.md`
§13.2/§13.7 (the constructor + offset + node-widen) and `effect-concurrency.md`
§8.1 (the carrier + first-writer-wins). The source rustdoc in
`crates/cranelisp-platform/src/lib.rs` (the retired-facade canonical surface) and
`public-api.txt` are updated in the same change-set.

The two `/design`-owned platform docs lag, but the lag is **pre-existing and
broader than this change**:

- `platform-dlls.md` lists `effect_on_resource` but not `effect_on_resource_with_capacity`.
- `platform.md` §"Constants" lists `IO_EFFECT_RESOURCE_OFFSET` but not
  `IO_EFFECT_FN_NAME_OFFSET` (ABI v4, FIXME 0327) nor the new `IO_EFFECT_CAPACITY_OFFSET`,
  and still states `ABI_VERSION = 5` (live value is 7).

## Proposed resolution

When `/design` (platform) next sweeps these docs, add the `effect_on_resource_with_capacity`
constructor + `IO_EFFECT_CAPACITY_OFFSET` to the constant/constructor inventories,
note the 40-byte `IO_TAG_EFFECT` payload (append-only), refresh the stale
`ABI_VERSION`/`IO_EFFECT_FN_NAME_OFFSET` entries, and mention `platforms/pool-demo`
alongside `test-capture` as a blocking test leaf. No source change is implied —
this is documentation reconciliation only; the implementation + the canonical
io-trampoline/effect-concurrency design already agree.

## Operational implication / Context

Low urgency: `platform.md`/`platform-dlls.md` are not the constructor-surface
source of truth (rustdoc + `io-trampoline.md` §13 are), and they already drifted
on the prior ABI-v4 fields. Filed for completeness so the platform docs catch up
in one pass rather than accreting further drift.
