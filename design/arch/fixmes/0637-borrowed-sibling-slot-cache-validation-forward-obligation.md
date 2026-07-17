---
number: 0637
target: /design
filed_by: /sprint
filed_at: 2026-07-17
sprint_filed: 111
refers_to: crates/cranelisp-types/src/module.rs:2134 (borrowed_sibling_slot, PrimitiveBody::Extern);
  crates/cranelisp-backend/src/cache/serialize.rs (deserialise_meta_with_build_id validation);
  callable_got_slot(); S111 CS-2 /review suggestion S-2
status: open
---

# `borrowed_sibling_slot` — a 2nd persisted GOT index the CS-2 cache-load validation does not cover (forward obligation, no live hole)

## Context

CS-2 (S111) added cache-load-seam validation of persisted GOT slots: `deserialise_meta_with_build_id`
checks `callable_got_slot() < GOT_TABLE_SIZE` for every symbol, violation ⇒ `CacheStale::GotSlotOutOfRange`
→ recompile (the one diagnosed error at the untrusted cache boundary).

`callable_got_slot()` covers the four slot-carrying kinds (UserFn-Concrete, Primitive-Extern,
Constructor, PlatformEffect). But `borrowed_sibling_slot` (`module.rs:2134`, `PrimitiveBody::Extern`)
is a **second persisted GOT index** that `callable_got_slot()` does NOT return — so it escapes the
new validation.

**No live hole today:** S102 made the borrowed-convention sibling carrier-only — zero production
readers. So a corrupt/out-of-range sibling from a bad cache reaches nothing.

## Forward obligation

The moment the borrowed-convention sibling gains a real consumer (a codegen read `base + slot*8`),
an out-of-range sibling from a corrupt cache becomes genuine emitted-GOT UB with no `assert!` in that
path. **Extend the `deserialise_meta` validation to include `borrowed_sibling_slot`** (either fold it
into `callable_got_slot()`'s coverage or add a sibling check) as part of whatever change lands that
consumer. Natural co-landing: the ownership/borrowed-convention track (cf. the schema-20 work, or a
future borrowed-sibling consumer sprint).
