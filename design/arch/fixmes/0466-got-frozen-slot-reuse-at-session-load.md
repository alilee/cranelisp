---
number: 0466
target: /design
filed_by: /sprint
filed_at: 2026-07-02
sprint_filed: 100
refers_to: design/arch/ownership-inference.md §5.6, crates/cranelisp-types/src/module.rs (allocate_got_slot, next_got_slot serde), design/int/ (session load path)
status: deferred
---

# GOT slot-hole reclamation at session load — deferred indefinitely (trigger-based)

## Issue

Under the R3 ABI-epoch slot-versioning model (`ownership-inference.md` §5.6), an
ABI-changing REPL redefinition allocates a fresh GOT slot and freezes the old one.
Because REPL definitions persist (regenerated backing file + `.o`/`.meta.json` via the
nice-worker path) and the `.meta.json` must record slot numbers **faithfully** — slot
indices are baked into the `.o`'s machine code (`load(slab_base + slot*8)`), so
`.meta`/`.o` renumbering desync is impossible by construction — the superseded slot
survives restart as a **permanent hole**: `next_got_slot` is a serialized monotone
high-water mark (`module.rs:135`, allocator at `:609`) with no free list, and a valid
cache reloads its holes indefinitely. Compaction only ever rides the cache-invalid
full-recompile path.

Reuse at the session boundary would be sound: after restart no referent survives (heap
gone, old body absent from the rewritten `.o`, cross-module stale `.o`s conservatively
invalidated by the backing-file source-hash change per §5.1). The optimisation would be
load-time reclamation: scan loaded entries' slots against the high-water mark, rebuild a
free list, and enforce reuse-only-at-load (never in-session while a freeze is live).

## Proposed resolution

Do **not** implement now. Cost of the hole is 8 bytes of GOT slab per ABI-changing
*persisted* redefinition (body-only edits take the §5.4 summary-diff fast path and keep
their slot); a pathological session wastes a few KB, recovered on any genuine recompile.
The reclamation invariant would be a new correctness obligation on the redefinition
subsystem — the hottest new machinery in the memory-model design — for negligible return.

If ever actioned: load-time free-list reconstruction in the session cache-load path
(`/int` half of the R3 machinery), with the invariant that in-session allocation never
reuses a frozen slot.

## Operational implication / Context

**Deferred indefinitely by user direction (S100 design discussion, 2026-07-02).**
Trigger to reopen: measured GOT slab growth from redefinition churn actually mattering
(e.g. long-lived dev sessions with thousands of ABI-changing redefinitions, or a future
GOT-size-sensitive deployment mode). Until that trigger fires, the standing design pin
(spine §5.6) is: holes persist across restarts by design; the persisted `next_got_slot`
high-water mark is the freeze boundary — new sessions allocate strictly above anything
any cache could reference.
