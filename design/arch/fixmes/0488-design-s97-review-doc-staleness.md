---
number: 0488
target: /design
filed_by: /sprint
filed_at: 2026-07-01
sprint_filed: 97
refers_to: design/backend/ring2-rc.md §3.3, design/intrinsics/reactor.md §8.2
status: open
---

# S97 /review-flagged design-doc staleness (2 spots)

## Issue

Two /review findings from the S97 Wave-3 drains are doc-only staleness (Important/Minor, non-blocking) with no durable record beyond the sprint log:

1. **`design/backend/ring2-rc.md §3.3`** (Important, /review of `386b07b`) — line ~308 + the table rows ~274–276 still describe `emit_vec_drop_if_temporary`'s **old unconditional** behaviour. The RC-corruption fix changed it to **rc-checked** (`emit_vec_rc_dec_with_drop`, free only when `old_rc==1`); the new semantics are documented only in the code doc-comment + a §5.5 cross-ref, not where §3.3 canonically describes the function. Update §3.3 to match shipped code.

2. **`design/intrinsics/reactor.md §8.2`** (Minor, /review of `787771a`) — §8.2 lists `timer_heap` as an armed-ness source, but the 0479 code checks `timer_waiters` (correct — `timer_heap` holds tombstones; checking it literally would risk a false-negative missed-deadlock). Reconcile §8.2 text to say `timer_waiters`. (Note: `reactor.md` relocated `design/int/` → `design/intrinsics/` in the S97 ownership tidy.)

## Proposed resolution

Wording-only edits to bring both sections into line with shipped code. No behaviour change.
