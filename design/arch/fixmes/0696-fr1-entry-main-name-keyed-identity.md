---
number: 0696
target: /dev
filed_by: /review
filed_at: 2026-07-20
sprint_filed: 114
refers_to: crates/cranelisp-backend/src/compiler/rc_emission.rs::protect_return_value (F-R1 suppression predicate)
status: open
---

# F-R1 suppression keys on the bare name "main" — name-as-identity, not the entry contract

## Severity
Suggestion

## Issue

The F-R1 suppression fires on `current_fn_name == "main"` + nullary + tail +
fresh construction (`rc_emission.rs:303-309`). Any module's nullary fn named
`main` matches, but the licensing rationale ("the entry trampoline consumes
the result exactly once") only holds for the actual program entry. Verified
behavior at the boundary: entry `main` balances (2/2); a non-`main` fn with
the identical shape keeps the protect (2/1 — the pre-existing G2/item-26
class, untouched as the plan §2.1 fence requires). The over-match stays
SAFE only because `body_is_fresh_construction` independently guarantees scope
cleanup cannot touch the fresh box — i.e. the mechanism that makes it correct
is freshness, not the trampoline contract the comment claims as the sole
license. Name-keyed identity is the 0632 class (`is_self_call`'s own rustdoc
at `fn_compiler.rs:1758` warns against it) and Principle 19 territory.

## Proposed resolution

When W-B5 collapses the fn-return patches, key the suppression on the entry
contract (the module+symbol the trampoline actually invokes, available from
the compile context) rather than the bare name — or, if freshness is the real
license, state that and consider the general fresh-construction return
(item-26) as the principled fix, superseding the main-special-case entirely.
No behavioral urgency: current over-match is leak-fixing, never unsafe.

## Context

Found by /review W4 (dispatch priority 3). Rides naturally with the W-B5
change-set (same three-patch flow).
