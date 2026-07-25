---
number: 0881
target: /design
filed_by: /review
filed_at: 2026-07-25
sprint_filed: 118
refers_to: design/intrinsics/diagnostic-modes.md §7.1 + §10 (diagnostics protocol row) vs crates/cranelisp-intrinsics/src/diagnostics.rs (PLANT LazyLock, ~line 493)
status: open
---

# Plant config-error timing: design says "before allocation", implementation aborts at the first hook call

## Severity

Important

## Issue

`diagnostic-modes.md` §7.1 states that unknown/empty/multiple plant spellings
"are a hard test-configuration error **before allocation**; they never become
a partial plant", and §10's `diagnostics` (protocol) matrix row repeats
"a hard config error **before** any allocation". As implemented, the parse
lives in the `PLANT` `LazyLock`, forced at the FIRST `test_fault_event` call —
which is the `PostAlloc` of the process's first allocation. A mis-armed child
therefore aborts after one allocation exists (header initialized, counters
bumped), though provably **before any `PlantState` is constructed and before
any action is applied** — the /dev comment at the static documents this
honestly, and the invariant that matters ("never a partial plant") holds.
`crates/cranelisp-intrinsics/CLAUDE.md` describes the protocol as following
§7.1 without noting the delta.

The unit row `unknown_empty_or_multiple_spellings_are_configuration_errors`
pins the implemented (first-hook-call) behavior, so the design text and the
committed evidence currently disagree on the letter.

## Proposed resolution

`/design` rules one of:

1. **Accept the weaker contract** (recommended by the implementation's
   rationale: forcing the parse earlier means an extra check on the allocation
   hot path for no additional guarantee) — amend §7.1 and the §10 row to
   "before any plant state exists and before any action is applied" and note
   the first-hook-call timing; or
2. **Require literal pre-allocation timing** — file `target: /dev` for a
   dedicated pre-main/entry validation seam (and say where it lives, since
   the crate has no startup hook today).

Either way the disposition should be recorded so `/qa`'s 0857 regrade grades
the config-error negative at the tier the design actually states.

## Context

S118 W2a delegated review (codex-cli 0.145.0) of the Track A change-set;
finding verified by the adjudicating `/review` against `diagnostics.rs` and
the design text. /dev flagged this deviation in the W2a outcome block
(`sprints/SPRINT.md`) but no durable design disposition existed — this FIXME
is that record. Principle 18 (enforce invariants structurally) / Principle 26
(record from settled state).
