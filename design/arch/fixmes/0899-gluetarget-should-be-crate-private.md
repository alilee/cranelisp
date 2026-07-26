---
number: 0899
target: /dev
filed_by: /review
filed_at: 2026-07-26
sprint_filed: 118
refers_to: src/result_owner.rs::GlueTarget (:47)
status: open
---

# `GlueTarget` is `pub` but crosses no boundary — downgrade to `pub(crate)`

## Severity

Important

## Issue

`src/lib.rs` makes `result_owner` a `pub` module with an inline justification:
`OwnedProgramResult` rides the binary-facing `EvalResult::Val` /
`CompilerSession::trampoline` surfaces that `src/main.rs` consumes. That
justification holds for `OwnedProgramResult` — but not for `GlueTarget`
(`src/result_owner.rs:47`), which is declared bare `pub` while appearing in no
public signature: its only constructor is `pub(crate)`, the field holding it
is private, the trait returning it (`ResultGlueResolver`) is `pub(crate)`, and
no file outside `result_owner.rs` names it. Every `pub` (not `pub(crate)`)
requires a justification for crossing the crate boundary
(`.claude/commands/review.md` §Quality checks; Principle 2 — narrow
interfaces); `GlueTarget` has none and needs none.

Found by the delegated Codex reviewer (codex-cli 0.145.0); the adjudicator
verified there are zero references outside the module.

## Proposed resolution

Declare `GlueTarget` `pub(crate)` (its siblings `SessionGlueResolver`,
`StartupResultExit`, `ResultGlueResolver` already are). No behaviour change;
`OwnedProgramResult`'s private field does not leak it.

## Context

S118 W4 change-set review. The int surface has no `public-api.txt` baseline,
so item-level `pub` discipline inside the binary crate is the only guard
against surface creep here.
