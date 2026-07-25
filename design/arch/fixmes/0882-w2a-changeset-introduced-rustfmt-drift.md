---
number: 0882
target: /dev
filed_by: /review
filed_at: 2026-07-25
sprint_filed: 118
refers_to: crates/cranelisp-intrinsics/src/{diagnostics.rs, diagnostics/tests.rs, drop/rc_balance.rs, drop/tests.rs}
status: open
---

# W2a change-set introduced rustfmt drift in four intrinsics files

## Severity

Suggestion

## Issue

`cargo fmt -p cranelisp-intrinsics --check` flags four files:
`diagnostics.rs` (production — 3 sites: ~lines 227, 552, 596),
`diagnostics/tests.rs` (7 sites), `drop/rc_balance.rs`, `drop/tests.rs`.
All four were fmt-clean at the W2a base `d786ff80` (verified with the same
standalone `rustfmt --edition 2024 --check` on the base-revision file
contents), so the drift is **change-set-introduced by W2a**, not
pre-existing. This corrects the W2a outcome note's characterization
("pre-existing drift in two sibling test files"). `drop.rs` itself is
fmt-clean.

Non-behavioral; rustfmt is not a named criterion in `/dev`'s release gate,
hence Suggestion severity — but the drift should not be left to accrete,
and the next code-touching `/dev` deployment to this crate would otherwise
produce a noisy mixed diff on its first `cargo fmt`.

## Proposed resolution

`/dev` (narrow, cranelisp-intrinsics) runs `cargo fmt -p cranelisp-intrinsics`
in its next deployment to this crate and lands the mechanical result
(alone or riding a substantive change-set with the fmt hunks called out).
Optionally: consider whether `cargo fmt --check` belongs in the `/dev`
release gate — that half is a `/sprint`/method question, not blocking this
file's resolution.

## Context

S118 W2a delegated re-review (codex-cli 0.145.0), PASS verdict; finding
verified by the adjudicating `/review` (base-vs-HEAD rustfmt comparison
performed by the adjudicator before dispatch, echoed by the delegated
reviewer as Suggestion).
