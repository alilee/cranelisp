---
number: 0887
target: /testing
filed_by: /review
filed_at: 2026-07-26
sprint_filed: 118
refers_to: tests/cache.rs, tests/mode_gating_guard.rs, tests/slist_sconcat_ownership_0835.rs
status: open
---

# Ambient rustfmt drift in three e2e test files (not change-set-introduced)

## Severity
Suggestion

## Issue

`cargo fmt --check` at HEAD (`3b4acc01`) reports drift in three e2e test
files: `tests/cache.rs` (three hunks), `tests/mode_gating_guard.rs` (one
hunk), `tests/slist_sconcat_ownership_0835.rs` (two hunks). All hunks are
mechanical re-flows (collapsing short multi-line expressions rustfmt now
prefers on one line).

This was found while gathering gate evidence for the S118 W2b re-review of
the runtime pair. It is NOT introduced by that change-set: the three files
were last touched at `d1c34699` (S117 close) and `9d06cbfc` (S118 W1), and
`3b4acc01` touches neither `tests/` nor any file that fails the check
(`crates/cranelisp-primitives/src/marshal/tests.rs` and the crate
`CLAUDE.md` are clean). The likely cause is a rustfmt toolchain update
changing preferred formatting since those commits landed.

## Proposed resolution

`/testing` runs `cargo fmt` over the three files (or the workspace) in an
opportunistic commit — mechanical, no semantic change. Worth landing before
the W8 Phase-5 gate's full-suite run so the gate's `cargo fmt --check` leg
is clean without a last-minute scramble.

## Context

Same class as resolved FIXME 0882 (S118 W2a intrinsics fmt drift), except
this instance predates the reviewed change-set, so it is filed as ambient
hygiene rather than a change-set finding. Verified with
`rustfmt`-via-`cargo fmt --check` at HEAD, 2026-07-26.
