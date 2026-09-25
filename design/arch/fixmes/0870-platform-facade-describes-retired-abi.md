---
number: 0870
target: /dev
filed_by: /sprint
filed_at: 2026-07-25
sprint_filed: 118
refers_to: crates/cranelisp-platform/src/lib.rs;
  crates/cranelisp-platform/src/concurrency.rs;
  crates/cranelisp-platform/src/poll_support.rs;
  crates/cranelisp-platform/src/declare.rs;
  crates/cranelisp-platform/src/tests.rs;
  crates/cranelisp-platform/CLAUDE.md
status: open
---

# Platform facade rustdoc describes a retired ABI — repaired except two test comments

Crate in scope: `cranelisp-platform`. Documentation repair only; no API
change is authorised. The originating recommendation is the S117 platform
audit's R1, accepted by the user at S118 Phase 1; the audit report is in Git
history.

## Current state (verified 2026-09-25)

The crate-root and module rustdoc now match the source:

- `ABI_VERSION` is 11, and `concurrency.rs` states the host-reactor types are
  core (ungated) at that version;
- `poll_support.rs` describes the core, ungated poll-leaf suite;
- schema validation is the layout-hash gate (`declare.rs`);
- `HostCallbacks` is documented under "Current shape (ABI v11)" as permanently
  two fields, `alloc` and `alloc_with_tag`, with the former
  `validate_schema` channel removed;
- the crate memory carries no stale-phrasing warning.

The version history in the `ABI_VERSION` rustdoc is a bump log, not a stale
claim.

## Remaining obligation (`dev`, platform)

Two unit-test comments in `crates/cranelisp-platform/src/tests.rs` still
describe the current shape as ABI v3: the `HostCallbacks::alloc` spec comment
cites the rustdoc section as `§"Current shape (ABI v3)"`, and the T27 comment
calls the two-field struct "ABI v3". Re-point both to the current section and
version.

## Closure

Both comments are corrected; `dev` deletes this filing.
