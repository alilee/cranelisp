---
number: 0369
target: /arch
filed_by: /sprint
filed_at: 2026-06-16
sprint_filed: 83
refers_to: audits/intrinsics-2026-06-14.md (HIGH-1, HIGH-2, MED-2), design/arch/bounded-contexts.md §4b, crates/cranelisp-intrinsics/src/lib.rs (//! preamble), crates/cranelisp-intrinsics/src/catalog.rs
status: open
---

# cranelisp-intrinsics: reconcile the catalog count + de-stale BC §4b against shipped code

## Issue (0101 audit — intrinsics, 2026-06-14)

Two HIGH doc-accuracy findings from `audits/intrinsics-2026-06-14.md` (the audit doc holds full detail):

- **HIGH-1 — three-way catalog entry-count disagreement** (Principle 7 single-source violated on the self-doc surface): `catalog.rs` says **29** (correct, matches the table literal + tests), `lib.rs` `//!` says **27**, BC §4b says **27/28** (invariants 11/12/13). Root: `cranelisp_ivar_dealloc` is the +1 core entry the BC narrative + lib.rs preamble drop. Reconcile all three to **29**.
- **HIGH-2 — BC §4b invariants 11/13/14 are stale-against-shipped:** they describe LANDED, unit-tested features as "TARGET-STATED / pending / owed pre-existing defect" — the catalog (309 LOC, exists), `catch-runtime-error` + the fork-join ferry (built in `panic.rs`/`ivar.rs`/`io.rs`), and the platform-Effect fault guard (built in `io_guard.rs`, wired into the EFFECT arm). The BC's "neither boundary ferries the slot … pre-existing defect" sentence is now factually false. Sweep §4b TARGET→as-built.
- **MED-2 — `IntrinsicEntry::is_runtime`** unused `pub` field — justify-or-drop.

## Proposed resolution
`/arch`: reconcile the count to 29 across BC §4b (and request `/dev` fix the `lib.rs` `//!` preamble count, or do it if within the doc-surface remit); sweep §4b invariants 11/13/14 to as-built; dispose of `is_runtime`. This is documentation/boundary-narrative reconciliation, no code behavior change.

## Context
0101 audit pass. The crate's BEHAVIOR conforms (Decision-0048 asymmetry, consuming convention, no-types-at-surface, JITBuilder::symbol narrowing all match) — these are self-doc/BC drift, not defects. Paired with FIXME 0370 (the /dev monolith-decomposition half). MED-1/LOW items recorded in the audit doc.
