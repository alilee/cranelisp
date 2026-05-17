---
number: 0206
target: /design (backend)
filed_by: /dev (int)
filed_at: 2026-05-16
sprint_filed: 67
refers_to: design/arch/facades/backend.md §"Intrinsic registration" + §"IntrinsicSymbol", crates/cranelisp-backend/src/jit.rs::intrinsic_symbols, design/arch/decisions/0040-runtime-trace-io-trace-relocate-to-int.md
status: open
---

# Refresh `facades/backend.md` for the deleted 12 trace `IntrinsicSymbol` entries

## Issue

Sprint 67 Wave 4 — FIXME 0197 — deleted the 12 `cranelisp_trace_*`
`IntrinsicSymbol` entries from
`crates/cranelisp-backend/src/jit.rs::intrinsic_symbols()` per
Decision 40 §"Backend surface" (Path B1). Registration of those
symbols now lives in
`src/session_v4.rs::int_intrinsics()` (per FIXME 0202 / S67 W4).
`facades/backend.md` §"Intrinsic registration" (or whichever section
inventories the symbols backend contributes to the JIT) needs to
reflect that backend no longer names the 12 trace symbols.

Backend's `cranelisp-intrinsics` Cargo dependency persists (the
non-trace intrinsics are still backend-registered); only the 12 trace
lines went.

## Proposed resolution

Edit `design/arch/facades/backend.md`:

1. The §"Intrinsic registration" inventory (or equivalent table)
   removes the 12 `cranelisp_trace_*` entries that backend used to
   contribute. Cite `src/session_v4.rs::int_intrinsics()` as the new
   registration site (and Decision 40 §"Backend surface" for the
   rationale).

2. If the facade carries a forbidden-patterns clause (per FIXME 0178's
   architectural-rationale work), confirm the rule "backend MUST NOT
   register trace symbols" is in place.

## Operational implication / Context

**Sequencing**: Lands after FIXME 0197 (the implementation deletion in
S67 W4). `/dev (backend)` does not edit `facades/backend.md`
(file-ownership boundary).

**Public-API impact**: The deletion is inside a fn body
(`intrinsic_symbols()`) — `cargo public-api` does not show the diff.
The facade refresh is documentation-only.

**Unit-of-work**: small (~5-10 lines of facade table).

**Cascade closure**: Paired with FIXME 0205 (int facade refresh) closes
the Decision-40 facade-doc work for S67 W4.
