---
number: 0371
target: /arch
filed_by: /sprint
filed_at: 2026-06-16
sprint_filed: 83
refers_to: audits/platform-2026-06-14.md (MED-3), crates/cranelisp-backend/src/schema.rs (generate_schema), crates/cranelisp-platform/src/schema.rs (Schema::parse), design/arch/platform-interface.md
status: open
---

# platform: pin the /platform-schema grammar generator↔parser agreement (round-trip corpus)

## Issue (0101 audit — platform, 2026-06-14)

The single latent **correctness** risk in `cranelisp-platform` (the crate is otherwise 0-HIGH, conforms to all 9 BC §5 invariants + the three-exports model). From `audits/platform-2026-06-14.md` MED-3:

The `/platform-schema` artifact grammar is **replicated across two crates that cannot depend on each other** — `cranelisp-backend::generate_schema` EMITS it, `cranelisp-platform::Schema::parse` CONSUMES it — and **nothing pins their agreement**. The parser's tests use hand-written literals, NOT generator output, so grammar drift escapes BOTH test suites AND the layout-hash gate (the hash is computed over the generated text; if the parser silently mis-reads a drifted grammar, the mismatch isn't caught). A generator/parser divergence would surface only as a runtime field-read error against a live platform DLL.

## Proposed resolution
`/arch` (owns the cross-crate contract): establish a **shared round-trip corpus** — canonical schema samples that `generate_schema` produces AND `Schema::parse` consumes, asserted equal, runnable from a test both crates can reach (a `cranelisp-types`-hosted fixture, or a workspace integration test). Pins the grammar agreement so drift fails a test instead of a production DLL load. Coordinate the home with `/qa`.

## Context
0101 audit pass. The 0229–0235 + 0289 cascade is confirmed fully closed by the audit; this is the remaining grammar-agreement gap. Forward-flow; low frequency but real correctness risk. MED-1/MED-2/MED-4/LOW (platform.md staleness → see FIXME 0372; R1 gate residue; declare_platform! extract; cosmetics) recorded in the audit doc.
