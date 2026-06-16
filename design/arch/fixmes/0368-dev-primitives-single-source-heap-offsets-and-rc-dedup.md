---
number: 0368
target: /dev
filed_by: /sprint
filed_at: 2026-06-16
sprint_filed: 83
refers_to: audits/primitives-2026-06-14.md (HIGH-1, MED-1), crates/cranelisp-primitives/src/marshal.rs (:27-33, :129), crates/cranelisp-primitives/src/string.rs, crates/cranelisp-types/src/heap.rs (HeapHeader::SIZE/RC_OFFSET)
status: open
---

# cranelisp-primitives: single-source the heap-layout offsets + reconcile the RC-inc helpers

## Issue (0101 audit — primitives, 2026-06-14)

Two findings from `audits/primitives-2026-06-14.md` warrant tracked remediation (the audit doc holds the full detail + the MED-2/LOW items):

- **HIGH-1 — `marshal.rs` hardcodes heap-layout offsets** (`:27-33` `PAYLOAD_OFFSET=16`/`FIELD0=24`/`FIELD1=32`, `:129` a magic `.add(8)` for RC) that have a canonical home in `cranelisp-types::HeapHeader::{SIZE, RC_OFFSET}` (statically asserted). This contradicts the crate's own single-source discipline that `string.rs`/`vec.rs`/`int.rs` correctly follow — the one re-entry of the sketch `codegen.md` "duplicate heap classification" HIGH pattern. Single-source these consts from `cranelisp-types::HeapHeader` (Principle 7); add compile-time asserts mirroring the sibling files.
- **MED-1 — RC-inc helpers duplicated/divergent:** `marshal.rs::shallow_rc_inc` (non-atomic `*rc_ptr += 1`) vs `string.rs::string_identity` (atomic `fetch_add`), neither sourced from the blessed `cranelisp_intrinsics::rc`. **Latent data-race hazard now that lenient-eval sparks are live** (S25). Source both from the intrinsics RC helper, or document why a non-atomic path is sound. The atomic-vs-non-atomic policy may need an `/arch` note (cross-ref Principle 7 + the runtime RC model).

## Proposed resolution
`/dev` narrow-deployed on `cranelisp-primitives`: single-source the offsets from `HeapHeader`; unify the RC-inc path on `cranelisp_intrinsics::rc` (or justify the divergence). Unit test per fix. If the RC atomicity policy needs an architectural ruling, file a sub-FIXME `target: /arch`.

## Context
0101 audit pass (post-D43 crates). Forward-flow remediation; not S83-blocking (the crate is in strong conformance otherwise — backend severance, static PRIMITIVES_TABLE, into_concrete mount all faithful). MED-2 (extern_shims hand-maintained registry) + LOW-1/LOW-2 remain recorded in the audit doc for opportunistic pickup.
