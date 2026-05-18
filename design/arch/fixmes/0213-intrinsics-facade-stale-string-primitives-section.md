---
number: 0213
target: /design (intrinsics)
filed_by: /sprint
filed_at: 2026-05-17
sprint_filed: 68
refers_to: design/arch/facades/intrinsics.md §"String primitives" (lines 124-168), crates/cranelisp-intrinsics/src/lib.rs (lines 8-19), crates/cranelisp-intrinsics/public-api.txt
status: open
---

# `facades/intrinsics.md` §"String primitives" section is stale post-S67

## Issue

`facades/intrinsics.md` §"String primitives (allocator + reader + user-callable ops; physically-here-until-FIXME-0180)" at lines 124-168 describes the 15 user-callable `str_*` extern fns (`str_concat`, `str_eq`, `str_len`, etc.) as "physically here pending FIXME 0180". But:

- S67 W3 already relocated those 15 fns to `cranelisp-primitives::string` (FIXME 0180 closed).
- `cranelisp-intrinsics/src/lib.rs` lines 8-19 confirm the relocation.
- `cranelisp-intrinsics/public-api.txt` does NOT contain `str_concat`/`str_eq`/`str_len`/etc.
- The facade's own §"Sprint 67 disposition snapshot" (line 388) correctly says "Relocated to `cranelisp-primitives` at Wave 3: user-callable `str_*` family (15 fns) + `vec-len`."

The facade contradicts itself: §"String primitives" describes a pre-S67 state; §"Sprint 67 disposition snapshot" describes the post-S67 state.

Wave 6 `/review (intrinsics)` flagged this as Important — the §"String primitives" section is now actively misleading.

## Proposed resolution

`/design (intrinsics)` reworks the §"String primitives" section:

- Drop the 15-fn extern table entirely.
- Replace with a one-paragraph historical note + pointer: "User-callable `str-*` ops relocated to `cranelisp-primitives::string` at S67 W3 — see `facades/primitives.md` §"Primitives inventory" for the canonical home."
- Keep the `heap_string` allocator/reader (`heap_alloc_string`, `string_read`, `alloc_string`, `read_string_as_str`, `HeapString` type) — these ARE the current baseline content and DO remain in `cranelisp-intrinsics`.
- Rename section header to "Heap-string allocator + reader (backend-emitted-call)" or similar to reflect the post-S67 content.

## Operational implication / Context

Not blocking S68 deliverables. Facade-doc drift; should be fixed in S69. The misleading section could cause future readers to incorrectly expect `str_*` fns to be accessible from `cranelisp-intrinsics` Rust paths.
