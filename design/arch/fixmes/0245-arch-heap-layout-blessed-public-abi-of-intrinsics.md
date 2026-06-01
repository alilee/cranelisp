---
number: 0245
target: /arch
filed_by: /sprint
filed_at: 2026-05-31
sprint_filed: 73
refers_to: design/arch/facades/intrinsics.md §"Heap allocator"/§"Vec primitives"/§"Consumed surface", design/arch/facades/primitives.md §"Consumed surface", design/arch/bounded-contexts.md §4a (Primitives)/§4b, crates/cranelisp-intrinsics/src/{heap_string,vec_runtime}.rs, crates/cranelisp-primitives/src/{string,vec}.rs, crates/cranelisp-intrinsics/public-api.txt, principles/07-single-source-of-truth.md
status: open
---

# Heap/Vec layout is `cranelisp-intrinsics`' blessed public ABI; primitives consumes it (no duplication)

## Decision (user-arbitrated 2026-05-31, S73 Phase 1 — option A)

The heap-object layout owned by `cranelisp-intrinsics` (the `HeapString` field
offsets and the Vec runtime's layout offsets) is a **stable, pinned public ABI**
of `cranelisp-intrinsics`. `cranelisp-primitives` (a legitimate Rust consumer of
intrinsics — see FIXME 0244 re the backend sever; intrinsics stays) consumes those
layout constants **directly from intrinsics** and holds **no duplicate copies**.

Option **(B)** — encapsulate layout behind reader functions (`read_string_as_str`,
a vec reader), layout consts private — was considered and **rejected this sprint**:
minimum mechanism (Principle 2); no second consumer needs the encapsulation yet; it
would restructure primitives' string/vec ops for no present gain. If a future
intrinsics audit wants full encapsulation, that is its deliberate call.

## Issue — layout coupling + duplication (Principle 7 violation)

primitives reaches into intrinsics' heap layout, partly via intrinsics' pub consts
and partly by **hand-copying** constants:

- `HeapString::{DATA_OFFSET, LEN_OFFSET}` — already `pub` on intrinsics; primitives
  reads via these in `string.rs::read_string_parts`. **Sound as-is.**
- **Vec layout — NOT currently exposed by intrinsics.** `vec_runtime` publishes only
  functions (`vec_new`/`vec_drop`/`vec_push_*`/`vec_set_*`), no layout consts.
  primitives therefore duplicates the offsets in **two** places:
  - `crates/cranelisp-primitives/src/vec.rs` — private `const LEN_OFFSET: usize = 16`
    ("duplicated here to avoid a dependency cycle" — but primitives already depends
    on intrinsics, so the cycle rationale is stale).
  - `crates/cranelisp-primitives/src/string.rs` — `VEC_LEN_OFFSET = 16`,
    `VEC_DATA_PTR_OFFSET = 32` (for `split`/`join`), with a comment admitting they
    are "a duplicate of `crate::vec::LEN_OFFSET`".

Three copies of one layout fact (intrinsics' real layout + two primitives copies) is
a single-source-of-truth violation: if the Vec heap layout ever changes, the copies
silently rot.

## Proposed resolution

1. **Intrinsics exposes canonical Vec-layout consts** — `pub const` layout offsets on
   `cranelisp_intrinsics::vec_runtime` (e.g. `LEN_OFFSET`, `CAP_OFFSET`,
   `DATA_PTR_OFFSET`), mirroring the existing `HeapString::{DATA_OFFSET, LEN_OFFSET}`
   pattern. Small additive `/dev (intrinsics)` source change; intrinsics' own
   `vec_runtime` code switches to its own consts (no magic numbers).
2. **Primitives single-sources from intrinsics** — delete `primitives::vec.rs`'s
   private `LEN_OFFSET` and `primitives::string.rs`'s `VEC_*` consts; consume
   `cranelisp_intrinsics::vec_runtime::{...}` and `HeapString::{...}` exclusively.
   `/dev (primitives)`.
3. **Both facades pin the consumed contract** (the "firm up the specifics so it is
   sound" part — more than a one-line consumer acknowledgment):
   - `facades/intrinsics.md` — name the blessed layout-ABI consts (`HeapString`
     offsets + the new `vec_runtime` offsets) as a **stable public contract**, and
     name `cranelisp-primitives` as a Rust consumer of the allocator/heap-string/
     drop/vec-layout surface (it is not only backend that consumes intrinsics by
     Rust path). Resolve the §"Vec primitives" / §"Heap allocator" sections to the
     post-S67 state.
   - `facades/primitives.md` §"Consumed surface" — pin the exact intrinsics items
     primitives depends on: `heap_string::{alloc_string, HeapString + layout consts}`,
     `vec_runtime::{vec_new, layout consts}`, `alloc::alloc_with_rc`,
     `rc::consume_shallow`, `drop::{consume_sexp, consume_slist}`,
     `panic::runtime_panic`. This is the standing consumed contract; any future
     intrinsics change to these items is bound by the baseline-diff discipline with
     primitives as a named consumer.
   - `bounded-contexts.md §4a/§4b` — corrected to match (primitives ⟂ backend per
     0244; primitives → intrinsics is the legitimate runtime-substrate edge incl.
     the layout ABI).
4. **Close the adjacent stale intrinsics-facade FIXMEs in the same pass** — 0190
   (renamed `heap_string`/`vec_runtime` modules not yet named in the facade) and 0213
   (stale §"String primitives" section) are facade-doc catch-up against
   already-current source; folding them in leaves the intrinsics facade *sound*
   w.r.t. this boundary without a full intrinsics audit.
5. **Baseline-diff discipline** — `crates/cranelisp-intrinsics/public-api.txt`
   regenerated for the new `pub const`s (additive); facade updated in the same
   change-set per `design/arch/CLAUDE.md` §"Baseline-diff discipline".

## Scope boundary (what this is NOT)

This firms up the **primitives↔intrinsics layout boundary only**. It does NOT pull
in the full intrinsics per-crate audit — extern-signature review, inventory
(FIXME 0178), facade retirement (the typecheck-style fold-into-rustdoc) — which
remain a separate future intrinsics sprint, naturally sequenced near the deferred
backend sprint.

## Operational implication / Context

- This is the soundness decision that lets S73 genuinely *settle* primitives rather
  than build-then-rework: with the layout contract pinned and duplication removed,
  primitives' structure is stable against the consumed interface.
- Pairs with FIXME 0244 (backend sever; `code: None`). Together they make primitives
  import only `cranelisp-types` (boundary) + `cranelisp-intrinsics` (runtime
  substrate, incl. the pinned layout ABI) — and **not** `cranelisp-backend`.
- Source split: `/dev (intrinsics)` exposes the vec consts (small); `/dev
  (primitives)` deletes the duplicate consts + consumes intrinsics'. So S73 touches
  intrinsics source *minimally* (additive const exposure), not a source audit.
