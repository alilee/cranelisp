# Heap layout owners

**Owner:** `design`, narrow-deployed to the primitives + intrinsics surface.

**Status:** designed for S124. This document is intrinsics' half of packet row
R10-9 ([S124 packet](../../sprints/s124-api-packet.md) Part B), approved by the
user on 2026-11-17; §2 is its intrinsics listing. §2 also carries row R10-10,
approved on 2026-11-17: the Vec offset readers that R10-9's deletion of the
backend `HeapVec` leaves. R10-9 supersedes S123 row
R10-6. At `4b58ab93` (read 2026-11-16) the ADT and closure offsets are defined
in several modules of this crate and again in the backend's `heap.rs`.

**Authority:** [BC §4b](../arch/bounded-contexts.md#4b-intrinsics-cratescranelisp-intrinsics)
invariants 2 (representation containment) and 5 (closures embed their drop
glue); the R10-9 position that intrinsics owns these layouts and the backend
reads its constants, as primitives already does for strings; R10-10, which
extends that to the Vec offsets for the backend and the binary.

---

## 1. One defining module per layout

**Rule.** Each runtime heap layout is defined once, in its owning module. Every
other reader, in this crate, the backend, primitives or the binary, reads that
module's constants and writes no offset of its own.

| Layout | Words | Owner | Readers |
|---|---|---|---|
| Header | `alloc_size`, `rc` | `cranelisp_types::HeapHeader` | everything below |
| String | header, `len`, bytes | `heap_string::HeapString` | unchanged |
| Vec | header, `len`, `cap`, `data_ptr`; separate buffer | `vec_runtime` | `drop`, `io`, `trace_format`, the backend, the binary's display and test runner; primitives only through `vec_runtime`'s functions, never its offsets |
| Data-constructor ADT | header, `tag`, fields | `alloc::HeapAdt` (§2) | `alloc_with_tag`, `drop`, `io` (IO nodes have this shape), `trace`, `trace_format`, the backend, primitives' marshalling, the binary's display and test runner |
| Closure | header, `code_ptr`, `drop_glue_ptr`, captures | `alloc::HeapClosure` (§2) | `drop`, `ivar`, `io`, the backend, the binary's test runner |
| IVar cell | header, `state`, `value`, `thunk` | `ivar`, private | `ivar` only |
| `TraceCall` | an ADT with five fields | `trace`, derived from `HeapAdt::field_offset` | `trace` only |

- **The ADT and closure layouts belong to `alloc`.** `alloc` already builds the
  ADT layout for host-built values: `cranelisp_alloc_with_tag` must produce
  what an emitted constructor produces. BC §4b invariant 2 names the allocator
  module as a layout owner. A new module would add a home without a distinct
  invariant. Rejected:
  - *`drop`*, which holds the ADT offsets and the closure drop-glue offset
    informally today. It reads layouts in order to tear them down, so
    publishing representation from it would put the public face in the
    teardown module.
  - *`cranelisp-types`*. BC §4b places representation in intrinsics; types
    holds only the header and the IO glue facts.
- **The form is the `HeapString` form:** a `#[repr(C)]` struct whose
  associated constants are derived with `offset_of!` and locked with
  `const _: () = assert!(…)`. The names and integer types match the backend's
  current items, so the backend's deletion is mechanical. The fields are
  public. An explicit ABI layout is the `#[non_exhaustive]` exception, and a
  private field that is never read would fail the zero-warning gate.
- **The IVar cell and `TraceCall` stay private to their modules.** Each has one
  owner and no reader outside it. BC §4b invariant 2's text lists only the
  allocator, string and vector modules, so `arch` words it as "one defining
  module per layout".

## 2. The constant list (R10-9, intrinsics' half)

**Added to `cranelisp_intrinsics::alloc`:**

| Item | Value |
|---|---|
| `#[repr(C)] pub struct HeapAdt { pub header: HeapHeader, pub tag: i64 }` | — |
| `HeapAdt::TAG_OFFSET: i32` | 16 |
| `HeapAdt::FIELDS_START: usize` | 24 |
| `const fn HeapAdt::field_offset(i: usize) -> i32` | 24 + 8i |
| `const fn HeapAdt::payload_size(field_count: usize) -> usize` | 8 + 8n |
| `#[repr(C)] pub struct HeapClosure { pub header: HeapHeader, pub code_ptr: i64, pub drop_glue_ptr: i64 }` | — |
| `HeapClosure::CODE_PTR_OFFSET: i32` | 16 |
| `HeapClosure::DROP_GLUE_PTR_OFFSET: i32` | 24 |
| `HeapClosure::CAPTURES_START: usize` | 32 |
| `const fn HeapClosure::capture_offset(i: usize) -> i32` | 32 + 8i |
| `const fn HeapClosure::payload_size(capture_count: usize) -> usize` | 16 + 8n |

**Added to `cranelisp_intrinsics::vec_runtime`:** `pub const PAYLOAD_SIZE:
usize` (24). It replaces the private `VEC_PAYLOAD_SIZE` and is the backend's
replacement for `HeapVec::payload_size`.

- **Unchanged in value and signature:** `vec_runtime::{LEN_OFFSET,
  CAP_OFFSET, DATA_PTR_OFFSET}` (`usize`) and the `HeapString` items. Outside
  this crate, no source names the three Vec constants at `4b58ab93`;
  primitives reaches Vecs only through `vec_runtime`'s functions, and its own
  source guard (`string/tests.rs`) asserts that it names none of the offsets.
  The backend converts the Vec offsets to `i32` from these constants in a
  constant context; it does not restate them (R10-10).
- **Rustdoc corrected (R10-10).** Each of the three Vec constants' rustdoc
  names its real outside readers, the backend and the binary, in place of
  the claim that primitives reads it. The crate-level rustdoc's primitives
  paragraph is corrected with it: it lists the Vec offsets among the
  heap-layout constants primitives reads, which is equally false. This is a
  documentation change only and has no `public-api.txt` effect.
- **Removed from the public surface:** nothing. No root re-export is added, as
  for the Vec and String constants.
- **Expected `public-api.txt` effect, intrinsics:** about +33 lines in the
  current format, counting the seven auto-trait rows each struct prints:
  `HeapAdt` 15, `HeapClosure` 17, `PAYLOAD_SIZE` 1; about +19 in K11-a's
  format. The regenerated diff is the exact figure.
- **The consumer edges the row approves.** Backend → `alloc::{HeapAdt,
  HeapClosure}` and `vec_runtime::PAYLOAD_SIZE`; root → `alloc::HeapAdt`
  (`src/display.rs`, `src/session_v4/test_runner/run.rs`) and
  `alloc::HeapClosure` (`src/session_v4/test_runner.rs`, which writes the
  closure layout as literals today); primitives → `alloc::HeapAdt`
  (`marshal.rs`). Each crate already depends on intrinsics.
- **The Vec offset edges (R10-10).** Backend → `vec_runtime::{LEN_OFFSET,
  CAP_OFFSET, DATA_PTR_OFFSET}` (`heap.rs`, for `compiler/vec_codegen.rs`),
  replacing `HeapVec`'s copies; root → `vec_runtime::{LEN_OFFSET,
  DATA_PTR_OFFSET}` (`src/display.rs`, replacing `HeapVec`'s copies, and
  `src/session_v4/test_runner.rs`, replacing its literal 16 and 32). No
  primitives edge to them is approved or needed.
- **The backend's half is `design`(backend)'s:** deleting `HeapAdt`,
  `HeapClosure` and `HeapVec` from `heap.rs`. R10-9 supersedes R10-6, so the
  backend `HeapClosure` is deleted, not narrowed.

## 3. Interior convergence

These changes land in the same change-set as §2 and have no public effect:

- `trace.rs` and `trace_format.rs`: the local payload and field offsets, and the
  `TraceCall` field offsets, derive from `HeapAdt`.
- `drop.rs`: its ADT offsets derive from `HeapAdt`, and
  `CLOSURE_DROP_GLUE_OFFSET` is deleted in favour of `HeapClosure`.
- `io.rs`: its tag and field offsets derive from `HeapAdt::field_offset`; its
  closure code-pointer and environment offsets come from `HeapClosure`; its
  local Vec length and data-pointer copies are deleted in favour of
  `vec_runtime`.
- `ivar.rs`: its closure code-pointer offset comes from `HeapClosure` and its
  RC offset from `HeapHeader::RC_OFFSET`. Its cell offsets stay private.
- `alloc.rs`: `cranelisp_alloc_with_tag` writes through `HeapAdt`.

## 4. Assurance

- **Values agree structurally.** The owner's constant locks fix each value,
  and each reader holds a name, not a number.
- **One definition is measured.** The crate's existing per-module source
  guard (`drop/tests.rs::drop_module_declares_no_local_reader_or_layout_copy`)
  widens to a crate-wide census: a layout offset constant defined outside its
  owner fails. Its detection proof is a planted definition that the census
  must reject, with a clean control.
- **Residual, asserted with a named falsifier:** an offset written inline as a
  literal evades a census of named constants. *Falsifier:* a `heap_access`
  call or pointer addition with a literal 16, 24 or 32 against an ADT, closure
  or Vec base.
- **Outside this crate.** The backend's copies are deleted by its half.
  `cranelisp-primitives`' `marshal.rs` restates the ADT payload and field
  offsets, against BC §4b invariant 2. R10-9 approves its edge to `HeapAdt`;
  designing and scheduling that convergence is `design`(primitives)'s and
  `sprint`'s. The binary's test-runner literals are int's.

## 5. Order

- The migration is callee first: this crate's additions and §3, then the
  backend's deletion and the binary's readers.
- No layout value changes, so emission and the golden corpus are unaffected,
  and the change-set may sit anywhere relative to the concreteness chain.
  It lands before K11-a.
