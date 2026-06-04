---
number: 0254
target: /dev (intrinsics)
filed_by: /arch
filed_at: 2026-06-04
sprint_filed: 76
refers_to: design/arch/tracing.md §3.4 §3.7 §4 §6, design/arch/bounded-contexts.md §4b invariant 12, crates/cranelisp-intrinsics/src/catalog.rs, crates/cranelisp-intrinsics/src/trace.rs
status: open
---

# Host the 12 trace bodies + the pure descriptor-driven formatter + the catalog entries + the nested-trace runtime guard in cranelisp-intrinsics

## Issue

The 2026-06-04 user ruling (formalised in `design/arch/tracing.md`, TARGET STATE) relocates the
`(trace ...)` runtime **back to `cranelisp-intrinsics`** (retracting D40's trace-relocation-to-int).
The bodies currently live in `src/trace.rs` (int); they must move to
`crates/cranelisp-intrinsics/src/trace.rs` and publish through `intrinsics_table()`.

## Proposed resolution

1. **Relocate the 12 bodies** from `src/trace.rs` to `crates/cranelisp-intrinsics/src/trace.rs`:
   `cranelisp_trace_enter`, `_exit`, `_swap_got`, `_restore_got`, `cranelisp_collect_trace`,
   `_first_child_nanos`, `_name`, `_params`, `_result`, `_children`, `_nanos`, `_format`. Bring
   `TRACE_STACK`, `TRACE_THREAD_ID`, the `THIS_THREAD_ID` thread-local counter, and
   `consume_trace_call` (the `TraceCall` ADT drop helper) with them. `consume_trace_call` is a leaf
   consumer of intrinsics' generic `consume_shallow` / SList drop glue — intrinsics' `drop` module must
   NOT reference `consume_trace_call` (no re-coupling; `tracing.md` §4.1).

2. **`cranelisp_trace_format(value: i64, descriptor_ptr: i64) -> i64` becomes a PURE intrinsic** over a
   backend-baked `#[repr(C)]` `DisplayDescriptor` (defined here; backend reads its layout to emit it —
   `tracing.md` §3.4). It walks `descriptor + value` with **zero symbol-table access and no thread-local
   state** — delete any dependence on a session/TypeChecker. Reuse the heap-layout reads from the
   existing int `format_value` logic (`HeapAdt`/`HeapVec`/`HeapString` offsets — intrinsics owns those
   consts). The arity stays `(2, true)` so backend's `declare_trace_extern` is unchanged. Define
   `DisplayDescriptor` per the §3.4 table (Int/Bool/Float/String/Fn/Vec/Adt/TypeVar kinds); the Adt kind
   bakes the per-constructor tag→name+arity + per-field child descriptors. Confirm the object-mode
   encoding with /dev (backend) — `/arch`'s target is a flat position-independent **arena blob** with
   child links as byte-offsets-within-the-blob (no intra-blob relocations).

3. **Add the 12 trace entries to `intrinsics_table()`** (`catalog.rs`) — table grows 15→27. Flip the
   "Trace runtime symbols are deliberately ABSENT" scope-note (crate-root `//!` + the catalog comment)
   to "trace present." Update the `#[cfg(test)] mod tests` `EXPECTED_NAMES` / arity / non-null-ptr
   assertions to the 27-name set (the catalog + its tests are now the single owner of the trace
   name-agreement contract — `tracing.md` §4.2). Arities: `enter (4,false)`, `exit (2,true)`,
   `swap_got (4,true)`, `restore_got (2,false)`, `collect_trace (0,true)`, `first_child_nanos (1,true)`,
   `name/params/result/children/nanos (1,true each)`, `format (2,true)`.

4. **Nested-trace runtime guard** (`tracing.md` §6): in `cranelisp_trace_swap_got`'s `current_owner ==
   my_tid` branch, distinguish a legitimate multi-module swap (no body running yet) from a re-entrant
   `(trace (trace …))` (a wrapper is on the stack). Use a thread-local `TRACE_BODY_RUNNING` flag set true
   after the swap loop / before the body, false after restore; a re-entrant swap (`current_owner ==
   my_tid && TRACE_BODY_RUNNING`) raises via the `runtime/panic` intrinsic with message `"nested trace
   is not supported: (trace ...) may not appear inside an actively-tracing (trace ...)"`. (Exact flag
   representation is /dev's call; a `TRACE_DEPTH` counter is an equivalent mechanism.) NOTE: setting
   `TRACE_BODY_RUNNING` across the body requires a runtime touch-point between the swap and the body —
   coordinate with /dev (backend): either the swap sets it on role-acquire and `collect_trace` clears it,
   or backend emits an explicit set/clear around the body. Resolve the exact placement with backend.

5. Run `cargo nextest run -p cranelisp-intrinsics` + regenerate `crates/cranelisp-intrinsics/public-api.txt`
   (the `intrinsics_table`/`IntrinsicEntry`/`DisplayDescriptor` surface) per the baseline-diff discipline.
   Fix warnings introduced by the change.

## Operational implication / Context

Depends on /dev (int)'s deletions (FIXME 0256) and /dev (backend)'s descriptor + discovery rework
(FIXME 0255) landing in concert — the descriptor `#[repr(C)]` layout is the contract between this
crate (reader) and backend (emitter), so co-design the layout. Sequencing within the S76 trace wave is
**/sprint + user's call** — note: this is the heaviest of the trace FIXMEs (new descriptor type +
formatter rewrite + body relocation + guard). Likely a dedicated trace wave rather than S76 W-Enablement.
