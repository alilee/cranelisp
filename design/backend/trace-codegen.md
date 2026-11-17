# Trace codegen

**Owner:** `design`, narrow-deployed to `cranelisp-backend`. **Subordinate to:**
[backend.md](backend.md).

**Status:** the backend's interior decisions for `(trace …)` that the
architecture leaves to it. The emitted sequence, the descriptor blob, the GOT
swap and the nested-trace guard are
[tracing](../arch/tracing.md) §3–§6 and are not restated here. Both sections
below are designed for S124 and not in source at `4b58ab93` (read 2026-11-16).
§2 realises packet row D8, approved by the user on 2026-11-17.

**Authority:** spec §4.12.2, §4.12.3 and §4.12.9;
[tracing §7](../arch/tracing.md#7-strict-evaluation-within-the-trace-extent)
for the strictness and allocation rules.

---

## 1. The traced set is fixed by slot claims, not by slot contents

**Fault (ACT-1039, mechanism provisional).** Under `--run` a trace records no
user-function call, while the REPL does. `discover_traced_fns_from_tables`
skips every entry whose GOT slot reads zero **at trace codegen**
([tracing §5](../arch/tracing.md#5-discovery-swap-every-symbol-table)
step 1). A batch compiles a module's functions before any of them is
finalised and published, so at the trace form's codegen its own module's slots
still read zero and are dropped from the set. In the REPL the callee was
published by an earlier input, so it is included. The set is therefore a
function of compilation order, which differs by mode
([Principle 11](../arch/principles/11-single-pipeline-mode-parameters.md)).
*Refuted if* `CRANELISP_GOT_TRACE` shows the user module's slots non-zero
while the `--run` trace form is compiled.

**Decision.**

- **Selection reads claims.** An entry is traced when it has a callable GOT
  slot (`callable_got_slot()`) and a function-typed scheme. The slot's
  contents are not read at codegen. Slot layout is pinned before codegen
  ([backend.md](backend.md) §4), so the set is the same in every mode and every
  compilation order.
- **The live check moves to run time, where it already has its value.** The
  emitted per-function sequence already loads the slot's pre-swap contents into
  `originals[i]`. It now installs the wrapper only when that original is
  non-zero, by storing zero into `wrappers[i]` otherwise. A slot that is still
  empty at swap time stays empty and is never wrapped, so no wrapper can call
  through a null original.
- **Unchanged:** the swap and restore intrinsics, their signatures, the
  descriptor bake and the wrapper body. No public item changes.
- **Evidence.** The committed `trace_records_user_function_calls_in_every_mode`
  cell is the end-to-end guard. A module row covers the selection: an entry
  with a claimed but empty slot is selected, and a slotless entry is not. The
  existing `discovery_skips_empty_got_slots_and_non_fn_schemes` module test
  asserts the old skip and is rewritten to that row in the same change-set.

## 2. The trace extent and the wrapper's allocation

The two rules of tracing §7 land in intrinsics. The backend's half is a
deletion and an unchanged call sequence.

- **Rule 1, no spark in the extent.** Every lenient spark is admitted only
  through the create-gate's `cranelisp_spark_budget_try_reserve`, which
  declines while the calling thread holds the trace role. The lexical
  `in_trace_body` flag is deleted
  ([lenient evaluation](lenient-eval.md) §2.3) after intrinsics' decline has
  landed, never before it. A decline is counted in intrinsics' own
  `trace_declines` statistic ([trace runtime](../intrinsics/trace-runtime.md)
  §2); the backend emits nothing for it.
- **Rule 2, no wrapper allocates before it has a consumer.** The wrapper
  formats its arguments before it calls `cranelisp_trace_enter`, so the
  decision must be made inside the formatting call. `cranelisp_trace_format`
  returns no string (`0`) on a thread that does not record, by the same
  predicate `cranelisp_trace_enter` and `cranelisp_trace_exit` already use to
  return early. Those two already ignore their string arguments off the
  recording thread, so they receive nothing to release. The predicate and its
  single source are intrinsics' ([trace runtime](../intrinsics/trace-runtime.md)
  §3).
- **The emitted wrapper is unchanged.** It does not branch on recording
  state. A backend-side branch would need a new query export and would be a
  second reading of a fact intrinsics owns.
- **Public surface: S124 packet row D8, approved 2026-11-17.** The backend
  needs no added or changed export. Both rules change the documented contract
  of an existing intrinsic while keeping its signature
  ([trace runtime](../intrinsics/trace-runtime.md) §6). Backend
  `public-api.txt` is expected to show +0/−0.
- **The descriptor round-trip tests change with intrinsics' rule 2.** The
  `fmt` helper in `compiler/trace_codegen/tests.rs` calls
  `cranelisp_trace_format` on the test thread, which holds no trace role, so
  under rule 2 every round trip would read no string. The helper acquires the
  role for its call through the public swap path, on a GOT buffer the test
  owns with no slots wrapped, and releases it through restore and collect,
  disposing of the collected trace. This is the only route open to a backend
  test: the crate-private hook intrinsics may add is not visible here. The
  change lands in intrinsics' rule 2 change-set. Its negative leg is
  intrinsics' (the call off the recording thread reads `0`).
- **Residual, asserted.** A thread that started a spark before the trace began
  can still call through a wrapper during the extent. Under rule 2 that call is
  unrecorded and allocates nothing. *Falsifier:* a trace whose body forces an
  IVar created outside it showing a residual or a lost frame.
