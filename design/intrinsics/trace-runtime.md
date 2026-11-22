# The trace runtime — recording thread, strict extent and the root's result

**Owner:** `design`, narrow-deployed to the primitives + intrinsics surface.
**Subordinate to:** [tracing](../arch/tracing.md) §3.6 (the root's result,
row B17), §4 (the runtime family, its stack and the trace role) and §7
(strict evaluation within the trace extent).

**Status:** describes source at the close of S124 (read 2026-11-22). §1–§6
landed in `3cdca9dc` (row D8); §7 in `ecae99c9` and the backend's `3c5e41ca`
(row B17). The user's rulings of 2026-11-22 on an unrecorded form (spec
§4.12.5, §4.12.6) are not yet in source; [ACT-1110](../../sprints/actions/ACT-1110-an-unrecorded-trace-root-is-named-skipped-with-an-empty-result-intake.md)
carries them, and §7.3 states where they differ.

**Authority:** spec §4.12.2, §4.12.3, §4.12.5 and §4.12.6; tracing §3.6 and
§7 rules 1–4;
[BC §4b](../arch/bounded-contexts.md#4b-intrinsics-cratescranelisp-intrinsics)
invariants 6 and 12 and the named-intrinsic convention rows. The backend's half
is [trace codegen](../backend/trace-codegen.md) and
[lenient evaluation](../backend/lenient-eval.md) §2.3.

---

## 1. One recording predicate

- **A thread records exactly when it holds the trace role**, that is, when
  `TRACE_THREAD_ID` holds the calling thread's id (tracing §4.2).
- **One crate-private predicate in `trace` answers it**
  (`trace::this_thread_records`). Its readers are the formatting entry (§3),
  `cranelisp_trace_enter`, `cranelisp_trace_exit`, spark admission (§2) and,
  under §7, `cranelisp_collect_trace`. None reads the role word itself, except
  role arbitration in `cranelisp_trace_swap_got` and the collect's release,
  which write it. Spark admission makes `ivar` depend on `trace` inside the
  crate.
- **A relaxed load is sufficient.** A thread compares the role word with its
  own id. Only that thread writes its id there (the acquire CAS) or clears it
  (`cranelisp_collect_trace`), and a thread always observes its own writes. A
  stale view of another thread's change reads 0 or a foreign id, and both mean
  "not recording".
- **The role changes on a thread only inside a trace form's own sequence:**
  acquired by its first `cranelisp_trace_swap_got`, released by
  `cranelisp_collect_trace` (tracing §3.3).

## 2. Rule 1 — spark admission declines on the recording thread

- **The decision.** `cranelisp_spark_budget_try_reserve` consults the predicate
  before the depth and budget checks. On the recording thread it returns 0
  without reserving. The create-gate then takes its direct arm, the site's
  sequential lowering, which allocates nothing. The caller's obligation for a 0
  is unchanged.
- **Per thread, not "while any trace is active".** The extent is the
  evaluation reached from the body. No spark is admitted on the recording
  thread, so the extent never leaves it. Evaluation on other threads is outside
  the extent and keeps its parallelism, including a second thread's own skipped
  trace form (spec §4.12.6, tracing §7 rule 4).
- **Complete because it is the only admission point** (asserted, with a named
  falsifier). An IVar is created and sparked only in the lenient arm of a
  granted reservation, which the backend reaches only through
  `emit_create_gate`. A waiting force does not run other pool work: the
  `ivar_force` wait loop spins, yields and sleeps, and never helps the pool, so
  no unrelated spark body runs on the recording thread. *Falsifier:* an IVar
  creation or pool spawn reachable from evaluation without a granted
  reservation, or a wait path that executes pool tasks.
- **The decline is counted separately.** With spark statistics on, a trace
  decline increments `trace_declines`, the final field of the `[SPARK_STATS]`
  line, and not `serial_continues`, so evidence can tell a trace decline from a
  budget or depth decline. The line carries counts only.

## 3. Rule 2 — the formatting entry formats only for the recording thread

- **The decision.** `cranelisp_trace_format` consults the predicate. Off the
  recording thread it returns 0 and allocates nothing. On it, it walks the
  descriptor and returns a fresh String.
- **The descriptor walk stays pure.** It reads only the baked descriptor and
  the heap value, with no symbol-table access and no role state (BC §4b
  invariant 12). It is the crate-private `trace_format::format_with_descriptor`;
  the extern gates and allocates. The collect entry (§7) is the walk's second
  caller.
- **`cranelisp_trace_enter` and `cranelisp_trace_exit`** return without storing
  off the recording thread, and there they receive zero words, so there is
  nothing to release.
- **Why the formatting entry.** The emitted wrapper formats its arguments
  before it calls `cranelisp_trace_enter`, so the decision must be made no later
  than formatting, and the formatting entry is the first intrinsic the wrapper
  calls. Rejected:
  - *A query export with an emitted branch.* It adds an export and makes the
    backend a second reader of a fact this crate owns.
  - *Releasing the Strings in enter and exit off the recording thread.* That
    is leak-free but allocates without a consumer, which rule 2 forbids.
  - *Gating on "a trace is active anywhere".* A thread that loaded a wrapper
    pointer before the restore can run the wrapper after the collect. It would
    then format with no consumer.
- **Consistency within one wrapper call** (asserted, with a named falsifier).
  The predicate is read by each `cranelisp_trace_format` and by the
  `cranelisp_trace_enter` or `cranelisp_trace_exit` that consumes its result,
  and the reads agree. The wrapper emits nothing between a format and its
  consuming call. A callee that runs a trace form between enter and exit has
  released the role before it returns, and a re-entrant swap on the recording
  thread ends the process (tracing §6). *Falsifier:* a recorded frame with a 0
  parameter or result word, or a non-zero String reaching enter or exit off the
  recording thread, which shows as an allocation-parity imbalance in a traced
  run with concurrent callers.

## 4. What stays concurrent during a trace

- **Callers outside the extent may run installed wrappers.** Examples: the
  sibling of a sparked binding whose initializer contains the trace form, a
  spark started before the trace began, or a second thread's skipped trace
  form. Their calls are unrecorded and allocate nothing (§3). That is correct,
  because they are outside the extent.
- **Residual — a force of an IVar created outside the extent** (asserted; the
  falsifier is in [trace codegen](../backend/trace-codegen.md)). If the
  recording thread claims the cell, the thunk runs there and is recorded. If a
  worker claimed it first, those calls are unrecorded. The tree then depends on
  scheduling, against tracing §7 rule 3. Nothing leaks in either case.

## 5. Evidence

Row D8's module rows, in source.

| Seam | Positive | Negative and control |
|---|---|---|
| Spark admission | On the recording thread it returns 0, the in-flight count is unchanged, and `trace_declines` advances under stats | The same call on a thread that does not record, with budget available, returns 1 |
| Formatting entry | On the recording thread the String renders | Off it, the result is 0 and the allocation count is unchanged |
| Enter and exit | — | Off the recording thread with zero words: no frame pushed, no allocation |

- The rows exercise the real predicate through `RecordingRole`, which acquires
  the role by the public swap path on a GOT the test owns.
- Rule 1 makes ACT-1038's premise, that a worker ran a traced call,
  unsatisfiable; `trace_declines` tells that correction apart from an absence
  of sparking.

## 6. Public surface — packet row D8

- **Signatures and catalog rows** are the crate's facade and `arch`'s
  (tracing §4.1); their rustdoc states the contracts this document realises.
- **Documented contracts realised in source:**
  `cranelisp_spark_budget_try_reserve` returns 0, reserving nothing, on the
  recording thread; `cranelisp_trace_format` returns 0 and allocates nothing
  off it; enter and exit receive zero words off it; `[SPARK_STATS]` ends with
  `trace_declines`.

## 7. The collect entry and the root's result (row B17)

`cranelisp_collect_trace(value, descriptor_ptr)` closes every trace form. It
returns the node the form evaluates to, whose result is the canonical display
of the body's value (spec §4.12.2, tracing §3.6). The backend passes the value
borrowed and releases it after the call; the entry neither consumes nor
retains it.

### 7.1 Who touches the trace stack

- **Only the role holder pushes or pops `TRACE_STACK`.** The root is pushed by
  the acquiring swap, frames by enter and exit on the recording thread, and the
  root is popped by that thread's collect while it still holds the role. The
  stack therefore holds exactly the recording form's frames, and its bottom
  frame is that form's root. This is what makes tracing §4.2's "the single
  stack stays coherent" true.
- **What the rule excludes.** A skipped swap records its form in a per-thread
  mark, not a frame on the shared stack; a collect on a thread that does not
  record reads no shared state; and the recording collect pops its root before
  it releases the role, so no second thread can push between the two. Any of
  these, reversed, makes the recorded tree and both forms' roots depend on
  scheduling, without a memory hazard: a frame's Strings move into whichever
  node is built, once. The §7.5 rows catch each.

### 7.2 Three states, read in a fixed order

The collect reads which state its form is in, first match wins:

| State | How the collect reads it | Name | Children | Elapsed | Result |
|---|---|---|---|---|---|
| **Recorded** | The predicate holds | `::trace::` | the root frame's | from the acquiring swap | the value, rendered |
| **Skipped** | This thread's skip mark is set | `::skipped::` | none | from the first skipped swap | empty (ruled otherwise; §7.3) |
| **Unswapped** | Neither | `::trace::` | none | 0 | the value, rendered |

- **The skip mark is per thread and per form.** The first swap of a form that
  finds the role held by another thread sets the calling thread's mark, holding
  that swap's start time, and pushes nothing. While the mark is set, every
  further swap on that thread returns the sentinel saved-GOT without
  arbitrating. A form is therefore wholly recorded or wholly skipped: a later
  swap of the same form cannot acquire a role the owner has meanwhile released.
  The collect takes the mark, clearing it.
- **The recorded sequence.** Stamp the root's elapsed time, pop the root, then
  release the role, lower the boundary flag and clear the swapped-base set, and
  only then render and build the node.
  - *Elapsed is stamped before rendering,* so a root's `nanos` measures the
    form's swaps, body and restores and not the display of its value. Rendering
    a large value is this entry's cost, not the body's.
  - *Popped before release,* so no other thread can push onto the stack while
    this thread's root is still on it.
  - *Rendered after release.* The walk touches no shared or role state, so
    holding the role or the stack lock across it buys nothing.
- **One build.** Each state supplies a root frame — popped, synthesised from the
  mark, or synthesised empty — and the existing node builder marshals it. The
  rendered value becomes the frame's result String; a frame with no result
  marshals the empty string, which is how the skipped state's result arises.
- **Rendering** is the crate-private walk (§3), never `cranelisp_trace_format`:
  that entry declines off the recording thread, and the unswapped state is off
  it. The result is a fresh String owned by the node. A zero descriptor renders
  the bare word, as the walk does for any caller.
- **Value and descriptor arrive in every state.** The skipped state does not
  read them as built.

### 7.3 Where source differs from the 2026-11-22 rulings

- **An unrecorded form (spec §4.12.6).** The ruling names its root
  `::untraced::` and gives it the body's displayed value. The skipped state
  still names its root `::skipped::` and gives it the empty result. The repair
  is interior to the collect entry: the value and descriptor already arrive.
  [ACT-1110](../../sprints/actions/ACT-1110-an-unrecorded-trace-root-is-named-skipped-with-an-empty-result-intake.md)
  holds it, including whether the unswapped state is also unrecorded.
- **A form entered inside an unrecorded form (spec §4.12.5)** raises no error.
  The skipped state's mark already makes the inner form skipped without
  arbitration (§7.4).
- **An unswapped root's elapsed time.** No start event exists for a form that
  swaps no slot, so its `nanos` is 0. Spec §4.12.2 gives the root
  `elapsed_nanos` without exception. Measuring it needs a start call, an
  interface change for `arch`; no cell reads it.
- **Typed value entries.** The collect and formatting entries take raw words;
  [ACT-1111](../../sprints/actions/ACT-1111-typed-runtime-entry-points-for-trace-values.md)
  carries row B18's typed replacement to `arch`.

### 7.4 Residuals (asserted, with named falsifiers)

- **A recorded collect closes the form that acquired.** The guard in
  `cranelisp_trace_swap_got` (tracing §6) stops a nested swapping form, but a
  nested form that swaps no slot calls no swap, so its collect on the recording
  thread would pop the enclosing form's frame and release the role mid-body.
  Discovery covers the form's own module, so a form inside a named function
  has at least that function's slot and swaps; the shape needs a form whose
  covered modules hold no slot, reached inside a recording body. *Falsifier:* a
  program in which a trace form compiled through the no-swap path runs inside
  another trace's body. This is §4.12.5's obligation, not B17's.
- **Nesting on a skipped thread.** A trace form entered inside a skipped form
  on the same thread is skipped too and takes the mark, so the enclosing form
  then reads as unswapped: named `::trace::`, with its value rendered. No error
  is raised, as §4.12.5 now requires. *Falsifier:* such a program returning
  anything other than two childless roots.

### 7.5 Module rows

In `crates/cranelisp-intrinsics/src/trace/tests.rs`, written first and observed
failing at step 3 (`ecae99c9`). Recorded rows acquire the role through
`RecordingRole`; the unswapped and skipped rows install a foreign owner.

| Seam | Positive | Negative and control |
|---|---|---|
| Recorded, `Int` | A collect of `42` with an `Int` descriptor returns a `::trace::` node whose result reads `"42"` | Afterwards the predicate is false and the stack is empty |
| Recorded, with a child | After one enter and exit, the root holds the child and its own result is the rendered value | The child's result is the String its exit passed |
| Recorded, heap value | A String value renders by its descriptor | Its reference count is unchanged by the call; after the node is consumed, allocations balance |
| Unswapped | With no role and no mark, the node is `::trace::`, rendered, with no children and `nanos` 0 | With a foreign owner and a planted frame on the stack, the stack's depth and top frame are unchanged |
| Skip mark | A swap under a foreign owner returns the sentinel and leaves the stack depth unchanged | After the owner clears, a second swap on the same thread still returns the sentinel and does not acquire |
| Skipped | The collect returns `::skipped::` with no children and the empty result, and clears the mark | A following collect on the same thread reads unswapped; the foreign owner still holds the role |

- **Tests:** `recorded_collect_renders_the_value`,
  `recorded_collect_keeps_children_and_renders_its_own_result`,
  `recorded_collect_borrows_a_heap_value`,
  `unswapped_collect_renders_a_childless_root`,
  `unswapped_collect_leaves_the_shared_stack_alone`,
  `skip_mark_pushes_nothing_and_holds_for_the_form` and
  `skipped_collect_returns_skipped_root_and_clears_the_mark`.
- **Detection proofs.** Dropping the render flips the recorded and unswapped
  rows; popping the shared stack off the recording thread flips the unswapped
  row's control; restoring the sentinel push flips the skip-mark row.
- **End to end.** T-TRACE-ROOT's nine subjects
  (`tests/trace.rs::s124_trace_root_call_cold` and its siblings) and the four
  child controls exercise the recorded state only. No fixture reaches the
  skipped state (ACT-1110).

### 7.6 The entry's documented contract

`cranelisp_collect_trace(value, descriptor_ptr) -> i64`; the catalog row
declares two parameters ([tracing §3.6](../arch/tracing.md#36-the-roots-result)).
Its rustdoc states: the value is borrowed; the descriptor follows
`cranelisp_trace_format`'s descriptor contract; the returned node is fresh,
owned by the caller, and carries the value's display as its result except for a
skipped form; the entry ends the role on the recording thread and touches no
shared state elsewhere.
