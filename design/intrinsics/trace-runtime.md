# The trace runtime — recording thread and the strict extent

**Owner:** `design`, narrow-deployed to the primitives + intrinsics surface.
**Subordinate to:** [tracing](../arch/tracing.md) §4 (the runtime family, its
stack and the trace role) and §7 (strict evaluation within the trace extent).

**Status:** §1 describes the role state as built. §2–§4 are designed for S124
and are not in source at `4b58ab93` (read 2026-11-16). They change the
documented contract of two existing intrinsics, which is
[S124 packet](../../sprints/s124-api-packet.md) row D8 (§6), approved by the
user on 2026-11-17.

**Authority:** spec §4.12.2 item 2, §4.12.3 and §4.12.6; tracing §7 rules 1–4;
[BC §4b](../arch/bounded-contexts.md#4b-intrinsics-cratescranelisp-intrinsics)
invariants 6 and 12 and the named-intrinsic convention rows. The backend's half
is [trace codegen](../backend/trace-codegen.md) §2 and
[lenient evaluation](../backend/lenient-eval.md) §2.3.

---

## 1. One recording predicate

- **A thread records exactly when it holds the trace role**, that is, when
  `TRACE_THREAD_ID` holds the calling thread's id (tracing §4.2).
- **One crate-private predicate in `trace` answers it.** Four readers consume
  that predicate and none reads the role word itself: the formatting entry
  (§3), `cranelisp_trace_enter`, `cranelisp_trace_exit` and spark admission
  (§2). Spark admission makes `ivar` depend on `trace` inside the crate.
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
  granted reservation. At `4b58ab93` the backend's two creation sites are
  `compile_let_lenient` (`compiler/control_flow/let_if.rs`) and the lenient
  closure in `compiler/apply.rs`, both reached only through
  `emit_create_gate`. A waiting force does not run other pool work: the
  `ivar_force` wait loop spins, yields and sleeps, and never helps the pool, so
  no unrelated spark body runs on the recording thread. *Falsifier:* an IVar
  creation or pool spawn reachable from evaluation without a granted
  reservation, or a wait path that executes pool tasks.
- **The decline is counted separately.** With spark statistics on, a trace
  decline increments a `trace_declines` counter that is appended to the end of
  the `[SPARK_STATS]` line. It is not counted in `serial_continues`, so
  evidence can tell a trace decline from a budget or depth decline. Parsers
  that read fields by name are unaffected. The line carries counts only.
- **This change alone closes both of ACT-1038's mechanisms.** The backend's
  deletion of the lexical `in_trace_body` flag (backend B10) removes a
  redundant test and must not land before it.

## 3. Rule 2 — the formatting entry formats only for the recording thread

- **The decision.** `cranelisp_trace_format` consults the predicate. Off the
  recording thread it returns 0 and allocates nothing. On it, it walks the
  descriptor and returns a fresh String as today.
- **The descriptor walk stays pure.** It reads only the baked descriptor and
  the heap value, with no symbol-table access and no role state (BC §4b
  invariant 12). The entry is split into that crate-private walk and the extern
  that gates and allocates. Intrinsics' descriptor tests call the walk.
- **`cranelisp_trace_enter` and `cranelisp_trace_exit` are unchanged.** Off
  the recording thread they already return without storing, and they now
  receive zero words, so there is nothing to release.
- **Why the formatting entry.** The emitted wrapper formats its arguments
  before it calls `cranelisp_trace_enter`, so the decision must be made no later
  than formatting, and the formatting entry is the first intrinsic the wrapper
  calls. Rejected:
  - *A query export with an emitted branch.* It adds an export and makes the
    backend a second reader of a fact this crate owns
    ([trace codegen](../backend/trace-codegen.md) §2 agrees).
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
  falsifier is in [trace codegen](../backend/trace-codegen.md) §2). If the
  recording thread claims the cell, the thunk runs there and is recorded. If a
  worker claimed it first, those calls are unrecorded. The tree then depends on
  scheduling, against tracing §7 rule 3. Nothing leaks in either case.

## 5. Evidence

Module rows for `dev`; `qa` allocates the end-to-end cells.

| Seam | Positive | Negative and control |
|---|---|---|
| Spark admission | On the recording thread it returns 0, the in-flight count is unchanged, and `trace_declines` advances under stats | The same call on a thread that does not record, with budget available, returns 1 |
| Formatting entry | On the recording thread the String renders as before | Off it, the result is 0 and the allocation count is unchanged |
| Enter and exit | — | Off the recording thread with zero words: no frame pushed, no allocation |

- The rows must exercise the real predicate. A row acquires the role either
  through the public swap path on a GOT buffer the test owns, or through a
  crate-private test hook; the choice is `dev`'s.
- **Detection proof:** removing the check from either intrinsic must flip its
  row.
- **End to end.** Rule 1 makes ACT-1038's premise, that a worker ran a traced
  call, permanently unsatisfiable. `qa` reallocates those cells as the action's
  reallocation trigger states. `trace_declines` is available as the
  observation that tells this correction apart from an absence of sparking.

## 6. Public surface — packet row D8

- **Approved 2026-11-17 as written in the packet.** No signature changes, and
  no export or catalog row is added or removed. Intrinsics and backend
  `public-api.txt` are expected to show +0/−0.
- **Documented contracts that change.** The baseline cannot show these
  semantic changes:
  1. `cranelisp_spark_budget_try_reserve` (`ivar::spark_budget_try_reserve`)
     also returns 0, reserving nothing, when the calling thread holds the
     trace role.
  2. `cranelisp_trace_format` (`trace_format::cranelisp_trace_format`,
     re-exported as `trace::cranelisp_trace_format`) returns 0 and allocates
     nothing when the calling thread does not hold the trace role. Its
     rustdoc's statement that it holds no thread-local state then describes
     the walk, not the entry.
  3. `cranelisp_trace_enter` and `cranelisp_trace_exit` keep their contracts;
     off the recording thread every string argument they receive is 0.
  4. With spark statistics on, the `[SPARK_STATS]` line gains a final
     `trace_declines` field (§2).
- **Rows that follow are `arch`'s:** BC §4b's convention row for
  `cranelisp_trace_format`; the enter and exit rows, which receive no String
  off the recording thread; invariant 12's purity sentence (the walk is pure,
  the entry reads the role); and tracing §4.1 and §4.2 as `arch` judges.
- **Affected consumers.** The emitted wrappers are unchanged. The only
  Rust-path caller outside this crate is the backend's descriptor round-trip
  tests (`compiler/trace_codegen/tests.rs`), which call the entry off the
  recording thread and would read 0. They must run as the recording thread,
  and they change in the same change-set (`design`(backend)). Verified by
  search at `4b58ab93`.
- **Order.** This crate's change, together with the backend test adaptation,
  then the backend's `in_trace_body` deletion (backend B10).
