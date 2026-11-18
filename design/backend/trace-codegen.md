# Trace codegen

**Owner:** `design`, narrow-deployed to `cranelisp-backend`. **Subordinate to:**
[backend.md](backend.md).

**Status:** the backend's interior decisions for `(trace …)` that the
architecture leaves to it. The emitted sequence, the descriptor blob, the GOT
swap and the nested-trace guard are
[tracing](../arch/tracing.md) §3–§6 and are not restated here.

- §2 is built: `3cdca9dc` (packet row D8) and its module row M-1038 at
  `997c6c2d`.
- §1's selection is designed and **not in source** at `79a8c94c` (read
  2026-11-18), and is not scheduled. `dev` built it and reverted it, because
  it fails `--link` (§1.2). It and ACT-1078 wait on the user's ruling on
  which modules a trace form covers
  ([tracing §5.1](../arch/tracing.md#51-which-modules-a-form-covers--with-the-user-2026-11-18));
  §1.3 is the backend's recommendation to that ruling.
- The descriptor baker's substitution correction (ACT-1062's backend reader)
  is not scheduled and is not in source.

**Authority:** spec §4.12.2, §4.12.3 and §4.12.9;
[tracing §5](../arch/tracing.md#5-discovery-swap-every-symbol-table) for the
traced set; [tracing §7](../arch/tracing.md#7-strict-evaluation-within-the-trace-extent)
for the strictness and allocation rules.

---

## 1. The traced set is fixed by slot claims, not by slot contents

**Fault (ACT-1039, attributed by `qa` with a control).** Under `--run` a trace
records no call to a function in its own module, and in every mode it records
no call to a function restored from the cache. `discover_traced_fns_from_tables`
skips every entry whose GOT slot reads zero **at trace codegen**. A batch
compiles a module's functions before it publishes any of them, and a cache
restore can write an import's slots after the entry's codegen, so the set is a
function of compilation and load order
([Principle 11](../arch/principles/11-single-pipeline-mode-parameters.md)).

### 1.1 Decision

- **Selection reads claims.** An entry is traced when it has a callable GOT
  slot (`callable_got_slot()`) and a function-typed scheme. The slot's
  contents are not read at codegen. Slot layout is pinned before codegen
  ([backend.md](backend.md) §4), so the set does not depend on compilation or
  load order.
- **The live check moves to run time, where it already has its value.** The
  emitted per-function sequence already loads the slot's pre-swap contents
  into `originals[i]`. It stores zero into `wrappers[i]` when that original is
  zero, and the wrapper's address otherwise. A slot that is still empty at
  swap time stays empty, so no wrapper calls through a null original.
- **Unchanged:** the swap and restore intrinsics, their signatures, the
  descriptor bake and the wrapper body. No public item changes.
- **The load-to-swap interval adds no new precondition.** A zero in
  `wrappers[i]` blanks the slot if another thread publishes it between the
  emitted load and the swap's copy. The whole-table copy-swap already presumes
  that no other thread publishes into a swapped GOT during the trace extent:
  the restore copies the saved table back and would revert such a publication
  ([tracing §3.5](../arch/tracing.md#35-got-copy-swap-and-completeness-by-construction)).
  The emitted load is the instruction before the swap call, so it widens that
  window by one call. *Asserted; falsifier:* `CRANELISP_GOT_TRACE` showing a
  write to a module's GOT from another thread while a trace form's swap of that
  GOT is live. The trigger for a change is any such publisher. The remedy then
  belongs to the copy-swap contract (§3.5), not to this sequence.
- **Evidence.** The committed `trace_records_user_function_calls_in_every_mode`
  and T-1039-w cells are the end-to-end guards. A module row covers the
  selection: an entry with a claimed but empty slot is selected, and a
  slotless entry and a non-function scheme are not. The existing
  `discovery_skips_empty_got_slots_and_non_fn_schemes` row asserts the old
  skip and is rewritten to that row in the same change-set.

### 1.2 What the built selection showed

Read against `dev`'s reverted patch and probed with the built binary at
`1e4b0ce4`. Each probe used a fresh directory.

- **The trace's object may reference only a GOT that every image holding it
  defines.** For each module it swaps, the trace form imports
  `__cranelisp_got_{M}`. The JIT binds that symbol for every loaded symbol
  table (`Jit::new`). A linked executable defines it only for modules that have
  an object, plus the primitives slab and the platform GOTs.
- **`macros` claims slots that no image fills.** Its synthetic constructors
  carry callable slots, but construction and constructor values are emitted at
  the use site, so no probe wrote to `macros`' GOT in any mode. A `--link`
  image defines no `__cranelisp_got_macros`. The content gate skipped these
  slots because they always read zero, so it hid the gap. Selection by claim
  swaps `macros`, and `--link` fails to link: eight previously green cells,
  for example `link_traced_extern_primitives_appear_as_children_exit_42` and
  the `trace_linked_*` cells.
- **A trace's object references modules outside its own dependencies.** This
  is a defect at source today, independent of the selection rule. Discovery
  reads every loaded table, so a cached object records the GOTs of whatever
  modules were loaded when it compiled, which its cache key does not cover.
  - *Reproduction.* `u` holds a trace form. Entry `e1` imports `u` and `x`;
    entry `e2` imports `u` only.
  - After `--run e1.cl`, both `--run e2.cl` and `--link e2.cl` fail with
    `unresolved symbol: __cranelisp_got_x`.
  - Under the content gate the reference depends on whether `x` was published
    before `u` compiled. Under selection by claim it is always made.

### 1.3 Blocked on `arch`: which modules contribute

The backend cannot close either gap inside its boundary.

- [Tracing §5](../arch/tracing.md#5-discovery-swap-every-symbol-table)
  specifies "every module in `symbol_tables`, with no project-root filter and
  no reachability set". The rationale in §3.5 governs any filter.
- Which modules an image defines a GOT for is int's. Which modules claim
  slots is bootstrap's and `cranelisp-types`'.

**Recommendation to `arch`.** Neither part changes a public item.

1. **The traced set is drawn from the trace form's module and its transitive
   imports.** Those are the modules every image holding the object also holds.
   With [ACT-1052](../int/int.md#763-slot-layout-identity-act-1052), their slot
   layout is covered by the object's dependency key, so the set becomes a
   function of that key. This is not the static callee graph that §3.5
   rejects. A closure, a function value or a trait implementation reaches the
   trace body only from code in that closure, so every call the body can make
   goes through a slot of a module in it.
   - *Falsifier:* a call made during a trace through the slot of a module
     outside the trace module's import closure.
2. **A mounted module that holds no code claims no slot.** The synthetic
   constructors in `macros` are seeded without a slot, as its host-promised
   callables already are (FIXME 0360, recorded in `src/bootstrap.rs`). The
   alternative is for a linked image to define a GOT for every table the JIT
   binds. That alternative keeps a claim that no image can fill, and every
   trace swaps a table that is always empty.

**What `dev`(backend) builds once the ruling is made:**

- §1.1, unchanged. The reverted patch realises it.
- The module filter of item 1, in `discover_traced_fns_from_tables`, if the
  ruling adopts it.
- Its module rows:
  - a claim in a module outside the closure is not selected;
  - a claim in an imported module is selected;
  - a claim in the trace module's own module is selected.

Item 2 lands before the backend change, or `--link` regresses. Its owners are
the ones `arch` names. Without item 1, the `e1`/`e2` failure stays, and it
needs `qa` intake as its own defect.

## 2. The trace extent and the wrapper's allocation

Built at `3cdca9dc`. The two rules of tracing §7 are intrinsics'. The backend's
half was a deletion and an unchanged call sequence.

- **Rule 1, no spark in the extent.** Every lenient spark is admitted only
  through the create-gate's `cranelisp_spark_budget_try_reserve`, which
  declines while the calling thread holds the trace role. The lexical
  `in_trace_body` flag is deleted
  ([lenient evaluation](lenient-eval.md) §2.3), so a trace form's own spark
  sites take the ordinary gate. A decline is counted in intrinsics' own
  `trace_declines` statistic ([trace runtime](../intrinsics/trace-runtime.md)
  §2); the backend emits nothing for it. Module row M-1038
  (`compiler/trace_codegen/tests.rs`) shows a trace form's spark site calling
  the gate. Its detection was observed: restoring a lexical suppression fails
  the row.
- **Rule 2, no wrapper allocates before it has a consumer.** The wrapper
  formats its arguments before it calls `cranelisp_trace_enter`, so the
  decision is made inside the formatting call. `cranelisp_trace_format`
  returns no string (`0`) on a thread that does not record, by the predicate
  `cranelisp_trace_enter` and `cranelisp_trace_exit` use to return early. The
  predicate and its single source are intrinsics'
  ([trace runtime](../intrinsics/trace-runtime.md) §3).
- **The emitted wrapper does not branch on recording state.** A backend-side
  branch would need a new query export and would be a second reading of a
  fact intrinsics owns.
- **Public surface: none.** Row D8 changed the documented contract of two
  intrinsic exports and kept their signatures; backend `public-api.txt` moved
  +0/−0.
- **The descriptor round-trip tests hold the trace role.** The `fmt` helper in
  `compiler/trace_codegen/tests.rs` acquires the role through the public swap
  entry, on a GOT buffer the test owns with no slot wrapped, and releases it
  through restore and collect. That is the only route open to a backend test.
  The negative leg, a call off the recording thread reading `0`, is
  intrinsics'.
- **Residual, asserted.** A thread that started a spark before the trace began
  can still call through a wrapper during the extent. Under rule 2 that call is
  unrecorded and allocates nothing. *Falsifier:* a trace whose body forces an
  IVar created outside it, showing a residual or a lost frame.
