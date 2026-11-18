# Trace codegen

**Owner:** `design`, narrow-deployed to `cranelisp-backend`. **Subordinate to:**
[backend.md](backend.md).

**Status:** the backend's interior decisions for `(trace …)` that the
architecture leaves to it. The emitted sequence, the descriptor blob, the GOT
swap and the nested-trace guard are
[tracing](../arch/tracing.md) §3–§6 and are not restated here.

- §1, the traced set, is decided and **not in source** at `401ed6c0` (read
  2026-11-19). The user ruled which modules a form covers on 2026-11-19
  (spec §4.12.3, scribed at `3a687501`), and `arch` approved how the set
  reaches the backend as row B10
  ([tracing §5.1.1](../arch/tracing.md#511-how-the-set-reaches-the-backend)).
  §1.3 states what `dev` builds; it corrects ACT-1039 and ACT-1078.
- §2 is built: `3cdca9dc` (packet row D8) and its module row M-1038 at
  `997c6c2d`.
- §3, the substitution correction (ACT-1062's backend reader), is designed
  and in scope (backend row B14); it is not in source at `401ed6c0`.

**Authority:** spec §4.12.2, §4.12.3 and §4.12.9;
[tracing §5](../arch/tracing.md#5-discovery-swap-every-symbol-table) for the
traced set and [§5.1](../arch/tracing.md#51-which-modules-a-form-covers) for
the covered modules;
[tracing §7](../arch/tracing.md#7-strict-evaluation-within-the-trace-extent)
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

- **Selection reads claims.** An entry of a covered module (§1.3) is traced
  when it has a callable GOT slot (`callable_got_slot()`) and a
  function-typed scheme. The slot's
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

The evidence behind §1.3: selection by claim cannot land alone. Read against
`dev`'s reverted patch and probed with the built binary at `1e4b0ce4`. Each
probe used a fresh directory.

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
- **A trace's object references modules outside its own dependencies**
  (ACT-1078). This is a defect at source until §1.3 lands, independent of
  the selection rule. Discovery
  reads every loaded table, so a cached object records the GOTs of whatever
  modules were loaded when it compiled, which its cache key does not cover.
  - *Reproduction.* `u` holds a trace form. Entry `e1` imports `u` and `x`;
    entry `e2` imports `u` only.
  - After `--run e1.cl`, both `--run e2.cl` and `--link e2.cl` fail with
    `unresolved symbol: __cranelisp_got_x`.
  - Under the content gate the reference depends on whether `x` was published
    before `u` compiled. Under selection by claim it is always made.

### 1.3 Which modules a form covers

Spec §4.12.3 states the rule and
[tracing §5.1](../arch/tracing.md#51-which-modules-a-form-covers) states it
architecturally. Int computes the set; the backend reads it. Under this split
the set is a function of the form's module's validity record, so it is the same
cold, warm and in every mode, and an object references only GOTs that every
image holding it defines (§1.2).

- **Input.** `compile_to_module` takes
  `trace_modules: &BTreeSet<ModuleFullPath>` after `symbol_tables` (row B10,
  [tracing §5.1.1](../arch/tracing.md#511-how-the-set-reaches-the-backend)).
  It names the modules a trace form in `module_path` covers besides
  `module_path`. Every call passes it, whether or not a target holds a trace
  form. The backend composes no copy of the enumeration
  ([Principle 7](../arch/principles/07-single-source-of-truth.md)).
- **The covered set is `module_path` and the listed modules.** The backend
  adds no other module and privileges none by name
  ([Principle 19](../arch/principles/19-no-module-privileged-by-name.md)):
  `primitives` is covered because it is listed. A listed `module_path`
  changes nothing.
- **Discovery reads only the covered tables.** A covered module with no
  table in `symbol_tables` is a located codegen error, not a skip
  ([backend.md](backend.md#2-the-reading-discipline--a-pure-keyed-consumer)
  §2). Within those tables, selection is §1.1's.
- **Group order is the set's order,** so the emitted object does not depend
  on table iteration order.
- **`macros` is never listed.** Its claims are never read, and nothing
  changes there. Constructor slots are FIXME 0931's subject.

#### What the set must contain

The backend does not check the set's contents; a wrong set is a wrong trace,
or an unresolved GOT symbol at load. Spec text decides each case below. Int
owns the composition.

- **Platform modules: decided by existing spec text.** A platform module is
  the synthetic module `platform.<name>` (spec §8.9.3). A non-entry module
  reaches it by import (§10.9.1); the entry reaches it by its `platform`
  declaration, which is a dependency edge (§8.10.1). §4.12.3's "every module
  it imports, directly or indirectly" therefore covers a platform module
  exactly when the form's module reaches it through those edges, and no
  other. An image holding the form's object has that platform declared
  (§10.9.1), so the platform's GOT is defined. Platform functions hold
  callable slots, so §1.1 selects them as it selects any other entry. Int's
  load edges exclude platform modules
  ([int §7.6](../int/int.md#76-dependency-record-and-validity)). The
  enumerator therefore adds the platform modules reached from the covered
  modules, which is how this design reads tracing §5.1's "the platform
  modules those modules declare". `link_traced_extern_primitives_appear_as_children_exit_42`
  expects `primitives` externs (`str-concat`, `str-len`), which §4.12.3's
  "plus the built-in primitives" covers. It expects no platform call.
- **The prelude: decided by existing spec text, and not in arch's
  wording.** Spec §8.8.1 makes the implicit prelude import a dependency
  "like the written import it stands for", so §4.12.3 covers the prelude,
  and every module it reaches, for a module whose fallback is on. Int's load
  edges exclude the prelude, which its injection loads rather than the walk
  ([int §7.6](../int/int.md#76-dependency-record-and-validity)). The
  transitive closure of the load edges alone would stop an entry form
  recording the standard-library frames that §4.12.3 and
  [tracing §3.5](../arch/tracing.md#35-got-copy-swap-and-completeness-by-construction)
  require. The enumerator adds the prelude when the fallback is on. This is
  returned to `arch` and int to state in §5.1.1 and int §7.6.
- **`macros`: consistent with §4.12.3.** §4.12.3 instruments a synthetic
  module's function only through a slot that holds a real code pointer, and
  no mode writes `macros`' GOT (§1.2). Excluding it therefore drops no
  frame. *Asserted; falsifier:* a write to `macros`' GOT in any mode.

#### What `dev`(backend) builds

In `lib.rs`, `compiler/trace_codegen.rs` and its tests:

- the parameter, threaded from `compile_to_module` to discovery, with
  rustdoc stating its meaning;
- §1.1's selection and the covered-table read; neither lands without the
  other (§1.2);
- module rows:
  - a claim in a module outside the set is not selected;
  - a claim in a listed module, and one in `module_path`, are selected;
  - a claimed slot that is still empty is selected;
  - a slotless entry and a non-function scheme are not selected;
  - a listed module whose table is missing is refused;
- the `discovery_skips_empty_got_slots_and_non_fn_schemes` row rewritten to
  the §1.1 row;
- the backend's test callers of `compile_to_module` pass the set their
  fixture means, usually empty.

**Build order** ([tracing §5.1.1](../arch/tracing.md#511-how-the-set-reaches-the-backend)):

1. `dev`(`src/`) lands int's enumerator with the restore walk as its
   consumer. It changes no public item and the tree builds.
2. One commit, callee-first. `dev`(backend) makes the change above, and
   `dev`(`src/`) passes the set at the binary's three production callers and
   its test callers. The tree does not build between the two halves.

**Cache.** No persisted shape changes and no `CACHE_SCHEMA_VERSION` bump is
owed. An object built under the old rule differs only in its own trace form's
emission: which GOTs it imports and which slots it swaps. It shares no
convention with code it was not compiled with, because the swap intrinsics,
descriptors and wrapper body are unchanged. So
[module caching](module-caching.md) §14.2's bump rule does not fire.

- The build identity separates the two. B10 is a commit, so `BUILD_ID`
  changes, and the manifest's compiler fingerprint catches an uncommitted
  rebuild.
- The remaining gap is module caching §12's existing empty-fingerprint
  residual. Its face here is a stale trace form, which fails as today, with
  an unresolved GOT symbol at load or a missing frame. *Asserted; falsifier:*
  that residual's own experiment, run on a module holding a trace form.
- B8's bump, 34 to 35, is for B8's own persisted shape. It lands before B10,
  so it does not separate B10's objects, and nothing needs it to.

**Cells that turn green:**
`trace::trace_records_user_function_calls_in_every_mode`,
`trace::s124_1039_w_subject_run`, `_link` and `_repl`, and
`trace::s124_1078_subject_run` and `_link`. `test` writes the held cell
T-1039-lib to expect no frames from the caller's function, as §4.12.3 now
states.

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

## 3. Field types in descriptors and the schema (ACT-1062)

**Status:** designed; in scope as backend row B14; not in source at
`081134ba`.

**Fault.** `schema::subst_for_ctor_fields` pairs a type's arguments with the
type variables of its constructors' fields in order of first appearance. Its
two callers are the trace descriptor baker (`trace_codegen`'s
`build_adt_subst`) and the platform schema walk (`schema::ctors_of`). For
`(deftype (P a b) (MkP [:b y :a x]))` at `(P Int String)`, the baker gives
`y` the type `Int` and `x` the type `String`. The descriptor then formats the
integer as a string, which faults with signal 11
([ACT-1062](../../sprints/actions/ACT-1062-match-field-binder-takes-another-parameters-type-intake.md),
REPRO-1062-f). A parameter that no field mentions shifts every later pairing
in the same way.

**Decision: pair each argument with the declared parameter in its
position.** This is the rule `cranelisp_types::ctor_field_types_at` applies
(release contract §7.4 step 1), here over `Type` rather than `ConcreteType`.
A traced function's scheme can still carry a residual variable.

- **One helper, both callers** (Principle 7). For one constructor, it takes
  the constructor's scheme, `Fn(fields, ADT(name, params))` or a bare
  `ADT(name, params)` when nullary, and the instantiation's type arguments.
  It pairs `params[i]` with `args[i]` and returns the constructor's field
  types under that substitution.
  - A declared parameter that is not a variable must equal its argument; a
    mismatch is the same keying error as `InstantiationMismatch`.
  - An argument count that differs from the declared count is a keying
    error.
  - The baker propagates either error as a located codegen error. The schema
    walk treats it as it treats its other keying misses today, because its
    public entries return a `String`. A miss there yields a wrong layout hash,
    which the DLL load refuses; it never reaches memory. Making the walk's
    misses errors changes `compute_layout_hash` and `generate_schema`, a
    public change that no failing test asks for.
  - The identity elision of FIXME 0284 stays: a declared `Var(id)` paired
    with `Var(id)` is not inserted.
- **Per constructor, not across constructors.** Each constructor's own result
  parameters decide its fields, so the result does not depend on whether
  constructors share variable ids.
- **Readers.** The baker reads each constructor's scheme through
  `CompileContext`, keyed as `constructor_metas` keys it today. The schema walk
  already holds each constructor's scheme. `subst_for_ctor_fields` and
  `collect_var_ids` are deleted with their last caller. The module rows that
  pin the identity elision move to the new helper.
- **No public item changes.** `src/display.rs::build_adt_subst` is the
  binary's own copy of the same rule and is not touched here (below).

**Platform layout hash.** The schema walk's output feeds
`compute_layout_hash`. The hash changes only for a schema type whose fields
name its parameters out of declared order, or omit one. The only in-tree
platform type in a schema is `shapes`' `Rectangle`, which has no parameters.
*Read from the in-tree platform sources on 2026-11-19*: no hash changes.
*Falsifier:* a platform DLL's layout-hash check failing after this change.

**What `dev`(backend) builds** (`schema.rs`, `compiler/trace_codegen.rs`,
`schema/tests.rs`):

1. The helper, and both callers moved onto it.
2. Module rows, each RED against the first-appearance pairing:
   - an out-of-order product (`P` above) yields `[String, Int]` for `MkP` at
     `(P Int String)`;
   - a sum whose constructors disagree on first appearance;
   - an unmentioned parameter (`(deftype (R a b) (MkR [:b y]))` at
     `(R Int String)` yields `[String]`);
   - the identity elision, carried over.
3. The existing in-order cells pass unchanged.

**Cells.** Of the four REPRO-1062 cells still RED, this change turns three
green: `match_field_parameter_order::s124_1062_f_subject_run`, `_link` and
`_repl`. Their ordered, scalar and untraced controls pass throughout.
`s124_1062_e_subject_repl` stays RED. Its locus is the binary's display
reader `src/display.rs::build_adt_subst`, owned by `dev`(`src/`) and carried
outside the focus module. The binary can keep its own copy of the rule, or
`arch` can publish a type-level helper for both crates; that decision is
`arch`'s, not the backend's.
