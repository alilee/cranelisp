# Trace codegen

**Owner:** `design`, narrow-deployed to `cranelisp-backend`. **Subordinate to:**
[backend.md](backend.md).

**Status:** the backend's interior decisions for `(trace …)` that the
architecture leaves to it. The emitted sequence, the descriptor blob, the GOT
swap and the nested-trace guard are
[tracing](../arch/tracing.md) §3–§6 and are not restated here.

Verified against `compiler/trace_codegen.rs`, `lib.rs` and `schema.rs` at
`26fbee2f` (2026-11-20).

- §1, the traced set, is built for one set per call (row B10: int's
  enumerator at `69cd9c18`, then the backend's parameter at `f8c55626`), and
  its within-module order at `e8a9cac5`. `arch` decided on 2026-11-20 that
  the set travels with each target (row B10-C2,
  [tracing §5.1.1](../arch/tracing.md#511-how-the-set-reaches-the-backend));
  that is designed in §1.3 and not built.
- §2 is built: `3cdca9dc` (packet row D8) and its module row M-1038 at
  `997c6c2d`.
- §3, the substitution correction (ACT-1062's backend reader), is built
  (row B14, `4d2bd8a4`).

**Authority:** spec §4.12.2, §4.12.3 and §4.12.9;
[tracing §5](../arch/tracing.md#5-discovery-swap-every-symbol-table) for the
traced set and [§5.1](../arch/tracing.md#51-which-modules-a-form-covers) for
the covered modules;
[tracing §7](../arch/tracing.md#7-strict-evaluation-within-the-trace-extent)
for the strictness and allocation rules.

---

## 1. The traced set is fixed by slot claims, not by slot contents

**The fault it corrected (ACT-1039, closed in S124).** Under `--run` a trace
recorded no call to a function in its own module, and in every mode it
recorded no call to a function restored from the cache. Discovery skipped
every entry whose GOT slot read zero **at trace codegen**. A batch
compiles a module's functions before it publishes any of them, and a cache
restore can write an import's slots after the entry's codegen, so the set was a
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
- **Evidence.** `trace_records_user_function_calls_in_every_mode` and the
  T-1039-w cells are the end-to-end guards. Module rows in
  `compiler/trace_codegen/tests.rs` cover the selection:
  `discovery_selects_claimed_slots_whatever_they_hold` (a claimed but empty
  slot is selected; a slotless entry and a non-function scheme are not) and
  `discovery_skips_constrained_poly_base_and_overloaded`.

### 1.2 What the built selection showed

The evidence behind §1.3: selection by claim cannot land alone. Read against
a reverted patch and probed with the built binary at `1e4b0ce4`. Each probe
used a fresh directory. It stays because a later change to selection or to
the covered set would meet the same constraints.

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
- **A trace's object referenced modules outside its own dependencies**
  (ACT-1078, closed by §1.3), independent of the selection rule. Discovery
  read every loaded table, so a cached object recorded the GOTs of whatever
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
architecturally. Int computes the set; the backend reads it and composes no
copy of the enumeration
([Principle 7](../arch/principles/07-single-source-of-truth.md)). The set is a
function of the form's module's validity record, so it is the same cold, warm
and in every mode, and an object references only GOTs that every image holding
it defines (§1.2).

**The form's module is the module whose source holds the form**, which for a
monomorphised instance is its template's module, not the module whose batch
compiles it (tracing §5.1, *The form's module*; ACT-1086). One set per
`compile_to_module` call cannot state a batch whose targets were written in
different modules, so the set travels with each target (row B10-C2, decided by
`arch` 2026-11-20; **not built** at `26fbee2f`).

- **Input (B10-C2).** `compile_to_module` takes
  `targets: &[CodegenTarget<'_>]`; each `CodegenTarget` pairs a
  `&CallableTarget` with the `&BTreeSet<ModuleFullPath>` a trace form in that
  target's body covers. The call-wide `trace_modules` parameter is removed
  ([tracing §5.1.1](../arch/tracing.md#511-how-the-set-reaches-the-backend)).
  Every target carries a set, whether or not its body holds a form.
- **The set is the whole covered set.** It lists the module that holds the
  body, the closure of that module's finished reference edges, and
  `primitives`. The backend adds no module, `module_path` included, and
  privileges none by name
  ([Principle 19](../arch/principles/19-no-module-privileged-by-name.md)).
  That the set lists the body's own module is the producer's obligation; the
  backend does not ask which module holds a body.
- **Where the set lives in the backend.** The body loop already builds one
  `CompileContext` per target; its covered set is that target's. Inner
  compilers (lambdas, wrappers) inherit the context, so a form in a lambda
  inside the body reads the same set. No other reader takes it.
- **Discovery, for a form in a target's body.** Groups are the modules of
  the set together with `module_path`, visited in `BTreeSet` order.
  - A listed module's table is read whole, under §1.1's selection.
  - When `module_path` is not listed, its group holds only the entries whose
    callable arm's `CallableArm::template_module()` is listed: the instances
    of a covered module's templates that this batch's module demanded
    (tracing §5.1). Every other entry of `module_path` is skipped.
  - A listed module with no table in `symbol_tables` is a located codegen
    error at the form, not a skip
    ([backend.md](backend.md#2-the-reading-discipline--a-pure-keyed-consumer)
    §2).
- **Within a group, entries are ordered by name** (built, `e8a9cac5`, row
  `discovery_orders_each_group_by_name`). Hash-map iteration would otherwise
  fix the wrapper, descriptor and swapped-slot order, and two compilations of
  one module could emit different CLIF ([backend](backend.md) §6;
  [JIT/object convergence](jit-object-convergence.md) §1.3).
- **`macros`.** The enumerator never lists it, so its claims are never read.
- **Open, `spec`'s: an instance frame's name.** A frame's name is
  `{module}/{entry}`. For an instance the entry is its canonical key, which
  already names its template's module, so B10-C2's instance frames read
  `lib/(h/helper [(base/Opt Int) Int] Int)`. Spec §4.12.4 says `name` is the
  traced function's fully qualified name and does not say which spelling an
  instance takes. The backend keeps today's spelling until `spec` states it.

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
  require. Int's enumerator adds the prelude when the fallback is on
  ([int §7.6.4](../int/int.md#764-reference-edges-and-the-covered-trace-set-row-b10));
  tracing §5.1 admits the prelude read as it stands.
- **`macros`: consistent with §4.12.3.** §4.12.3 instruments a synthetic
  module's function only through a slot that holds a real code pointer, and
  no mode writes `macros`' GOT (§1.2). Excluding it therefore drops no
  frame. *Asserted; falsifier:* a write to `macros`' GOT in any mode.

#### As built (B10) and what changes (B10-C2)

Built at `f8c55626`: `compile_to_module` threads one call-wide `trace_modules`
to discovery, which covers `module_path` and the listed modules.

**What `dev`(backend) builds for B10-C2** (`lib.rs`,
`compiler/context.rs`, `compiler/trace_codegen.rs`, their tests, and every
backend test caller of `compile_to_module`), in one commit with
`dev`(`src/`)'s callers (batch record steps A3b and A3c), after `arch`'s
`CallableArm::template_module` (A3a):

1. `CodegenTarget<'a>` with private fields, `new(&'a CallableTarget,
   &'a BTreeSet<ModuleFullPath>)`, `Clone`, `Copy` and `Debug`, and rustdoc
   stating the set's meaning (above). Crate-private accessors only.
2. `compile_to_module` takes `&[CodegenTarget<'_>]` and loses
   `trace_modules`. Target collection reads each target's `CallableTarget`
   as today. The body loop sets each target's `CompileContext` covered set
   from its own `CodegenTarget`.
3. Discovery reads the groups above. The `chain([module_path])` union is
   replaced by the filtered `module_path` group.
4. Test callers pass the set their fixture means. A fixture that relied on
   `module_path` being added lists it.

Module rows in `compiler/trace_codegen/tests.rs`, each RED against the
built rule where it differs:

- **A listed `module_path` is read whole; an unlisted one is not.** With
  `module_path` absent from the set, an ordinary claim in its table is not
  selected. RED today, because the backend adds `module_path`.
- **An instance of a covered template is selected from `module_path`.**
  `module_path` unlisted; its table holds an instance whose
  `template_module()` is listed, and one whose template module is not. Only
  the first is selected. RED today.
- **Two targets, two sets, one batch.** Two targets whose bodies each hold a
  form and carry different sets select different groups. RED today, because
  one set serves the call.
- Carried, adapted to the new input:
  `discovery_covers_module_path_and_listed_modules_only` (renamed to the
  listed-modules rule), `discovery_selects_claimed_slots_whatever_they_hold`,
  `discovery_refuses_a_covered_module_with_no_table` and
  `discovery_orders_each_group_by_name`.

End to end, the ACT-1086 cells are `qa`'s; spec §4.12.3's generic library
row names them.

**Cache.** No persisted shape changed and no `CACHE_SCHEMA_VERSION` bump was
owed. An object built under the old rule differs only in its own trace form's
emission: which GOTs it imports and which slots it swaps. It shares no
convention with code it was not compiled with, because the swap intrinsics,
descriptors and wrapper body are unchanged. So
[module caching](module-caching.md) §14.2's bump rule does not fire.

- The build identity separates the two. B10 is a commit, so `BUILD_ID`
  changed, and the manifest's compiler fingerprint catches an uncommitted
  rebuild.
- The remaining gap is module caching §12's existing empty-fingerprint
  residual. Its face here is a stale trace form, which fails as today, with
  an unresolved GOT symbol at load or a missing frame. *Asserted; falsifier:*
  that residual's own experiment, run on a module holding a trace form.
- B8's bump, 34 to 35, is for B8's own persisted shape. It landed before
  B10, so it does not separate B10's objects, and nothing needs it to.
- B10-C2 is the same case. An object whose trace form sits in an instance
  changes content, and the build identity separates it; no bump is owed.

**End-to-end cells:** `trace::trace_records_user_function_calls_in_every_mode`,
`trace::s124_1039_w_subject_run`, `_link` and `_repl`, and
`trace::s124_1078_subject_run` and `_link`; T-1039-lib expects no frames from
the caller's function, as §4.12.3 states.

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

**Status:** built at `4d2bd8a4` (backend row B14).

**The fault it corrected.** The trace descriptor baker and the platform
schema walk paired a type's arguments with the type variables of its
constructors' fields in order of first appearance. For
`(deftype (P a b) (MkP [:b y :a x]))` at `(P Int String)`, the baker gave
`y` the type `Int` and `x` the type `String`, and the descriptor then
formatted the integer as a string, which faulted with signal 11
([ACT-1062](../../sprints/actions/ACT-1062-match-field-binder-takes-another-parameters-type-intake.md),
REPRO-1062-f). A parameter that no field mentions shifted every later pairing
in the same way.

**Decision: pair each argument with the declared parameter in its
position.** This is the rule `cranelisp_types::ctor_field_types_at` applies
(release contract §7.4 step 1), here over `Type` rather than `ConcreteType`,
because a traced function's scheme can still carry a residual variable.

- **One helper, both callers** (Principle 7): `schema::ctor_field_types_at`,
  with `schema::declared_params` reading the declared parameters from a
  constructor's scheme, `Fn(fields, ADT(name, params))` or a bare
  `ADT(name, params)` when nullary. It pairs `params[i]` with `args[i]` and
  returns the constructor's field types under that substitution.
  - A declared parameter that is not a variable must equal its argument; a
    mismatch is a keying error, as is an argument count that differs from
    the declared count.
  - The baker propagates either error as a located codegen error. The schema
    walk treats it as a leaf, as it treats its other keying misses, because
    its public entries `compute_layout_hash` and `generate_schema` return a
    `String`. A miss there yields a wrong layout hash, which the DLL load
    refuses; it never reaches memory. Making the walk's misses errors would
    change those entries, a public change that no failing test asks for.
  - The identity elision of FIXME 0284 stays: a declared `Var(id)` paired
    with `Var(id)` is not inserted.
- **Per constructor, not across constructors.** Each constructor's own result
  parameters decide its fields, so the result does not depend on whether
  constructors share variable ids.
- **Readers.** The baker reads each constructor's scheme through
  `CompileContext::constructor_metas`. The schema walk already holds each
  constructor's scheme.
- **No public item changed.** `src/display.rs::build_adt_subst` is the
  binary's own copy of the same rule and is outside this design (below).

**Platform layout hash.** The hash changes only for a schema type whose fields
name its parameters out of declared order, or omit one. The only in-tree
platform type in a schema is `shapes`' `Rectangle`, which has no parameters.
*Read from the in-tree platform sources on 2026-11-19*: no hash changed.
*Falsifier:* a platform DLL's layout-hash check failing after this change.

**Evidence.** Module rows in `schema/tests.rs`, each RED against the
first-appearance pairing: an out-of-order product, a sum whose constructors
disagree on first appearance, an unmentioned parameter, a concrete declared
parameter and the schema walk over an out-of-order product, beside the
carried identity-elision row.
`compiler/trace_codegen/tests.rs` holds the baker's refusal of an
instantiation whose arguments do not pair. End to end,
`match_field_parameter_order::s124_1062_f_subject_run`, `_link` and `_repl`
pass, with their ordered, scalar and untraced controls.

`s124_1062_e_subject_repl` stays RED. Its locus is the binary's display
reader `src/display.rs::build_adt_subst`, owned by `dev`(`src/`) and carried
outside the focus module. The binary can keep its own copy of the rule, or
`arch` can publish a type-level helper for both crates; that decision is
`arch`'s, not the backend's.
