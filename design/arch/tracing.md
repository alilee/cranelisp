# Execution tracing — `(trace …)`

**Status.** Adopted architecture contract, landed. The user ruled the shape on
2026-06-04 (root special form; intrinsics-hosted runtime; codegen-baked display
descriptors; swap every symbol table; nested trace is a runtime error; every
build mode including `--link`); S76–S82 delivered it. Owner `arch`. Decision
40's trace half is withdrawn ([label index](decisions/README.md) row 40); this
document is the sole architecture authority for tracing. Strict evaluation
within the trace extent (§7) is built. The mode-independent traced set (§5) and
the covered-module rule the user ruled on 2026-11-19 (§5.1) are in source at
`f8c55626`; the form's module (§5.1, *The form's module*) at `94749709`; the
slot obligation (§3.5) at `1238b31c`. Source does not meet the contract in two
places: the root's result (§3.6; decided 2026-11-20, to be built in S124), and
the first batch of a module compiled before the prelude publishes (§5.1, *Not
met in source*; accepted residual).

**Normative surface.** [Spec §4.12](../../spec/04-expressions.md#412-trace-expression)
(form, semantics, what is traced, nested trace, concurrency, build modes);
[§3.2.4](../../spec/03-types.md#324-trace-type) (the `Trace` ADT);
[§2.3.10](../../spec/02-grammar.md#2310-trace----execution-trace) and
[§2.9](../../spec/02-grammar.md#29-reserved-words) (root special form, reserved
word); [§12.9](../../spec/12-runtime.md#129-value-display-format) (value
display). [§11.5](../../spec/11-stdlib.md) (`core.trace`) is non-normative.

**Cross-context statement.** [BC §3](bounded-contexts.md#3-backend-cratescranelisp-backend)
(backend codegen, discovery and descriptor baking),
[BC §4b](bounded-contexts.md#4b-intrinsics-cratescranelisp-intrinsics) invariant
12 (the runtime is an intrinsic family), [BC §6](bounded-contexts.md#6-binary-int-src-cratescranelisp-exe-bundle)
(the binary hosts no trace runtime). Companion:
[test discovery](test-discovery.md) shares the runtime shape;
[display protocol](display-protocol.md) extends the descriptor ABI of §3.4.

---

## 1. Scope

- This document covers `(trace expr)` only: the root special form that
  evaluates an expression while instrumenting function calls and returns a
  `Trace` value recording the call tree.
- `io_trace` / `IoObserver` (the `CRANELISP_IO_TRACE=1` ring buffer over the
  IO trampoline) is a separate mechanism that shares no state with `(trace …)`
  and never feeds the `Trace` ADT. Its homes are unchanged: the registration
  contract in `crates/cranelisp-intrinsics/src/io_observer.rs` and the
  binary-side buffer in `src/io_trace.rs` (BC §4b, §6).

## 2. Language surface

### 2.1 Form and type

- `trace` is a **root special form** ([Principle 10](principles/10-parser-keywords-distinct-syntax.md)):
  recognised in head position by the AST builder and lowered to `Expr::Trace`
  before any name lookup; always available, no import, no module path, no
  `primitives/trace`.
- Its name is **reserved**. `crates/cranelisp-frontend/src/ast_builder.rs::reject_reserved_binder_name`
  rejects `trace` in every binder and definition position
  (`RESERVED_BINDER_NAMES`); head position is not a binder.
- The static type is always `Trace`, whatever the body's type. The body's
  value is not returned; it produces the root node's result string (§3.6).

### 2.2 The `Trace` ADT and the form/ADT asymmetry

- `Trace` is a compiler-seeded, non-parameterised `primitives` ADT with one
  constructor, `TraceCall [name params result children nanos]`; `params` and
  `children` are `macros/SList`, so traversal is ordinary pattern matching.
  `params` and `result` are pre-formatted `String`s: formatting happens at
  capture time (§3.4), never lazily from raw values.
- The **form** needs no import; the **ADT names** (`Trace`, `TraceCall`, the
  five field accessors) are `primitives` entries that require import or a
  qualified name. This mirrors the `Sexp`-in-`macros` precedent and is
  deliberate (spec §3.2.4).
- `stdlib/core/trace.cl` re-exports the ADT names and adds `trace-show-tree`,
  `trace-show` and `trace-call-string`; none of it is in the prelude.

### 2.3 Why a value, not a slash command

A print-only `/trace` command would stop at the session boundary; the program
could not inspect its own trace. The form returns a first-class value the
program owns — bound, walked, summed, filtered, stored. The `core.trace`
helpers depend on that: they are ordinary functions over `Trace`. Do not
re-shape tracing as output.

The compiler's test runner is not a consumer. `/run-tests`, `/run-all-tests`
and `--test` compile no form and trace nothing; the runner times a run by wall
clock ([test runner](../int/test-runner.md)).

### 2.4 What is traced

Spec §4.12.3 is the normative list. The architectural rule behind it is
**completeness by construction**: every callable whose GOT slot holds a real
code pointer when the trace begins is instrumented, whichever module defines it
and however the call reaches it (§3.5, §5), among the modules the form covers
(§5.1). Structurally invisible: inline-CLIF primitives (no
callable entry), host-promised externs and intrinsic-backed `primitives`
entries (no slot of their own), anonymous lambdas (no named slot; their effects
appear inside the enclosing traced call), and overloaded or constrained-poly
base names (dispatch placeholders — their variants and specialisations are
slotted and traced on their own).

### 2.5 Build modes

`(trace …)` works identically in REPL, `--run` and `--link` (spec §4.12.9).
One codegen path serves every mode (§3.3): backend declares the trace externs
`Linkage::Import`, and they resolve from the intrinsics catalog at each of the
three resolution points (§4.1). `crates/cranelisp-exe-bundle/src/lib.rs`
force-links `cranelisp_intrinsics::trace` so the bodies are present in the
staticlib. Nothing in the frontend or the binary rejects `trace` by mode.

## 3. Pipeline

Frontend (`Expr::Trace`) → typecheck (`infer_trace`) → backend
(`compile_trace`: discovery, wrapper emission, descriptor baking) → intrinsics
(the runtime bodies of §4.1, the descriptor formatter, the nesting guard) →
stdlib display helpers. The binary contributes nothing (§4.3).

### 3.1 Frontend

`crates/cranelisp-frontend/src/ast_builder.rs::build_trace` accepts exactly
one body operand (an optional `:Type` ascription rides the shared body seam)
and produces `Expr::Trace { modules, body, span }`. Quoted occurrences
(`'(trace x)`) are desugared to `Sexp` constructor applications before the
builder sees them and are data, not trace forms.

### 3.2 Typecheck

`crates/cranelisp-typecheck/src/infer.rs::infer_trace` infers the body for its
constraint side effects and records `Type::ADT(primitives/Trace, [])` as the
expression's type. There is no lexical nested-trace check in typecheck: the
dynamic case is only observable at runtime, so a single runtime guard (§6)
covers both shapes.

### 3.3 Backend codegen

`crates/cranelisp-backend/src/compiler/trace_codegen.rs::compile_trace` emits,
for one `(trace body)`:

1. `discover_traced_fns_from_tables` over the modules the form covers
   (§5.1), grouped by the module whose table holds the slot — each module
   owns one GOT and one GOT data symbol. An empty result emits no group and
   no restore: the form is steps 3, 5 and 6, and returns the minimal
   `::trace::` node with its result (§3.6).
2. Per group: the GOT base as a `global_value` against the module's GOT data
   symbol; a read-only `slots` buffer; writable `wrappers` and `originals`
   buffers; then, per traced function, a load of the pre-swap slot contents
   into `originals[i]` and a `compile_trace_wrapper_fn` whose address is
   stored into `wrappers[i]` when that original is non-zero, and zero
   otherwise (§5); then `cranelisp_trace_swap_got(got_base, n, slots,
   wrappers)`.
3. The body, compiled with `in_tail_position = false` and otherwise as any
   expression. Codegen does not mark the body: the runtime declines sparks
   for the trace's dynamic extent (§7).
4. `cranelisp_trace_restore_got` per group in reverse order.
5. `cranelisp_collect_trace(value, descriptor)`, emitted exactly once and as
   the form's last trace call. It receives the body's value and a descriptor
   baked for the body's static type (§3.4, §3.6). Its result is the form's
   value, and it is the guard's clear point (§6).
6. The release of the body's value, which the collect call borrowed. It is
   the release every other value of that type gets: the category gate, then
   the type's drop glue.

Steps 5 and 6 are not in source. Source releases the body's value before the
restores, with no drop glue, and calls `cranelisp_collect_trace` with no
argument (§3.6).

Each wrapper formats every argument through `cranelisp_trace_format(value,
descriptor)` (§3.4), calls `cranelisp_trace_enter(name, len, n, strings)`,
calls the original through `originals[i]` (never the swapped slot, which now
holds the wrapper), formats the result and passes it through
`cranelisp_trace_exit`.

**Every address is a relocation.** GOT bases, buffers, name bytes and
descriptor blobs are data symbols referenced through `declare_data_in_func` +
`global_value`; nothing bakes a compiling-process pointer as an `iconst`. JIT
patches the `global_value`, `ObjectModule` emits a relocation `ld` resolves,
and a linked binary runs in another process. The synthetic `primitives` GOT
is an exported static slab (`crates/cranelisp-primitives/src/lib.rs::PRIMITIVES_GOT_SLAB`,
symbol `__cranelisp_got_primitives`), so it swaps in object mode like any
other module. The externs are declared `(param_count, has_return)`-shaped
through `declare_trace_extern`; every parameter and return is `i64`.

`crates/cranelisp-backend/src/compiler/mod.rs::TracedFnInfo` is
backend-internal. The one trace input that crosses the backend boundary is the
covered set (§5.1.1).

### 3.4 Display descriptor

**Problem.** Rendering a captured argument as canonical display text needs
constructor names and field layouts, which live in the symbol tables. Reading
them at capture time would make the formatter a session concern and was the
one reason tracing once needed the binary.

**Contract.** Backend, which holds the symbol tables at codegen, bakes
everything the renderer needs into a self-contained **display descriptor**
per traced parameter and result (`bake_descriptor_blob`), substituting the
call site's concrete type arguments so polymorphic ADT fields are rendered
concretely. `crates/cranelisp-intrinsics/src/trace_format.rs::cranelisp_trace_format(value, descriptor) -> String`
walks the descriptor and the heap value with **no symbol-table access and no
thread-local state**.

**Ownership and ABI.** `DisplayDescriptor` and `DescriptorKind` are owned by
intrinsics, the crate that consumes them ([Principle 15](principles/15-facade-types-live-with-behavior.md));
backend is the emitter and reads the layout through that rustdoc, never by
re-deriving offsets. One kind per renderable shape (`Int`, `Bool`, `Float`,
`String`, `Fn`, `Vec`, `Adt`, `TypeVar` residual). The exact record, string and
constructor-table layouts are rustdoc on those types — the layout is a
cross-crate ABI in the BC §4b invariant-2 family, and a size change on either
side fails a compile-time assertion.

**One encoding for both modes.** A descriptor tree is a flat,
position-independent **arena blob**: fixed-size records plus the strings and
constructor tables they reference, every cross-link a self-relative byte
offset. The blob carries no absolute address and needs no intra-blob
relocation, so it is identical as a JIT data symbol and as `.rodata` in a
cached `.o`; each wrapper references its blob root through one relocation.
Backend bounds recursive types by identity memo and `MAX_DESCRIPTOR_DEPTH`,
degrading a cycle back-edge to `TypeVar` (bare value) rather than emitting an
unbounded blob. Descriptors are program-lifetime and never freed.

**Consequence.** With the descriptor self-contained the formatter is an
ordinary intrinsic (§4.1). The REPL's result-display path
(`src/display.rs`, `:Type value` envelope) is not involved in capture; the two
renderers share the display format, not code.

### 3.5 GOT copy-swap and completeness by construction

Calls go through per-module GOT indirection, so instrumentation is a table
swap, not a recompilation of callees. `cranelisp_trace_swap_got`, per group:

1. Copies the live GOT (`GOT_TABLE_SIZE × 8` bytes) into a saved buffer.
2. Builds a debug copy with the wrapper addresses at the traced slots.
3. Installs the debug copy over the live GOT in one `memcpy` — no
   partial-swap window.
4. On the first successful swap of a form (role acquire, §4.2) pushes the
   `::trace::` root frame and runs the nesting check (§6).

`cranelisp_trace_restore_got` copies the saved buffer back and frees it. After
the swap every call through a swapped slot — including a callee's own
recursive calls — lands in a wrapper; wrappers reach the original through the
pre-swap `originals` load (§3.3), so they never recurse into themselves.

**Why every slot of a covered table, not the body's static callee graph.** A trace
narrowed to callees reachable from the body would be unsound: a closure called
through a slot, a trait method resolved at runtime, or a function passed as a
value is a call the static graph cannot see, so a narrowed trace would silently
drop calls. Swapping every slot of every covered GOT has no such hole inside
the covered modules (§5.1) — any call through any swapped slot is recorded
however the callee was reached. The user accepted the
consequence that stdlib and extern primitives appear in trace trees. This
rationale governs §5 and must survive any future filtering proposal.

**Every call to a slotted function goes through its slot.** Completeness
rests on it, so it is a backend obligation: no emitted call reaches a named
function that claims a callable slot by any route other than a load of that
slot. This includes the wrapper the backend generates when a named function
is used as a value. A direct call saves one load, a constant factor the dev
tier does not keep
([Principle 27](principles/27-dev-tier-optimises-only-against-blow-up.md)).

- **Met in source at `1238b31c`.** The wrapper calls a target declared in the
  unit being compiled through the target's slot in the current module's GOT,
  as it calls every other target. Before that commit it called such a target
  directly, so a trace covering a function taken as a value in the batch that
  defines it recorded no frame for the call, and the tree depended on how the
  program was batched
  ([Principle 11](principles/11-single-pipeline-mode-parameters.md);
  ACT-1088). Interior:
  [compile-to-module §12.2](../backend/compile-to-module.md#122-every-call-to-a-slotted-function-goes-through-its-slot).
- **Grade: measured.** The backend's module rows
  `fn_as_value::slot_call_tests::wrapper_over_same_unit_target_calls_through_its_slot`
  and its other-module control repoint the target's slot after compilation
  and observe the call follow it; the first failed before the correction.
  `tests/trace.rs::s124_1088_value_subject_run` and its `link` and `repl`
  siblings observe the frame in every mode. The obligation is not structural:
  a new emission site that calls a slotted function by its function id still
  compiles.

### 3.6 The root's result

**Decided, `arch`, 2026-11-20 (row B17); not in source.**
[Spec §4.12.2](../../spec/04-expressions.md#4122-semantics) requires the
body's value to produce the root node's formatted result string. Source
releases the value unformatted, so the root's result is the empty string in
every mode (ACT-1094). `tests/trace.rs::s124_trace_root_call_cold` and its
eight siblings fail on it; the four child controls beside them
(`tests/trace.rs::s124_trace_root_child_control_cold` and its siblings) pass.

- **Contract.** The node a form returns carries, as its result, the canonical
  display of the body's value, rendered from a descriptor baked for the
  body's static type (§3.4). This holds when the form's thread recorded and
  when the form swapped no slot.
- **Who owns what.** The root frame is intrinsics' (§4.2), so the runtime
  writes its result. The backend holds the value and its type, so it supplies
  the value and the descriptor. The form's closing call carries both; no
  datum changes owner.
- **Delta, intrinsics.** One export changes signature. Its name and its
  catalog membership are unchanged, and the catalog row declares two
  parameters.

  ```rust
  // was: pub extern "C" fn cranelisp_collect_trace() -> i64
  pub extern "C" fn cranelisp_collect_trace(value: i64, descriptor_ptr: i64) -> i64
  ```

  - `value` is the body's value, borrowed: the emitting site releases it
    after the call ([BC §4b](bounded-contexts.md#4b-intrinsics-cratescranelisp-intrinsics),
    the convention row).
  - `descriptor_ptr` is the blob root for the body's static type, under the
    contract `cranelisp_trace_format` already states for its descriptor.
  - The entry renders through the crate-private descriptor walk, not through
    `cranelisp_trace_format`. That entry declines off the recording thread
    because a wrapper there has no consumer (§7 rule 2). The collect call
    always has one, the node it returns.
- **Delta, backend.** No public item changes. The emitted sequence changes
  as §3.3 steps 4 to 6 state, with one tail for a form that swaps and a form
  that does not. The backend bakes one more descriptor per form and calls
  `cranelisp_trace_format` only from wrappers.
- **A skipped form (spec §4.12.6).** This row does not decide a skipped
  form's result. Source returns the empty string. Spec §4.12.6 says a skipped
  form returns "no recorded children" and does not name its result, and spec
  §4.12.2 states no exception. Current behaviour stands until `spec` records
  a ruling. Either answer is interior to the collect entry under this
  signature, because the value and the descriptor arrive on every path.
- **Persistence and ABI.** The call sequence baked into a cached object
  changes meaning: an object built before the change calls the entry with no
  argument. `CACHE_SCHEMA_VERSION` is bumped once, in the backend change-set
  that changes the emitted sequence
  ([Principle 14](principles/14-ffi-layout-discipline.md)). `BUILD_ID` does
  not cover an uncommitted build. No serialised shape, descriptor layout,
  platform ABI or layout hash changes.
- **Between the two change-sets.** Intrinsics changes first
  ([approved migrations](../../sprints/METHOD.md#23-gates-that-are-cranelisps-own)).
  - Until the backend follows, a trace form does not compile. Every module
    declares each catalog entry with the catalog's signature
    (`crates/cranelisp-backend/src/jit.rs::declare_intrinsics_generic`), and
    the trace codegen's own declaration of the entry with no parameter is
    then refused. Grade: asserted, read in source and not run. Falsifier: a
    trace form compiles while the backend and the catalog declare different
    parameter counts for the entry.
  - A cache written before the intrinsics change still loads until the
    backend's bump. A trace-form object in it would call the two-parameter
    body with no argument. The intrinsics change-set is therefore not a
    handoff, and no cached end-to-end run is taken between the two.
- **The three questions.**
  - *Bounded context:* yes, for both crates. The runtime keeps the frame and
    the rendering; the backend keeps discovery, baking and emission
    ([BC §3](bounded-contexts.md#3-backend-cratescranelisp-backend), BC §4b
    invariant 12). No dependency is added.
  - *Simple API:* yes. One call finishes a form. The backend does not ask
    whether the thread recorded and handles no "no string" word.
  - *Strongly typed:* yes, within the raw-word emitted ABI that BC §4b
    fixes. The entry that could finish a form without its value no longer
    exists, and no parameter has an absent value. That the descriptor
    matches the value's type stays the emitter's obligation, as it is for
    every wrapper; the nine cells above measure it for an `Int` literal, a
    call and a heap value. No register row's grade drops.
- **Not chosen.**
  - *The backend formats, then passes the String:*
    `cranelisp_trace_format(value, descriptor)` followed by
    `cranelisp_collect_trace(result_str)`. The formatting entry returns `0`
    off the recording thread, so a form that swaps no slot would keep an
    empty result, the parameter would carry an absent value, and a ruling
    for a skipped form's result would need a second interface change.
  - *A second export that sets the root's result before the collect.* It
    adds a path, and a form that omits the call stays expressible.
  - *`cranelisp_trace_exit` for the root.* Exit appends the finished node to
    its parent's children, and the root has no parent.
- **A second defect the release closes.** Source's discard decrements the
  body's value with no drop glue
  (`crates/cranelisp-backend/src/compiler/trace_codegen.rs::emit_body_discard`
  passes `None`). A body whose value owns heap memory, for example an ADT
  with a `String` field, frees its cell and leaks what the cell owns. A
  `String` body owns nothing further, so the T-TRACE-ROOT heap cell does not
  see it. Read in source, not run; no end-to-end cell holds it. Its
  classification and cell are `qa`'s. Interior:
  [trace codegen §4.3](../backend/trace-codegen.md#43-the-release).
- **Residual: a form that swaps no slot reports `nanos` 0** (decided,
  `arch`, 2026-11-20; asserted, with a named falsifier). Spec §4.12.2 gives
  the root an elapsed time without exception, and no start event exists for
  such a form. No program reaches the path: every covered set holds
  `primitives` (§5.1), whose extern primitives claim slots, so only a test
  fixture's empty set swaps nothing (§5.1.1). A start call would be a second
  export on every form's path that corrects no program. Falsifier: a program,
  not a fixture, whose trace form swaps no slot. If one appears, the start
  call returns to this gate. The same falsifier covers a form that swaps no
  slot running inside a recording body, whose collect would close the
  enclosing form ([trace runtime §7.4](../intrinsics/trace-runtime.md#74-residuals-asserted-with-named-falsifiers)).
- **Independent of the root's name.** ACT-1094 routes one question to
  `spec`: whether `(trace (fact 5))` returns a root named for `fact`, as
  spec §4.12.8's example shows, or the synthetic `::trace::` root that source
  returns. Under either reading a synthetic root exists for a body that is
  not one call, and its result is the body's value, so this row stands. A
  ruling for the named root needs a further decision on which bodies omit
  the synthetic root. That decision returns to this gate, and it is not
  assumed here.

## 4. Intrinsics runtime

### 4.1 The trace bodies and the catalog

`crates/cranelisp-intrinsics/src/trace.rs` hosts `cranelisp_trace_enter`,
`cranelisp_trace_exit`, `cranelisp_trace_swap_got`, `cranelisp_trace_restore_got`,
`cranelisp_collect_trace`, the five field
readers `cranelisp_trace_{name,params,result,children,nanos}`, and re-exports
`cranelisp_trace_format` from `trace_format.rs`. They are intrinsics by the BC
§4b definition — string-named targets of backend-emitted calls — and publish
through `crates/cranelisp-intrinsics/src/catalog.rs::intrinsics_table` like
every other intrinsic.

**Name agreement has one owner.** The catalog and its tests own the trace
name set: a renamed or dropped symbol is a catalog test failure, not a runtime
unresolved-symbol crash. Backend's `declare_trace_extern` strings are the
emitted-call ABI names the catalog republishes. The three resolution points
consume the entries uniformly: JIT construction (`crates/cranelisp-backend/src/jit.rs`,
`JITBuilder::symbol` per entry), cache-hit load (`src/worker.rs` registers the
same table into the linker), and `--link` (archive resolution through the
exe-bundle force-link, §2.5).

`consume_trace_call` — the drop helper that walks a `TraceCall` — lives beside
the bodies as a leaf consumer of intrinsics' generic drop glue; the `drop`
module does not reference it, so relocating it created no coupling.

### 4.2 Trace stack and thread ownership

- `TRACE_STACK` (a process-global `Mutex<Vec<TraceFrame>>`) mirrors the live
  call stack while the body runs: enter pushes a frame; exit pops it, stamps
  `nanos`, builds the `TraceCall` and appends it to the new top's children;
  `cranelisp_collect_trace` pops the root and marshals the tree.
- `TRACE_THREAD_ID` holds the trace role, and a thread records exactly when
  it holds it. Under §7 one crate-private predicate in `trace` answers that
  question for every reader: the formatting entry, enter, exit and spark
  admission. Role acquire is a CAS from 0. Enter/exit are no-ops on a thread
  that does not own the role.
- **Only the role holder pushes or pops the stack.** That is what keeps the
  single stack coherent without per-thread stacks: it holds exactly the
  recording form's frames, and that form's collect pops its root before it
  releases the role.
- **A form is wholly recorded or wholly skipped.** A thread whose swap finds
  the role held elsewhere gets a sentinel saved-GOT for every swap of that
  form, evaluates normally and yields a `::skipped::` node with no children
  (spec §4.12.6). The skip is the thread's own state and never a frame on
  the shared stack.
- **Not in source at `4a58af99`; built with row B17's intrinsics step.**
  There a skipped swap pushes a `::skipped::` frame onto the shared stack, a
  collect on a thread that does not record pops it, and the recording collect
  releases the role before it pops. A concurrent skipped form can therefore
  take or displace the recording form's frames, and the tree depends on
  scheduling; no memory is misused. The correction changes no export and no
  emitted call, so it is interior to intrinsics and takes no gate decision
  ([trace runtime §7.1 and §7.2](../intrinsics/trace-runtime.md#71-who-touches-the-trace-stack)).
- Lock acquisition recovers from poisoning: the stack is append-only during a
  trace, so a partially built frame is safe to discard.

### 4.3 The binary hosts nothing

The binary contributes no trace body, no registration, no formatter and no
discovery. Its one residual touch is ordinary: it loads `core.trace` as
stdlib. `discover-tests` is not part of this
family; its placement is [test discovery](test-discovery.md).

## 5. Discovery — swap every symbol table

`discover_traced_fns_from_tables` runs at trace-codegen time over the modules
the form covers (§5.1). Within them it applies no project-root filter and no
reachability set:

1. Select every entry with a callable GOT slot (`callable_got_slot()`;
   overloaded and constrained-poly base names answer `None` structurally).
   Selection reads the slot **claim**, never the slot's contents.
2. Take arity, parameter types and result type from the entry's `Type::Fn`
   scheme; skip anything else.
3. Emit a backend-internal `TracedFnInfo { name, module_path, got_slot,
   arity, param_types, result_type }`; descriptors are baked from it at
   wrapper-compile time.
   - `name` is the frame name spec §4.12.4 requires: an authored entry's own
     qualified name, and for an instance its template's, read from
     [`template_owner()`](interfaces.md#an-instances-template-owner-row-b16).
     Two instances of one template share a name; the table key stays the
     entry's identity
     ([trace codegen §1.4](../backend/trace-codegen.md#14-a-frames-name)).

**The traced set is a function of the program, not of compilation order**
([Principle 11](principles/11-single-pipeline-mode-parameters.md)). Slot claims
are fixed before codegen in every mode. Slot contents are not: a batch
compiles a module's functions before it publishes any of them, while the REPL
published them in an earlier input. Whether a slot holds code is therefore
decided when the trace begins, by the emitted sequence, from the pre-swap
contents it already loads (§3.3 step 2). A slot that is empty then stays empty
and gets no wrapper, so no wrapper calls through a null original.

Selection by claim and §5.1's covered set are one change (`f8c55626`).
Selection by slot contents made the set depend on compilation and
cache-restore order, which was ACT-1039's mechanism. Selection by claim over
every loaded table makes every reference of §5.1's first constraint
unconditional, so neither half stands without the other.
Interior: [trace codegen §1](../backend/trace-codegen.md#1-the-traced-set-is-fixed-by-slot-claims-not-by-slot-contents).

The callable address comes from the slot rather than from a code marker. That
is what includes extern primitives (whose entries carry no code but whose
pointers live in the primitives GOT) without a special case.

### 5.1 Which modules a form covers

**Ruled by the user, 2026-11-19; in source at `f8c55626`.** A trace form
covers its own module, every module that module's reference edges reach
transitively, and `primitives`, whose GOT every image defines.
[Spec §4.12.3](../../spec/04-expressions.md#4123-what-is-traced) states the
rule.

**The form's module is the module whose source holds the form** (decided
2026-11-20; in source at `94749709`). It is not always the module whose batch
compiles it.

- A generic or constrained function is instantiated in the module that
  demands it, with a slot in that module's table, and compiled in that
  module's batch
  ([monomorphisation §3.7](../typecheck/monomorphisation.md#37-cross-module-body-recheck-scoping)).
  A form in its body was written in the template's module, so it covers that
  module's set. Spec §4.12.3 states the library rule with exactly this
  spelling, `(defn profile [f] (trace (f)))`.
- An instance belongs to its template's module for coverage as well. A form
  records a call to an instance whose template is defined in a covered
  module, when the instance's slot is in a covered table or in the table of
  the module being compiled. A generic library function that calls its own
  generic helper therefore records the helper, although both instances live
  in the caller's table. An instance held in any other module's table is
  reached only from inside a function the caller passed, and is not recorded.
- Source before `94749709` rooted every form at the module being compiled, so
  a form in a generic library function covered its caller's closure and
  recorded calls inside the caller's function (ACT-1086). The cells are
  `tests/trace.rs::s124_1086_subject_run` and its two siblings; §5.1.1 states
  the input that corrects it.
- Grade of the second bullet: asserted. That a nested instance is minted in
  the demanding module is read from the typecheck design, not run.
  Falsifier: `m` holds `(defn helper [x] x)` and
  `(defn run [h] (trace (helper (h 1))))`, and the entry calls `(run zf)`
  with `zf` from a module `m` does not reach. The trace holds a `helper`
  frame and no `zf` frame, in every mode. Whether it becomes a cell is
  `qa`'s; without one, the correction of ACT-1086 can drop the `helper`
  frame unobserved.

A module's **reference edges** are the modules it makes an image load:

- each module it imports or re-exports names from;
- each module it calls into, including one named only by a qualified
  reference;
- the prelude, when the module resolves names through the prelude fallback.

A declared child the module neither imports nor calls is not an edge. A
platform module is covered as an ordinary edge of the module that imports or
calls it. Only the entry module declares a platform
([spec §5.10](../../spec/05-definitions.md#510-platform-declaration)), so no library module's own
declaration brings one in.
[Int §7.6.4](../int/int.md#764-reference-edges-and-the-covered-trace-set-row-b10)
owns the enumeration.

- A form in the entry module or at the REPL prompt covers the whole program,
  because every module the program loads is reached from that module by a
  reference edge.
- A form in a module `u` does not record calls made inside a module `u` does
  not reach. `(defn profile [f] (trace (f)))` in a library records the
  library's own callees and none inside the function its caller passed.
- Inside the set there is no reachability filter (§3.5): a closure, a trait
  method or a function value defined in a covered module is recorded however
  it is reached.
- `macros` is outside the set. It has no object and no image defines its GOT,
  so tracing never reads its slot claims.

**What the rule satisfies.** Reading every table loaded when the form
compiles, as source did before `f8c55626`, fails both constraints.

- **An object may reference only a GOT that every image holding it defines.**
  A form imports `__cranelisp_got_{M}` for each module it swaps, and int's
  restore walk loads exactly the reference edges
  ([int §7.1](../int/int.md#71-cache-hit-flow-inside-register_module)).
  Observed with every loaded table
  ([trace codegen §1.2](../backend/trace-codegen.md#12-what-the-built-selection-showed)):
  a cached object failed with `unresolved symbol: __cranelisp_got_x` under an
  entry that does not load `x` (ACT-1078).
- **The set is a function of the program**
  ([Principle 11](principles/11-single-pipeline-mode-parameters.md)). The
  loaded set at a form's codegen depends on scheduling and on what an earlier
  run cached. The covered set is a function of the module's validity record
  ([int §7.6](../int/int.md#76-dependency-record-and-validity)), so it is the
  same cold, warm and in every mode, and a change to it invalidates the object.
  *Members that have not published*, below, states the one exception.

**The set is rooted at the finished module.** For a module compiled from a
file, a form's covered set is the closure from the reference edges of the
whole file, wherever the form stands in it. `--run`, `--link` and a restored
object record the same frames for the same source.

- The specification decides this. An import takes effect for the whole module
  whatever its position
  ([spec §8.3.10](../../spec/08-modules.md#8310-placement)); a form in the
  entry file covers the whole program, with no qualification by position
  (spec §4.12.3); and a form behaves identically in every mode (spec §4.12.9).
  Coverage fixed at the form's own position in the file satisfies none of the
  three.
- **An ordinary form.** A file is one cluster, and its ordinary forms compile
  in one batch against a view that holds every import and every callee module
  of the file
  ([int §7.6.4](../int/int.md#764-reference-edges-and-the-covered-trace-set-row-b10)).
  The set that batch passes is the finished module's, as the object pass's
  is. No ordinary form compiles before a later form of its file adds an edge.
- **A form in a macro clause body.** A `defmacro` publishes at its source
  position, before the file's ordinary batch. Its batch passes the closure of
  the checkpoint's view, a subset of the finished module's set, while the
  module's object covers the whole set. Row B10's meaning admits the subset
  (§5.1.1) because the modules it lacks are reached only through the file's
  ordinary forms, which the clause cannot call.
  - Grade: asserted. The argument holds for calls the clause writes and for
    its arguments, which are syntax. It does not cover a function value the
    clause obtains at run time from a module outside the checkpoint's
    closure, for example from `discover-tests`.
  - Falsifier: a trace form in a clause body records fewer frames when the
    clause is compiled cold than when it runs from a restored object.
- **Falsifier for the rule.** A file module holds `(defn g [h] (trace (h 1)))`
  and, below it, a caller of `(g x/f)`, where `x` is reached by a qualified
  name or by an import written above or below the form. The trace holds an
  `x/f` frame in `--run`, under `--link` and at the REPL. The cells are
  `tests/trace.rs::s124_finished_module_qualified_run` and its eight
  siblings.

**Members that have not published.** The set is read from members' slot
claims, and a member fixes its claims when it publishes a generation. Int
waits for an unpublished member before the batch, through its one dependency
seam, and the cluster retries when the member publishes
([int §7.6.4](../int/int.md#764-reference-edges-and-the-covered-trace-set-row-b10)).
Two members are read as they stand, and a wait is correct for every other.

- **A failed member.** It publishes nothing further, so a wait cannot end.
  The covered set adds no refusal: whether a failed dependency refuses the
  root is the dependency seam's decision. Reading it is safe, because a slot
  that holds no code gets no wrapper (§5).
- **The prelude, for a module the prelude's publication waits on.** A wait
  would close `prelude → parent → child → prelude`
  ([int §6.12](../int/int.md#612-the-implicit-prelude-dependency)). The batch
  covers the prelude as it stands and does not follow its edges.

Both exceptions belong to a batch on a publication path. **The object pass
reads only published members.** It is on no publication path, so it can wait
for any member, the prelude included, and a failed member is the only one it
reads as it stands. A module's object, and every restore and linked image
that uses it, is therefore a function of the program.

**Not met in source: the first batch of a form compiled before the prelude
publishes.** The promise "the same cold, warm and in every mode" does not hold
for the second case's first batch. It is the accepted residual the bullets
below state. The object pass waits for an unpublished covered member
([int §7.6.4](../int/int.md#764-reference-edges-and-the-covered-trace-set-row-b10),
*The object pass waits*, C1; `fe385164`), so the module's object, a restore
of it and a linked image cover the full set:
`tests/trace.rs::s124_1087_subject_run_restored` and `s124_1087_subject_link`
pass.

- **Which modules.** A module whose implicit prelude import is active and
  whose batch runs while the prelude is unpublished. These are the declared
  children of the modules the prelude depends on, such as the stdlib's
  `(mod- test)` children, and the modules those children load. A module the
  prelude reaches by reference edges is not one: it must suppress the
  implicit import
  ([spec §8.8.1](../../spec/08-modules.md#881-implicit-import)), so
  the prelude is no edge of it in any mode.
- **What differs.** The batch that first compiles such a module covers the
  prelude's claims as they stand and no module reached only through the
  prelude. Under the contract the module's object, a restore of it and
  `--link` cover the prelude's whole closure. A first `--run`, a
  `--no-cache --run` or a REPL start therefore omits frames that a second
  `--run` and `--link` record.
- **When it is visible.** Only for a call, inside the form's extent, into the
  prelude or a module the form's module reaches only through the prelude. A
  call the module writes makes the callee's module its own edge, so the call
  must go through a function value passed in from outside.
- **What the specification requires.** The implicit import has the effect of
  the written one (spec §8.8.1), so spec §4.12.3 covers the prelude's closure
  and spec §4.12.9 requires the same frames in every mode. The first batch is
  the nonconforming side.
- **Decision (`arch`, 2026-11-19): the residual stands.** The failure is
  missing frames in a diagnostic tree. It reads and writes no memory it
  should not, because covering fewer modules stays inside the first
  constraint. No shipped stdlib module holds a trace form. Each control costs
  more than that residual:
  - *Waiting on the prelude* deadlocks.
  - *Removing the prelude edge from these modules in every mode* needs their
    membership before the prelude publishes: a source walk from the prelude
    over reference edges and declared children, memoised per prelude
    generation, and the same answer derived again at the object pass. It also
    contradicts spec §8.8.1 and needs the ruling below.
  - *Recompiling the form after the prelude publishes* compiles published
    code twice.
- **Grade: asserted, with a named falsifier.** A project prelude holds
  `(export [m [k]])` and `(export [p [f]])`; `m` and `p` suppress the implicit
  import; `m` declares a child `c` that does not, and `c` holds
  `(defn run [h] (trace (h 1)))`. The entry calls `(m.c/run f)`. A first
  `--run` records no `p/f` frame; a second `--run` and `--link` record one.
  The cells are `tests/trace.rs::s124_1087_subject_run_first_launch`,
  `s124_1087_subject_run_restored` and `s124_1087_subject_link` (ACT-1087).
  The first-launch cell fails for as long as this residual stands; it is a
  defect of the binary, carried on that test.
- **Reopened by** a project that needs the frame, or by a module outside
  this population whose batch can run while the prelude is unpublished.
  `design`(int) read the load paths and found none
  ([int §7.6.4](../int/int.md#764-reference-edges-and-the-covered-trace-set-row-b10),
  *Which modules compile while the prelude is unpublished*; asserted, with
  its falsifier there). If one appears, its cold set depends on scheduling
  and int waits on the prelude for it.

**Open, with the user.** Current behaviour stands for each until ruled.

- *A REPL definition and a later turn.* A function defined at the prompt
  holds a trace form; a later turn loads a module the session had not loaded;
  a third turn calls the function. Spec §4.12.3 says a form at the prompt
  covers the whole program and does not say whether that is the program when
  the form was entered or when it runs. Source compiles the form in its own
  turn, so it covers the program as of that turn. Covering later modules
  needs the whole-program mechanism listed under *Not chosen*.
- *A module reached only by a qualified name.* Spec §4.12.3 says "every
  module it imports". This contract covers such a module from a library form
  as it does from the entry, where the whole-program rule requires it,
  because no module is privileged by name
  ([Principle 19](principles/19-no-module-privileged-by-name.md)). The
  specification's wording does not state that for a library module.
- *A form compiled before the prelude publishes.* Spec §4.12.3 and §4.12.9
  make no exception for the residual above, so a failing cell for it is a
  defect. An exception would be one sentence in spec §4.12.3: a trace form in
  a module that the prelude's compilation waits on, a declared child of a
  module the prelude depends on, does not cover the prelude or a module it
  reaches only through its implicit prelude import. With that sentence the
  conforming build removes the prelude edge from those modules in every
  mode, by the source walk described above.

#### 5.1.1 How the set reaches the backend

Int owns the reference-edge enumeration and decides which module holds each
form; the backend receives the result. The backend composes no copy of either
([Principle 7](principles/07-single-source-of-truth.md)): a drift between two
enumerations is an unresolved symbol on a warm start only, and a drift
between two readings of a form's module is ACT-1086 again.

**Decided, `arch`, 2026-11-20 (row B10-C2); in source at `94749709`.** The
set travels with each target. Row B10 (`69cd9c18`, `f8c55626`) passed one set
for the call, to which the backend added `module_path`; that could not state a
batch whose targets were written in different modules (§5.1, *The form's
module*).

- **Delta, backend.** A new public type and a changed entry point.

  ```rust
  /// One callable to compile and the modules a trace form in its body covers.
  #[derive(Clone, Copy, Debug)]
  pub struct CodegenTarget<'a> { /* private fields */ }

  impl<'a> CodegenTarget<'a> {
      pub fn new(
          target: &'a CallableTarget,
          trace_modules: &'a BTreeSet<ModuleFullPath>,
      ) -> Self;
  }

  pub fn compile_to_module<M, C, L>(
      module_path: ModuleFullPath,
      targets: &[CodegenTarget<'_>],
      symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
      module: &mut M,
      capture_clif: bool,
  ) -> Result<CompilationArtifacts, CompilationError>
  ```

  `targets` changes its element type and the `trace_modules` parameter is
  removed. The bounds are unchanged.
- **Delta, types (in source, `bb217cdc`).**
  `CallableArm::<C>::template_module(&self) -> Option<&ModuleFullPath>`: the
  module that defines the template a minted instance was made from, and
  `None` for any other arm. It is the module of
  [`template_owner()`](interfaces.md#an-instances-template-owner-row-b16),
  which reads the recorded instance link and derives nothing. Int and the
  backend both need this one fact, and the method keeps it in one place.
- **Meaning of a target's `trace_modules`.** Every module a trace form in
  that target's body covers: the module whose source holds the body, the
  transitive closure of that module's finished reference edges, and
  `primitives`. It is the whole set; the backend adds no module to it and
  privileges none by name
  ([Principle 19](principles/19-no-module-privileged-by-name.md)).
  - A batch may pass a subset only where §5.1 admits one: a macro
    checkpoint's view, and the prelude read as it stands.
  - It is passed for every target, whether or not the body holds a form;
    there is no "not computed" value. An empty set means a form that swaps
    nothing, which only a test fixture passes.
  - A set carries no order or repetition, and the backend emits groups in its
    iteration order.
- **Producer.** The binary, at its two production callers: the one JIT caller
  in `src/worker.rs`, from the sets commit planning stored on the prepared
  turn, and the object pass in `src/session_v4/nice_worker.rs`.
  - The module that holds a target's body is the arm's `template_module()`,
    and the batch's module where that is `None`.
  - Both callers derive one set per distinct such module among the batch's
    targets, with the one crate-private function over the enumerator that
    the restore walk also reads, and pair each target with its set
    ([int §7.6.4](../int/int.md#764-reference-edges-and-the-covered-trace-set-row-b10)).
  - Both callers also derive the batch's own module's set when no target was
    written there, and for a batch with no targets. No target carries that
    set. It keeps §5.1's wait a property of the batch: a batch waits for the
    unpublished members of its module's closure whatever its targets are, as
    it did under row B10.
  - Test callers pass the set their fixture means.
- **Consumer.** The backend's discovery, for a form in a target's body:
  - reads the table of each listed module whole;
  - where `module_path` is not listed, reads from `module_path`'s table only
    the entries whose `template_module()` is listed. These are the instances
    §5.1 assigns to a covered module;
  - refuses a listed module that has no table with a located codegen error,
    not a skip. `module_path` with no table is refused the same way when it
    is not listed: its table is where the covered instances are read, so a
    skip would drop their frames without an error.

  The backend does not ask which module holds the target's own body.
- **What an object may reference.** A target's set is inside the closure of
  the module being compiled, because that module demanded the instance and
  so reaches the template's module by a reference edge. The object still
  imports only GOTs that every image holding it defines (§5.1).
- **Persistence.** No persisted shape, schema version or ABI changes. An
  object holding a form in an instance changes content, and the cache's build
  identity separates it from one built under the old rule
  ([trace codegen §1.3](../backend/trace-codegen.md#13-which-modules-a-form-covers)).
- **The three questions.**
  - *Bounded context:* yes. Which module holds a form stays the binary's
    reading of typecheck's recorded link; the backend gains no instance
    concept beyond the two projections of the instance link, the template's
    module here and its owner for the frame name; no dependency is added.
  - *Simple API:* yes. One path: each target arrives with its set, and the
    backend looks nothing up.
  - *Strongly typed:* yes. A target without a set cannot be passed, which a
    map keyed by module would allow. That a set lists the body's own module
    is the producer's obligation, like the rest of its contents; every trace
    cell that records a call in the form's own module fails if it does not.

**Not chosen.**

- *Whole-program coverage from a library-held form.* Each object would own
  wrappers and descriptors for its own slotted functions and every image
  would carry a registry a form swaps. It costs every object and every image
  whether or not the program traces. Reopened if the user wants a library's
  form to record its caller's functions.
- *Moving the reference-edge enumeration into `cranelisp-types`.* A larger public
  change that separates the null-import rule from the walk that owns it.
- *A slice, `&[ModuleFullPath]`.* It can repeat a module and it carries the
  enumerator's traversal order into the emitted object.
- *A map from module to set, with the backend finding each target's module.*
  A missing key is expressible and is found only when a form compiles. Two
  crates would each decide which module holds a body, and a disagreement
  that still finds a key is a wrong trace with no error.
- *One `compile_to_module` call per module of origin.* A batch is one unit:
  its bodies call one another by function identifier, and each call defines
  the module's GOT data symbol once.
- *Instantiating a generic in its template's module.* That moves slot
  ownership in typecheck (monomorphisation §3.7) and is a far larger change.

## 6. Nested-trace guard

Same-thread re-entry (`(trace … (trace …))`, lexically or through a call) is a
runtime error (spec §4.12.5); cross-thread concurrency is the §4.2 skip.
Without the guard the inner form's swap took the same-thread multi-module
branch, its `collect` released the role, and the outer form's bookkeeping was
silently corrupted.

**Placement.** The check is `crates/cranelisp-intrinsics/src/trace.rs::arbitrate_trace_role`,
reached from `cranelisp_trace_swap_got` when the calling thread already owns
the role. It must distinguish a legitimate second-group swap of the *same* form
(all of a form's swaps precede its body) from a re-entrant form. Two
intrinsics-owned signals do so; backend emits nothing for the guard:

- `TRACE_BODY_RUNNING` (thread-local) is raised by the first
  `cranelisp_trace_enter` after role acquire and cleared by
  `cranelisp_collect_trace`. A same-thread swap while it is set is **dynamic**
  re-entry.
- `SWAPPED_GOT_BASES` (thread-local) records each base the active form has
  swapped; `restore_got` removes it. A same-thread swap of a base already in
  the set is **lexical** re-entry, which the flag alone misses because the
  inner form's swap runs before any wrapper fires.

Either signal raises through the `runtime/panic` intrinsic with the message
`nested trace is not supported: (trace ...) may not appear inside an
actively-tracing (trace ...)`. A panic inside the bracket ends the process
([bounded contexts](bounded-contexts.md) §4b invariant 13), so no later form
runs and the guard needs no panic cleanup.

**Open, with `spec`: a form entered inside a skipped form on the same
thread.** Spec §4.12.5 forbids a form "while another `(trace ...)` is
actively tracing on the same thread" and does not say whether a skipped form
is actively tracing. The guard reads the role, which a skipped thread does
not hold, so no error is raised. Under row B17's runtime both forms return
childless roots and the enclosing one reads as a form that swapped nothing
([trace runtime §7.4](../intrinsics/trace-runtime.md#74-residuals-asserted-with-named-falsifiers)).
That behaviour stands until a ruling; no cell reads it.

**Backend obligations the guard relies on.** Backend never clears the flag,
and emits `cranelisp_collect_trace` exactly once per form, as the form's last
trace call (§3.3).

## 7. Strict evaluation within the trace extent

**Status:** ruled by the user on 2026-11-16 and stated by spec §4.12.2 item 2;
built at `3cdca9dc` (S124 packet row D8). ACT-1038 carries the two guards in
`tests/trace.rs`; its closure is `qa`'s.

**The fault.** Wrappers are installed in the process-wide GOT (§3.5), so a
traced callee that sparks runs its calls through wrappers on worker threads.
A wrapper formats its arguments before the runtime knows whether the calling
thread records, and enter and exit are no-ops off the role thread (§4.2).
Worker calls are therefore unrecorded and their formatted strings are never
released ([BC §4b](bounded-contexts.md#4b-intrinsics-cratescranelisp-intrinsics),
the `cranelisp_trace_enter` and `cranelisp_trace_exit` convention rows).

**The contract.**

1. **No spark is admitted inside a trace's dynamic extent.** From role acquire
   to `cranelisp_collect_trace`, every evaluation reached from the body is
   strict and sequential on the role thread, including code compiled outside
   the form. The extent is dynamic, so the decision is the runtime's: emitted
   code cannot know at compile time whether it will run under a trace. A
   compile-time mark on the form's lexical body is not the mechanism; the
   former `in_trace_body` flag is deleted.
2. **No wrapper allocates before it has a consumer.** A wrapper that will not
   record formats nothing. With rule 1 no wrapper runs off the role thread
   during a trace, but the rule stands alone: it is what makes a wrapper
   reached by any other route leak-free.
3. **The recorded tree is a function of the program**, not of scheduling. A
   trace does not show how the program parallelises and its timings are
   sequential. Recording worker frames was rejected for now: it needs a
   cross-thread merge in the trace runtime and makes the tree depend on
   scheduling. It is revisited when a need arises.
4. **Cross-thread trace forms are unchanged.** A second thread that evaluates
   its own `(trace …)` concurrently still takes the §4.2 skip (spec §4.12.6).

**Ownership.** Both rules cross the backend/intrinsics seam: spark admission
is an intrinsics gate (BC §4b in scope) reached from backend-emitted spark
sites, and the wrapper's call sequence is backend-emitted (§3.3) against
intrinsics-owned role state (§4.2). The two interior designs place each rule.
The binary contributes nothing (§4.3).

**Placement.** Both rules live in existing intrinsics and change no emitted
call sequence. `design`(backend) proposed it
([trace codegen §2](../backend/trace-codegen.md#2-the-trace-extent-and-the-wrappers-allocation))
and `design`(intrinsics), which owns both bodies, confirms it
([trace runtime](../intrinsics/trace-runtime.md)):

- Rule 1: `cranelisp_spark_budget_try_reserve`, the gate every lenient spark
  passes, declines while the calling thread holds the trace role.
- Rule 2: `cranelisp_trace_format` returns no string (`0`) on a thread that
  does not record. `cranelisp_trace_enter` and `cranelisp_trace_exit` already
  ignore their string arguments on such a thread.
- The backend does not branch on recording state. That would need a query
  export and a second reading of a fact intrinsics owns.
- Rule 1 is decided per thread, not while any trace is active: evaluation on
  other threads is outside the extent and keeps its parallelism.
- **Residual (asserted, with a named falsifier).** An IVar created before the
  trace began and forced inside it runs on whichever thread claims the cell.
  If a worker claims it, its calls are unrecorded and the tree depends on
  scheduling, against rule 3; nothing leaks. The falsifier of "nothing leaks" is the backend's
  ([trace codegen §2](../backend/trace-codegen.md#2-the-trace-extent-and-the-wrappers-allocation)).
  Closing the scheduling dependence is not scheduled.

**Public surface (S124 packet row D8, built).**
No signature changed and no export was added, so the baselines read +0. The
documented contract of the two exports changed, which a baseline cannot show;
the row carries it. Any changed or added export returns to the gate.
The convention rows of BC §4b state it. With spark statistics on, a
trace decline is counted in its own `trace_declines` field, so evidence can
tell it from a budget or depth decline.

**Mode parity.** ACT-1039 records that a `--run` trace omits user functions
that the REPL trace records. §2.5 already requires identical behaviour in every
mode, so that is a defect against this contract. §5 states the rule it
violates.

