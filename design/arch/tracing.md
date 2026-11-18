# Execution tracing — `(trace …)`

**Status.** Adopted architecture contract, landed. The user ruled the shape on
2026-06-04 (root special form; intrinsics-hosted runtime; codegen-baked display
descriptors; swap every symbol table; nested trace is a runtime error; every
build mode including `--link`); S76–S82 delivered it. Owner `arch`. Decision
40's trace half is withdrawn ([label index](decisions/README.md) row 40); this
document is the sole architecture authority for tracing. Strict evaluation
within the trace extent (§7) is built. The mode-independent traced set (§5) is
not in source at `e6d566bf`, and the set of modules a form covers is with the
user for decision (§5.1). §5 marks where source differs.

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
- The static type is always `Trace`, whatever the body's type; the body's
  value is discarded.

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
program owns — bound, walked, summed, filtered, stored. Two consumers depend on
that: the `core.trace` helpers are ordinary functions over `Trace`, and the
REPL `/run-tests` handler (`src/repl/commands.rs`) re-runs a failing test as
`(trace (test-fn))` and reads the first child's `nanos` through
`cranelisp_trace_first_child_nanos`. Do not re-shape tracing as output.

### 2.4 What is traced

Spec §4.12.3 is the normative list. The architectural rule behind it is
**completeness by construction**: every callable whose GOT slot holds a real
code pointer when the trace begins is instrumented, whichever module defines it
and however the call reaches it (§3.5, §5). Which modules a form can cover is
open (§5.1). Structurally invisible: inline-CLIF primitives (no
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
(the twelve runtime bodies, the descriptor formatter, the nesting guard) →
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
   (§5.1; every module in `symbol_tables` at `e6d566bf`), grouped by defining
   module — each module owns one GOT and one GOT
   data symbol. An empty result takes `compile_trace_no_swap` (body, discard,
   `cranelisp_collect_trace`), which returns the minimal `::trace::` node.
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
4. `emit_body_discard` — a category-driven RC release of the body value.
5. `cranelisp_trace_restore_got` per group in reverse order.
6. `cranelisp_collect_trace`, emitted exactly once and last — its result is
   the form's value, and it is the guard's clear point (§6).

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
backend-internal; nothing about tracing crosses the backend boundary as input.

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

**Why every symbol table, not the body's static callee graph.** A trace
narrowed to callees reachable from the body would be unsound: a closure called
through a slot, a trait method resolved at runtime, or a function passed as a
value is a call the static graph cannot see, so a narrowed trace would silently
drop calls. Swapping every GOT has no such hole — any call through any swapped
slot is recorded however the callee was reached. The user accepted the
consequence that stdlib and extern primitives appear in trace trees. This
rationale governs §5 and must survive any future filtering proposal.

## 4. Intrinsics runtime

### 4.1 The twelve bodies and the catalog

`crates/cranelisp-intrinsics/src/trace.rs` hosts `cranelisp_trace_enter`,
`cranelisp_trace_exit`, `cranelisp_trace_swap_got`, `cranelisp_trace_restore_got`,
`cranelisp_collect_trace`, `cranelisp_trace_first_child_nanos`, the five field
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
  admission. Role acquire is a CAS from 0; a
  second thread swapping concurrently pushes a `::skipped::` sentinel and
  returns a sentinel saved-GOT, so it evaluates normally and yields an empty
  trace (spec §4.12.6). Enter/exit are no-ops on a thread that does not own the
  role, which keeps the single stack coherent without per-thread stacks.
- Lock acquisition recovers from poisoning: the stack is append-only during a
  trace, so a partially built frame is safe to discard.

### 4.3 The binary hosts nothing

The binary contributes no trace body, no registration, no formatter and no
discovery. Its residual touches are ordinary: it loads `core.trace` as stdlib,
and `/run-tests` consumes the value (§2.3). `discover-tests` is not part of this
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

**The traced set is a function of the program, not of compilation order**
([Principle 11](principles/11-single-pipeline-mode-parameters.md)). Slot claims
are fixed before codegen in every mode. Slot contents are not: a batch
compiles a module's functions before it publishes any of them, while the REPL
published them in an earlier input. Whether a slot holds code is therefore
decided when the trace begins, by the emitted sequence, from the pre-swap
contents it already loads (§3.3 step 2). A slot that is empty then stays empty
and gets no wrapper, so no wrapper calls through a null original.

**Not in source at `e6d566bf`**, where step 1 reads the slot at codegen and
skips a zero. That makes the set depend on compilation and cache-restore
order, which is ACT-1039's mechanism, confirmed by `qa` with a control.
Selection by claim was built and reverted: it cannot land before §5.1 is
decided, because it makes every reference of §5.1 finding 1 unconditional.
Interior: [trace codegen §1](../backend/trace-codegen.md#1-the-traced-set-is-fixed-by-slot-claims-not-by-slot-contents).

The callable address comes from the slot rather than from a code marker. That
is what includes extern primitives (whose entries carry no code but whose
pointers live in the primitives GOT) without a special case.

### 5.1 Which modules a form covers — with the user (2026-11-18)

**Status: not decided.** The user's 2026-06-04 ruling and spec §4.12.3 say
every module. Source reads every table loaded when the form compiles. Two
findings show that this reading cannot stand; the replacement narrows a
normative statement, so it is the user's.

- **Finding 1 — an object may reference only a GOT that every image holding
  it defines.** A trace form imports `__cranelisp_got_{M}` for each module it
  swaps. Int already owes the general rule: every table an object references
  is reached by its restore walk ([int §7.1](../int/int.md#71-cache-hit-flow-inside-register_module),
  asserted there with the loader's unresolved-symbol error as falsifier). A
  form that reads every loaded table breaks it. Observed by `design`(backend)
  ([trace codegen §1.2](../backend/trace-codegen.md#12-what-the-built-selection-showed)):
  `u` holds a form, entry `e1` imports `u` and `x`, entry `e2` imports `u`
  only; after `--run e1.cl`, both `--run e2.cl` and `--link e2.cl` fail with
  `unresolved symbol: __cranelisp_got_x`. Separately, `macros` claims slots
  and no linked image defines `__cranelisp_got_macros`.
- **Finding 2 — "every loaded table" is not a function of the program.** The
  loaded set at a form's codegen depends on scheduling and on what an earlier
  run cached. For a form outside the entry module it generally omits the
  modules that import the form's module, because they compile later. Spec
  §4.12.3's "however the callee was reached" is therefore not delivered today
  for such a form. *Derived from the pipeline's dependency order and the
  observation above; not probed.* Falsifier: a form in an imported module
  `u`, called from entry `e` with a function of `e`, records `e`'s calls
  identically cold, warm and in every mode.
- **What binds any answer.** The covered set is a function of the object's
  validity record ([Principle 11](principles/11-single-pipeline-mode-parameters.md)),
  and every covered module is one the restore walk loads for the form's
  module (finding 1). One enumeration of those load edges serves the walk and
  discovery ([Principle 7](principles/07-single-source-of-truth.md)); the
  edge set, with its null-import rule, is int's today
  ([int §7.6](../int/int.md#76-dependency-record-and-validity)).

**Proposed, `arch`'s recommendation.** A form covers its own module, every
module that module's load edges reach transitively, and the compiler-owned
modules whose GOT every image defines (`primitives`, and the platform modules
those modules declare).

- The §3.5 rationale survives inside the set: no reachability filter, so a
  closure, a trait method or a function value defined in a covered module is
  recorded however it is reached.
- A form in the entry module or at the REPL prompt covers the whole program,
  because its module reaches every module the program loaded by import.
- **The narrowing.** A form in a module `u` does not record calls made
  inside a module `u` does not reach. The case is a function value or a
  trait implementation handed to `u` by one of its importers:
  `(defn profile [f] (trace (f)))` in a library records the library's own
  callees and none of the caller's. Spec §4.12.3 would state that boundary.
- `macros` is outside the set: it has no object and no image defines its
  GOT. Its slot claims are then never read by tracing and need no change.
- **Not settled by the proposal:** how the backend reads the load-edge set.
  Moving the enumeration into `cranelisp-types` or passing the set through
  the backend's compile entry is an inter-crate public change and returns to
  the [gate](AGENTS.md#public-api-discipline) with its exact delta. A second
  enumeration inside the backend is rejected (Principle 7): a drift between
  the two is an unresolved symbol on a warm start only.

**Alternative that keeps §4.12.3 whole.** Each module's object owns the
wrappers and descriptors of its own slotted functions, every image keeps a
registry of its modules' GOTs and wrapper tables, and a form swaps the
registry. Each object is then a function of its own module and the set is the
running image. The cost is a wrapper and its descriptors for every slotted
function in every object, whether or not the program traces, new intrinsic
exports and a table every linked image must carry. Not recommended for the
dev tier; it stays available if whole-program coverage from a library-held
form is wanted.

**Rejected.**

- *Keep every loaded table and make each image define or load what an object
  references.* It cures finding 1 and leaves finding 2.
- *Seed the `macros` constructors without slots, alone*
  ([trace codegen §1.3](../backend/trace-codegen.md#13-blocked-on-arch-which-modules-contribute)
  item 2). The proposal does not need it, and the unfillable claims are
  constructor-slot retirement's subject (FIXME 0931).

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

**Backend obligations the guard relies on.** Backend never clears the flag,
and emits `cranelisp_collect_trace` exactly once per form, last (§3.3).

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

