# Execution tracing — `(trace …)`

**Status.** Adopted architecture contract, landed. The user ruled the shape on
2026-06-04 (root special form; intrinsics-hosted runtime; codegen-baked display
descriptors; swap every symbol table; nested trace is a runtime error; every
build mode including `--link`); S76–S82 delivered it. Owner `arch`. Decision
40's trace half is withdrawn ([label index](decisions/README.md) row 40); this
document is the sole architecture authority for tracing.

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
**completeness by construction**: every callable holding a GOT slot with a real
code pointer is instrumented, whichever module defines it and however the call
reaches it (§3.5, §5). Structurally invisible: inline-CLIF primitives (no
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

1. `discover_traced_fns_from_tables` over every module in `symbol_tables`
   (§5), grouped by defining module — each module owns one GOT and one GOT
   data symbol. An empty result takes `compile_trace_no_swap` (body, discard,
   `cranelisp_collect_trace`), which returns the minimal `::trace::` node.
2. Per group: the GOT base as a `global_value` against the module's GOT data
   symbol; a read-only `slots` buffer; writable `wrappers` and `originals`
   buffers; then, per traced function, a load of the pre-swap slot contents
   into `originals[i]` and a `compile_trace_wrapper_fn` whose address is
   stored into `wrappers[i]`; then `cranelisp_trace_swap_got(got_base, n,
   slots, wrappers)`.
3. The body, compiled with `in_trace_body = true` (no lenient sparking, so the
   tree is complete and deterministic) and `in_tail_position = false`.
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
- `TRACE_THREAD_ID` holds the trace role. Role acquire is a CAS from 0; a
  second thread swapping concurrently pushes a `::skipped::` sentinel and
  returns a sentinel saved-GOT, so it evaluates normally and yields an empty
  trace (spec §4.12.6). Enter/exit are no-ops on a thread that does not own the
  role, which keeps the single stack coherent without per-thread stacks.
- Lock acquisition recovers from poisoning: the stack is append-only during a
  trace, so a partially built frame is safe to discard.

### 4.3 The binary hosts nothing

The binary contributes no trace body, no registration, no formatter and no
discovery. Its residual touches are ordinary: it loads `core.trace` as stdlib,
and `/run-tests` consumes the value (§2.3). `discover-tests` and
`catch-runtime-error` are not part of this family; their placement is
[test discovery](test-discovery.md).

## 5. Discovery — swap every symbol table

`discover_traced_fns_from_tables` runs at trace-codegen time over every module
in `symbol_tables`, with no project-root filter and no reachability set:

1. For every entry with a callable GOT slot (`callable_got_slot()`; overloaded
   and constrained-poly base names answer `None` structurally), read the
   callable address **from the GOT slot** — the single source of truth for
   callable addresses (BC §3) — and skip a zero.
2. Take arity, parameter types and result type from the entry's `Type::Fn`
   scheme; skip anything else.
3. Emit a backend-internal `TracedFnInfo { name, module_path, got_slot,
   arity, param_types, result_type }`; descriptors are baked from it at
   wrapper-compile time.

Reading the address from the slot rather than from a code marker is what
includes extern primitives (whose entries carry no code but whose pointers
live in the primitives GOT) without a special case.

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
actively-tracing (trace ...)`. A panic that crosses the bracket without
reaching `collect` is cleaned by `clear_trace_guard_on_panic` from
`catch-runtime-error`, so the next form starts clean.

**Backend obligations the guard relies on.** Backend never clears the flag,
and emits `cranelisp_collect_trace` exactly once per form, last (§3.3).

## 7. Open obligations

- [ACT-0984](../../sprints/actions/ACT-0984-trace-link-test-claim-intake.md)
  (`qa`): `tests/s68_primitives_uniform.rs` still carries a test asserting
  link-mode rejection of `(trace …)`, contrary to spec §4.12.9 and §2.5.
  Positive link-mode evidence is `tests/link.rs`. Its disposition does not
  reopen the build-mode ruling.
