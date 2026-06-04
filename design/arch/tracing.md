# `(trace ...)` — the runtime execution-trace feature

**Status.** Canonical subsystem design (TARGET STATE, S76). The body of this document
states the **target architecture decided by the user 2026-06-04**: tracing is encapsulated
in the trace keyword-node + the **intrinsics crate** (bodies, table, runtime guard) + the
**backend** (codegen + display-descriptor baking + discovery-in-codegen) — with **no int
runtime involvement**. The historical path that got us here (D40 relocation-to-int, the S76
`Jit::new` registration seam) is preserved compactly in §7 (History) — but §7 is archaeology;
§§1–6 are the target. The previous two passes of this document (current-state consolidation +
the §7 FOR-USER-REVIEW proposal) have been **enacted**: the proposal is now the decision, the
counterpoints are resolved as recorded in §3.5 / §6.

**Owner.** `/arch`. Subsystem-design doc per `.claude/commands/arch.md` §"Target documentation
set" — cited by `bounded-contexts.md` §3 (backend emits + bakes + discovers), §4b (intrinsics
hosts the bodies + table + guard), and §6 (int does nothing but discovery-deletion). Remains
referenced while `(trace ...)` is part of the language.

**Reads.** `spec/04-expressions.md` §4.12 (the normative source); `spec/03-types.md` §3.2.4
(the `Trace`/`TraceCall` ADT); `spec/11-stdlib.md` §11.1/§11.2/§11.5 + `spec/appendix-a-builtins.md`
(`trace` entry); `bounded-contexts.md` §3 (backend), §4b (intrinsics), §6 (int); Principle 10
(special forms: root vs module-scoped — `trace` is root-scoped + reserved); Principle 7 (single source of truth); Principle 18
(enforce invariants structurally); Decision 0040 (amended/partially-retracted — see §7);
Decision 0048 (the synthetic-module mount + dispatch-asymmetry precedent). Source (target sites):
`crates/cranelisp-frontend/src/ast_builder.rs` (`build_trace` — unchanged), `crates/cranelisp-typecheck/src/infer.rs`
(`infer_trace` — unchanged), `crates/cranelisp-backend/src/compiler/trace_codegen.rs` (`compile_trace`,
the descriptor-baking, discovery-in-codegen), `crates/cranelisp-intrinsics/src/trace.rs` (TARGET —
the relocated 12 bodies + `trace_format` + `TRACE_STACK`/`TRACE_THREAD_ID` + `consume_trace_call`
+ the nesting guard), `crates/cranelisp-intrinsics/src/catalog.rs` (`intrinsics_table()` — gains
the trace family). What DELETES: `src/trace.rs`, `src/session_v4.rs::build_traced_fns` /
`repl_trace_format` / `TRACE_DISPLAY` / the trace half of `int_intrinsics()`.

---

## 1. Scope

This document covers **`(trace expr)` only** — the language-level root special form that evaluates an
expression while instrumenting function calls and returns a `Trace` ADT recording the call tree.

**`io_trace` / `IoObserver` is OUT of scope and UNRELATED, and STAYS WHERE IT IS.** Despite the
shared word "trace", the IO-observation pathway (`CRANELISP_IO_TRACE=1` ring-buffer diagnostics of
the IO trampoline / scheduler) is a separate, independent mechanism with its own callback contract.
It does not feed the `Trace` ADT, is not reachable from `(trace ...)`, and shares no runtime state.
Its canonical home is unchanged by this target: the `IoObserver` extension-point contract in
`crates/cranelisp-intrinsics/src/io_observer.rs` (the ~50-line registration API), the int-side
ring-buffer implementation in `src/io_trace.rs`, and `bounded-contexts.md` §4b (intrinsics — IO
observation) + §6 (int — observability). The D40 ruling that relocated `io_trace.rs`'s ring buffer
to int **remains valid** — only the `(trace ...)` half of D40 is retracted here. For `io_trace`,
go there; this document says nothing further about it.

---

## 2. Spec grounding + usage pattern

### 2.1 The normative behaviour (spec §4.12)

`(trace expr)` evaluates `expr` once, under normal strict evaluation, while instrumentation records
every call to an instrumented function. On completion it constructs and returns a `Trace` value —
a **pure data value, not a side effect** (§4.12, §4.12.2). The traced expression's own value is
discarded; only the recorded call tree is returned. The static type is always `Trace` regardless of
the body's type (§4.12.1):

```
E |- expr : T
----------------------------
E |- (trace expr) : Trace
```

Each recorded call captures: the fully-qualified function name, the arguments formatted via the
canonical value-display format (§12.9), the formatted return value, the child calls (in call order),
and the wall-clock elapsed nanoseconds (§4.12.2).

**What is traced (§4.12.3) — TARGET widens this.** The decided target swaps **all** symbol tables
at trace-codegen time (§5), so the traced set is now *every* callable with a GOT slot, **including
stdlib/lib-search-path modules and the synthetic `primitives` module's extern primitives**. The
"project-root filter" that the prior implementation used is **deleted** (§5). Spec §4.12.3's
"library modules / extern primitives are NOT instrumented" exclusions therefore become **stale** and
join the /spec cascade (§6, FIXME-for-/spec): the target is *completeness by construction* — if it
has a GOT slot and a real code pointer, it appears in the tree. The one category that remains
genuinely invisible is **inline-CLIF arithmetic** (`+`, `-`, comparisons) — those compile to inline
instructions and have no callable entry to wrap; that exclusion is structural and unchanged. Anonymous
lambdas (no named GOT entry) and constrained-poly base-name dispatch placeholders (skipped — their
monomorphised specializations *are* traced) also remain invisible. See the §5.2 taxonomy.

**Nesting (§4.12.5) — TARGET changes this to an ERROR.** Same-thread re-entrant `(trace (trace e))`
is **disallowed via a runtime guard** (§6): it raises a runtime error through the §12.7 panic
machinery. The prior spec rule ("only the outermost trace is active … single tree") is replaced by
"nested trace is an error" (the /spec cascade carries the §4.12.5 amendment text in §6).

**Concurrency (§4.12.6) — UNCHANGED.** Cross-thread concurrent tracing keeps the existing CAS +
`::skipped::` sentinel semantics: at most one thread holds the trace role; a second concurrent tracer
on a different thread evaluates normally and returns an empty trace (§5.4).

### 2.2 The `Trace` ADT (spec §3.2.4, §4.12.4)

`Trace` is a compiler-seeded, non-parameterised ADT in the `primitives` module with one constructor:

```clojure
(deftype Trace
  (TraceCall [:String          name
              :(SList String)  params
              :String          result
              :(SList Trace)   children
              :Int             nanos]))
```

**Form/ADT asymmetry (deliberate).** The keyword **`trace` is NOT a `primitives` entry** — there is
no `primitives/trace`. It is a root special form (§2.4, §3.1, Principle 10): always available, no
import, no module path, recognised by the parser before any name lookup. The *ADT* it returns is the
opposite: `Trace`, `TraceCall`, and the field accessors (`name`, `params`, `result`, `children`,
`nanos`) ARE `primitives`-module entries and are **NOT auto-imported** — to destructure a returned
trace, user code imports the names explicitly (`(import [primitives [Trace TraceCall name params
result children nanos]])`) or uses qualified names. This asymmetry is deliberate and mirrors the
existing `Sexp`-in-`macros` precedent (quasiquote works without import because the expander emits
qualified constructors; bare `Sexp` constructors need the import). Spec §3.2.4 states the asymmetry
explicitly; §11.1's "module-scoped, requires import for `trace`" framing is the **stale side** (it
conflates the form with the ADT names) and is reconciled by the /spec cascade (FIXME 0257). The
`params` and `children` fields use `SList` (from the `macros` module, `SCons`/`SNil`), so traversal
is ordinary pattern matching. The ADT shape is unchanged by this target — `params`/`result` remain
pre-formatted `String`s (the descriptor design §3 formats *at capture time*, exactly as today; it
does not change the ADT to carry raw values).

### 2.3 Usage pattern — trace is a value, bound/traversed/transformed (§4.12.7, §4.12.8)

Because the return is an ordinary ADT, programs bind it, pass it, store it, and pattern-match it:

```clojure
(let [t (trace (fact 5))]
  (match t [(TraceCall n p r c ns) n]))      ; => "user/fact"

(nanos (trace (factorial 4)))                ; => Int wall-clock nanoseconds
```

The stdlib `core.trace` module (spec §11.2/§11.5) re-exports the primitives and adds display helpers —
`trace-show-tree` (full indented call tree), `trace-show` (single-node summary), `trace-call-string`
(call signature). `(import [core [trace [*]]])` brings the re-exported primitives and the display
functions together. These are deliberately NOT in the prelude — tracing is a developer tool.

### 2.4 Why a language form, not a `/trace` slash command (UNCHANGED)

This is the load-bearing design rationale, and it is the **Composability** property made explicit
(`sketch/docs/trace.md` §Design properties — "a regular value: bind it, pass it, transform it"):

- A slash command would print a tree at the **session boundary** and stop there — the trace would be
  output, not data. The program could not inspect it.
- The form returns a **first-class `Trace` value the program owns**. A program can bind it, walk its
  `children`, sum `nanos`, filter sub-trees, feed it to user-written analysis, or store it. The trace
  becomes part of the computation, not a side effect of running it.
- Concrete dependents on this property: the stdlib `core.trace` helpers (ordinary functions over
  `Trace` values), and `/run-tests`'s re-run-failures-under-trace flow — a failing test is re-run
  inside `(trace (test-fn))` and the resulting `Trace` value drives per-call timing
  (`cranelisp_trace_first_child_nanos` reads the first child's `nanos`). A print-only command could
  not hand a value to either.

This is the Principle-10 **root special form** category in action (user ruling 2026-06-04): `trace`
is recognised by the parser/AST-builder and the typechecker as a dedicated `Expr::Trace` node — the
same recognition family as `defn`/`let`/`if`/`match` — and is **always available, no import, no
module path**. There is no `primitives/trace`. As a root special form its name is **reserved**: user
code cannot define or bind `trace` (`(defn trace …)`, `(let [trace …] …)`, `(fn [trace] …)` are
rejected outright, not allowed-but-shadowed; §3.1 + §6). The earlier "module-scoped special form" /
"standalone keyword exception" framings are superseded; the keyword-vs-module-scoped tension is
resolved by root-scoping (see Principle 10's two-category amendment + §6).

### 2.5 Mode availability — TARGET: ALL MODES, INCLUDING `--link`

`(trace ...)` is available in **all build modes — REPL, `--run`, AND `--link`** (user ruling
2026-06-04: "happy to let tracing applications be linked"). This **retracts** Decision 0040's
REPL/`--run`-only mode restriction (§7).

The mechanism: the trace bodies live in `cranelisp-intrinsics` (§4) and are published through
`intrinsics_table()` like every other intrinsic. Because the exe-bundle force-links the intrinsics
crate, the trace bodies are pulled into the `--link` staticlib exactly as `alloc`/`drop`/`io`/`rc`
are — **the deliberately-deleted `pub use cranelisp_intrinsics::trace;` force-link line returns**
(now justified: trace is an ordinary intrinsic, not a dev-only int concern). Backend emits the trace
externs as `Linkage::Import` in every mode (one codegen source path; the `Module` instance is the
only mode difference), and they resolve in every mode:

- **JIT (REPL / `--run`)** — `JITBuilder::symbol(name, ptr)` from `intrinsics_table()` at
  `Jit::new(symbol_tables)` setup.
- **`--link`** — the names resolve against the `cranelisp-intrinsics` archive bundled into
  `libcranelisp_exe_bundle.a`.

The spec §4.12.9 "link-time rejection" clause is therefore **replaced** with all-modes availability
(the /spec cascade carries the §4.12.9 amendment text in §6). The only mode-specific consideration:
the display-descriptor (§3) must survive `.o` caching + relocation in object mode — that constraint
shapes the descriptor's data encoding (§3.4).

---

## 3. Pipeline walk — parse → typecheck → codegen → intrinsics-runtime → stdlib

The target pipeline is **five surfaces with NO int runtime involvement**: frontend (`Expr::Trace`
keyword node) → typecheck (`infer_trace`) → backend (`compile_trace` + descriptor baking + discovery)
→ **intrinsics** (the 12 runtime bodies + the pure `trace_format` + the nesting guard) → stdlib
(`core.trace` display helpers). int's only residual touch is *deletion* — the discovery that used to
live in `build_traced_fns` moves into backend codegen (§5), and the int-hosted bodies + formatter
delete (§4.3).

### 3.1 Parse (frontend — `crates/cranelisp-frontend/src/ast_builder.rs`) — recognition UNCHANGED; reserved-name enforcement is NEW

`trace` is a **root special form** — recognised by the parser/AST-builder (and typechecker, §3.2),
always available with no import and no module path. `build_form` matches the head symbol `"trace"`
and dispatches to `build_trace` (`ast_builder.rs:991`), which produces a dedicated
`Expr::Trace { modules, body, span }` variant (`ast_builder.rs:1036`) — NOT an `Expr::Apply`.
`build_trace` enforces exactly one body argument and recursively builds the body via `build_expr`.

**The as-built recognition CONFORMS to the target** (user's "trace node" framing, 2026-06-04): the
`Expr::Trace` node + `infer_trace` dispatch (§3.2) are exactly the root-special-form shape, so the
recognition change is **near-zero code**. Two cascade items remain:

1. **Reserved-name enforcement (NEW — does not exist in source today).** As a root special form,
   `trace` is a **reserved name**: `(defn trace …)`, `(let [trace …] …)`, and `(fn [trace] …)` (any
   binder or definition position) MUST be **rejected outright**. The as-built compiler does NOT
   enforce this — `build_form` matches `"trace"` only in *head* position, so the name `trace` as a
   `defn`-name argument or a `let`/`fn` binder flows through `expect_symbol` (`build_let_bindings`,
   the defn-name path) with no reserved-word check and is silently accepted-and-shadowed. The fix is a
   small reserved-name reject in the AST builder's binder/definition paths (owner: `/dev (frontend)`;
   FIXME 0259). User-accepted cost (a user cannot name a function/binding `trace`).
2. **Stale comment.** The `build_trace` comment documenting the (now-retracted) `--link` rejection is
   stale and updated as part of the /spec + /dev cascade (the rejection is gone; §2.5).

Quoted occurrences (`'(trace x)`, `` `(trace x) ``) are desugared by the expander into `Sexp`
constructor calls before reaching `build_trace`, so they appear as `Expr::Apply` to those
constructors — they are data, not trace forms.

### 3.2 Typecheck (typecheck — `crates/cranelisp-typecheck/src/infer.rs`) — UNCHANGED

`Expr::Trace` is dispatched directly in `infer_expr` (`infer.rs:64`) to `infer_trace`
(`infer.rs:907`). There is **no "callee resolves to `primitives/trace`" intercept** — the keyword
already produced a distinct node, so typecheck switches on the variant. `infer_trace`:

1. Infers the body's type **for its constraint side-effects only** (`infer_expr(state, body)`) — the
   result is discarded. Inference must run so constraints propagate and errors inside the body are
   detected.
2. Records the result type as `Type::ADT(primitives/Trace, [])` — always `Trace`, independent of the
   body's type (spec §4.12.1).

The other typecheck touch-points are mechanical walks (`program.rs` recursion descends into
`Trace { body }`); no special resolution. (A lexical nested-trace pre-reject is NOT taken in
typecheck — the guard is runtime, §6, because the dynamic-through-a-call case is only catchable at
runtime and a single enforcement point is simpler than two; §6 records this sub-choice.)

### 3.3 Codegen (backend — `crates/cranelisp-backend/src/compiler/trace_codegen.rs`)

`compile_trace` emits the GOT copy-swap wrapper around the body. The target shape differs from the
prior shape in three ways: (a) **discovery moves into codegen** (§5 — backend iterates `symbol_tables`
itself rather than receiving a pre-built `traced_fns` from int); (b) **a display descriptor is baked
per traced param/result** (§3.4 — replacing the leaked `Box<Type>` + the int-side `repl_trace_format`
symbol-table dispatch); (c) the externs resolve to **intrinsics** bodies, not int bodies (§4). The
CLIF emitted around a non-empty trace:

1. **Declare the trace externs** as `Linkage::Import` via `declare_trace_extern(name, n_params,
   has_return, span)` — `cranelisp_trace_swap_got` (4 params, returns), `cranelisp_trace_restore_got`
   (2 params, void), `cranelisp_collect_trace` (0 params, returns), plus per-wrapper
   `cranelisp_trace_enter` (4, void) / `cranelisp_trace_exit` (2, returns) /
   `cranelisp_trace_format` (2, returns). Declaration is `(param_count, has_return)`-shaped — every
   param/return is `i64` (heap pointers cross as integers). Re-declaration is idempotent for Import
   linkage. **These names are published by `intrinsics_table()` and resolved at the three resolution
   points (§4.2) — the name-agreement contract gains an OWNER: the catalog + its tests (§4.2).**
2. **Discover + group traced functions by GOT base address** (§5). This is now a plain iteration over
   `symbol_tables` inside codegen (backend already receives `symbol_tables` in `compile_to_module`).
   ALL modules' GOTs, primitives included.
3. **For each group, compile a thin wrapper fn per traced function** (`compile_trace_wrapper_fn`).
   Each wrapper: formats each arg via `cranelisp_trace_format(arg, descriptor_ptr)` (§3.4 — the
   second arg is now a **display descriptor pointer**, not a `Box<Type>` pointer); calls
   `cranelisp_trace_enter(name_ptr, name_len, params_count, array_ptr)`; calls the **original
   implementation via `call_indirect` on an embedded `iconst` code-ptr** (bypassing the swapped GOT so
   the wrapper reaches the real fn); formats the result; calls `cranelisp_trace_exit(orig_result,
   result_str)` and returns its passthrough. Name bytes and the per-param/result descriptors are
   emitted as program-lifetime data (§3.4 — JIT: leaked `Box`; object: a data symbol with relocations).
4. **Emit `cranelisp_trace_swap_got(got_base, n_slots, slots_ptr, wrappers_ptr)`** per group, capturing
   the returned saved-GOT pointer.
5. **Compile the body** with `in_trace_body = true` (disables lenient/sparkable evaluation so the
   trace tree is deterministic — §3.6) and `in_tail_position = false`.
6. **Discard the body result** (`emit_body_discard` dec's RC if heap-typed — the trace result is the
   `Trace` ADT, not the body value).
7. **Emit `cranelisp_trace_restore_got(got_base, saved_got)`** per group, in reverse order (clean
   nesting).
8. **Emit `cranelisp_collect_trace()`** → the `Trace` ADT heap pointer, which is the value of the form.

The `compile_trace_no_swap` fallback (empty traced set) is retained only for the degenerate case where
discovery finds nothing to wrap; with all-symbol-table discovery (§5) this is now rare (it triggers
only when no module has a GOT-slotted callable, e.g. a single-form program with no defns) — it still
calls `cranelisp_collect_trace()` which returns a minimal `::trace::` node from an empty stack.

### 3.4 Display descriptor — the codegen-baked, self-contained value-render contract (the meatiest new element)

**The problem the descriptor solves.** Today, the wrapper formats values by calling
`cranelisp_trace_format(value, type_ptr)` where `type_ptr` is a leaked `Box<Type>`, and the int-side
`repl_trace_format` (`session_v4.rs:5154`) walks that `Type` **plus the live `symbol_tables`** to
resolve ADT constructor names + field layouts (`src/display.rs::format_value`, which does
`lookup_type_def_from_tables(fqtn, symbol_tables)` for every ADT, reads `TypeDefInfo.constructors`
for tag→ctor-name, recurses into field types). That makes `trace_format` depend on the live session
symbol tables — an int concern, and the one genuine reason trace had an int hook. **The target
removes that dependency**: backend (which already traverses the symbol tables at codegen time) bakes
everything `format_value` needs into a **self-contained display descriptor**, and the intrinsics
`cranelisp_trace_format` becomes a **pure walk of descriptor + heap value with zero symbol-table
access**.

**`DisplayDescriptor` — the data.** A descriptor is a recursive, self-contained description of how to
render one value of a known static type. It is **owned by `cranelisp-intrinsics`** (the formatter that
consumes it lives there; Principle 15 — behaviour lives with the type it operates on) as a
`#[repr(C)]` data structure read by the intrinsic, and **emitted by backend** as program-lifetime
data. Minimum-mechanism content (this is an `/arch` sub-choice — flagged in the summary), one variant
per renderable shape, mirroring `src/display.rs`'s `format_field_value` match:

| Descriptor kind | Carries | Renders as |
|---|---|---|
| `Int` / `Bool` / `Float` / `String` | nothing (scalar tag) | decimal / `true`\|`false` / `d.d` / quoted |
| `Fn` | nothing | `<closure>` |
| `Vec` | one child descriptor (element) | `[e1 e2 …]` (walk `HeapVec` len/data) |
| `Adt` | type-name bytes; per-constructor: `tag`, ctor-name bytes, ctor-arity, single-ctor-product flag; per-field: a child descriptor | nullary `Type.Ctor` / data `(Type.Ctor f1 f2 …)` per spec §1.5 |
| `TypeVar` (residual) | nothing | bare `value` fallback (a monomorphic trace should not hit this; baked as the substituted concrete descriptor where the call site's type is known) |

The descriptor is the **closure over `TypeDefInfo` that backend resolves once at codegen** — for an
ADT it bakes the constructor table (tag → name + arity + field-descriptors) so the formatter never
needs `lookup_type_def_from_tables`. Recursion is bounded by the static type: a `(List (Option Int))`
descriptor nests `Adt(List) → field Adt(Option) → field Int`. Polymorphic ADT fields are baked **after
substituting the call site's concrete type args** (backend already has the monomorphic `Type` at the
wrapper-compile site — `tf.param_types` / `tf.result_type` — exactly the substitution
`build_adt_subst` does today), so the residual-`TypeVar` case is a defensive fallback, not a normal
path.

**`cranelisp_trace_format(value, descriptor_ptr) -> CLString` — the contract.** The intrinsic walks
`descriptor_ptr` (a `*const DisplayDescriptor`) and `value` (an `i64` heap pointer or scalar) together,
producing a heap `String` (alloc-base pointer, RC=1) — the same output shape `alloc_string` produces
today. It performs **zero symbol-table access** and holds **no thread-local state** (the `TRACE_DISPLAY`
thread-local + `set/clear_trace_display_state` machinery is **deleted**). It reuses the heap-layout
reads the existing `format_value` does (`HeapAdt::TAG_OFFSET`/`field_offset`, `HeapVec` len/data,
`HeapString` len/data) — those layout consts are intrinsics-owned already (BC §4b invariant 2), so the
formatter is *more* at-home in intrinsics than it was in int. Signature is `(value: i64, descriptor:
i64) -> i64` at the C-ABI (descriptor passed as an integer pointer), arity `(2, true)` — identical to
today's `cranelisp_trace_format` arity, so backend's `declare_trace_extern("cranelisp_trace_format",
2, true)` is unchanged.

**Emission in BOTH module modes — the survives-`.o`-caching constraint.** The descriptor must be
emittable as data in JIT mode AND object mode (since trace now works in `--link`, §2.5). This is the
**same pattern family** backend already uses for other compile-time-baked data that must survive
relocation — literal pools and the per-module GOT data symbol (`got_data_symbol_name`):

- **JIT mode** — backend leaks a `Box<DisplayDescriptor>` (recursively, with child descriptors and
  name-byte buffers also leaked / arena-allocated for program lifetime) and embeds its address as an
  `iconst` in the wrapper, exactly as the leaked `Box<Type>` is embedded today (`trace_codegen.rs:285`).
  No relocation needed — the address is a runtime constant.
- **Object mode (`--link`)** — backend emits the descriptor tree as a **read-only data symbol** in the
  object file (one `DataDescription` per descriptor tree, or a flattened arena blob), with the
  wrapper's reference to it as a **relocation** against that data symbol (same mechanism as the GOT
  data symbol and string literals). At link time `ld` resolves the relocation; at runtime the wrapper
  loads a real pointer. The descriptor's `#[repr(C)]` layout is the contract between the emitter
  (backend) and the reader (intrinsics) — it is a layout-ABI surface in the §4b invariant-2 family
  (offset-keyed reads against a `#[repr(C)]` struct intrinsics owns), governed the same way: backend
  reads the layout through the owned consts, never by re-deriving offsets.

  *Object-mode encoding sub-choice (flagged):* a flat, position-independent **arena blob** (descriptors
  as fixed-size records with child references stored as byte-offsets-within-the-blob rather than
  absolute pointers) is the minimum-mechanism encoding that survives relocation cleanly — one data
  symbol per wrapper's descriptor set, one relocation per wrapper reference, no intra-blob relocations.
  The alternative (one data symbol per descriptor node + intra-tree relocations) is more relocations
  for no benefit. `/dev (backend)` confirms the exact encoding; `/arch`'s call is "arena blob with
  offset-relative child links," recorded here as the target so the descriptor is genuinely
  position-independent and `.o`-cacheable.

**Ownership / lifetime.** Descriptors are program-lifetime (leaked in JIT; static `.rodata` in object
mode). They are never freed — there is one descriptor set per traced wrapper, bounded by the program's
trace-form count × traced-fn count, and a trace build is a one-time codegen event. This matches the
existing leaked-`Box<Type>` + leaked-name-bytes discipline (`trace_codegen.rs:281`, `:288`); the
descriptor *replaces* those leaks, it does not add a new lifetime class.

**Why this removes int from the capture path.** With the descriptor self-contained, the formatter needs
nothing from the session — so it is an ordinary intrinsic (§4). The REPL's richer live-`symbol_tables`
display path (`format_result_value` with `:Type` prefix) is **no longer involved at trace-capture
time**; that path stays in int for *REPL result display* (where it belongs — it formats the top-level
evaluation result with the qualified-type prefix), but trace-capture formatting is now the
descriptor-driven intrinsic. The two formatters share the heap-walking logic conceptually; the trace
one is the pared-down, descriptor-driven, no-`:Type`-prefix variant that already exists as
`format_value` (vs `format_result_value`) — the target moves `format_value`'s *logic* into intrinsics
as the descriptor walker (it stops taking `symbol_tables`; it takes a descriptor instead).

### 3.5 GOT effects — the copy-swap, and why module-scoping is now completeness-by-construction

Functions are called through per-module GOT indirection. The runtime swap (`cranelisp_trace_swap_got`,
now in `cranelisp-intrinsics::trace`) does, per group:

1. `memcpy` the live GOT table (`GOT_TABLE_SIZE * 8` bytes) into a freshly-allocated **saved-GOT** copy.
2. Build a **debug-GOT** = clone of saved-GOT with the wrapper pointers substituted at the traced slots.
3. Install the debug-GOT over the real GOT in **one `memcpy`** — no partial-swap window (atomicity by
   single-buffer install).
4. On the first successful swap (role-acquire), push a synthetic `"::trace::"` root frame, AND check
   the nesting guard (§6 — role-acquire is where the re-entrancy check lives).

`cranelisp_trace_restore_got` memcpy's the saved copy back and frees it. After the swap, every call
through a swapped slot lands in a wrapper, which pushes/pops `TraceFrame` entries on `TRACE_STACK`,
building the call tree. Recursive calls inside an original function still go through the swapped GOT, so
nested calls are recorded naturally; the wrapper itself reaches the original via its embedded code-ptr,
not the GOT, avoiding infinite recursion.

**Module-scoping is now completeness-by-construction (the user "all symbol tables" ruling).** The
prior implementation's project-root filter (which excluded stdlib + primitives) is **deleted** (§5).
The target swaps **all** symbol tables, primitives included. The consequence the user accepted:
**stdlib AND extern primitives now appear in trace trees**. This is the right default because the
disqualifying alternative — narrowing the traced set to the *callee graph reachable from the body* —
is unsound: dynamic dispatch (a closure called through a GOT slot, a trait method resolved at runtime,
a fn passed as a value) creates a **dynamic-call hole** where the static callee graph cannot see the
actual callee, so a callee-narrowed trace would silently drop calls. Swapping all GOTs has no such
hole: if a call goes through *any* swapped slot it is recorded, regardless of how the callee was
reached. This is the recorded rationale for "all symbol tables" over "callee-narrowing."

#### 3.5.1 What appears in a trace tree (TARGET taxonomy)

| Category | Has GOT slot? | Dispatch | Discovered (§5)? | Traced? | Why |
|---|---|---|---|---|---|
| **User module** (any module under any path) | Yes | GOT-indirect | Yes | **Traced** | Real `got_slot` + `code_ptr`. |
| **Stdlib / lib-search-path module** | Yes | GOT-indirect | **Yes (TARGET change)** | **Traced** | The project-root filter is deleted; all GOTs swapped. |
| **Synthetic `primitives` — extern primitives** (`str-concat`, `int-to-string`, …) | Yes (Decision 0048 `PRIMITIVES_TABLE` GOT) | GOT-indirect | **Yes (TARGET change)** | **Traced** | All symbol tables swapped, primitives included (user "all symbol tables" ruling). |
| **Inline primitives** (`+`, `-`, comparison, boolean) | No | inline CLIF | No | **Invisible** | Compile to inline instructions — no callable entry to wrap. The only category genuinely invisible, and structurally so. |
| **Synthetic `macros` module fns** | Varies | GOT-indirect where slotted | Yes where slotted | **Traced where slotted** | All symbol tables swapped; the macros module is no longer specially excluded. (Expansion already ran at compile time; runtime macro-clause fn calls, if any reach a swapped slot, record.) |
| **Platform functions** (DLL-loaded) | Routed via platform trampoline / platform-module GOT | trampoline / GOT | Yes if the platform module has GOT-slotted entries | **Traced if GOT-slotted** | Platform-as-module migration (BC §5 invariant 1) gives platform fns GOT slots; if present in `symbol_tables` they are swapped like any module. |
| **Anonymous lambdas** (`fn` closures) | No named GOT entry | code-ptr in closure | No | **Invisible** | No named `ModuleEntry::Def` slot; effects appear inside the enclosing traced fn. |
| **Constrained-poly base name** (dispatch placeholder) | Has a base entry | — | **Skipped** | **Invisible** | `DefKind::UserFn { constrained_fn: Some(_) }` is a dispatch placeholder, not directly callable; its monomorphised specializations *are* traced. |

### 3.6 Lenient-evaluation interaction — UNCHANGED

Lenient evaluation sparks independent `let` bindings onto rayon pool threads, which do not own the
trace role and whose calls would therefore be absent from the tree. Codegen sets `in_trace_body` so the
body compiles fully sequentially inside a trace, keeping the tree complete and deterministic.

### 3.7 `TRACE_STACK` — the in-flight call-frame stack — UNCHANGED (relocates with the bodies)

`TRACE_STACK` is the runtime data structure that *builds* the call tree while the body executes. It is a
process-global `Mutex<Vec<TraceFrame>>` accessed under `lock_trace_stack()` (recovers from mutex
poisoning). Each `TraceFrame` carries: the function `name`, the pre-formatted parameter String heap
pointers, the pre-formatted result String pointer (0 until exit), a `start: Instant`, and a
`children: Vec<i64>` of completed child `Trace` ADT heap pointers in call order. The stack mirrors the
live call stack:

- **Root.** First successful `swap_got` on a thread (role-acquire) pushes the synthetic `"::trace::"`
  root frame; all top-level traced calls attach as its children.
- **Enter pushes / Exit pops + attaches.** `cranelisp_trace_enter` pushes a frame; `cranelisp_trace_exit`
  pops the top, stamps `nanos`, builds the `TraceCall` ADT, and pushes it into the new top frame's
  `children`. Both are no-ops on any thread that does not own the trace role (the `TRACE_THREAD_ID`
  guard) — so exactly one thread mutates `TRACE_STACK` during a trace, keeping the single shared stack
  coherent without per-thread stacks.
- **Collect pops the root.** `cranelisp_collect_trace` releases the role (CAS `my_tid → 0`), pops the
  remaining root frame, and marshals it into the final `Trace` ADT (or a minimal `::trace::` node if the
  stack is empty).

`TRACE_STACK`, `TRACE_THREAD_ID`, the `THIS_THREAD_ID` thread-local counter, and `consume_trace_call`
all relocate from `src/trace.rs` to `crates/cranelisp-intrinsics/src/trace.rs` with the bodies (§4).

---

## 4. Symbols, registration, and the cross-crate contract — TARGET

### 4.1 All twelve bodies live in `cranelisp-intrinsics`

Per the user ruling, **all 12 trace bodies relocate to `cranelisp-intrinsics`** and publish through
`intrinsics_table()` (the catalog grows 15 → 27 entries; the catalog's "trace deliberately ABSENT"
scope text flips — §4.2). The twelve:

`cranelisp_trace_enter`, `cranelisp_trace_exit`, `cranelisp_trace_swap_got`,
`cranelisp_trace_restore_got`, `cranelisp_collect_trace`, `cranelisp_trace_first_child_nanos`,
`cranelisp_trace_name`, `cranelisp_trace_params`, `cranelisp_trace_result`, `cranelisp_trace_children`,
`cranelisp_trace_nanos`, and `cranelisp_trace_format` (now the **pure descriptor-driven formatter**,
§3.4 — no longer a thread-local-dispatched int shim).

`TRACE_STACK` / `TRACE_THREAD_ID` / `consume_trace_call` move with them. They are runtime support code
with a stable ABI contract called by JIT/object-emitted code — i.e., they are intrinsics **by the BC
§4b definition** ("backend-emitted-call targets … called by JIT-emitted code"). 11 of 12 already need
no session state; the 12th (`trace_format`) loses its session dependency once the descriptor (§3.4)
makes it self-contained. The `consume_trace_call` drop helper walks the `TraceCall` ADT layout, which
moves to intrinsics with the bodies — and intrinsics already owns the generic `consume_shallow`
(Strings) + `consume_slist`/`consume_sexp` drop glue it calls, so the re-coupling risk that D40's
counterpoint raised (relocating `consume_trace_call` back to intrinsics might force `drop` to reference
it) **does not materialise**: `consume_trace_call` is a leaf consumer of intrinsics' generic helpers,
not a dependency of them — intrinsics' `drop` module does not reference `consume_trace_call`.

### 4.2 The name-agreement contract — NOW SINGLE-SOURCED in the catalog (the no-owner gap closes)

The prior architecture had a **known structural gap**: the trace symbol names had to agree across three
independent sites (backend's `declare_trace_extern` Import string; int's `#[no_mangle]` body name; int's
`int_intrinsics()` registration string) with **no single owner** and no compiler-enforced link. The
target **closes this gap**: the trace bodies join `intrinsics_table()`, which is the established
single-source `name → (signature, ptr)` catalog (BC §4b invariant 11) — the same table that already
single-sources the other intrinsics. The contract's owner is now the **catalog + its tests**
(`crates/cranelisp-intrinsics/src/catalog.rs` + the `#[cfg(test)] mod tests` name-set / arity /
non-null-ptr assertions). The three resolution points (BC §4b invariant 11) consume the trace entries
identically to every other intrinsic:

- **(a) JIT construct** — `JITBuilder::symbol(name, ptr)` at `Jit::new(symbol_tables)` setup. **The S76
  registration seam (the OPEN `Jit::new` question of the prior pass) DISSOLVES for trace** — because the
  trace symbols are now in `intrinsics_table()`, `Jit::new(symbol_tables)` picks them up with no int
  fold-in and no special case. None of the prior pass's candidate shapes (mount-as-synthetic-module /
  extra-symbols param / int-published catalog) is needed for trace.
- **(b) cache-hit load** — `Linker::register_symbol(name, ptr)`.
- **(c) `--link`** — names resolve against the `cranelisp-intrinsics` archive (the force-link `pub use`
  returns — §2.5).

`backend`'s `declare_trace_extern` Import string remains the emitted-call ABI name; the catalog
republishes exactly those names (the §6 emitted-call-ABI invariant is unchanged — only the *enumeration
source* of the trace names moves from "int-hand-assembled `int_intrinsics()`" to "catalog"). The catalog
test pins the full name-set, so a renamed or dropped trace symbol is a **test failure**, not a latent
runtime unresolved-symbol crash.

### 4.3 What DELETES from int (the int wave's entire trace burden)

The int wave's trace work is **nothing but deletions**:

- `src/trace.rs` — **deleted in full** (the 12 bodies + `TRACE_STACK` + `TRACE_THREAD_ID` +
  `consume_trace_call` + the unit-test fallback `cranelisp_trace_format`); their target home is
  `crates/cranelisp-intrinsics/src/trace.rs`.
- `src/session_v4.rs::build_traced_fns` (`:2727`) — **deleted**; discovery moves into backend codegen
  (§5). The call site (`:2663`) and the surrounding `traced_fns` plumbing into
  `compile_and_execute_expr` delete with it.
- `src/session_v4.rs::repl_trace_format` (`:5154`) + `TraceDisplayState` + the `TRACE_DISPLAY`
  thread-local + `set_trace_display_state` / `clear_trace_display_state` (`:5127`–`:5170`) — **deleted**;
  the formatter is now the descriptor-driven intrinsic (§3.4).
- `src/session_v4.rs::int_intrinsics()` (`:4938`) — the **trace half deletes** (the 12 trace entries +
  the `cranelisp_trace_format` entry). `int_intrinsics()` reduces to **`discover-tests` / `run-test`**
  (the two test-runner symbols). **Test intrinsics are PARKED** — explicitly out of scope per the user;
  their relocation (if any) is a separate future question. `int_intrinsics()` therefore shrinks from
  14 entries to **2**, and the `Jit::new(symbol_tables)` collapse must still account for those two
  (that residual is the S76 `Jit::new` seam for the *test* intrinsics, untouched here and unresolved by
  this document — it is parked with the test intrinsics).

int's display path for *REPL results* (`src/display.rs::format_result_value`) is **untouched** — it is
not part of trace capture (§3.4). `int` retains `core.trace` as a stdlib it loads, but that is stdlib,
not int runtime code.

### 4.4 Why `(trace …)` is a codegen item, not a pure runtime intrinsic call — UNCHANGED rationale, sharpened

`(trace …)` is irreducibly a codegen item even though the 12 bodies are pure runtime intrinsics, because
the **orchestration around them** needs compile-time-only knowledge:

1. **Per-function wrapper generation** — each traced fn needs a bespoke wrapper carrying its name bytes,
   arity, and per-param/result **display descriptors** (§3.4) baked in. Cranelift functions are emitted
   at compile time; a runtime call cannot synthesise an arity-N wrapper.
2. **GOT layout / slot knowledge + discovery** — the wrapper table, slot indices, per-module GOT bases,
   and the **descriptor data** are all read out of `symbol_tables` at codegen (§5).
3. **`call_indirect` on the embedded original code-ptr** — the wrapper must reach the original via an
   `iconst` code-ptr to bypass the swapped GOT.
4. **`in_trace_body` lenient-eval disabling** — a property of *how the body is compiled* (§3.6).

So the 12 bodies are pure runtime intrinsics; `compile_trace` is the codegen that wires them together
with compile-time-only information. The target makes this cleaner: the *only* compile-time-only datum
that previously forced an int hook (symbol-table-driven value formatting) is now baked into the
descriptor at codegen, so even the formatting becomes a pure intrinsic.

---

## 5. Discovery moves into backend codegen — swap ALL symbol tables

**Discovery is no longer an int session-orchestration step.** The prior `build_traced_fns`
(`src/session_v4.rs:2727`) iterated the session's typecheck products, applied the project-root filter,
and handed a pre-built `traced_fns: Option<&[TracedFnInfo]>` to backend through the compile context.
The target **deletes that** and computes the traced set **inside backend's trace-codegen**, because
backend already receives `symbol_tables` in `compile_to_module` (BC §3 — "`symbol_tables` is the single
codegen source"). Discovery is then a plain iteration at trace-codegen time.

### 5.1 The target discovery algorithm (in `trace_codegen.rs`)

1. **Iterate every module in `symbol_tables`** — ALL of them. No project-root filter, no reachability
   set from the body. (User ruling: "all symbol tables, primitives included.")
2. **Per module, take its GOT base** — `symbol_tables.get(module_path).got().base_ptr()`. Each module
   (including the synthetic `primitives` module, Decision 0048) has its own GOT; the base identifies the
   group.
3. **Iterate the module's entries** and select each `ModuleEntry::Def { got_slot: Some(slot), code:
   Some(c), .. }` whose `c.ptr()` is non-zero. Skip constrained-polymorphic base names
   (`DefKind::UserFn { constrained_fn: Some(_) }` — dispatch placeholders). Take `arity` / `param_types`
   / `result_type` from `entry.scheme.ty` (must be a `Type::Fn`, else skip).

   *Primitives note:* primitives entries carry `code: None` (Decision 0048 A2-reversal, FIXME 0244) but
   their fn pointers live in `PRIMITIVES_TABLE.got()`. Discovery selects a primitive for tracing when its
   GOT slot holds a non-zero code pointer — read the slot from `got()` rather than from `entry.code`. The
   `code: Some(c)` predicate above is the user-module shape; the primitives shape reads the address from
   the GOT slot. `/dev (backend)` reconciles the exact predicate (the two shapes — `entry.code` for
   user/stdlib, `got().slot(n)` for primitives — both resolve to "the fn ptr at this slot"); `/arch`'s
   call is "discovery reads the callable address from the GOT slot, which is the single source of truth
   for callable addresses (BC §3 invariant 3), not from `entry.code`" — this naturally includes
   primitives without a code-marker special case.
4. **Emit `TracedFnInfo`** per surviving entry: `{ name: "module/symbol", got_base, got_slot, arity,
   code_ptr, param_descriptor_set }` — where the descriptor set (§3.4) is built here at discovery/
   wrapper-compile time from `param_types` + `result_type` + the module's `TypeDefInfo`s (which backend
   has in `symbol_tables`). `TracedFnInfo` moves from "an int → backend compile-context input" to "a
   backend-internal codegen value."

### 5.2 Consequences (recorded)

- **Stdlib + extern primitives now appear in trace trees** (the taxonomy §3.5.1). This changes existing
  trace tests' expectations — a `(trace (fact 5))` over a prelude-using program now shows the prelude/
  primitive calls fact makes (e.g. `*`, `-` if those are GOT-slotted primitives rather than inline).
  The /qa cascade (§6) rewrites those expectations.
- **Inline-CLIF arithmetic remains structurally invisible** — `+`, `-`, comparison, boolean ops compile
  to inline instructions, no slot to swap. This is the only structural invisibility.
- **The dynamic-call hole rationale** (§3.5) is the recorded reason "swap all" beats "callee-narrow":
  callee-narrowing cannot see dynamically-dispatched callees and would silently drop calls; swap-all has
  no hole.
- **`TracedFnInfo` + the compile-context `traced_fns` field** leave the cross-crate boundary — they were
  a backend↔int seam; with discovery in backend they are backend-internal. The compile-context
  `traced_fns: Option<&[TracedFnInfo]>` field is removed from `compiler/mod.rs`.

---

## 6. Nested trace — runtime guard (the §4.12.5 defect fix)

**Nested trace is disallowed via a RUNTIME GUARD** (user ruling). Same-thread re-entrant
`(trace … (trace …))` raises a runtime error; cross-thread concurrent tracing keeps the existing
§4.12.6 CAS + `::skipped::` sentinel semantics (UNCHANGED).

**The defect being fixed.** Today the same-thread re-entrant case is **unguarded and diverges from spec
§4.12.5**. Each `(trace …)` is its own `compile_trace`, so an inner form emits its own `swap_got` /
wrappers / `restore_got` / `collect_trace`. At runtime the inner `swap_got` sees `current_owner ==
my_tid` and takes the **multi-module same-thread branch** (designed for swapping a *second module's* GOT
within one trace, §3.5): it re-swaps and returns a real saved-GOT — it does NOT detect re-entrancy. Then
the inner `cranelisp_collect_trace` releases the trace role (`CAS my_tid → 0`) and pops a frame, so the
*outer* trace's subsequent enter/exit calls become no-ops and the outer bookkeeping is corrupted. The
role-CAS that protects the cross-thread case does not protect the same-thread re-entrant case.

**Where the guard lives — the role-acquire / enter path.** The guard must **distinguish re-entrant
trace from legitimate multi-module swap** (both currently hit `current_owner == my_tid`). The
minimum-mechanism distinguisher (an `/arch` sub-choice — flagged) is a **`TRACE_ACTIVE` depth flag**
(thread-local `Cell<bool>`, or equivalently a check on whether the `::trace::` root frame is already
present for `my_tid`):

- `compile_trace` already emits the swap as the *first* GOT operation for a given trace form. The guard
  sits at the **role-acquire point in `cranelisp_trace_swap_got`** — specifically, the branch reached
  when `current_owner == my_tid`. That branch must distinguish:
  - **legitimate multi-module swap within one trace** — the same `compile_trace` invocation swapping a
    second GOT group. These swaps happen *before* the body runs, while no wrapper has fired. ⇒ allowed.
  - **re-entrant `(trace (trace e))`** — the inner form's first swap, which happens *while the outer
    body is executing* (a wrapper is on the stack). ⇒ ERROR.

  The clean distinguisher: set a thread-local `TRACE_BODY_RUNNING` flag true after the swap loop and
  before the body, false after restore (mirroring the codegen `in_trace_body` boundary, but at runtime).
  An inner `swap_got` that finds `current_owner == my_tid && TRACE_BODY_RUNNING == true` is re-entrant
  and **raises the runtime error**; one that finds `TRACE_BODY_RUNNING == false` is a multi-module swap
  and proceeds. (Equivalently, a `TRACE_DEPTH` counter incremented once per `compile_trace`-emitted
  prologue distinguishes them; the flag is the lighter mechanism. `/dev (intrinsics)` picks the exact
  representation; `/arch`'s call is "a thread-local boundary flag set across the body, checked at the
  re-entrant swap.")

**The error shape.** The guard raises through the §12.7 runtime-panic machinery — the existing
`runtime/panic` intrinsic (`crate::panic::runtime_panic`, already in `intrinsics_table()`), with a
clear message: **`"nested trace is not supported: (trace ...) may not appear inside an actively-tracing
(trace ...)"`** (exact wording is an `/arch` sub-choice, flagged; `/spec` may pin the normative text).
This is a runtime error, not a crash — it surfaces like any other runtime panic (match-exhaustiveness
failure, etc.).

**Why runtime, not typecheck.** A lexical typecheck reject (`infer_trace` sets a flag, a nested
`Expr::Trace` under the flag is a type error) would catch the *lexical* case earlier (Principle 7) but
**not** the dynamic case — `(trace (f))` where `f`'s body contains `(trace …)` is only detectable at
runtime. The user ruled "runtime guard"; a single runtime enforcement point covers both the lexical and
dynamic cases with one mechanism (minimum mechanism). Typecheck stays unchanged.

**Spec §4.12.5 amendment (for the /spec cascade).** Proposed replacement text (the /spec FIXME carries
this verbatim):

> ### 4.12.5 Nested Trace
> A `(trace ...)` expression MUST NOT be evaluated while another `(trace ...)` is actively tracing on
> the same thread. An implementation MUST raise a runtime error when a `(trace ...)` form is entered
> during the evaluation of an enclosing `(trace ...)` body — whether the inner form appears lexically
> (`(trace (trace expr))`) or is reached dynamically through a function call. Concurrent tracing on
> different threads is governed by §4.12.6 (at most one thread traces; others return an empty trace).

---

## 7. History & how we got here (cited; brief — archaeology, not target)

The body above is the target. This appendix is the navigation index of the path that reached it; the
substance lives in the cited decisions/sprints.

- **S20 — birth.** `(trace ...)` introduced as a Ring-4 module-scoped special form; the genesis of
  Principle 10 (parser keywords vs module-scoped forms).
- **D43 — runtime split.** `cranelisp-runtime` split into `cranelisp-primitives` +
  `cranelisp-intrinsics`; trace bodies landed in intrinsics on the way through.
- **D40 + Path B1 — relocation to int (NOW PARTIALLY RETRACTED).** Decision 0040 (S67 W4,
  user-arbitrated) scoped `(trace ...)` REPL/`--run`-only and relocated `trace.rs` + the 12 bodies +
  registration **to int**, deleting backend's 12 `IntrinsicSymbol` entries and exe-bundle's trace
  force-link line. The 2026-06-04 user ruling **retracts the trace half of D40**: the bodies return to
  intrinsics, the mode restriction lifts (all modes including `--link`), the force-link line returns.
  D40's **IoObserver / io_trace half remains valid** (§1). See the D40 file's S76 amendment box for the
  per-clause disposition.
- **S66 — no-gating.** Per-program trace/test gating helpers deleted; intrinsics registered
  unconditionally. (Unchanged — the catalog registers unconditionally too.)
- **S67 — D40 relocation landed.** The 12 bodies moved to `src/trace.rs`; backend's `IntrinsicSymbol`
  entries + the exe-bundle force-link line deleted. **This is what the target reverses for trace.**
- **S76 — collapse + this target.** `Jit::new(symbol_tables)` absorbs int's hand-assembly. The prior two
  passes of this document recorded the current state and then proposed (FOR-USER-REVIEW) the
  relocate-to-intrinsics + descriptor + nested-disallow + all-modes shape. The user **decided** that
  shape on 2026-06-04; this revision enacts it as the target. The "OPEN S76 `Jit::new` registration
  seam" of the prior pass **dissolves for trace** (the trace symbols are now in the catalog, §4.2); it
  survives only for the two parked test intrinsics.
