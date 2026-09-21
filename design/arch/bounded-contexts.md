# Bounded Contexts — per-surface target shape

Owned by `arch`. This is the canonical statement of what each crate-shaped
surface is responsible for, why its boundary lies where it does, and what
crosses it. `sprints/METHOD.md` §1.1 lists the surfaces the triad is deployed to.

- **Exact Rust API** lives in each crate's rustdoc (crate-root `//!` plus
  per-item `///`); the generated `crates/{crate}/public-api.txt` is the as-built
  enumeration, governed by [the baseline discipline](CLAUDE.md#public-api-discipline).
  This document does not enumerate items.
- **Interior mechanism** lives in the context's own `design/{context}/` documents.
- **Focused shared contracts** are linked from each section; they own their detail.
- **Invariant numbers are stable citation targets.** Source comments, tests and
  the [decision-label index](decisions/README.md) cite them as "§N invariant M".
  A retired number is never reused.
- Rulings cited as "Decision N" resolve through the decision-label index.

## Dependency direction

Cargo enforces this graph; an edge not listed here is a boundary change that
returns to `arch` and the user.

| Context | Workspace dependencies |
|---|---|
| `cranelisp-types` | none |
| `cranelisp-frontend` | types |
| `cranelisp-typecheck` | types, frontend (expression and type-expression builders) |
| `cranelisp-platform` | types |
| `cranelisp-intrinsics` | types, platform |
| `cranelisp-primitives` | types, intrinsics |
| `cranelisp-backend` | types, intrinsics, platform |
| `cranelisp-exe-bundle` | intrinsics, primitives, platform |
| binary (`src/`) | every crate above |

Two absences are load-bearing: backend and primitives do not depend on each
other in either direction (§4a invariant 3), and nothing depends on the binary.

---

## 1. Frontend — `crates/cranelisp-frontend/`

**Bounded context.** Source text becomes structured data. The frontend reads
source into S-expressions and builds the AST. It is purely structural: it knows
shape, never types, code or semantics. Every downstream stage consumes the same
well-formed tree whether the input came from a file, the REPL or a macro
expansion.

**In scope.**
- Lexing and parsing source into `Sexp` trees, including the comment-preserving
  reader and module-preamble capture.
- Quote and quasiquote desugaring — a pure syntactic rewrite.
- AST construction form by form, including `:Type` annotation pairing.
- Module-identity normalisation and structural-declaration extraction.
- `defmacro` parsing and macro-clause definition synthesis for the two
  consumers that prepare macro clauses (typecheck and the binary).
- Synthetic-span allocation for compiler-generated forms.

**Out of scope.** Type inference (typecheck); macro recognition (typecheck, via
the types resolution primitive); macro execution and module loading (binary);
code generation (backend); language definition (`spec`).

**What crosses the boundary.** Source text in; `Sexp`, AST values, `ParsedEntry`
transients and extracted declarations — all types-owned — out. The frontend
consults no symbol table and exposes no window types.
[Macro expansion ownership](macro-expansion-ownership.md) records why
recognition and execution live elsewhere.

**Invariants.**

1. **No type inference.** Frontend types are `TypeExpr` (syntactic), never
   `Type`, `Scheme` or `TypeId`. `parse_type_expr` returns `TypeExpr`;
   typecheck's `check_type_expr` resolves it.
2. **No code generation, no macro recognition or execution.** The frontend never
   names backend, primitives or intrinsics, looks up no macro entry and calls no
   compiled clause.
3. **`super` is resolved at parse.** `ImportSpec.module_path` never contains a
   literal `super` after parsing; resolution uses the parsing module's own path.
4. **Synthetic spans are unique** within a session (`next_synthetic_span` is
   monotonic).
5. Retired — the expansion fixpoint bound is typecheck and binary territory
   (§2 invariant 11).
6. Retired — gap surfacing moved with recognition (§2 invariant 8).
7. **Public error and DTO types stay `#[non_exhaustive]`.**
8. **Form by form; a macro is defined before it is used.** There is no
   `defmacro` pre-pass. A use textually before its `defmacro` is an ordinary
   unresolved reference. The frontend's per-form output supports the
   source-order availability model in
   [macro availability](macro-availability-model.md); the frontend itself
   publishes nothing.
9. **`:Type` annotation pairing is wholly frontend-owned, in every position.** A
   `:Type` token binds the immediately following form and lowers with it into
   one `Expr::Annotate`; it is never a standalone atom. Sub-form positions pair
   inside the expression builders; top-level sequences pair in `build_forms`. A
   leading annotation with nothing to bind is a frontend parse error. Where the
   binary must split a form stream for its own orchestration it only selects
   which span is one form (§6); construction and validation stay here.
10. **Quote desugaring runs inside the form builders, in every position.** The
    reader lowers reader-quote syntax to `quote`/`quasiquote` forms and the
    builders rewrite them before AST dispatch, so no downstream stage sees a
    quasiquote form. The rewrite is idempotent. The structural reader-quote
    classifier is the single types-owned `quote_head`; the frontend fold and the
    binary's expansion shield both consume it.

---

## 2. Typecheck — `crates/cranelisp-typecheck/`

**Bounded context.** Untyped AST becomes typed AST plus settled symbol-table
state. Typecheck infers types, resolves traits and dispatch, monomorphises,
infers ownership summaries and checks match exhaustiveness. It carries no
session state and no cadence: the binary invokes it synchronously, one cluster
at a time.

**In scope.**
- Hindley–Milner inference over every AST variant; ADT exhaustiveness.
- Trait declaration, implementation checking and method resolution.
- Monomorphisation from the program's roots, including demand replay.
- Per-callable callee extraction and ownership summaries
  ([ownership inference](ownership-inference.md)).
- Macro-head recognition within a form, through the types resolution primitive.
- Production of every codegen view and resolved identity backend consumes.

**Out of scope.** AST construction (frontend); code generation (backend); macro
execution, publication cadence, scheduling, module loading and REPL state
(binary); runtime helpers (intrinsics).

**What crosses the boundary.**
- **In:** a cluster's `ParsedEntry` list; a caller-supplied `SymbolTableAccess`
  window abstracting staging versus live tables; read-only `SymbolTables`, the
  session `ModuleAliases` and the prelude-fallback decision.
- **Out:** settled state written through the window; `CheckResult` (display
  information, warnings, unresolved return-polymorphic dispatch sites) or
  `CheckError` (a recoverable `Gap` or a located type error).
- **Entries:** `check_forms` (the cluster), `check_type_expr` (one type
  expression against a view; the platform loader pairs it with frontend's
  `parse_type_expr`) and `instantiate_demands` (replay of recorded
  monomorphisation demands, consumed by the binary's reload driver). The
  demand carrier and instance identity are types-owned
  ([symbol-table lifecycle](symbol-table-lifecycle.md)); the replay rules are in
  [monomorphisation](../typecheck/monomorphisation.md) and the reload handoff in
  [session transaction](../int/session-transaction.md).
- A **cluster** is the unit of non-macro typecheck atomicity: one REPL form, the
  contents of one `begin`, or a file's fully expanded non-macro forms. Signature
  registration then body checking is an ordering inside `check_forms`; no pass
  discriminator or accumulator crosses the boundary.

**Types originated here.** `SymbolTableAccess` and its two borrow guards are typecheck-owned because the
binary is their only consumer ([Principle 15](principles/15-facade-types-live-with-behavior.md));
the unioned `View` read surface is types-owned because it has several.

**Invariants.**

1. **No code generation.** Typecheck never invokes Cranelift and produces no
   machine code.
2. **No writes to live tables from `check_forms`.** Typecheck writes only through
   the supplied accessor and cannot distinguish staging from live. The binary
   owns staging, publishes it only on whole-cluster success and drops it on any
   error; on `Gap` it loads the dependency and retries the whole call against
   fresh staging. The live table is unchanged across any failure.
3. **One compilable predicate.** What backend may compile is the table's
   `codegen_targets()` projection. Typecheck authors entries that satisfy or
   fail it and keeps no parallel store.
   3a. Per-callable products that survive the cluster (checked body, codegen
   view, callees, ownership summary, minted instances) land on the staged
   declaration. Working state between the two internal passes lives in
   `check_forms`'s frame and is dropped on return.
4. **The call graph is typecheck-sourced**: callee edges are recorded on each
   callable during checking.
5. **Dispatch is resolved here.** Backend has no trait knowledge (§3 invariant
   10, §4a invariant 4).
6. **`generalize` collects trait constraints into `Scheme.constraints`**; a
   non-empty set marks a constrained template, monomorphised at its uses.
7. **Error rollback is the staging drop.** There is no snapshot/restore
   primitive. The type-variable counter is monotonic and is not rolled back.
8. **A missing module surfaces as `CheckError::Gap`** — the only cross-module
   concern typecheck has. It never blocks, schedules, loads or registers a
   module. It follows module aliases; it does not populate them.
9. **No session or scheduler dependency** — a pure function of its inputs.
10. **Module locality ([Principle 17](principles/17-module-locality-in-typecheck.md)).**
    Typecheck never iterates the universe of modules. Unqualified lookup uses
    the current module's view and follows import edges one hop at a time;
    qualified lookup probes one named module; implementation lookup follows the
    trait reference to its defining module and probes the one keyed shell; bulk
    introspection is current-module only. The walk is the types-owned
    `ResolutionScope`; typecheck supplies the first-hop view. Writes go through
    the accessor only. This is the structural precondition of invariant 2.
11. **Macro recognition uses the types primitive; execution and checkpoint
    publication are the binary's.** `check_forms` receives fully expanded
    non-macro forms (§6; [macro availability](macro-availability-model.md)).
12. **Concreteness is delivered here.** Cranelisp is rank-1 Hindley–Milner, so
    monomorphisation from the roots is complete: every callable backend compiles
    has a fully concrete scheme, and an unpinned type variable at a
    codegen-reaching value position is the located ambiguity error rather than
    a codegen input. Discovery-driven entry points (tests) are monomorphisation
    roots like `main`. Contracts:
    [concrete codegen boundary](concrete-boundary-type.md),
    [total concreteness](total-concreteness.md).
13. **Typecheck is the sole producer of resolved identities and codegen views.**
    Every statically resolved reference carries the storage identity under
    which it resolved; minting and the ambiguity check share one value-position
    walk. Contracts: [backend keyed consumption](backend-keyed-consumer.md),
    [typed resolution carriers](typed-resolution-carrier.md).
14. **Unresolved return-polymorphic dispatch crosses on `CheckResult`.** The
    types live with their producer because the binary is the only consumer; the
    binary raises the diagnostic at its two execution boundaries and backend
    does not interpret dispatch state
    ([design](../typecheck/return-poly-dispatch-signal.md)).

---

## 3. Backend — `crates/cranelisp-backend/`

**Bounded context.** Concrete typed bodies become executable code. Backend emits
Cranelift IR and produces in-memory code, object files and the cache pair. There
is one compilation entry regardless of mode: the mode is a property of the
Cranelift module the caller supplies. The crate has no cadence; compilations
with disjoint inputs may run concurrently.

**In scope.**
- IR emission for every language construct, including reference-count
  discipline and type-directed drop glue.
- In-memory artefacts with reclaim on drop; object files; cache read and write.
- Per-module GOT binding for cross-module indirection.
- `(trace …)` codegen: wrapper emission, traced-set discovery from the symbol
  tables and display-descriptor baking ([tracing](tracing.md)).
- Platform codegen: GOT-indirect dispatch against the DLL's exported table, the
  schema generator and layout hash, and the tag-guarded effect-name stamp
  ([platform interface](platform-interface.md)).
- Effect-concurrency node construction ([effect concurrency](effect-concurrency.md)).

**Out of scope.** Inference and resolution (typecheck); scheduling and code
retention (binary); runtime helpers (intrinsics) and primitive bodies
(primitives).

**What crosses the boundary.**
- **In:** the symbol tables and module aliases, the targets to compile, and a
  Cranelift module to emit into.
- **Out:** the populated GOT slot for each compiled target, and returned
  artefacts (IR text, code size, duration, per-type drop-glue addresses). On a
  cache hit, `load_object` returns the linker artefact and restored table.
- The **caller composes the lifecycle owner**: backend names `Code` but never
  constructs it; the binary builds it from the `Jit` or linker artefact it owns
  and publishes it through the types table.
- **Minimal JIT-setup boundary.** The `Jit` boundary is constructor, module handoff, `define_symbol` and `Drop`.
- The GOT-population observer is an extension point; observer state is the
  binary's.
- Drop glue crosses by key, never by ambient lookup: the types-owned
  `drop_glue_symbol_name` names it per module and concrete type. Glue has no GOT
  slot because it is neither language-callable nor redefinable.
- The **cache is an implementation mechanism of this context**, not a separate
  one. Its sidecar is the serialized symbol table; its interior invariants live
  in the cache module rustdoc.

**Invariants.**

1. **One emission path.** `compile_to_module` is the sole IR emission entry;
   JIT and object differ only in the supplied module. Mode is not a parameter.
2. **Uniform consuming calling convention.** The conservative call transfers
   ownership of heap arguments; the callee owns its heap parameters.
   Constructors, user functions, trait methods, primitives and externs follow
   the same rule. Ownership inference narrows from this point and never widens
   past it ([ownership inference](ownership-inference.md)).
3. **The GOT is the single home of callable addresses.** Backend writes the
   pointer to the target's slot; the lifecycle owner carries retention only.
4. **Backend trusts `codegen_targets()`.** A requested target outside that
   projection is a typed compilation error, never a synthesised body.
5. **Published-pointer reclaim safety.** Dropping `Jit` frees executable
   memory. Closures embed raw code and glue pointers from their owning
   compilation. The binary owns the guarantee that no derived pointer is
   reachable when the owner drops
   ([Principle 22](principles/22-published-pointers-have-retention-owners.md));
   backend relies on it and does not enforce it.
6. **One IR, two GOT resolutions.** Every emission imports the per-module GOT
   symbol; the JIT resolves it to the live table and the object file defines it
   as data. Backend does not branch on mode.
7. **Bare names, local linkage.** No entry-module special case; the linked
   `main` alias is the binary's.
8. **`Jit::define_symbol` is the one host-symbol escape hatch**, for
   host-promised externs whose body lives in the binary (§7). It forks no
   constructor and adds no registry.
9. **Reference counting requires static representation knowledge, so only
   concrete types reach codegen.** Heap classification is total over
   `ConcreteType`; there is no type-variable arm and no runtime representation
   guess. A concrete body realization carries its codegen view by
   construction. Constructor and accessor templates are signature-driven
   and may classify a residual declared field conservatively. Open residuals:
   FIXME 0903, FIXME 0931 and FIXME 0934 under `design/arch/fixmes/`.
   Representation freedom beyond the one-word value model is a user-arbitrated
   language question raised in the
   [release-backend proposal](release-llvm-backend.md).
10. **Backend is a pure keyed-lookup consumer
    ([Principle 24](principles/24-resolve-once.md)).** Every identity arrives
    resolved and fully qualified; a carrier miss is a located codegen error,
    never a re-resolution, precedence walk or scan. The only by-name references
    are the fixed intrinsic catalog and the naming primitives.

**Effect concurrency.** Backend constructs poll-shape, launch and select nodes;
the arm is chosen by the effect's declared shape, never by a build feature. The
poll node is uniform regardless of resource role. Holding a deferred effect's
arguments alive across suspension is runtime-owned (§4b invariant 15).

---

## 4a. Primitives — `crates/cranelisp-primitives/`

**Bounded context.** Language-defined operations callable from user code through
the `primitives` module. They appear in a symbol table and are addressable as
values. Together with intrinsics this crate is the backend-emitted runtime
library; the binary is only its host. It is a leaf with no cadence and no trait
knowledge.

**In scope.** Scalar arithmetic, comparison and logic; conversions; string and
vector operations defined by the language; the static `PRIMITIVES_TABLE` and its
GOT; the declared ownership and ABI facts for each primitive.

**Out of scope.** Code generation (backend); backend-emitted call targets
(intrinsics); trait dispatch (typecheck and the standard library); session
mounting (binary).

**What crosses the boundary.**
- **Out:** one static, `PRIMITIVES_TABLE`, an `Arc<SymbolTable<(), ()>>` whose
  GOT backs every slot-dispatched primitive. The binary concretises it with the
  types `into_concrete` bridge at session start; the inner GOT is shared, so the
  process has exactly one primitives GOT.
- **In:** types vocabulary; the intrinsics allocator, blessed layout constants,
  typed counted-reference funnels and the two Vec-of-String operations
  (§4b invariant 17). Nothing from backend.

**Invariants.**

1. **User-callable surface.** Every populated entry is reachable as
   `primitives/<name>`. Adding, renaming or removing one is a language change.
2. **Symbol-table addressable.** A slot-dispatched primitive's slot holds its
   address, so an operator used as a value works like any function value.
3. **Uniform dispatch, structurally enforced.** Primitive calls follow the
   ordinary cross-module GOT sequence. Backend does not depend on this crate and
   therefore cannot name a primitive's extern function. Direct JIT symbol
   registration is reserved for intrinsics.
4. **No trait knowledge.** Backend's inline table maps a resolved primitive name
   to an instruction, never a trait, method and type to a name.
5. **Inline substitution is optional.** Backend may inline a known direct call;
   a slot-dispatched primitive's pointer remains the fallback for indirect use.
   A primitive realised only inline has no slot by construction (§7).
6. **Process-static lifecycle.** The table is built once and never invalidated;
   entries own no reclaimable code; primitives are never cached.
7. **Language-driven evolution.** Backend convenience belongs in intrinsics.
8. **Consuming convention at the extern boundary.** Every extern consumes the
   heap arguments it does not return.

---

## 4b. Intrinsics — `crates/cranelisp-intrinsics/`

**Bounded context.** Runtime support reached as stable-ABI call targets from
emitted code, plus a narrow Rust-path surface through which the sibling runtime
crate reaches intrinsics-owned representation and lifetime mechanics. Intrinsics
are not callable from user code, are in no symbol table and have no GOT slot.
The crate knows nothing of compilation, scheduling or the REPL: runtime
semantics depend only on the running program. It hosts the **runtime cadence** —
atomic reference counting, fork-join evaluation and the effect reactor — which
produces no handoff to any other cadence.

**In scope.**
- Heap model: allocation, the two-word header and the base-pointer convention.
- Reference counting, shallow release and the protocol-specific `consume_*`
  walks; `free_io_node`, the zero-count IO teardown beneath the typed handles.
- The typed counted-reference vocabulary (`handle::Owned`, `handle::Borrowed`)
  and the nine consuming funnels that take `Owned`
  ([design](../runtime/s119-typed-consume-funnel.md)).
- String and vector runtime; fork-join cells (`IVar`); the spark-budget gate.
- The IO trampoline, effect reactor, permit pools, launch supervision and the
  `HostCtx`/waker vtable ([reactor design](../intrinsics/reactor.md)).
- The program driver `cranelisp_run_program` and the runtime-error slot.
- `catch-runtime-error` and the fork-join error-slot ferry.
- The `(trace …)` runtime family and its display-descriptor layout.
- The fault guard at the platform-effect force site.
- The IO-observer registration point; observer state is the binary's.
- The published catalog `intrinsics_table()` and the single
  `host_callbacks()` builder.

**Out of scope.** Code generation; user-callable primitives; observability state
and diagnostics composition (binary); platform DLL loading (binary).

**What crosses the boundary.**
- **Out:** the `extern "C"` symbol surface named by the catalog; the Rust-path
  operations above; the observer registration API.
- **In:** types layout constants and identifiers; platform's IO tags, host
  context and effect-outcome types.
- Emitted-call and platform entry signatures remain raw ABI words. `Owned` and
  `Borrowed` are a Rust-side discipline for primitives, backend fixtures and the
  binary's macro marshalling; they change no emitted ABI. A public allocation
  API redesign is separate future work
  ([ACT-0959](../../sprints/actions/ACT-0959-public-allocation-api-redesign.md)).
- Primitives' private adoption, borrowed-projection and storage-transfer sites
  are a bounded, named trusted base; the approved site set and its evidence
  obligations are in
  [the allocation proposal](../../sprints/s122-primitives-allocation-proposal.md).

**Invariants.**

1. **Runtime substrate only.** The dominant surface is emitted-call targets and
   trampoline operations. A Rust-path operation is admissible only with a named
   cross-crate consumer and `arch` approval of the public delta.
2. **Representation containment.** Layout constants are defined only in the
   allocator, string and vector modules. Backend reads layout through named
   externs and blessed constants; primitives read blessed constants and never
   re-derive offsets.
3. **Atomic reference counting.** Every increment and decrement is atomic, with
   an acquire fence on the free path before glue reads fields. Every Rust-path
   increment routes through `rc::rc_inc` (release ordering, the NFR floor)
   unless a stronger ordering is documented at the site. The one documented
   exception is the `IVar` spark increment, which stays sequentially consistent
   because the cell's count and state machine share one total order.
4. **Strings are opaque to backend.** All string operations are extern calls.
5. **Closures embed their drop-glue pointer** beside the code pointer, so a
   closure released in another module needs no side table. The glue is
   backend-generated per lambda and null when nothing is captured by heap.
6. **Consuming convention at the extern boundary.**
7. **The trampoline releases an intermediate IO node shallowly**, because its
   fields are already re-owned during the walk; transitive release is a
   distinct operation.
8. **No state across sessions, and no reset seam.** The allocation counters are
   process-lifetime evidence. The absence of a public reset is deliberate: a
   reset could zero the only evidence the allocation-parity check has.
   Consumers needing a window snapshot and subtract.
9. **Backend-driven evolution and deliberate dispatch asymmetry.** Intrinsics
   resolve by name through direct symbol registration; primitives dispatch
   through a module GOT. Intrinsics are not a module, and forcing them through a
   synthetic one would invent a module with no user-visible surface.
10. **No type names at the public surface.** The crate operates on heap words
    and marshalling tags.
11. **The catalog is flat and self-published.** `intrinsics_table()` returns
    `name → (arity, has-return, pointer)` records. It is read at three
    resolution points — JIT construction, cache-hit linking and the linked
    executable — and never at codegen, which names intrinsics by string. It is a
    function rather than a static to avoid an `unsafe impl Sync` over raw
    pointers. The catalog's own name-set test owns the entry list; no count is
    restated here. `IntrinsicEntry::is_runtime` is documentation metadata with
    no dispatch consumer. Host-promised externs (§7) are not catalog entries.
12. **The `(trace …)` runtime is an intrinsic family** published through the
    catalog and working in every mode, including linked executables. The value
    formatter is a pure walk of a backend-baked descriptor and the heap value,
    with no symbol-table access. Discovery and baking are backend's; the binary
    hosts no trace runtime ([tracing](tracing.md)).
13. **`catch-runtime-error` is a self-contained intrinsic** over the thread-local
    error slot. Both fork-join join paths ferry a worker's error into the
    joining thread's slot, first error wins, so the combinator stays a plain
    own-thread reader. Both parallelism forms are structured, so every spark
    joins inside the combinator's dynamic extent
    ([test discovery](test-discovery.md)).
14. **Intrinsics captures a platform fault; the binary composes the
    diagnostic.** The guard at the single effect force site keeps the signal
    half host-side, reads the DLL-returned effect outcome and the effect name
    carried on the node, and records an internal fault. It constructs no
    `PlatformError` (§5 invariant 9).
15. **Argument lifetime across suspension is runtime-owned.** A reactor-deferred
    effect's baked arguments stay alive until the reactor resolves the effect
    by completion or cancellation, and the state closure is consumed exactly
    once on those same two paths that release the permit. Backend's obligation
    is unchanged: it emits data and does not model when the runtime polls. A
    compile-time suspension transform is deferred
    ([effect concurrency](effect-concurrency.md)).
16. **Deep release is type-directed; every displacement and typed-context exit
    has a named owner.** The header stays two words, so there is no generic deep
    release of an untyped word: `consume_shallow` is shallow and each
    `consume_*` owns one known layout. Generated values are released by
    backend's type-directed glue at any depth. Replacement inside generated code
    (a tail-call parameter overwrite) releases the superseded value through the
    same glue unless ownership moves forward. A forced `Pure` retains its
    payload for the result while the node keeps its own reference, so a repeated
    force is valid. The binary's result seam and the linked startup stub own
    release after observation. A header type word is rejected: it would tax
    every allocation to solve an enumerable set of typed exits. Register:
    [safety invariants](safety-invariants.md); seam detail:
    [total concreteness](total-concreteness.md).
17. **Vec-of-String crossing.** Primitives' `split` and `join` reach the vector
    layout owner through exactly two Rust-path operations,
    `vec_strings_from_owned` and `with_vec_strings`. They are absent from the
    catalog, are never emitted call targets and expose no offsets. Their
    `unsafe` caller obligations — transferred references, initialise-before-
    publish, the bounds checked before a slice is formed, and a non-escaping
    non-owning read — are stated in their rustdoc. String semantics stay in
    primitives.

---

## 5. Platform — `crates/cranelisp-platform/`

**Bounded context.** The shared interface contract between the host binary and
platform DLLs; both link this crate. It defines the C-ABI types, safe wrappers
over them, the layout constants both sides agree on, and the macro DLL authors
use to publish a manifest. It owns no session state and no cadence; its only
state is per-DLL write-once globals initialised at load (the allocator slots
and the parsed schema).

**External audience.** This is the only implementation crate with out-of-tree
consumers. DLL authors depend on it alone, so it re-exports the types-owned
vocabulary they need — for example `SchedulingClass`, `PlatformError`, the
concurrency descriptor vocabulary and `GOT_TABLE_SIZE` — under
[Principle 15](principles/15-facade-types-live-with-behavior.md)'s
external-audience exception.

**The three exports.** A platform exports exactly its GOT (one slot per effect
in manifest order), its manifest and its schema with a layout hash, each
namespaced by platform name. The crate builds both a dynamic library for live
sessions and a static library for linked executables: same exports, two
binders. **The DLL builds the GOT (its facts); the host builds the symbol table
(its invariants).** Platforms author no schema dialect and export no function
names; dispatch is slot-indexed. Canonical contract:
[platform interface](platform-interface.md); interior design:
[platform design](../platform/platform.md).

**In scope.** `#[repr(C)]` contract types governed by `ABI_VERSION`; transparent
wrappers over the one-word value representation; shared layout constants and IO
tags; `declare_platform!`; host-side manifest conversion; the schema parser;
poll-leaf authoring support.

**Out of scope.** DLL lifecycle, the load path and the `/platform-schema`
command (binary); the trampoline (intrinsics); the schema generator and layout
hash (backend); type-signature parsing (frontend and typecheck, driven by the
binary); ADT declaration — a platform's data types are ordinary modules
referenced by qualified name.

**Contracts stated here.**
- **Heap values cross as allocation-base pointers.** Wrapper increments and
  decrements match emitted-code atomicity. `CLOwned<T>` is the host-side
  ownership wrapper; the consuming conversion follows the consuming convention.
- **The schema is a machine-written artefact**, generated from the loaded
  platform's tables and embedded by the platform. The host never takes schema
  text from the DLL: at load it regenerates, hashes and compares. `--run` and
  linked executables refuse a mismatch; the REPL warns and loads, because it is
  where the artefact is regenerated.
- **`ABI_VERSION` is the single layout gate**
  ([Principle 14](principles/14-ffi-layout-discipline.md)). Any layout-affecting
  change to a contract struct, or to a constant a DLL reads by offset, bumps it;
  a transparent wrapper or method alone does not. The current value and the
  per-version history live in the `ABI_VERSION` rustdoc only.
- **The effect call is a poll-based async C ABI.** The platform is a leaf that
  owns *what*; the host owns *when*. Each effect is independently blocking or
  poll-shaped through its concurrency descriptor. Resource scheduling flows
  through the host's `HostCtx` vtable (register, acquire, retire); release is
  trampoline-owned and cancellation never re-enters the poll function. Resource
  role is a compile-time fact. Resource handles are opaque to the trampoline and
  ordinary ADTs to the program.
- **`HostCallbacks` is permanently the two allocator entries.** It is built by
  the single `cranelisp_intrinsics::host_callbacks()` for every host mode.

**Invariants.**

1. **Platform function pointers live in the platform module's GOT**, which wraps
   the DLL's exported table in place; the slot is the manifest index. A loaded
   platform is a synthetic module whose callables carry a platform-effect origin
   with their scheduling class and poll shape. The binary retains the DLL handle
   for the session.
2. **Stable C ABI.** Contract structs are `#[repr(C)]`; the loader refuses a
   mismatched `ABI_VERSION`.
3. **No closure crosses the boundary.** The boundary is poll-in, wake-out. There
   is no host-mediated closure call and `HostCallbacks` will not grow
   reference-count entries. An uninvertible synchronous C dispatcher is handled
   inside the platform in its own language.
4. **One word representation per wrapper type**, agreed with intrinsics; strings
   are intrinsics-allocated.
5. **Host callbacks are installed once per loaded platform**, when the host
   calls its manifest function, and are never rewritten.
6. **No DLL unloading mid-session.** This bounds the crate's deliberate leaks and
   keeps slot pointers valid.
7. **Concurrency facts are declared by the DLL and consumed by the host.** The
   loader lifts the scheduling class and poll shape onto the callable; runtime
   permits flow through the vtable, never on values.
8. **No resolved type identifiers at this surface.** Signatures cross as text and
   are resolved by the binary's loader.
9. **Faults are funnelled, never aborts.** A platform fault surfaces as a located
   `PlatformError::DispatchError` naming the effect. The effect name travels
   with the effect node, stamped by backend only when the returned node is an
   effect node; an unstamped node degrades to an unknown name. The panic catch
   is DLL-local because each dynamic library carries its own panic runtime; the
   fault crosses as a returned value. Intrinsics captures; the binary composes
   (§4b invariant 14).

Open: marker-binding ergonomics for multi-ADT platforms (FIXME 0873 under
`design/arch/fixmes/`).

---

## 6. Binary / int — `src/` + `crates/cranelisp-exe-bundle/`

**Bounded context.** The integration layer wires the other contexts into a
deployable compiler and a working REPL. It hosts three cadences, coordinates
their handoffs, owns all development tooling and is the only context that knows
the concrete carrier of compiled code. `src/` and the exe-bundle are one surface
for design, development and review. Interior design:
[binary design](../int/int.md).

**Host-client of the runtime.** The binary constructs nothing inside the effect
runtime. It calls the single program driver and configures no reactor policy;
the runtime lives in intrinsics because a linked program contains no `src/`.
The compiler's own scheduler is a separate concurrency axis and is this
context's. The only runtime-facing code here is the host-promised externs that
must read live session state.

### 6.1 Internal cadences

- **Compilation.** Workers claim work packets, publish results into
  compilation-scoped state and notify the scheduler. Closed loop; no external
  clock.
- **REPL.** Turn-based: one prompt, one parse, one submission, one display. It
  owns input, slash commands, formatting and the diagnostic surface, not
  compilation state.
- **Watcher.** Open loop: the operating system dictates its timing. Captured
  changes cross to the REPL at a poll point and become re-register requests.

### 6.2 Inter-cadence handoffs

- **REPL → compilation:** submit and wait on a terminal signal. A worker that
  meets a missing dependency drops its stack-local cluster state, registers the
  dependency, returns its thread to the pool and is requeued when the dependency
  is ready; nothing is parked in shared maps.
- **Compilation → REPL:** a displayable result or an error.
- **Watcher → REPL → compilation:** file changes are polled at prompt boundaries
  and never interleave with input.

The runtime cadence inside a running program produces no handoff.

### 6.3 Within-cadence access

Each cadence reaches shared state only through handles scoped to it. There is
no ambient session handle that any consumer may reach into; REPL, compilation
and watcher state cannot cross-contaminate.

### In-scope

- The cadences, scheduler and worker pool; module loading; the cache writer;
  save and source regeneration; the file watcher; CLI parsing.
- The concrete code carrier, the retention pool for displaced code and DLL
  retention.
- **Staging and publication policy.** The binary owns the staging table handed
  to typecheck, the gap-retry loop, and the choice of publication decisions the
  types table executes ([symbol-table lifecycle](symbol-table-lifecycle.md)).
  Candidate work is isolated until publication
  ([design](../int/prelude-table-write-isolation.md)).
- **Macro execution and source-ordered checkpoints.** The binary implements
  `MacroExpander` and owns the expansion loop that runs before `check_forms`.
  Each direct or expansion-produced `defmacro` is prepared, compiled and
  published as one module-local checkpoint before later forms expand. A failed
  checkpoint exposes nothing; a successful one survives later failures.
  Same-module non-macro definitions are unavailable at expansion. The walk
  shields quoted subtrees, qualifies references and never binders, and only
  selects annotation spans for the frontend (§1 invariant 9). A committed
  checkpoint's redefinition effects are carried on the orchestrating stack and
  settled exactly once; they never enter a scheduler mailbox or shared map and
  are not retry state.
  Contracts: [macro availability](macro-availability-model.md),
  [macro expansion ownership](macro-expansion-ownership.md),
  [quote shield](../int/quote-shield.md).
- **Macro clause ownership is pinned, not inferred.** A clause receives an owned
  argument list and returns an owned result, so the binary clears any inferred
  ownership summary from a synthesised clause before publication; two clauses
  of one macro could otherwise demand opposite host protocols
  ([design](../int/macro-turn-ownership.md)).
- **Development tooling.** Observability ring buffers and introspection.
  Introspection is REPL-only: its store does not exist in batch modes, and
  anything the compile pipeline reads lives on the symbol table
  ([introspection ownership](d1-introspection-repl-only.md)). On a cache hit,
  display records are rehydrated lazily from the backing source file and are
  never cached. The explicit run mode, not the presence of introspection, is
  what mode-conditional behaviour reads.
- **Ordered definition results.** A REPL turn that publishes several definitions
  reports each in emitted order from a stack-local receipt of exact identities,
  without scanning the table. Each binding renders through its ordinary
  declaration classification, so a macro stays a macro in its echo.
- **Synthetic-module bootstrap**: mounting the primitives table, seeding the
  `Option`, `Pair` and `Result` types, and publishing the host-promised
  `discover-tests` extern whose body reads live session state
  ([test discovery](test-discovery.md)).
- **The platform load path** and the `/platform-schema` command
  ([platform interface](platform-interface.md)).
- **Exe-bundle:** force-linking the runtime crates and the startup stub.

### Out of scope

Parsing (frontend); inference (typecheck); emission (backend); runtime helpers
and primitives (§4b, §4a); the platform ABI (§5).

### What crosses the boundary

- **In:** the public surface of every other context.
- **Out:** nothing to another crate — this is the application root. The
  root library's session surface serves its own binary target and tests; it has
  no generated baseline, but a public change still takes contract review and the
  applicable user approval. The exe-bundle exposes a startup stub to the system
  linker only.
- **Windows:** cadence-scoped and never exposed.

### Known architectural constraints

- **One pipeline, mode as a parameter
  ([Principle 11](principles/11-single-pipeline-mode-parameters.md)).** REPL-only
  facilities are side effects gated in the REPL arm and provably inert
  elsewhere; they reuse the shared pipeline functions against an isolated
  substrate rather than forking them.
- **One program driver.** `--run`, the REPL and linked executables all reach the
  runtime through intrinsics' `cranelisp_run_program`, which returns an outcome
  and neither exits nor clears the error slots. The host translates the outcome
  into an error or a value; the linked stub branches on it. Error-slot checks
  therefore exist at one site and cannot diverge across modes.
- **Mutual imports are a cycle error, not a deadlock.** All signatures of a
  module's import closure register, in topological order, before any body
  checks; a cyclic closure has no order and is diagnosed at the import.
  Mutually importing modules are not compiled.
- **The signature barrier is a requeue gate, never a parked pool thread.** A
  worker that reaches an unready closure registers the missing members, frees
  its thread and is requeued when the closure is ready, so a bounded pool cannot
  deadlock by exhaustion. The REPL thread waits without consuming a pool slot
  and holds its entry module exclusively while driving. Readiness is the
  module's terminal pool state; there is one readiness protocol
  ([design](../int/signature-body-prepass.md)).
- **Bare-name ambiguity hints are cluster-robust by data, not by mode**: the
  same path serves one large batch cluster and per-form REPL clusters.

---

## 7. Cross-crate types — `crates/cranelisp-types/`

**Bounded context.** The single home for everything that crosses crate
boundaries: data that flows by ownership, and marker traits downstream crates
implement to supply concrete types where a boundary is generic. It depends on
nothing in the workspace. The crate is `arch`'s own; consumers route shape
changes to `arch`. [Principle 15](principles/15-facade-types-live-with-behavior.md)
governs membership: crossing one boundary alone does not move a type here.

**Catalog by family.** AST and type expressions; the type representation,
schemes, substitutions and the concrete boundary type; `Sexp` and the
reader-quote classifier; the symbol table, its declarations and lifecycle;
resolution; module aliases; typed resolution and ownership carriers; the
post-monomorphisation codegen view; heap header and value-layout classification;
the GOT table; marshal tags; scheduling and concurrency vocabulary; identifier
newtypes; spans, errors and warnings; shared constants. Narrative companion:
[boundary types](interfaces.md).

**Contracts stated here.**

- **Symbol table and lifecycle.** Types owns the per-spelling candidate and
  binding store, the declaration families, callable lifecycle states, slot
  claims and atomic module publication. One authored declaration has one
  canonical `Binding`; imports and re-exports are candidate references that
  carry identity and local visibility, never a copied scheme or lifecycle.
  **Callability is structural:** a callable has a GOT slot only in a concrete state whose scheme is concrete, and
  slots are minted only by the table. Templates, inline primitives and
  host-promised externs have no slot by construction
  ([Principle 20](principles/20-model-invariants-by-representation.md)). The
  compilable projection is `codegen_targets()`; the table is deliberately both
  the checking environment and the codegen manifest, because a second structure
  would be a parallel store. Contract:
  [symbol-table lifecycle](symbol-table-lifecycle.md). Executable identity:
  [uniform executable identity](s122-overload-reorder-publication.md).
  Concreteness: [total concreteness](total-concreteness.md) and its
  [retained reasoning](concreteness-types-first.md).
- **Plain fields under a table guard are the concurrency end state.** Every
  per-module write is serialized by the session map's guard; the GOT is the one
  genuinely concurrent surface and is atomic per slot. The session collection is
  a map of module path to table; there is no per-symbol concurrent map.
- **Visibility is per exposure; documentation is per declaration.** A
  declaration's visibility lives once on its binding and an exposure's on its
  candidate. Docstrings live on the declaration facet that owns them. A module
  preamble is a table-level field, deliberately off the symbol axis so it cannot
  leak into import or export enumeration.
- **Form records and effects are complementary.** The table's import and export
  lists record what the user wrote, in order, for source regeneration and
  duplicate warnings. Binding and candidate visibility record the effect used by
  resolution. Neither retires the other; parse-time installers keep them
  consistent.
- **Insertion-time conflict enforcement.** Rename collisions within a table and
  mount collisions within one owner's aliases are structural. A mount that
  collides with a loaded module path crosses two tables, so the installer must
  check it atomically.
- **Module aliases are session-level**, keyed by owner and name through the one
  types key function, and looked up by a referring-module-scoped walk
  ([scoped module aliases](module-alias-scoped-lookup.md)). Module path,
  in-module symbol and receiver-pinned type name remain three distinct keying
  domains.
- **Resolution is a types-owned query.** `ResolutionScope` performs the import,
  alias, visibility and chain walk with the prelude fallback fixed at scope
  construction; the caller chooses the first-hop view. The binary's macro
  recognition passes committed tables and typecheck passes staging over live.
  Cross-module hops always land in committed modules
  ([prelude and explicit imports](prelude-import-convergence.md),
  [resolve home before enumeration](resolve-home-enumeration.md)).
- **Trait implementations split by placement.** The discovery shell lives in the
  trait's defining module under a keyed name and points at the writer's module,
  which holds the method bodies and their slots. Importers follow the trait
  reference and probe one key
  ([trait-implementation persistence](trait-impl-cache-carrier.md)).
- **Trait methods are addressed by a composite member key** in the trait's
  defining module. A trait is not a module namespace and `FQSymbol` stays two
  components. Constructor keys follow
  [constructor keys](dotted-ctor-canonical-keys.md).
- **FQTypeName binding — resolved-stage type identity is module-qualified.** Bare type names are
  confined to syntactic-lift sites and receiver-pinned helpers.
- **One structural renderer.** `render_type` is the single type-to-text walk;
  naming conventions are configuration values, and REPL-only decoration stays in
  the binary.
- **Soundness-coupled predicates are single-sourced here.** Value-layout
  eligibility, concreteness, the IO result-root rule and the
  ownership-analysis toggle each have one definition that typecheck and backend
  both delegate to, because two copies could disagree unsoundly. FIXME 0898
  under `design/arch/fixmes/` tracks the result-root rule's second encoding.
- **Registration funnels.** ADT registration derives its complete entry set
  through one builder shared by typecheck and the binary's bootstrap. No generic
  "module table from a source" abstraction exists, because no consumer
  dispatches over an unknown source kind.
- **State types expose accessors; data-record DTOs expose fields.**
- **Test support is feature-gated.** `test_support` is compiled only for tests
  or the `test-support` feature, and the production baseline is generated
  without it.
- **Marker traits** (`CodeStore`, `LinkerStore`) keep this crate ignorant of
  backend and runtime concrete state; `MacroExpander` is the execution callback
  the binary implements.

**Out of scope.** Anything that would invert the dependency graph (Cranelift,
JIT or linker types, the concrete code carrier); orchestration; runtime
intrinsics; typecheck's per-form transient state.

**What crosses the boundary.** Every public item is a boundary type; the crate
is its surface. Cache serialization rules and runtime-only exceptions are in the
[types memory](../../crates/cranelisp-types/CLAUDE.md).
