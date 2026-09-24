# Platform interface — how a platform DLL exposes itself to the host

**Status.** Current cross-context contract, owned by `arch`; delivered in source.
The user ratified the three-exports model and the generated schema on
2026-06-07, and later ruled per-platform export namespacing (S86), the single
ABI with a single trampoline (S96), the `ctx` vtable handle model (S97) and the
closed poll-in / wake-out boundary (S98). Open points are in §2.1. Earlier
proposals and the delivery record are in Git.

**Neighbouring authorities.** This document states the boundary; it does not
restate its neighbours.

- [Bounded contexts](bounded-contexts.md) §5 summarises the platform context and
  its invariants; §3 and §6 place the backend and binary responsibilities.
- Exact C-ABI items, their layout rules, the current `ABI_VERSION` and its
  per-version history live in rustdoc in
  `crates/cranelisp-platform/src/lib.rs`, `crates/cranelisp-platform/src/declare.rs`,
  `crates/cranelisp-platform/src/concurrency.rs` and
  `crates/cranelisp-types/src/scheduling.rs`.
- [Platform design](../platform/platform.md) and its siblings own the crate
  interior; [Writing platforms](../../user/guide/writing-platforms.md) is the
  author guide.
- [Effect concurrency](effect-concurrency.md) owns the concurrency architecture
  that §6.8 projects onto this boundary.
- Required behaviour is in `spec/08-modules.md` (platform modules, search order)
  and `spec/10-io.md` (platform declarations, ABI contract).

**Section numbers are cited from source, tests and designs.** Keep them stable;
retire a number only with the incoming citations repaired in the same change.

---

## 1. Overview

A platform is an out-of-tree Rust crate that supplies native effect functions to
cranelisp programs. **It exports exactly three things**, each namespaced by the
platform name (§5.5.5):

1. **Its GOT** — a function-pointer table, one slot per effect, in manifest
   order. Compiled code calls a platform effect indirectly through its slot
   (§5.1).
2. **Its manifest** — declarative data describing the platform and each effect.
   A live session builds the platform module's symbol table from it (§5.2, §5.3).
3. **Its schema and layout hash** — a compiler-generated description of the
   ADTs its signatures marshal, plus a hash binding that description to the
   host's live type tables (§5.5). A platform that marshals no ADT omits both.

The governing split:

> **The DLL builds the GOT — those are its facts. The host builds the symbol
> table — those are its invariants.**

A DLL knows its own function pointers. The host alone can decide module
mounting, sequence numbering and its Rust `SymbolTable` representation
consistently across every loaded module. So C-ABI facts cross the boundary and
the host composes the table from them (§3).

**One crate, two artifacts, two binders.** A platform crate builds a cdylib and
an rlib:

- a live session (REPL, `--run`, and the compile step of `--link`) opens the
  cdylib and resolves the exports with `dlsym`;
- `--link` statically force-links the rlib, so the same exports resolve as
  ordinary linker symbols. A linked executable contains no `dlopen`.

The platform's own code has no mode fork. Which platforms load is decided by the
program's `(platform name)` declaration.

**Consumers.** A linked executable uses the GOT, calls each manifest entry point
once at startup (§7.3) and checks the layout hash there; it builds no symbol
table. A stale rlib therefore builds and refuses at run — the accepted trade
against reading symbols out of archives at build time (§5.5.4). A live session
uses all three exports.

**New capability rides an exported symbol, never manifest-struct growth.** A
platform adds an effect by adding a slot and a manifest entry.

**Vocabulary.** *GOT* is the function-pointer table (not "slab", which survives
only in source identifiers). *Manifest* is the declarative effect data. *Schema*
is the generated type-layout artifact.

## 2. Open points and settled questions

### 2.1 Open points

- **A platform signature with a residual type variable must refuse at mint** —
  FIXME 0933 under [open filings](fixmes/).
- **Source rustdoc describing retired ABIs** (FIXME 0870) under
  [open filings](fixmes/). Until 0870
  closes, rustdoc that disagrees with this document about a *retired* mechanism
  is the stale side; rustdoc remains authoritative for exact current items.
- **`spec/10-io.md` §10.10.1 still carries a forward commitment** (its `Fn a b`
  row, marked future) to a host callback through which a platform invokes a
  cranelisp closure, with reference-count callbacks for retention. The later
  user ruling in [effect concurrency](effect-concurrency.md) §12.1 closes the
  boundary to closures and says `HostCallbacks` will not grow those entries
  (§3a). The two carriers disagree. Reconciling them is a normative question for
  `spec` and the user; this document applies the later ruling and does not
  decide the specification's wording.
- **The layout-hash symbol is a Rust `&'static str`, not a C-ABI layout.** The
  host (`src/platform.rs::load_platform_dll`) and the startup check
  (`crates/cranelisp-intrinsics/src/layout.rs::cranelisp_check_layout_hash`)
  both read it as a Rust fat reference. It is the one boundary datum outside
  [Principle 14](principles/14-ffi-layout-discipline.md)'s `#[repr(C)]`
  discipline. Grade: asserted. Falsifier: a platform built by a toolchain whose
  `&str` representation differs from the host's, which the `ABI_VERSION` gate
  does not detect. No change is approved; re-representing it is a public-ABI
  change under the user gate.
- **Platform-name collision with the module-path escape image.** The
  `platform.<name>` GOT symbol keeps a verbatim join rather than the escaped
  mint, so a platform name beginning `d`, `h`, `u` or `_` can collide with a
  contrived root-module spelling. The residual and its closure (loader-side name
  validation) are recorded at
  `crates/cranelisp-types/src/module.rs::got_data_symbol_name`.
- **The GOT and layout-hash symbol names are formatted inline** on the emit and
  consume sides; only the manifest name has a shared helper (§5.5.5). Adding
  sibling helpers is an optional consolidation and a public-API change under the
  user gate. It is not owed.
- **Lazy reactor construction** is a workload-triggered refinement, not an
  obligation (§6.8.0a).

### 2.2 Settled implementation questions

- **q-tag-stability — settled.** Constructor tags are source-positional and
  schema entries are emitted from an ordered map, so regeneration over unchanged
  resolved source is byte-identical
  (`crates/cranelisp-backend/src/schema.rs::generate_schema`; its unit tests
  assert hash stability and change sensitivity).
- **q-schema-grammar — settled: an S-expression dialect.** The generator emits
  it and the platform crate parses it with its own replicated reader (§5.5.1).
  The grammar is stated once, in the module rustdoc of
  `crates/cranelisp-platform/src/schema.rs`. A grammar change is a named
  three-site change: the generator, that parser, and the compile-time scanner
  `crates/cranelisp-platform/src/declare.rs::schema_declares_type`.

## 3. The requirement

**A linked executable needs code pointers only.** It has no typechecker, REPL or
symbol-table scan. The exported GOT is a link-time data symbol resolved like
`__cranelisp_got_primitives` and every user module's GOT.

**A live session needs the GOT and a symbol table.** It typechecks call sites,
answers `/sig`, `/doc` and `/imports`, and dispatches GOT-indirect. The table is
host-built from the manifest.

**A DLL-built or serialised `SymbolTable` must not cross the boundary.**

- *Rust-ABI hazard.* `SymbolTable` is a generic `#[repr(Rust)]` type. Its layout
  is not a contract across compiler versions; a DLL built by another `rustc`
  would hand over a mis-laid-out value — silent corruption
  ([Principle 14](principles/14-ffi-layout-discipline.md)).
- *Serde format as ABI.* Shipping serialised bytes makes the wire format a public
  ABI every DLL author must track: heavier and more brittle than an array of
  pointers.
- *Host-owned invariants.* Slot adoption, mounting and sequence numbering must be
  decided once for all modules
  ([Principle 7](principles/07-single-source-of-truth.md)).

**Specification anchors.** `spec/08-modules.md` §8.9.3 makes a platform a
synthetic `platform.<name>` module whose functions all return `IO`; §8.11.3
orders the DLL search. `spec/10-io.md` §10.9 restricts the declaration to the
entry module and §10.10 states the C calling convention. ADTs cross as heap base
pointers under the consuming convention; this contract decides only *where an
ADT's shape is declared* — an ordinary module, never the DLL (§5.4).

## 3a. Application: the web-server platform

`exemplar/platforms/web/` is the first production platform to marshal
application ADTs. It applies this model without extending it.

- **Model A — cranelisp owns the serve loop.** The platform supplies leaf
  effects (`bind-listener`, `accept-conn`, `read-conn`, `send-conn`); the accept
  → handle → send → recur loop is tail-recursive cranelisp. The leaves are
  poll-shaped (§6.8), so the loop is also the seed for concurrent serving.
- **Model B — a platform-owned loop calling back into a cranelisp handler — is
  retired by design.** The platform-effect boundary is poll-in / wake-out only:
  no closure crosses it, `HostCallbacks` gains no closure-invocation entry, and
  no `CLClosure`/`CLFn` wrapper exists. The ruling and its grounds are in
  [effect concurrency](effect-concurrency.md) §12.1. An uninvertible synchronous
  C dispatcher is handled inside the platform, in Rust, exposing only a
  poll-shaped effect.
- **Platforms do not declare ADTs.** `Listener`, `Connection`, `Request` and
  `Response` are ordinary types in `exemplar/web.cl`, referenced from the
  signatures as `web/Request` and so on. The DLL reads fields by name against
  the embedded schema and constructs values through
  `HostCallbacks::alloc_with_tag` (§5.5). Request accessors are ordinary
  cranelisp field access, not platform functions.
- **Hand-rolled HTTP/1.0 over `std::net`, no external crate.** A showcase
  platform stays legible and dependency-light
  ([Principle 6](principles/06-complexity-has-a-budget.md)).
- **Integration is the ordinary path.** The crate is a workspace member building
  both artifacts; `web.cl` resolves by ordinary module resolution; the e2e link
  prerequisites build it alongside the other platforms.

## 4. The platform-author experience

The author guide is [Writing platforms](../../user/guide/writing-platforms.md).
The boundary fixes the following.

- **Effect functions** are `extern "C"` Rust functions over the `CL*` wrapper
  family, defined outside the macro. ADT fields are read **by name**
  (`r.read_field("w")`), never by hard-coded offset.
- **`declare_platform!`** is invoked once per DLL. It names the platform, lists
  the effects in slot order with fully-qualified signatures, a docstring,
  parameter names and a concurrency key (§6.8.0), and — for a platform that
  marshals ADTs — embeds the generated schema with
  `schema: include_str!("<name>.platform-schema")`. There is no schema
  declaration dialect: the embedded file is machine-written and never
  hand-edited. The macro's keys are documented on
  `crates/cranelisp-platform/src/declare.rs::declare_platform`.
- **The platform's types are an ordinary `.cl` module** (§5.4), for example
  `platforms/shapes/` with `(deftype Rectangle [:Int w :Int h])` in `shapes.cl`.
- **The generate cycle** is *write signatures → build → load in the REPL →
  `/platform-schema <name>` → save the printed text as the embed file → rebuild*
  (§7.2a). It re-runs whenever a signature or a reachable `deftype` changes
  shape.
- **The REPL is the regeneration bootstrap.** Regeneration requires loading the
  platform, and the first build necessarily carries an absent or stale schema.
  So on a hash mismatch the REPL warns and loads, while `--run` and `--link`
  refuse (§5.5.4). This is the single deliberate mode asymmetry in the contract.

## 5. The language / ABI constructs

### 5.1 The exported GOT — the DLL's facts

- **Symbol and shape.** `__cranelisp_got_platform_<name>` is a static
  `[AtomicPtr<u8>; GOT_TABLE_SIZE]` in a writable data section, modelled on the
  primitives GOT (`__cranelisp_got_primitives`).
- **Manifest order is GOT slot order.** The macro emits the GOT population and
  the manifest from one declaration list, so slot *i* and manifest entry *i* are
  the same function by construction. The host adopts `got_slot = manifest index`;
  it allocates no slots for a platform module. Guarded by the macro's
  order test in `crates/cranelisp-platform/src/declare.rs`.
- **Population.** The static starts null. The manifest entry point stores each
  function pointer into its slot, so **the GOT is valid only after the manifest
  entry point has run** — at load in a live session, and from the startup stub
  in a linked executable (§7.3). A const-initialised array whose entries are
  linker relocations was the originally preferred form and is not built; it
  would change no symbol and no consumer, and is not owed.
- **The host wraps; it never copies.** A live session builds the platform
  module's `GotTable` over the exported address with
  `crates/cranelisp-types/src/got.rs::with_static_backing`. The exported table is
  the only function-pointer table ([bounded contexts](bounded-contexts.md) §5
  invariant 1). Writability is required because the `(trace …)` GOT swap reaches
  platform slots like any other slot.

### 5.2 The manifest

`PlatformManifest` and `PlatformFn` are `#[repr(C)]` layout contracts governed by
`ABI_VERSION`; rustdoc owns their exact fields.

- The manifest carries the facts the host cannot derive: ABI version, platform
  name and version, and per effect its cranelisp name, type-erased function
  pointer, optional poll-state teardown hook, parameter count, signature text,
  docstring, parameter names and concurrency descriptor (§6.8.0).
- **No exported function names.** Dispatch is slot-indexed, so an effect needs no
  linker-visible name; there is no per-function mangled name in the manifest.
- **No schema field.** Neither the schema text nor the layout hash is a manifest
  field. The schema is embedded in the DLL and read DLL-side; the hash is its own
  data symbol (§5.5.4).

### 5.3 The symbol table the host builds

Per effect, the host inserts one definition into the `platform.<name>` module
(`src/platform.rs::register_platform_in_tc`):

| Field | Source |
|---|---|
| Name | The manifest's cranelisp name. |
| Scheme | The signature text, parsed and checked with **fully-qualified leaf references** (`primitives/Int`, `shapes/Rectangle`). A bare lowercase leaf is a type variable and is refused; every effect must return `IO`. |
| Origin | `CallableOrigin::PlatformEffect` carrying the scheduling class and poll shape derived from the concurrency descriptor. |
| GOT slot | The manifest index (§5.1). |
| Docstring, parameter names | Manifest metadata for REPL introspection. |
| Visibility | Public — a host invariant. |

- **No imports are injected into the platform module.** Signatures are
  fully qualified precisely so that resolution needs no injected scope.
- Everything else — sequence numbering, mount order, the GOT wrapper — is a host
  invariant.
- **The session retains the DLL handle for its lifetime** (`SharedState`'s
  retained-DLL pool in `src/session_v4/lifecycle.rs`). No DLL unloads
  mid-session, which keeps slot pointers valid.

### 5.4 ADTs are ordinary modules

- A platform's data types are ordinary `.cl` modules compiled through the normal
  pipeline. They land as ordinary type and constructor entries; a program builds
  and matches them like any user ADT. The platform declares nothing about them.
- **Discovery is ordinary module resolution** (`src/pipeline.rs::resolve_module_file`,
  `spec/08-modules.md` §8.11). There is no platform-specific discovery or
  `platform.<name>.*` mounting for type modules. The accepted cost is that the
  binary and its type module are not automatically co-located; the layout hash
  exists to catch exactly that deployment drift (§5.5.4).
- **Load-ordering invariant.** A type module is in the symbol tables before any
  signature naming it is checked. The loader drives each referenced module as a
  dependency first (§7.2).
- **Two-module rule.** Because the type module is checked before the platform
  registers, it must not import that platform. Wrappers that call the platform's
  effects live in a different module
  ([poll-leaf authoring](../platform/poll-leaf-authoring.md) §6).

### 5.5 The field-by-name design — compiler-generated schema, bound by hash

Putting the `deftype` outside the DLL leaves the DLL's Rust code with no
compile-time view of the layout. The resolution:

> **Layout truth lives in the resolved module graph. The compiler reads it,
> closes over nested types and writes the schema as a build artifact. The
> platform embeds the artifact; a layout hash binds it to the live tables.**

Rejected alternatives, and why they stay rejected:

- *A hand-authored DLL-side schema dialect* — a second, weaker type system that
  cannot compose with constructors, `match` or traits
  ([Principle 7](principles/07-single-source-of-truth.md)).
- *Embedding the `.cl` source* — `include_str!` captures lexical file content,
  but layout is whatever the resolved graph produces. The two diverge as soon as
  a type module imports or re-exports an ADT. It would also need the DLL and the
  host to agree on a canonical form without the platform crate depending on the
  frontend.
- *The host as a layout oracle* (a field-index callback plus a baked link-time
  blob) — two new channels to avoid embedding one text file.
- *Build-script-generated Rust bindings* — a second maintained copy of the
  layout, creating the drift it polices.
- *A schema pointer in the manifest, or a host schema-validation callback* —
  there is no DLL-authored schema to carry or validate.

#### 5.5.1 The `/platform-schema <name>` command

A REPL introspection-family command over a **loaded** platform
(`src/repl/commands.rs::handle_platform_schema`). It:

1. **derives the root set** — every ADT named in a platform effect's scheme;
2. **takes the transitive closure** over constructor field types — nested ADTs
   join, scalar leaves terminate;
3. **prints the schema text** with a `;; layout-hash:` header line.

`/platform-schema` is the only producer and the platform build the only
consumer. The platform crate's parser reads the artifact DLL-side for the field
name → offset map. That parser **replicates** the small grammar instead of
depending on the frontend, which would invert the dependency direction
([Principle 3](principles/03-dependency-flows-toward-stability.md)).

#### 5.5.2 The schema shape

```
Map<FQTypeName, Vec<(CtorName, tag, Vec<(Symbol, FieldType)>)>>

FieldType ::= Scalar(FQTypeName)              ; primitives/Int, primitives/String, …
            | Adt(FQTypeName, Vec<FieldType>) ; geometry/Point, (Option shapes/Rectangle)
            | Vec(FieldType)                   ; (Vec primitives/Int)
```

- Each type maps to its constructor list; a constructor carries its name, heap
  tag and ordered **named, typed** fields. A product is the one-constructor
  case; an enum's constructors have no fields.
- **Typed fields make nesting work.** Reading field `origin` of a `Rectangle`
  yields the field type `geometry/Point`, which is looked up in the same map.

#### 5.5.3 Concrete instantiations — keys are structured type expressions

Platform signatures are monomorphic, so the generator emits concrete
instantiations with type arguments substituted. **The map key is the structured
type expression itself** — `(Option shapes/Rectangle)` — never a human-readable
mangle. The key is machine-written and machine-read; no person pastes it.

#### 5.5.4 The layout hash — bind the artifact to the live tables

- **What is hashed.** The canonical text of the whole generated schema: one hash
  per platform. It is comment- and whitespace-insensitive by construction
  because the generator emits canonical text.
- **Where it is carried.** As the artifact's `;; layout-hash:` header and as the
  data symbol `__cranelisp_layout_hash_<name>`, extracted from the header at
  platform compile time. An absent or headerless artifact yields an empty hash,
  which is how a first build is tolerated. A platform without a `schema:` arm
  exports no hash and is not gated.
- **One generator, one hash routine, both in the compiler.** The host
  regenerates the schema from its live tables and hashes that
  (`crates/cranelisp-backend/src/schema.rs::compute_layout_hash`). The DLL's
  hash was produced by the same code at `/platform-schema` time, so agreement on
  canonical form holds by construction and the platform crate carries no
  canonicaliser.
- **The gates.**
  - *Session load* (`src/process_form/platform.rs::layout_hash_gate`): after the
    type modules and signatures are registered, regenerate, hash and compare
    with the DLL's symbol. The REPL warns and loads (§4); every other run mode
    refuses with `PlatformError::LayoutHashMismatch`, naming the platform, both
    hashes and the regenerate-and-rebuild guidance. `--link` loads the cdylib
    through this gate during compilation.
  - *Linked executable start.* The compiler bakes its regenerated hash into the
    startup object; the stub compares it with the statically linked symbol
    before `main` and aborts with the same guidance
    (`crates/cranelisp-intrinsics/src/layout.rs::cranelisp_check_layout_hash`).
    This binds the **rlib**, which the load gate never sees. A stale rlib
    therefore *builds* and refuses at *run* — the accepted trade against
    teaching the compiler to read symbols out of archives at build time.

#### 5.5.5 Export naming — every per-platform export is name-suffixed

**Invariant.** Every C-ABI symbol a `declare_platform!` invocation exports
carries a `_<name>` suffix, where `<name>` is the **raw `name:` literal
verbatim** — not the hyphen-to-underscore crate form, which is used only for
rlib filenames. The host computes the same names from the platform name, so emit
and consume agree ([Principle 7](principles/07-single-source-of-truth.md)).

| Symbol | Kind | Purpose |
|---|---|---|
| `__cranelisp_got_platform_<name>` | data | The GOT (§5.1). |
| `cranelisp_platform_manifest_<name>` | `extern "C"` function | The manifest entry point (§5.2). |
| `__cranelisp_layout_hash_<name>` | data | The layout hash (§5.5.4); present only with a `schema:` arm. |

- **Why.** Several platforms force-link into one executable; an un-suffixed
  export is a duplicate definition at link.
- **The manifest name has one source of truth:**
  `crates/cranelisp-platform/src/lib.rs::platform_manifest_symbol`. The macro
  cannot call a function inside an `export_name` attribute, so it concatenates
  the same literal, and a unit test pins the two equal. Host consume sites call
  the helper and never format the name inline.
- **The host knows the name before it reads the manifest.** It comes from the
  `(platform name)` declaration, which is also the DLL lookup key.
- The GOT and hash names are formatted inline on both sides (§2.1).

---

## 6. The implementation — mapped onto crates

### 6.0 The schema generator and the `/platform-schema` command — placement

- **The command is binary/REPL dispatch.** It looks up the loaded platform's
  table, calls the generator and prints the text.
- **The generator lives in `cranelisp-backend`**
  (`crates/cranelisp-backend/src/schema.rs`), for two reasons: the closure walk
  with concrete-instantiation substitution is the walk the trace
  display-descriptor baker already needs ([tracing](tracing.md)), and the
  link-time hash computation runs where no REPL exists, so the generator cannot
  be a REPL-only module. Backend already depends on the
  types crate, so no dependency edge is added.
- **One generator, three callers:** the command, the session-load gate and the
  link-time hash bake.
- **Share the walk, not the serialisation.** The schema module is the single
  home of the substitution primitives; the trace baker consumes them. The baker
  emits a program-lifetime binary descriptor and the generator emits
  build-artifact text. Forcing one output format on consumers with different
  lifetimes would over-couple them
  ([Principle 6](principles/06-complexity-has-a-budget.md)).

### 6.1 Platform crate (`cranelisp-platform`)

`declare_platform!` emits the three exports (§5.5.5) and, inside the manifest
entry point: initialises the host context from the supplied `HostCallbacks`,
parses and installs the embedded schema when present, populates the GOT (§5.1)
and returns the manifest. The schema parser and name-based `CLAdt::read_field`
are this crate's; construction goes through the host allocator (§6.6). Interior:
[platform design](../platform/platform.md).

### 6.2 Backend (`cranelisp-backend`)

Backend does not emit the platform's GOT — the DLL exports it. A call to a
platform effect emits **GOT-indirect dispatch** against
`__cranelisp_got_platform_<name>` at the entry's slot, imported as a data symbol
and resolved by `dlsym` (JIT) or the linker (`--link`)
(`crates/cranelisp-backend/src/compiler/apply.rs`). This is structurally the
dispatch used for a user-module function. Backend also owns the schema generator
(§6.0), the effect-name stamp ([bounded contexts](bounded-contexts.md) §5
invariant 9) and poll-node construction (§6.8).

### 6.3 Why platform dispatch is GOT-indirect

Direct imports of per-function exported names were rejected as the dispatch
mechanism for three reasons, which are why they must not return:

1. **No GOT swap.** A direct call is fixed at link and cannot take part in the
   `(trace …)` copy-swap.
2. **Two dispatch paths for one concept.** Platform effects would dispatch by
   name while user, stdlib and primitive functions dispatch by slot
   ([Principle 7](principles/07-single-source-of-truth.md),
   [Principle 11](principles/11-single-pipeline-mode-parameters.md)).
3. **A flat-namespace hazard.** Exported effect names squat in the runtime's
   `cranelisp_*` prefix, collide between platforms at link, and require a
   hand-kept agreement between an attribute and a manifest string that a live
   session never exercises — so a typo surfaces only under `--link`.

Slot-indexed dispatch through a per-platform-named GOT removes all three, in all
three run modes.

### 6.4 Binary (`src/`) — load path

The platform load path belongs to the binary
(`src/process_form/platform.rs`, `src/platform.rs`); its interior is
[integration design](../int/int.md). The boundary obligations, in order:

1. Resolve the DLL by the specified search order; open it; call the namespaced
   manifest entry point with the single host-callbacks value; refuse an
   `ABI_VERSION` mismatch; lift the manifest into owned descriptors.
2. Drive every type module a signature references as an ordinary dependency
   before any signature is checked (§5.4).
3. Wrap the exported GOT in place and build the symbol table (§5.3).
4. Apply the layout-hash gate (§5.5.4).
5. Retain the DLL handle for the session.

A cache hit re-runs this same path for each persisted platform declaration; a
load failure is a cache miss.

### 6.5 Cache

A platform adds nothing to the persisted module metadata. Its types cache as
ordinary modules, there is no schema literal to round-trip, and function
pointers are re-established by re-running the load path (§6.4). The cache
version history in `crates/cranelisp-backend/src/cache/mod.rs` records the
removed field.

### 6.6 Host callbacks and retired surface

- **`HostCallbacks` is permanently the two allocator entries**, `alloc` and
  `alloc_with_tag`, built for every host mode by
  `crates/cranelisp-intrinsics/src/lib.rs::host_callbacks`. `alloc_with_tag`
  stays because constructing an ADT across the boundary needs the host
  allocator; it is orthogonal to the schema. New capability rides exported
  symbols, so the struct does not grow; layout changes bump `ABI_VERSION`
  freely, with no reserved-slot hedging.
- **Retired, and not to be reintroduced:** the schema declaration dialect with
  its DLL-side marker and lookup plumbing; the host schema-validation callback
  (superseded by the layout-hash gate); per-function exported names and
  name-registered JIT symbols; injected imports in the platform module; a schema
  literal in the cache; a per-type `/abi` emitter and mangled instantiation
  names (subsumed by `/platform-schema` and structured keys).

### 6.7 Per-platform export namespacing (DEF-5)

Two force-linked platforms each defining a bare manifest symbol failed to link
with a duplicate definition. The manifest entry point therefore follows the
invariant the other two exports already followed (§5.5.5). This is naming only:
manifest content, the schema and the three-exports model are unchanged. Emit and
consume flip together, so an export rename is one atomic change across the
platform crate, the binary and every platform rebuild, with an `ABI_VERSION`
bump. The binary's startup emission is naming-agnostic: it imports the names
`src/exe.rs::collect_platform_manifest_names` derives from the platform names
through the shared helper.

### 6.8 The async-leaf ABI

[Effect concurrency](effect-concurrency.md) §12–§13 changes the *effect-call
shape*: a platform effect is either a blocking `extern "C"` function or a
poll-shaped async leaf driven by the host reactor. The three-exports model, the
two artifacts, GOT-indirect dispatch and export namespacing carry over
unchanged. §6.8.0 states the single platform ABI, §6.8.0a the single trampoline
with its always-present reactor, and §6.8.0b the `ctx` vtable handle model. The
reactor substrate and its placement in `cranelisp-intrinsics` are in effect
concurrency Appendix B; the interior is
[reactor design](../intrinsics/reactor.md).

#### 6.8.0 One platform ABI

User direction (2026-06-29): there are no external users, so there is one ABI
and no backward-compatible second channel.

- **One manifest type, one macro, one GOT export, one loader path.** Each effect
  is independently blocking or poll-shaped through its `ConcurrencyDescriptor`:
  `blocking == 1` is a blocking `CLIO`-returning function, `blocking == 0` a
  `PollFn`. One manifest may mix both, as `stdio` does.
- **Dispatch is shape-agnostic.** The slot holds a type-erased pointer; backend
  reads the origin's poll shape to decide which IO node to build. The host
  derives both the scheduling class and the poll shape from the descriptor.
- **Per-effect concurrency key.** The author writes either `scheduling:` — sugar
  that lowers to a blocking descriptor — or `descriptor:` for a poll-shaped
  leaf, with an optional `drop_state:` teardown hook. This is a per-function
  choice inside one macro, not two macros.
- **The ABI types are core and ungated.** `ConcurrencyDescriptor`, `Poll`,
  `PollFn`, `HostCtx`, `Waker` and `WakerVTable` are present in every build; no
  cargo feature selects them.
- The linked startup stub is unaffected in shape: it calls each namespaced
  manifest entry point for its initialisation effect.

#### 6.8.0a Single trampoline, always-present reactor

**The obligation is the collapse, not the construction timing.** One ABI, one
async trampoline and no feature split are the user-directed end-state (S96), and
they hold in source: the IO drive has one async body, and `mio`, `futures` and
`rayon` are plain `cranelisp-intrinsics` dependencies. There is no non-reactor
build, so a poll-shaped effect always works and no "rebuild with the runtime
feature" error arm exists. Carrying two `#[cfg]`-selected trampolines would have
been an interim
([Principle 8](principles/08-no-interim-implementations.md)). When the
`mio::Poll` is built is a performance position inside that end-state.
[Effect concurrency](effect-concurrency.md) §6 owns the statement of what a
program without concurrent effects pays; this section records the platform-ABI
consequence and defers to it.

**Delivered form: eager-cheap.** Each top-level drive constructs its reactor
first — `block_on_reactor_capped` calls `Reactor::new()` as its first statement
— building one `mio::Poll` and one bridge waker. The executor drives the top future
on the **calling thread**; there is no dedicated reactor thread, and only
`rayon::spawn` uses other threads. A pure-blocking program therefore pays two
syscalls and two descriptors per top-level drive, spawns no thread and never
turns the reactor. Eager-cheap is a permanently valid behaviour, **not a
correctness interim**, and it is the conservative side: it carries no lost-wake
obligation.

**What the source establishes** (`crates/cranelisp-intrinsics/src/io.rs`,
`crates/cranelisp-intrinsics/src/reactor.rs`):

1. **A pure-blocking tree completes with no reactor activity.** The async
   stepper forces blocking effect thunks synchronously and walks `Pure`/`Bind`
   purely. Only a poll effect that would block, a `Par` rayon bridge or a
   capacity park returns `Pending`. For a pure-blocking tree the first poll
   returns `Ready` and the drive returns before any turn. This no-turn property
   follows from the drive loop's order; no executing check measures it
   (effect concurrency §6 names its falsifier).
2. **The sequential blocking path needs no reactor.** A blocking effect runs
   inline. Only a `Par` with a blocking branch spawns rayon, and it is woken
   back through the bridge waker. The synchronous per-branch driver
   `run_io_trampoline` is retained as the rayon-worker run-to-completion body.
3. **A linked executable runs the same always-linked reactor.** The reactor's
   `HostCtx` is built at one site inside intrinsics, separate from
   `HostCallbacks` (§6.6). Reactor construction therefore has one site and
   cannot diverge between modes.

**Lazy construction is a workload-triggered refinement, not delivered and not
owed.** Deferring the `Poll` and bridge waker to the first `Pending` would save
the two syscalls per drive. No lazy path and no construction counter exist in
source.

- *Trigger:* a measured per-drive construction cost that matters to a delivered
  workload.
- *Wake condition:* **every** source of `Pending` must force construction, on
  the calling thread, before it parks. That set is fd registration
  (`register_fd`), timer registration (`register_timer`), the `Par` blocking
  bridge (before `rayon::spawn`), and the capacity park. The capacity park is
  the case a happens-before argument over registrations alone omits: a
  permit-release wake of a parked acquire travels through the executor waker to
  the bridge `mio::Waker`, so a lazy form that leaves that path unforced can
  lose a wake.
- *Unchanged by it:* the ABI, the single trampoline, the feature set and binary
  size. The refinement's interior belongs to `design` for intrinsics
  ([reactor design](../intrinsics/reactor.md) §5); `qa` allocates its evidence
  if and when the trigger fires.

**Evidence position.** The one-ABI / one-trampoline obligation is structural:
the features and a second drive arm do not exist to select, and the default test
lane drives the reactor. The existing reactor and `Par`-overlap e2e rows
exercise the eager reactor. A "pure-blocking program constructs no `Poll`"
assertion was proposed with the lazy form and never built; it is not delivered
evidence and is not owed while construction is eager.

**Public surface.** The reactor and strand modules are crate-private to
intrinsics; the cutover adds no reactor item to any public-API baseline.

**Launch-and-continue, supervision, backpressure, cancellation and the
combinators** build on the single async trampoline. Construction timing is not
part of their substrate.

#### 6.8.0b The `ctx` vtable handle model

The canonical model is [effect concurrency](effect-concurrency.md) §4.1.1; this
section is its ABI projection.

**Scheduling state never rides on user values.** It flows through a
trampoline-owned `ctx` vtable that the platform's poll functions call.

- **Resource handles are tramp-opaque, user-readable ADTs.** A handle such as
  `web/Connection` carries the platform's descriptor in an ordinary field. The
  trampoline never inspects it; the program may destructure it; only the
  platform interprets it. It is not a hidden header slot and not a sealed value,
  so `CLAdt::construct` mints a normal object.
- **Why.** Stamping a per-value descriptor into a header slot failed
  structurally: a handle minted inside the DLL had no room for the slot, and
  reserving it would have been an undesigned cross-crate allocation interface.
  Keeping scheduling off values removes the slot altogether.
- **The poll-function skeleton is uniform:**
  `acquire(token, capacity, waker)` → syscall → *would block?* register the
  waker and return `Pending` : return `Ready`. A commutative leaf omits
  `acquire`. Leaf signatures carry no token or capacity parameters.
- **The token is a platform-computed projection of the handle** — by default the
  descriptor, split per direction for full duplex, `0` for commutative. The
  manifest imposes no shared-token constraint between distinct effects.
- **The manifest carries compile-time facts; the vtable carries all runtime
  scheduling.** `ConcurrencyDescriptor.role` (`ResourceRole`) grounds inference
  and documents the leaf. The trampoline never branches on it at runtime.
- **A singleton resource** such as stdin declares a manifest-static serial
  token; its poll function acquires that constant, so it is single-in-flight by
  construction.

**`HostCtx`** carries `register_readable`, `register_writable`,
`register_timer`, `acquire`, `retire` and the opaque `host` pointer. `acquire`
returns `Acquire` (`Acquired` or `Parked`). `PollFn` takes the state, the
`HostCtx` and the `Waker` and returns `Poll`; it has no descriptor out-parameter.

| Operation | Caller | When |
|---|---|---|
| `acquire(token, capacity, waker)` | platform poll function | Start of each poll, when the token is non-zero. |
| `register_readable` / `register_writable` / `register_timer` | platform poll function | On would-block. |
| `retire(token)` | a retire leaf such as `close` | After closing the resource. |
| **release** of the permit | **host trampoline** | On the effect's `Ready`, or on cancel or drop. |

- **`acquire` takes the waker.** On `Parked` the host queues it on the token's
  permit-wait queue and the strand suspends. The reactor thread never blocks in
  `acquire`; a permit is a counter, so parking cannot deadlock.
- **`acquire` is idempotent per in-flight effect** — the host keys held permits
  by the effect's identity, so a re-poll does not double-count.
- **There is no `release` entry.** Release is trampoline-owned, and cancellation
  never re-enters the poll function.
- **`retire` is idempotent.** A double close, or a close while waiters are
  parked, retires once and wakes the waiters to observe the closed resource
  through their own failing syscall. There is no drain barrier.
- **Forward axis.** Degree and backpressure ride the reserved
  `ConcurrencyDescriptor.global_budget`; they need no reshape of this model.

The backend poll node is uniform and the host implements the vtable's permit
map; those interiors are [IO trampoline design](../backend/io-trampoline.md) and
[reactor design](../intrinsics/reactor.md).

---

## 7. Data structures, functions and sequence

### 7.1 Shapes

```
__cranelisp_got_platform_<name>    : [AtomicPtr<u8>; GOT_TABLE_SIZE]
                                   ; exported by the DLL; slot i = manifest.functions[i]
                                   ; populated by the manifest entry point (§5.1)

cranelisp_platform_manifest_<name> : extern "C" fn(*const HostCallbacks) -> PlatformManifest
                                   ; initialises the host context, installs the schema,
                                   ; populates the GOT, returns the manifest

__cranelisp_layout_hash_<name>     : the layout hash of the embedded schema (§5.5.4)
                                   ; present only with a schema: arm

embedded schema artifact           : not a link symbol — /platform-schema text baked into
                                   ; the DLL and parsed DLL-side for read_field (§5.5.2)
```

`PlatformManifest`, `PlatformFn`, `HostCallbacks`, `HostCtx` and
`ConcurrencyDescriptor` are stated field-by-field in rustdoc only.

### 7.2 REPL / `--run` load sequence

```
(platform <name>) in the entry module
  → resolve the DLL by the specified search order; dlopen
  → call cranelisp_platform_manifest_<name>(host_callbacks)
        ; DLL side: init host context, install schema, populate GOT
  → refuse an ABI_VERSION mismatch
  → manifest → owned descriptors
  → dlsym the GOT base and, if present, the layout hash
  → for each type module a signature references, not yet loaded:
        drive it as an ordinary dependency; block and retry from the top
  → ensure module platform.<name>; wrap the GOT in place (no copy)
  → for i, descriptor:
        scheme = check(parse(descriptor.type_sig))     ; FQ leaves; must return IO
        insert Def { scheme, PlatformEffect{class, poll_shape}, got_slot = i, metadata }
  → layout-hash gate (§5.5.4): REPL warns and loads; otherwise refuse
  → retain the DLL handle for the session
  ; call sites dispatch GOT-indirect at got_slot
```

### 7.2a The schema generate cycle (`/platform-schema`)

```
author: FQ signatures in declare_platform! + the .cl type module(s)
  → build the platform           ; embedded schema absent or stale — tolerated
  → REPL: load the platform      ; hash mismatch → warn and load
  → /platform-schema <name>
        roots   = ADTs named in platform-effect schemes
        closure = transitive walk over field types
        entries = key (FQ name | structured type expression) → [(ctor, tag, [(field, type)])]
        print   ";; layout-hash: <hash>" + canonical schema text
  → save the text as <name>.platform-schema; rebuild the platform
  → --run and --link now accept
```

### 7.3 `--link` sequence

```
compile: the session loads the platform's cdylib exactly as §7.2 (non-REPL gate:
         refuse on mismatch) and emits GOT-indirect dispatch against
         __cranelisp_got_platform_<name>, imported as a data symbol.
         Type modules compile like any source.
         Per platform that exports a hash: regenerate + hash from the compiled
         tables and bake the expected hash into the startup object.
link:    ld resolves the GOT, manifest and hash symbols against the force-linked
         platform rlib. No name-registered symbols, no symbol table.
start:   for each platform, the stub calls its manifest entry point through
         cranelisp_init_platform — installing the host callbacks and the schema and
         populating the GOT — then compares each baked hash with the linked symbol
         and aborts with rebuild guidance on mismatch; then runs main.
```
