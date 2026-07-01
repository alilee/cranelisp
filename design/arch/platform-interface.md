# Platform interface — how a DLL exposes itself to the host (GOT export + ADTs-in-modules)

**Status.** Subsystem design. The S-PLAT-1 / FIXME 0282 resolution, re-scoped by
the user's **third convergence (2026-06-07)** — the field-by-name access problem is now
settled by a **compiler-generated schema**: a `/platform-schema <name>` REPL command
derives the referenced-type set from the loaded platform's symbol table, takes the
transitive closure over field types, and emits a machine-written build artifact the
platform embeds; a `layout-hash` header binds it to the live tables at load and link.
This **replaces** the second convergence's embed-the-`.cl` (`include_str!`) design — the
schema is a *build artifact* now, never hand-authored, and layout truth is read from the
**resolved module graph**, not from lexical file content (the `include_str!` form breaks
when the type module imports/re-exports its ADTs — brittle; §8). Companion to
`design/platform/host-wiring-s76.md` (the seam map this supersedes for the schema seam),
`crates/cranelisp-platform/src/lib.rs` (the landed S71 boundary), and
`cranelisp-primitives::PRIMITIVES_GOT_SLAB` (the FIXME-0280 precedent this design
generalises). Owner `/arch`.

**USER-RATIFIED 2026-06-07 — CASCADED into the architecture configuration (S76 /arch).**
The target is set in place in `facades/int.md` (load path + `/platform-schema` command +
injection/`jit_name` retirement) and `bounded-contexts.md` §5 (platform — three exports,
no schema dialect, no exported fn names), §3 (backend — schema generator + GOT-indirect
dispatch + startup hash bake), §6 (int — load path + command), §7 (`SymbolTable.schema_literal`
retires). **Implementation status (updated S79 /arch Phase-2, 2026-06-12):** the mechanism
LANDED across S76 W4a/W4b — **0286** (platform macro), **0287** (backend generator + dispatch
arm + startup bake), and **0288** (int load path + `/platform-schema` command + hash gate) are
all resolved + deleted; the `PlatformError::LayoutHashMismatch` variant + `schema_literal`
removal (the Decision-0042 / §7 cascade residue) both LANDED — `schema_literal` is gone from
`cranelisp-types` (only a cache version-history changelog comment remains). `ABI_VERSION`
bumped 2→3. **Only `0289` (qa e2e) remains open** — gated on the `shapes` ADT-typed test-DLL
fixture (`/platform`), which does not yet exist; the backend GOT-indirect arm is landed-and-
dormant, activating on `got_slot: Some(_)` when that fixture appears. FIXMEs 0233/0238 are now
STALE (superseded by W4b) → close; 0229's `validate_schema` half retired (`alloc_with_tag` KEEP
landed). Where this
contradicts the as-built S71 boundary, that is the *point* — as-built is marked SUPERSEDED
in the configuration; the contradictions are surfaced in §2 and §8 (superseded options).

---

## 1. Overview

A platform DLL is an out-of-tree Rust crate that ships native effect functions
(`print`, `read-line`, file IO, …) for cranelisp programs to call. **A platform exports
three things, and only three:**

1. **Its GOT** — a function-pointer table, one slot per effect function, in a fixed order.
   This is how a compiled program *calls* a platform function: indirect through the GOT
   slot. The exported link symbol is `__cranelisp_got_platform_<name>`.
2. **Its manifest** — a small block of declarative data describing the platform and each
   of its functions (platform name/version/abi_version, and per function: name, type_sig,
   scheduling class, docstring, param-names). **The manifest is the data a live session
   builds a *symbol table* from when it needs one.** The manifest also names the
   layout-hash export (point 3).
3. **Its schema + layout hash** — a generated description of the data shapes (ADTs) the
   functions marshal across the FFI, plus a hash that binds the description to the live
   type tables. The schema is `/platform-schema`-generated and embedded in the DLL; the
   hash is exported as the data symbol `__cranelisp_layout_hash_<name>` and checked at
   load/link.

**The platform crate builds two artifacts, one per delivery mode** — this is the deployment
model everything below assumes:

- a **cdylib** for live sessions: the REPL/`--run` host `dlopen`s it from
  `CRANELISP_PLATFORM_PATH` at session load and resolves the three exports via `dlsym`;
- an **rlib** for `--link`: the compiler statically links it into the standalone binary
  (`-force_load`, `src/exe.rs:549`) — no dlopen exists anywhere in a linked program; the
  same three exports resolve as ordinary linker symbols. Which platforms are linked is
  decided at compile time by the program's `(platform "…")` declaration.

Same exports, two binders — `dlsym` in sessions, `ld` in `--link` — with no mode fork in
the platform's own code.

The three exports serve different consumers. **`--link` consumes only the GOT** (plus the
layout hash, to refuse a stale platform): a standalone executable has no live session, so
it needs nothing but resolved code pointers. Because the compiler links an rlib rather than
loading a library, the `--link` hash check is **baked into the startup stub**: the compiler
embeds the hash it computed from the live `.cl` modules into the startup object, and the
stub compares it against the statically-linked `__cranelisp_layout_hash_<name>` at process
start, aborting with rebuild guidance on mismatch. (A stale platform therefore *builds* and
refuses at *run* — the accepted trade against teaching the compiler to read symbols out of
rlib archives at build time.) **The REPL and `--run` consume all three:** a live session
typechecks call sites and introspects via `/sig`/`/doc`, so it builds a symbol table from
the manifest; and the host checks the layout hash at `dlopen` time — warning in the REPL
(so `/platform-schema` regeneration is possible), refusing in `--run`.

The whole design turns on one principle the user drew from the just-landed primitives work
(FIXME 0280):

> **The DLL builds the GOT — those are its facts. The host builds the symbol table —
> those are its invariants.**

A DLL knows its own function pointers; the host knows its session invariants (module
mounting, `seq` numbering, the Rust `SymbolTable` representation). So the DLL exports the
GOT and the manifest as C-ABI facts, and the host composes the `SymbolTable` from them.
Note what is deliberately ABSENT here: for a platform module there is **no host
slot-allocation step at all**. For ordinary modules the host assigns `got_slot` on demand
at registration; for a platform module the manifest's array order IS the slot order — the
DLL declares it, the host adopts it (`got_slot = manifest index`), and nothing is ever
allocated or discovered.

### The four things the user asked, answered plainly

**(1) Where does the slot order come from — and how can the GOT be built ahead of it?** *There is one ordering, declared in one place:
the manifest's function array order IS the GOT slot order.* Nobody "discovers" an order.
The `declare_platform!` macro emits both the GOT and the manifest from the same declaration
list, so slot *i* of the GOT and entry *i* of the manifest are the same function by
construction — they cannot disagree. The host does not build the platform's GOT at all (the
DLL exports it); it builds the symbol table, and it assigns `got_slot = manifest index` for
each function. The order is declared by the manifest, adopted by the host. (§5.1, §5.3.)

**(2) Can the GOT be const-initialised, or does it have to be filled with linker fixups?**
*Both statements are true, at different levels — say both.* From the platform author's
(Rust) point of view, the GOT is a const-initialised static array of function pointers:

```rust
static __cranelisp_got_platform_shapes = [rectangle_area as _, /* … */];
```

At the *object* level, the compiler emits each of those entries as a **relocation** that
the linker fixes up at load/link time — the **dynamic loader** for a dylib, the **static
linker** for `--link`. So there is **no runtime population code** either way: the author
writes a const array; the toolchain turns each function-address entry into a fixup that is
resolved before the program runs. This is exactly how `define_module_got_data` populates a
user module's GOT today (per-slot function-address relocations) — the same mechanism, a
different emitter. (§5.1.)

**(3) Does the host build the symbol table over the DLL's memory, or does the DLL publish a
data structure the host copies into its own memory?** *Two distinct artifacts — keep them
apart.* The host builds the platform module's **SymbolTable in its own memory, from the
manifest** (name / type_sig / scheduling class / docstring per function). That SymbolTable's
**GotTable wraps the DLL's exported GOT** — it is constructed *over* the dlsym'd GOT address
(`GotTable::with_static_backing`), under the dlopen handle the session already retains.
**There is no copy of the GOT:** the DLL's exported GOT is the one and only function-pointer
table; the host's GotTable is a wrapper around it (BC §3 invariant 3 — the GOT is the single
source of truth for callable addresses). `--link` needs no SymbolTable at all — only the
GOT, resolved by the linker. (§5.3, §7.2.)

**(4) Naming.** This document calls the function-pointer table a **GOT** — not a "slab".
The exported symbol stays `__cranelisp_got_platform_<name>`; prose says "the platform's
GOT". It calls the declarative function data the **manifest** — "the data the host builds a
symbol table from when it needs one". The generated type-layout artifact is the **schema**
(unchanged from the third convergence). (Naming reset 2026-06-07, fourth convergence.)

### What this collapses (relative to today's as-built)

1. The platform fn pointer no longer reaches the host via `JITBuilder::symbol(jit_name,
   ptr)` registration + direct `Linkage::Import` dispatch (§9 archaeology). It reaches the
   host as a slot in the exported GOT; dispatch becomes GOT-indirect against
   `__cranelisp_got_platform_<name>`, structurally identical to every user/stdlib module
   and to primitives. This **closes a latent `--link` correctness gap** (§6 verdict).
2. **Platforms stop declaring ADTs.** The `schema:` DSL *declaration arm*, the DLL-local
   `LazyLock<Schema>`-as-DSL, and the host-side `validate_schema` channel **retire**. A
   platform's data types become **ordinary `.cl` source modules** compiled through the
   normal pipeline; the platform's fn signatures reference them by name. This is the user's
   sharpening: *"the platform doesn't declare ADTs — they live in associated cranelisp
   modules."* The schema does **not** vanish — it changes role: it becomes a
   **machine-written build artifact**, compiler-generated by `/platform-schema` and embedded
   by the platform build, never hand-authored (§5.5).
3. The manifest shrinks to the **facts the host cannot derive**: ABI version, name, version,
   and per-fn (name, type_sig, scheduling_class, docstring, param-names). The answer to the
   user's symbol-table-content question (§2, §5) is essentially **yes** — that manifest data
   plus host-derived invariants is the whole SymbolTable. The sigs are written
   **fully-qualified** (`(Fn [primitives/Int] shapes/Rectangle)`); no imports are injected
   into the platform module (the bare-name primitives injection introduced this sprint
   **retires** — §2 q-sig-ref-style).

The center of gravity: **new platform capabilities ride exported link symbols, not struct
growth.** The exported GOT and the layout-hash symbol are the future-proof channels — a DLL
adds a function by adding a slot and a manifest entry; it never grows the `#[repr(C)]`
manifest *struct* to expose a new capability.

### The field-by-name solution — compiler-generated schema (third convergence)

The hard problem this document orbits is: putting the platform's `deftype` **outside** the
DLL (ruling (c)) leaves the DLL's Rust code (`r.read_field("w")`) with no compile-time view
of the layout. The **third convergence** solves it with a compiler-generated schema, not a
hand-maintained one:

> **The layout truth lives in the RESOLVED module graph. A compiler command reads it,
> closes over nested types, and writes the schema as a build artifact. The platform
> embeds the artifact; a layout hash binds it to the live tables.**

The flow: the author writes `declare_platform!` with fully-qualified sigs and builds the DLL
(the schema may be absent or stale at first build). They load the platform in a REPL
session — the referenced `.cl` type modules resolve through ordinary module resolution
(ruling (c)). They run **`/platform-schema <name>`**, a sibling of the introspection command
family (`/sig`, `/doc`, `/info`, …): it derives the referenced-type set from the loaded
platform's symbol table (the `PlatformEffect` sig schemes), takes the **transitive closure**
over field types (nested ADTs in; scalar leaves out), and emits the schema as **text** with
a `;; layout-hash:` header. The platform build embeds that text; the macro's field-access
codegen reads it (a genuinely verbatim read of the generated dialect — no re-grammar). At
load the host **recomputes the hash** from the live tables and compares: `--run`/`--link`
**refuse** on mismatch (hard error, both hashes + "run /platform-schema and rebuild"
guidance); the **REPL warns and loads** anyway — that is the bootstrap, the only place the
schema can be regenerated.

Why this beats embedding the `.cl` text (the second convergence's `include_str!`):
`include_str!` captures **lexical file content**, but the layout the host actually uses is
whatever the **resolved module graph** produces — which diverges from the file the moment
the type module imports or re-exports its ADTs from elsewhere. Reading the symbol table
makes the schema track the same truth the typechecker and codegen track (Principle 7 —
single source of truth). And one generator + one checker, both in the compiler, dissolves
the second convergence's canonical-form/DAG tangle entirely (§5.5, §8).

### Document map

| Section | Contents |
|---|---|
| §1 Overview | The three things a platform exports (GOT / manifest / schema+layout-hash) and their consumers (`--link` = GOT only; REPL/`--run` = all three); **the four plain answers** (ordering, const-init-vs-relocations, wrap-not-copy, naming); the DLL-builds-GOT / host-builds-table split; what this collapses; **the field-by-name solution — compiler-generated schema (third convergence)**. |
| §2 Open questions | All earlier-convergence questions ruled. Near-empty: pending the user's read of this convergence; any genuine residue (sum-type tag stability across regenerations; the schema text grammar) listed. |
| §3 The requirement | GOT-only for `--link`; GOT + SymbolTable for REPL/`--run`; why a DLL-built/serialized SymbolTable was rejected; the spec promises. |
| §4 The platform-author experience | What a DLL author writes + the showcase **walkthrough around the `/platform-schema` flow**: write FQ sigs → build → load → `/platform-schema` → embed → rebuild; the stale-hash REPL warning text. |
| §5 The language/ABI constructs | The exported GOT symbol; the shrunk manifest; the SymbolTable the host builds (FQ sigs, no injection); ADTs-as-modules; **§5.5 the field-by-name design** (the `/platform-schema` command, the `Map<FQTypeName, Vec<(CtorName, tag, Vec<(Symbol, FieldType)>)>>` shape, `FieldType`, the layout hash, the embedded artifact, the dual gate). |
| §6 The implementation | Mapped onto crates: the command in int/repl dispatch; the generator + closure walk (placement) shared with the trace descriptor baker; the platform-crate macro embed arm; the load-time hash check; the `--link` check; HostCallbacks shrink; retirement list. |
| §7 Data structures, functions & sequence | The GOT + manifest shapes; the schema shape; the generate cycle; the load walk with hash check (REPL/`--run`) and the `--link` walk. |
| §8 Appendix: superseded options | FIXME 0282 Options A/B; the schema DSL; the JITBuilder-symbol dispatch path; **the second-convergence embed-the-`.cl` (B′) design + its disproof**; **0234 /abi** (subsumed-not-implemented). |
| §9 Appendix: as-built archaeology | The current platform pipeline, compressed to what informs the design. |
| §10 Change history | Dated evolution of this document. |

---

## 2. Open questions

The first and second convergences left their questions; the **third convergence
(2026-06-07)** rules the last of them (the field-access problem) with the
compiler-generated schema design (§5.5). This section is now **near-empty**: the
substantive direction is settled.

### 2.1 Status

- **None blocking — pending user read of this convergence.** Every design choice is made.
  The document awaits the user's read of the third-convergence solution (§1, §5.5), not a
  pending decision.

### 2.2 Genuine residue (real questions surfaced, not blocking)

Two genuine open mechanism questions remain — narrow, recorded so they are not lost; they
are implementation-detail settlements, not direction changes:

- **q-tag-stability — are sum-type constructor tags stable across schema regenerations?**
  The schema records each constructor's `tag` (the discriminant the heap node carries).
  That tag is assigned by the typechecker/codegen when the `deftype` is compiled. **Open:
  is the tag assignment deterministic across two independent `/platform-schema` runs over
  the same (resolved) `.cl`?** It must be, or a regenerated schema embeds different tags
  than the DLL was built against and the field-access codegen mis-reads. The layout hash
  catches a *change*, but the requirement is that no spurious change occurs from
  re-running the generator over identical source. Almost certainly already true (tag =
  declaration order), but **flag for the implementer to confirm** the assignment is
  source-positional, not allocation-order or hash-map-iteration dependent.

- **q-schema-grammar — the exact textual grammar of the emitted schema.** The schema is
  text (machine-written, machine-read) carrying the `Map<FQTypeName, Vec<(CtorName, tag,
  Vec<(Symbol, FieldType)>)>>` shape plus the `;; layout-hash:` header. **Open: the
  concrete surface grammar** — whether it reuses an S-expression form the existing reader
  already round-trips (preferred — one parser), or a bespoke line format. The design
  requirement is "the retained parser reads it verbatim"; settling *which* dialect the
  generator emits and the parser consumes is a one-decision implementation detail
  (recommend: an S-expr form so the frontend reader is the parser, avoiding a second
  grammar — same instinct that retired the bespoke schema dialect).

### 2.3 Settled rulings (carried from the first/second convergences, 2026-06-07)

- **q-assoc-discovery — RULED (c): plain importable modules.** The platform's associated
  `.cl` modules are **ordinary importable modules**; the platform declares *nothing*
  about them. A program's (and the platform sigs') FQ references auto-load the type
  module via FIXME 0268. The (a) sibling-convention + `platform.<name>.*` mounting is
  **REJECTED** (recorded in §8). **Consequence — where the files live (stated plainly):**
  discovery for the FQ auto-load follows the **ordinary module-file resolution rules**,
  not a platform-specific path. `resolve_module_file` (`src/pipeline.rs:27`) maps a
  dotted module path `a.b.c` → `a/b/c.cl` **relative to the configured roots**: the
  project tree (the entry program's `project_root`) and the `CRANELISP_LIB` search dirs
  (`src/session.rs:218–256`). So a platform-adjacent type module named `shapes` must be
  resolvable as `shapes.cl` somewhere on that ordinary lib/project search — it is **not**
  found on `CRANELISP_PLATFORM_PATH` (that var locates the *dylib*, `src/platform.rs:53`,
  and stays dylib-only). In practice a platform author ships the `.cl` alongside the dylib
  and the deployer places it (or a copy) where the program's module resolution will find
  it — project tree or a `CRANELISP_LIB` dir. **This split — dylib on
  `CRANELISP_PLATFORM_PATH`, types on the ordinary `.cl` search — is the honest cost of
  ruling (c): there is no automatic co-location, and §5.5's layout-hash is exactly what
  catches the deployment-drift case it opens (the dylib built against one `shapes.cl`,
  deployed beside an edited one).** *The load-ordering invariant is unchanged: the type
  module must be in the symbol tables before a sig naming it is parsed; under (c) the FQ
  auto-load (0268) drives that ordering.*

- **q-sig-ref-style — RULED (a): fully-qualified refs; the injection RETIRES.** Sigs are
  written FQ: `(Fn [primitives/Int] shapes/Rectangle)`. The first-convergence
  recommendation (b) (host injects an import) is **OVERRULED**. **The injected primitives
  glob (`inject_primitives_import_for_platform`, `src/platform.rs:325`) is DEAD WRONG and
  RETIRES.** It was introduced only this sprint by the 0233-step-1 fire as a bare-name
  convenience; under (a) the platform module carries **ZERO injected imports**. Sig
  parsing resolves FQ leaf refs directly — `primitives/Int`, `shapes/Rectangle` — with
  the named type modules auto-loaded per 0268 (q-assoc-discovery (c)). The rustdoc on
  `parse_and_check_platform_type_sig` (`src/platform.rs:354–358`) that today *relies on*
  the injection for bare-name resolution is corrected by this ruling: the resolver path
  is FQ-driven, not injection-primed. **Every mention of the injection in this document
  is swept** (the §5.3 module-level rider included).

- **q-drift-mitigation — SETTLED by §5.5 (third convergence).** The first convergence's
  options (a) accept-runtime-errors / (b) load-time count handshake / (c) codegen'd
  bindings, AND the second convergence's embed-the-`.cl` (B′), are all retired in favour
  of the **compiler-generated schema + layout-hash** design (§5.5). §5.5 is the canonical
  treatment; this question no longer stands. *(The under-backgrounded original treatment
  prompted the user's field-access question; the second-convergence embed-the-`.cl`
  answer was itself superseded this session because `include_str!` reads lexical file
  content while layout truth lives in the resolved module graph — §8.)*

- **q-callbacks-shrinkage — RULED: bump freely.** ABI version is not a big deal pre-1.0
  (no external users). `HostCallbacks` shrinks (drop `validate_schema`), `ABI_VERSION`
  bumps **2 → 3**, **no reserved-slot hedging.** This confirms the first convergence's
  recommendation (a) and removes (b) (reserved slot) from consideration. The governing
  principle stands: new capabilities ride exported symbols (the GOT, the
  `layout_hash` export of §5.5), not struct fields, so the callbacks struct shrinks to
  its true minimum.

- **q-symbol-table-content — RULED: confirmed.** Per fn the host needs: **name** (the
  cranelisp symbol, key into the table); **type_sig (FQ)** (the S-expr string → `Scheme`
  via `parse_type_expr`/`check_type_expr`, resolving FQ leaf refs); **GOT index** (the
  manifest array order, adopted as `got_slot`); **scheduling_class** (the one extra
  *semantic* field — it rides `DefKind::PlatformEffect { scheduling_class }`,
  `src/platform.rs:299`); and **optional docstring + param-names** (REPL `/sig`/`/doc`
  metadata). **No injected imports** (per q-sig-ref-style above — the prior "plus the
  injected import" rider is struck). Everything else in a `SymbolTable` — `seq`,
  visibility defaults, the GOT base, the `dll` retention handle — is host-derived
  invariant, not DLL-provided. §5.3 states the boundary precisely.

---

## 3. The requirement

**`--link` needs GOT-only.** A standalone executable (`cranelisp --link`) has no live
session: no typechecker, no REPL, no symbol-table scan. It needs exactly the platform's
code pointers, resolved at `ld` time. The exported GOT delivers this for free — it
is a link-time data symbol, resolved by the linker the same way
`__cranelisp_got_primitives` and `__cranelisp_got_{user_module}` are (§9). The host
builds *no* SymbolTable in `--link` runtime; the SymbolTable that drove codegen existed
only at compile time.

**REPL/`--run` needs GOT + SymbolTable.** A live session typechecks call sites,
introspects via `/sig` `/doc` `/imports`, and dispatches GOT-indirect. It needs the
SymbolTable in addition to the GOT. **That SymbolTable is HOST-built from declaration
data** — the settled principle: the DLL builds the GOT (its facts); the host builds the
table (its invariants — slot adoption, `seq`, mounting). No imports are injected (sigs
are FQ; §2 q-sig-ref-style).

**Why a DLL-provided built/serialized SymbolTable was rejected.** A `SymbolTable` is a
behaviour-bearing Rust type in `cranelisp-types` with `Serialize`/`Deserialize`. Three
reasons it must not cross the DLL boundary pre-built:

- **Rust-ABI hazard.** `SymbolTable<C, L>` is a `#[repr(Rust)]` generic type; its layout
  is unstable across compiler versions and is not a C-ABI contract. A third-party DLL
  built with a different rustc than the host would hand over a mis-laid-out struct —
  silent corruption, the worst failure mode (Principle 14's rationale).
- **Serde-format-as-ABI.** Serialising the table to JSON/bincode and handing the host
  bytes makes the *serde wire format* a public ABI the DLL author must track across host
  versions. That is a heavier, more brittle contract than "export an array of pointers."
- **Host-owned invariants.** Slot adoption, mount sequencing, and `seq` numbering are
  decisions only the host can make consistently across all loaded modules (Principle 7 —
  single source of truth). A DLL-built table would either duplicate or violate them.

So the boundary carries **C-ABI facts** (the exported GOT + a `#[repr(C)]` manifest); the
host composes the Rust `SymbolTable` from them.

**The spec promises.** `spec/08-modules.md §8.9.3` already frames a platform as a
synthetic `platform.<name>` module with its own `SymbolTable` + `GotTable` and the DLL
handle retained on `SymbolTable.dll` — exactly the shape this design completes (today's
as-built holds the DLL on the int side and dispatches via direct extern; §9). The
platform calling convention (`spec/10-io.md §10.10.1`) permits `Int`/`Bool`/`String`/`Float`/`IO a`
as boundary types; ADTs cross as heap base pointers under the consuming convention,
unchanged by this design — what changes is *where the ADT's shape is declared* (a `.cl`
module, not a DLL schema).

---

## 3a. Application: the web-server platform (S86 Wave E, FIXME 0405)

The Sudoku exemplar's web front-end is the **first effectful platform beyond
stdio/test-capture, and the first to marshal application-defined ADTs across the
FFI in production** (the `shapes` DLL is the test fixture that proved the path;
the web platform is the first real user). The S86 review (this section) rules its
shape against the three-exports model above. **Nothing here changes the model — it
is a straight application of it, with one named GAP (Model B) deferred.**

**Decision — serve model: Model A only for S86.** Two models were proposed
(`exemplar/plan-exemplar.md §"Two IO Models"`):

- **Model A** — `listen`/`accept`/`send` effect functions (`SchedulingClass::Sequential`)
  + a tail-recursive `serve-loop` written in cranelisp. **BUILDABLE NOW.** A
  `Sequential` effect's thunk is forced synchronously on the calling thread
  (`io_guard.rs::force_effect_thunk_protected` → `cranelisp_platform::call_effect_thunk`,
  a synchronous C-ABI call — no timeout, no polling, no non-blocking assumption);
  a blocking `accept()` inside the thunk simply blocks that thread until a request
  arrives. The scheduling class is a **compile-time parallel-scheduling hint**, not
  a runtime latency contract — an unbounded-blocking Sequential effect is legal.
  TCO on `serve-loop` (an established language feature) bounds the stack.
- **Model B** — `serve port handler`, where the platform DLL owns the loop and
  **calls back into a cranelisp closure `(Fn [Request] (Option Response))` per
  request.** **NOT BUILT — and RETIRED BY DESIGN (S98), not deferred.** Calling a
  cranelisp closure from native code is established as-built **only inside
  `cranelisp-intrinsics`** (`io::call_continuation`, `ivar.rs`, `session_v4.rs` — load
  `code_ptr` from the heap closure, transmute to `extern "C" fn`, call with the env
  pointer). The **platform crate's public surface exposes no such capability**: there
  is no `CLClosure`/`CLFn` wrapper type and no `HostCallbacks` method to invoke a
  passed-in closure. A platform fn taking `(Fn [Request] (Option Response))` would
  receive it as a raw `i64` with no host-side calling support, no RC discipline for
  the captured closure across the boundary, and no error-slot ferry.

  **The S98 platform-effect-boundary ruling settles it** (`effect-concurrency.md`
  §12.1, user 2026-07-01): the boundary is **poll-in / wake-out only** — the platform
  returns `Ready`/`Pending` and signals the host waker; a cranelisp closure never
  crosses it. Letting a platform own its loop and call back into a cranelisp handler is
  the Roc/"Model B" platform-owned-loop degeneration the reactor rejects
  (`effect-concurrency.md` §2, Appendix A). **No `CLClosure`/`CLFn` wrapper type and no
  `HostCallbacks::invoke_closure` method will be introduced** — `HostCallbacks` stays
  the two-pointer allocator surface. The concurrent-serve case is served by the
  scheduler-trampoline (cranelisp owns the accept loop — Model A is the seed); the only
  residual (an un-invertible synchronous C dispatcher — a `qsort` comparator, a GUI
  `run()` loop) is handled one layer lower, with the callback written in the platform's
  own language (Rust) exposing only a poll-shaped effect to cranelisp. The former
  "escape hatch, build on demand" disposition (FIXME 0407) is retired.

  This is consistent with the deliberate design boundary recorded in `test-discovery.md`
  (the `catch-runtime-error` combinator is a `cranelisp-intrinsics` primitive *because*
  closure-calling is confined to intrinsics, where thread-locals, RC, and the error
  slot can be managed safely — the platform crate is kept minimal for FFI safety).
  Model A loses nothing the showcase needs: it serves the full GET-form / POST-solve
  roundtrip; Model B's only added value was the "purity enables concurrency" teaching
  moment, which is documentation, not a required capability.

**Decision — Request/Response representation: ordinary `.cl` ADTs, exactly the
`shapes/Rectangle` precedent.** The plan's "opaque heap values (pointer as i64)"
framing predates the third convergence and is superseded. Under the settled model
**platforms do not declare ADTs** — `Request` and `Response` are ordinary `.cl`
type modules (e.g. `exemplar/web.cl`: `(deftype Request [:String method :String path :String body])`,
`(deftype Response [:Int status :String content-type :String body])`), referenced
FQ in the sigs (`web/Request`, `web/Response`). The DLL:

- **reads** request fields by NAME via `CLAdt<Request>::read_field("method")` etc.,
  resolved against the compiler-generated embedded schema (§5.5) — the exact
  `rectangle_area` pattern (`platforms/shapes/src/lib.rs`);
- **constructs** a `Response` via `CLAdt::construct` → `HostCallbacks::alloc_with_tag`
  (the host allocator; `alloc_with_tag` is KEEP per §6.6) — the `response status ct body`
  effect builds the heap ADT and returns it.

So `request-method`/`request-path`/`request-body` are NOT separate platform accessor
functions reading an opaque blob — they are **ordinary cranelisp field access on an
ordinary ADT** (`(.method req)` / `match`), and the DLL only needs `read_field` for the
fields it consumes when handling the request. `response` is the one constructor-shaped
platform fn (or, equivalently, an ordinary `.cl` constructor the handler calls directly
— the handler is cranelisp). This **collapses four proposed platform fns to at most
`listen`/`accept`/`send` (+ `Response` construction)** and reuses the `shapes` ABI v3
path end-to-end with zero new platform-model surface. The layout-hash gate (§5.5.4)
guards `web.cl` ⟷ DLL drift exactly as it guards `shapes.cl`.

**Decision — HTTP dependency: hand-rolled HTTP/1.0 over `std::net::TcpListener`, no
external crate.** A showcase platform should be readable and dependency-light; the
roundtrip the exemplar needs is a single-threaded read-request / parse-method-path-body /
write-response loop over blocking TCP — a few dozen lines of `std::net` with no `tiny_http`
(or any) dependency. Hand-rolling keeps the DLL legible as a teaching artifact, avoids
a transitive-dep ABI/build-surface in the workspace, and is *exactly* the Model-A shape
(`listen` = bind a `TcpListener`; `accept` = `listener.accept()` + read+parse one request
into a `Request` ADT; `send` = serialize a `Response` ADT to the held `TcpStream`).
`tiny_http` is rejected on the showcase-legibility + zero-dep grounds (Principle 6 —
complexity budget). (If a future Model-B concurrent variant wants a thread pool, revisit
then — not now.)

**Build/link + discovery integration.** The web platform joins the workspace exactly
as `shapes` did:

- new workspace member `exemplar/platforms/web/` (`crate-type = ["cdylib", "rlib"]`,
  dep on `cranelisp-platform`), added to the root `Cargo.toml` members;
- the dylib is found on `CRANELISP_PLATFORM_PATH`; `web.cl` (the Request/Response type
  module) is found on the **ordinary `.cl` resolution path** (project tree / `CRANELISP_LIB`),
  NOT `CRANELISP_PLATFORM_PATH` (§2 q-assoc-discovery (c));
- the embedded `web.platform-schema` is generated by `/platform-schema web` in a REPL
  session after first build (the build-load-generate-embed-rebuild cycle, §4), and the
  `__cranelisp_layout_hash_web` gate binds it;
- for the e2e `--link` path, the crate is added to `tests/scripts/build-link-prereqs.sh`
  (the `cargo build -p` prerequisite list) so the linker finds `libcranelisp_web.{rlib,so}`
  — the same line `shapes`/`shapes-badabi` occupy. No layout-hash/schema-flow change: the
  web platform uses ABI v3 unchanged.

No platform-model change is required for Model A. The model is sufficient as-is; Model B
is **retired by design** — the platform-effect boundary is poll-in / wake-out only, with
no closure-callback-into-cranelisp capability (§3a; `effect-concurrency.md` §12.1).

---

## 4. The platform-author experience

The showcase is the **build-load-generate-embed-rebuild cycle** built around
`/platform-schema`. The author writes three source artifacts (effect fns, `declare_platform!`,
the `.cl` type module), then runs one generate step to produce the embedded schema.

**1. The effect functions** — unchanged from today: `extern "C"` Rust fns over the `CL*`
wrapper family. Field access is **by name**, resolved against the embedded schema (§5.5):

```rust
pub extern "C" fn rectangle_area(r: CLAdt<Rectangle>) -> CLInt {
    let w: CLInt = r.read_field("w");   // by NAME — resolved against the generated schema (§5.5)
    let h: CLInt = r.read_field("h");
    CLInt::from(i64::from(w) * i64::from(h))
}
```

**2. `declare_platform!` WITHOUT a `schema:` declaration arm** — the schema *dialect* is
gone. The macro's job: emit the manifest (FQ sigs), call `HostContext::init`,
**export the GOT**, **embed the generated schema artifact**, and **export the
`layout-hash`** the artifact's header carries (§5.5):

```rust
declare_platform! {
    name: "shapes",
    version: "0.1.0",
    host: HOST,
    schema: include_str!("shapes.platform-schema"),  // GENERATED build artifact (§5.5) — machine-written, never hand-edited
    functions: [
        rectangle_area {
            cl_name: "rectangle-area",
            sig: "(Fn [shapes/Rectangle] primitives/Int)",   // FULLY QUALIFIED (§2 q-sig-ref-style)
            doc: "Compute the area of a rectangle",
            params: [r],
            scheduling: SchedulingClass::Commutative,
        },
    ]
}
```

Note the file embedded is **not** the `.cl` source — it is `shapes.platform-schema`, the
text `/platform-schema` writes (step 4). It carries the closed-over layout (every type the
sigs reach, transitively) plus a `;; layout-hash:` header line.

**3. The associated `.cl` module** — the platform's data types as ordinary cranelisp
source. It is an **ordinary importable module** (q-assoc-discovery (c)); the platform
declares nothing about it:

```clojure
;; shapes.cl  — an ordinary module resolvable on the project tree / CRANELISP_LIB
(deftype Rectangle [:Int w :Int h])
```

This `.cl` file compiles through the normal pipeline — no special platform path. The
`Rectangle` constructor and field accessors are ordinary cranelisp; a *program* that
wants to build a `Rectangle` to hand to `rectangle-area` does so with the same
constructor any user ADT uses. **Where it lives:** the host's ordinary module-file
resolution (`resolve_module_file`, project tree + `CRANELISP_LIB`) must find `shapes.cl`
when a sig or program names `shapes/Rectangle` — NOT `CRANELISP_PLATFORM_PATH` (that
locates the *dylib*). The author ships the `.cl` beside the dylib; the deployer places it
where module resolution reaches it (§2 q-assoc-discovery).

**4. Generate the schema — the new step.** With the FQ sigs and the `.cl` module written,
the author builds the DLL **once** (the embedded schema may be absent or stale — that first
build is tolerated). They then load the platform in a REPL session and run the generator:

```text
$ cranelisp                          # REPL
> ;; the schema is stale/absent, so loading the platform WARNS (does not refuse):
> ;;   warning: platform 'shapes' embedded schema layout-hash (abc123…) does not match
> ;;   the live layout (def456…) of shapes/Rectangle resolved from ./shapes.cl;
> ;;   the schema is out of date — run /platform-schema shapes and rebuild the platform.
> ;;   (loading anyway — REPL is the regeneration bootstrap)
>
> /platform-schema shapes              # derive + transitively close + emit
;; layout-hash: def456...
(schema
  (shapes/Rectangle
    (Rectangle 0 ((w primitives/Int) (h primitives/Int)))))
```

The author redirects that text to the embedded file and rebuilds:

```text
> /platform-schema shapes > src/shapes.platform-schema    # (or copy from REPL output)
$ cargo build -p shapes-platform                          # embeds the fresh artifact
```

Now `--run` and `--link` accept the platform: at load the host recomputes the hash from
the live tables and it matches the embedded `;; layout-hash:`. The cycle is **write sigs →
build → load → `/platform-schema` → embed → rebuild**; it is re-run whenever a sig changes
or a referenced `deftype`'s shape changes.

**Field access by name (the §5.5 design — the third-convergence answer).** The DLL author
reads fields **by name** (`read_field("w")`), not by hard-coded offset. This works because
the DLL embeds the **generated schema** (`schema: include_str!("shapes.platform-schema")`),
whose typed, named fields the retained parser reads DLL-side to compute the name→index map.
The schema is **derived from the resolved module graph** — the same layout the host
compiles — so name-based access composes with the whole language (constructors, `match`,
traits) and never diverges from the file content the way `include_str!`-ing the `.cl` would
(§8). Drift between the embedded artifact and the host's live tables (a sig or `deftype`
edited after the DLL was built) is caught by the `layout-hash` gate at both session load
and `--link` (§5.5).

**The stale-hash REPL warning is the bootstrap.** Because regeneration requires loading the
platform, and loading a stale platform would otherwise be impossible, the REPL **warns and
loads** on hash mismatch (the warning text above), where `--run`/`--link` **refuse**. This
is the one asymmetry between the modes, and it is deliberate: the REPL is the only place the
schema can be regenerated, so it must tolerate the very staleness it exists to fix.

---

## 5. The language / ABI constructs

### 5.1 The exported GOT — the DLL's facts

Each DLL exports the platform's GOT as a static array of function pointers under a
per-platform link symbol, modelled exactly on the primitives precedent
`cranelisp-primitives::PRIMITIVES_GOT_SLAB` (`crates/cranelisp-primitives/src/lib.rs:142`,
the FIXME-0280 landing). The exported symbol is `__cranelisp_got_platform_<name>`; the Rust
static the author's macro emits can carry any local identifier (e.g. `PLATFORM_GOT`):

```rust
#[unsafe(export_name = "__cranelisp_got_platform_shapes")]
pub static PLATFORM_GOT: [AtomicPtr<u8>; GOT_TABLE_SIZE] =
    [const { AtomicPtr::new(std::ptr::null_mut()) }; GOT_TABLE_SIZE];
```

- **Const-initialised in Rust; relocations at the object level — both are true, at
  different levels (answer 2).** From the platform author's Rust view, the GOT is a
  const-initialised static array of function pointers — `static … = [rectangle_area as _,
  …]`. Function items are consts in Rust, so each `fn as _` entry is a compile-time
  constant. At the *object* level, the compiler emits each of those entries as a
  **relocation** — a fixup the linker resolves at load/link time: the **dynamic loader**
  for the dylib (REPL/`--run`), the **static linker** for `--link`. There is therefore
  **no runtime population code** either way — the author writes a const array, and the
  toolchain turns each function-address entry into a fixup resolved before `main` runs.
  This is exactly how `define_module_got_data` populates a user module's GOT today (per-slot
  fn-address relocations, `crates/cranelisp-backend/src/lib.rs:322`) — the **same
  mechanism, a different emitter** (the DLL's macro emits the platform GOT; backend emits
  user-module GOTs). The shown `AtomicPtr<…null…>` form is the worst case (host populates
  the GOT at load by writing each slot from the manifest); the const-array-with-relocations
  form is the better one (no load-time store loop). Either way the GOT lives in the writable
  `__DATA` segment, and the `AtomicPtr` interior-mutability + writability constraints from
  the primitives rustdoc (`lib.rs:120-137`) carry over verbatim — the writability is what
  lets the `(trace …)` GOT copy-swap reach platform slots like every other slot (§6.3).
- **Manifest order IS the GOT slot order — one declared ordering, two derivations (answer
  1).** The `declare_platform!` macro emits both the GOT and the manifest from the *same*
  declaration list, so GOT slot *i* and manifest entry *i* are the same function by
  construction; they cannot disagree. Nobody discovers an order: the manifest **declares**
  it, and the host **adopts** it by assigning `got_slot = index in
  PlatformManifest.functions` when it builds the symbol-table entries. There is no host-side
  slot allocation for platform fns (contrast user modules, which `allocate_got_slot`) — the
  *assign-on-demand-at-registration* discipline (`memory/feedback_assign_on_demand`) made
  trivial, because the DLL already assigned them.
- **The host wraps the GOT; it never copies it (answer 3).** In REPL/`--run`,
  `dlsym("__cranelisp_got_platform_<name>")` yields the GOT's base address, and the host
  constructs its `GotTable` *over* that address via `GotTable::with_static_backing`
  (`crates/cranelisp-types/src/got.rs:116`). The DLL's exported GOT is **the one and only**
  function-pointer table — the host's GotTable is a wrapper around it, not a copy (BC §3
  invariant 3 — the GOT is the single source of truth for callable addresses; Principle 7).
  In `--link`, the static linker resolves the symbol against the force-loaded platform rlib
  (`-force_load`, `src/exe.rs:549`), exactly as it resolves `__cranelisp_got_primitives`;
  no GotTable is built at all (no live session). One GOT serves JIT, cache-restore, and
  `--link`.

### 5.2 The shrunk manifest — what stays, what retires

`PlatformManifest` (`#[repr(C)]`, `lib.rs:473`) **keeps**: `abi_version`, `name`/`name_len`,
`version`/`version_len`, `functions`/`function_count`. `PlatformFn` (`lib.rs:282`)
**keeps**: `name`, `type_sig`, `scheduling_class`, `docstring`, `param_names` (+ lengths).

**Retires** — `PlatformFn.jit_name` + `jit_name_len`. With dispatch becoming GOT-indirect
through the platform's GOT (not `Linkage::Import` against the mangled name), the `jit_name`
and the `derive_jit_name` helper (`lib.rs:1310`) lose their consumer. The slot index
replaces the mangled name as the dispatch coordinate. *(This is the second collapse — see §6 dispatch
verdict. Mark as a candidate; confirm no other consumer at implementation.)*

**Never existed; stays absent** — no `schema_ptr`/`schema_len` *manifest* field is added
(FIXME 0282 Option A is rejected, §8). No schema literal crosses the `#[repr(C)]`
manifest. The embedded **generated schema artifact** of §5.5 is **not** a manifest field —
it is baked into the DLL by `include_str!` and read DLL-side by the retained parser; the
`layout-hash` is carried as the artifact's own `;; layout-hash:` header line **and** is
exported as a **separate data symbol** (`__cranelisp_layout_hash_<name>`, §5.5.5) for the
host to compare without parsing the whole artifact — neither is a manifest field. The
manifest stays at its true minimum; new capability rides exported symbols (§1 center of
gravity).

### 5.3 The SymbolTable the host builds — the precise boundary

Answering q-symbol-table-content exactly. Per platform fn, the host constructs one
`ModuleEntry::Def` in the `platform.<name>` module's `SymbolTable`:

| Field | Source | Notes |
|---|---|---|
| key (`Symbol`) | `PlatformFn.name` (`desc.name`) | the cranelisp-visible name, e.g. `rectangle-area` |
| `scheme` | `PlatformFn.type_sig` → `parse_type_expr` → `check_type_expr` | resolves **FQ leaf refs** (`primitives/Int`, `shapes/Rectangle`) directly; named type modules auto-load per 0268; `src/platform.rs:280`. **No injected imports prime this** (q-sig-ref-style (a)). |
| `kind` | `DefKind::PlatformEffect { scheduling_class }` | `scheduling_class` lifted from the `u32` discriminant; the one extra semantic field |
| `got_slot` | **the manifest array index** (NEW) | adopted from the declared order (manifest entry *i* = GOT slot *i*, §5.1); replaces today's `got_slot: None` + direct-extern dispatch |
| `param_names` | `PlatformFn.param_names` | REPL metadata |
| `docstring` | `PlatformFn.docstring` | REPL metadata |
| `visibility` | `Public` (host-set) | host invariant |

Module-level, the host supplies (all host invariants, not DLL-provided):

- the GOT wrapper — `GotTable::with_static_backing(dlsym("__cranelisp_got_platform_<name>"))`,
  **wrapping the DLL's exported GOT in place, not copying it** (answer 3; the dlopen handle
  the session retains keeps it alive);
- `seq` numbering, mount order, and the `dll` retention handle (`SymbolTable.dll`, spec §8.9.3).

**No imports are injected into the platform module.** The first-convergence rider —
"inject `(import [primitives [*]])`" + "inject the types-module import" — is **struck**.
Sigs are FQ (q-sig-ref-style (a)); the injection mechanism
(`inject_primitives_import_for_platform`, `src/platform.rs:325`) **retires** entirely (it
was a this-sprint bare-name convenience, never load-bearing under FQ sigs).

**This is the user's "just name, signature and got entry number" — confirmed, with
scheduling_class as the one rider and the two metadata fields for the REPL.** Everything
structural is host-derived.

### 5.4 ADTs as associated modules

A platform's types are ordinary `.cl` modules (§4). They compile through the normal
pipeline and land in the symbol tables as ordinary `TypeDef` + constructor entries —
indistinguishable from user ADTs. The platform fn sigs reference them by **FQ name**
(`shapes/Rectangle`); the sig's leaf names resolve through the standard `check_type_expr`
path that already handles `primitives/Int`/`primitives/String`/`IO`
(`src/platform.rs:358`), with named type modules auto-loaded per 0268. No import is
injected (q-sig-ref-style (a)). **Load ordering invariant:** the associated module MUST
be in the symbol tables before a sig naming it is parsed (§7 sequence); under
q-assoc-discovery (c) the FQ auto-load drives that ordering.

The DLL-side field access reads the heap ADT **by name**, resolved against the
**embedded generated schema artifact** by the retained parser (§5.5). The schema
*declaration arm* retires: the DLL-only type *language* (`FieldType`-as-DSL over
`CLInt`/`CLBool`/…, the `schema:` declaration arm, `LazyLock<Schema>`-as-DSL,
`validate_schema`) **dies**. What **survives** is the schema *parser* (`Schema::parse` +
its name/field-index lookups, `schema.rs`), reading the **machine-generated artifact**
`/platform-schema` emits — a genuinely verbatim read of the generated dialect (the
generator and the parser agree on the artifact grammar by construction; §5.5 settles the
grammar). `CLAdt<T>` stays (the typed heap-pointer wrapper); `read_field` keys off the
artifact's name→index map, not a hand-authored schema literal.

### 5.5 The field-by-name design — compiler-generated schema, bound by hash

This is the document's center. The user framed the problem precisely:

> *"The platform's types have to be established outside the DLL (and therefore imported by
> FQ). This does make it harder to reference fields by name. How can we solve this?"*

The tension is real: ruling (c) puts the `deftype` **outside** the DLL, so the DLL's Rust
code has no compile-time view of the layout. The **third convergence's** answer: the
compiler **generates** the schema from the resolved module graph and the platform embeds
that generated artifact. The schema does not vanish — it changes role from a hand-authored
declaration (S71) to a **machine-written build artifact**.

The earlier options are all superseded (full disproofs in §8): **(A)** host-as-layout-oracle
(a `field_index` callback + a `--link` baked blob — most machinery); **(B)** a build-script
codegen'ing Rust bindings (a second maintained copy of the layout); **(B′)** the
second-convergence embed-the-`.cl` (`types: include_str!`) — rejected this session because
`include_str!` captures **lexical file content**, while the layout the host actually uses
comes from the **resolved module graph**; the two diverge the moment the type module imports
or re-exports its ADTs. The generated-schema design reads the same graph the typechecker and
codegen read, so it tracks the truth they track.

#### 5.5.1 The `/platform-schema <name>` command

A new REPL slash command, a sibling of the introspection family (`/sig`, `/doc`, `/info`,
`/imports`, ...). Given a **loaded** platform, it:

1. **Derives the referenced-type set** from the platform's symbol table — the
   `DefKind::PlatformEffect` entries' sig schemes. Every type named in a sig (parameter or
   return) that is an ADT (not a scalar) is a root of the set.
2. **Takes the transitive closure** over field types: for each root ADT, walk its
   constructors' field types; any field whose type is itself an ADT joins the set; recurse.
   Scalar leaves (`primitives/Int`, `primitives/Bool`, `primitives/Float`,
   `primitives/String`) terminate the walk — they need no schema entry (their layout is the
   ABI). This is the **same closure-walk + substitution** the trace `DisplayDescriptor`
   baker performs (§6.0 names the sharing requirement + the generator's placement).
3. **Emits the schema as text** (to stdout — the author redirects it to the embed file),
   prefixed by a `;; layout-hash:` header line (§5.5.4).

The schema is **machine-written, never hand-authored.** `/platform-schema` is the only
producer; the platform build is the only consumer. Because the command reads the *loaded*
platform's tables, the platform must be loadable first — which is why the load-time hash
gate **warns-and-loads in the REPL** (§5.5.4): regeneration is impossible otherwise.

The retained parser (`Schema::parse`, `schema.rs`) reads this generated artifact DLL-side
for the field name→index map. It keeps its structure (two-pass, ParseLoc diagnostics,
name/field lookups) and stays **frontend-independent** (no `cranelisp-frontend` dep —
Principle 3; the DAG forbids platform→frontend). Its input grammar is the
**`/platform-schema` artifact format**, which the generator and the parser agree on by
construction (the grammar itself is settled at implementation — §2.2 q-schema-grammar;
recommend an S-expr form so the existing reader is the parser).

#### 5.5.2 The schema shape

The user-specified shape:

```
Map<FQTypeName, Vec<(CtorName, tag, Vec<(Symbol, FieldType)>)>>
```

Every ADT entry is keyed by its `FQTypeName` and maps to its **constructor list**. Each
constructor carries its `CtorName`, its `tag` (the heap-node discriminant), and an
**ordered list of NAMED + TYPED fields** `(Symbol, FieldType)`. A product type
(single-constructor `deftype`) is the degenerate one-constructor case; a sum type lists all
constructors; an enum's constructors have empty field lists.

The **typed** fields are what make nesting work: `CLAdt::read_field("origin")` on a
`Rectangle` finds the field's `FieldType` is `geometry/Point`, so the Rust code looks
`geometry/Point` up **in the same map** (it is in the closure, §5.5.1) and reads *its*
fields by name. Without typed fields the parser could find a field's offset but not navigate
into a nested ADT.

`FieldType` is a small **recursive type-expression**, NOT a bare name:

```
FieldType ::= Scalar(FQTypeName)              ; primitives/Int, primitives/String, ...
            | Adt(FQTypeName, Vec<FieldType>) ; geometry/Point, (Option shapes/Rectangle)
            | Vec(FieldType)                   ; (Vec primitives/Int)
```

The recursion lets a field type be a parameterized ADT or a `Vec` of one — exactly the
type-expression shapes a `deftype` field can carry. (The grammar of the *textual* encoding
of `FieldType` is one of the two residual implementation questions, §2.2 q-schema-grammar —
recommend an S-expr form so the existing reader is the parser.)

#### 5.5.3 Concrete instantiations — keys are structured type expressions

Platform sigs are **monomorphic** (a platform fn over `(Option shapes/Rectangle)` names a
concrete instantiation, not a scheme with a free variable). The generator emits **concrete
instantiated entries**: for `(Option shapes/Rectangle)` it substitutes `Rectangle` for the
`Option` type parameter and records the instantiated constructors (`Some` with a field of
type `shapes/Rectangle`, `None` with no fields) — the **same substitution the trace
`DisplayDescriptor` baker** performs when baking a concrete descriptor (§6.0).

**The map key for an instantiation is the STRUCTURED type expression itself** — the
`FQTypeName`-rooted applied form `(Option shapes/Rectangle)`, machine-read — **not** a
human-readable mangle like `OptionRectangle` or `OptionInt`. This **settles and supersedes
FIXME 0234 §1.3's mangled-name naming convention**: that convention existed to produce
paste-able human identifiers for the hand-authored arm; with the key machine-read by the
parser there is no human in the loop and no mangle is needed. The key is the type
expression; the parser matches it structurally. *(This is a flagged cascade item: 0234's
naming convention is retired by this ruling — recorded in §8, not actioned doc-only.)*

#### 5.5.4 The layout hash — bind the artifact to the live tables

The generated artifact is a build-time snapshot of the resolved layout; at runtime the host
compiles whatever the `.cl` modules currently resolve to — which may have been edited (a sig
changed, a `deftype` field added) after the DLL was built. The binding that catches this:

- **What is hashed:** the canonical form of the **whole generated schema** — one hash for
  the platform (minimum mechanism: one header line, one exported symbol, one comparison).
  Because the schema is already the closed-over, normalized representation of every layout
  the platform's sigs reach, hashing *it* (rather than the source `.cl` text) hashes exactly
  the bytes that matter and is whitespace/comment-insensitive by construction (the generator
  emits canonical text).
- **Where it is carried:** as a `;; layout-hash: <hash>` **header line** in the artifact (so
  it travels with the schema and is human-visible), AND exported as a data symbol
  `__cranelisp_layout_hash_<name>` (so the host can compare without parsing the whole
  artifact). New capability rides an exported symbol, not a manifest field (§1 center of
  gravity).
- **How the host recomputes — the crux that dissolves the DAG problem:** at load, the host
  **regenerates the schema from the live tables** (the same closure-walk + substitution
  `/platform-schema` ran, §6.0 — one generator, invoked on both sides) and canonical-hashes
  the result. This is why the second convergence's canonical-form/DAG tangle **dissolves**:
  there is **one generator and one hash routine, both in the compiler**, so "the DLL side
  and the host side must agree on the canonical form" is satisfied by construction — the DLL
  side's hash was *produced by the same compiler code* at `/platform-schema` time. **No
  platform-crate canonicalization rule, no second canonicaliser, no
  frontend-printer-reachability problem** (the prior B′ design's hardest open question, §8).
- **The dual gate:**
  - **Session load** (`load_platform_dll`, `src/platform.rs:148`): after compiling the
    resolved type modules, the host regenerates + hashes and compares to
    `dlsym("__cranelisp_layout_hash_<name>")`. Mismatch → **REPL warns-and-loads** (the
    bootstrap, §5.5.1); `--run` (non-REPL) → **hard refusal**.
  - **`--link` compile** (the platform-link step, `src/exe.rs:549` neighbourhood): the
    compiler regenerates + hashes from the modules it compiled and compares to the same
    exported symbol in the force-loaded platform rlib. Mismatch → **hard refusal** at link
    time, before an executable is produced.
- **Error shape:** a hard refusal naming **both hashes** + the platform name + the guidance
  *"the platform DLL's embedded schema is out of date — run `/platform-schema <name>` and
  rebuild the platform."* This is a `PlatformError` variant (per Decision 0042 —
  `PlatformError` is `cranelisp-types`-hosted with `ErrorLocation` carriers; this is a new
  variant, flagged for the cascade, not authored doc-only).

#### 5.5.5 The GOT/symbols naming convention — EVERY per-platform export is name-suffixed (ABI v4)

**Invariant (binding).** *Every* C-ABI symbol a `declare_platform!` invocation exports
is namespaced by the platform name: the export name carries a `_<name>` suffix, with
`<name>` the **raw platform name verbatim** (the `name:` literal — NOT the
crate-name `replace('-', '_')` form, which is only ever used for rlib *filenames* in
`find_platform_rlibs`). The host computes the same suffixed name on the consume side from
the manifest-reported `name`, so emit and consume agree by construction (single source of
truth, Principle 7). This is the rule the GOT and layout-hash already followed; **the
manifest fn was the lone violator** (it exported the bare `cranelisp_platform_manifest`
`#[unsafe(no_mangle)]`), so two `--whole-archive`/`-force_load`'d platform rlibs collided
on that one symbol — `cc: multiple definition of cranelisp_platform_manifest` (DEF-5). The
fix extends the existing convention to the manifest fn; nothing else about the
three-exports model changes.

The full per-platform export table:

| Symbol | Kind | Owner | Purpose |
|---|---|---|---|
| `__cranelisp_got_platform_<name>` | data (GOT) | DLL | the platform's GOT — fn pointers (§5.1) |
| `cranelisp_platform_manifest_<name>` | fn (extern "C") | DLL | the manifest entry point (§5.2) — **namespaced as of ABI v4 (was bare `cranelisp_platform_manifest`)** |
| `__cranelisp_layout_hash_<name>` | data | DLL | the platform's generated-schema layout hash (§5.5.4) — one per platform |

All three are resolved by `dlsym` (JIT/`--run`) or `ld` against the force-loaded rlib
(`--link`), consistently with `__cranelisp_got_primitives`. The hash is **one per platform**
(not per module): the generated schema is whole-platform (the transitive closure of all the
platform's sigs), so a single hash over it covers every type any sig reaches.

**Shared naming function — one helper, used by emit AND consume.** The suffix derivation
is a single `pub fn` in `cranelisp-platform` (the natural home — both the macro and the
host depend on this crate; out-of-tree DLL authors get it for free):

```rust
// cranelisp-platform
pub fn platform_manifest_symbol(name: &str) -> String {
    format!("cranelisp_platform_manifest_{name}")
}
```

The macro cannot call a runtime `fn` in `#[unsafe(export_name = …)]` (it needs a
compile-time `concat!`), so the macro emits the suffix with the same `concat!(…,
$platform_name)` form it already uses for the GOT and layout-hash exports — but the
*pattern string* (`"cranelisp_platform_manifest_"`) is documented to match
`platform_manifest_symbol` exactly, and a unit test in `cranelisp-platform` pins the two
in agreement (assert `platform_manifest_symbol("shapes")` equals the macro-expanded export
name for a `name: "shapes"` platform). The host (`--run` dlopen + `--link` startup-stub
import) calls `platform_manifest_symbol(name)` — never an inline `format!` — so the two
sides cannot drift. (The GOT and layout-hash suffixes are *already* consistent inline
`format!`s on both sides; promoting them to sibling `platform_got_symbol` /
`platform_layout_hash_symbol` helpers is a welcome consolidation but is NOT required for
the DEF-5 fix — the manifest helper is the one this change mandates.)

**ABI version: v3 → v4.** This is a breaking change to a layout-discipline-governed
boundary (an exported-symbol name change — a host built against v3 looks up
`cranelisp_platform_manifest`, a v4 DLL exports `cranelisp_platform_manifest_<name>`;
neither finds the other), so `ABI_VERSION` bumps (`crates/cranelisp-platform/src/lib.rs`,
the single `pub const ABI_VERSION: u32`). **Every platform DLL must rebuild** against the
new macro: the in-tree members (`platforms/{stdio,test-capture,shapes,shapes-badabi,boom}`
+ `exemplar/platforms/web`) recompile automatically with the workspace; the
`tests/scripts/build-link-prereqs.sh` setup-script already `cargo build -p`s the e2e set
so the e2e platforms pick up the new symbol with no script edit. `check_abi_version` in
`src/platform.rs` rejects a stale (v3) DLL at load with the standard rebuild guidance, so
a not-yet-rebuilt third-party DLL fails loudly rather than missing-symbol-ing. *(Note: the
`ABI_VERSION` const is currently `5` in source — it bumped past the doc's stated `3`
through S77/S83 work; the operative instruction is "bump it by one as part of this change-
set", landing whatever `current + 1` is.)*

---

## 6. The implementation — mapped onto crates

### 6.0 The schema generator + the `/platform-schema` command — placement

Two new pieces: the **generator** (derive referenced types → transitive closure →
substitution → emit text + hash) and the **REPL command** that drives it. Placement:

- **The command (`/platform-schema <name>`) is `int`/REPL dispatch.** It is a slash command
  alongside the introspection family (`/sig`, `/doc`, `/info`); its handler lives in the
  REPL command dispatch in `src/` (the same place `/imports`/`/exports` are dispatched). The
  command looks up the loaded platform's `SymbolTable`, calls the generator, prints the text.
- **The generator (closure-walk + substitution + canonical emit) lives in the compiler,
  shared with the trace `DisplayDescriptor` baker.** Placement call: **`cranelisp-backend`**,
  beside the trace descriptor baker. Rationale: (1) the trace baker already performs the
  identical closure-walk + concrete-instantiation substitution over `SymbolTable` type
  layouts to bake `DisplayDescriptor`s (tracing.md §3 — the baker walks an ADT's
  constructors, substitutes concrete type args, emits a self-contained descriptor), so the
  shared logic is *already* a backend concern; (2) the **`--link`-side host recompute**
  (§5.5.4) — the compiler recomputes the hash from the live `.cl` modules at compile time
  and bakes it into the startup object (the startup stub does the compare at process
  start) — runs inside the backend/exe-bundle path where no live REPL session exists; the
  generator must be reachable from backend codegen, not from a REPL-only `int` module; (3) backend already depends on `cranelisp-types` (where `SymbolTable`, `FQTypeName`,
  `DefKind` live) and owns the descriptor baker, so the generator pulls in no new dep edge.
  The `int` command is a thin caller of the backend generator; the `--link` check is a
  second caller of the same routine — **one generator, two callers** (the REPL command and
  the link-time host recompute), satisfying the "one generator, one checker" requirement
  that dissolves the canonical-form/DAG problem (§5.5.4).

  **Name the sharing requirement, do not force one serialized representation.** The shared
  asset is the **closure-walk + substitution logic** — the algorithm that, given a root
  type and a `SymbolTable`, produces the closed-over set of concrete constructor layouts.
  The trace baker consumes that to emit a `DisplayDescriptor` (a baked binary blob, baked
  into the startup object, lifetime = the compiled program); the schema generator consumes
  it to emit `/platform-schema` text (a build artifact, lifetime = until the next
  regeneration). **Different consumers, different lifetimes, different serializations** —
  the requirement is that the *walk* is one routine, not that the *output representation* is
  one format. Forcing a single serialized form on both would over-couple two consumers that
  legitimately differ (a Principle-6 complexity-budget call).

### 6.1 Platform crate (`cranelisp-platform`) — macro change + GOT export

`declare_platform!` (`lib.rs:1450`):

- **Emit the exported GOT** under `__cranelisp_got_platform_<name>` (the
  `PRIMITIVES_GOT_SLAB` pattern from `cranelisp-primitives`), as a const array of fn
  pointers whose entries the linker fixes up via relocations (§5.1, answer 2) — or, in the
  worst-case `AtomicPtr` form, populated by the host at load.
- **Drop the `schema:` declaration arm**; **add the `schema:` embed arm** taking
  `include_str!("<name>.platform-schema")` — the macro embeds the **generated artifact text**
  and **exports `__cranelisp_layout_hash_<name>`** parsed from the artifact's
  `;; layout-hash:` header at build time (§5.5.4). The schema *declaration* static / marker
  types / `GetSchema`-as-DSL go; the schema **parser** is **kept** (it reads the embedded
  artifact for the name→index map).
- **Drop `validate_schema` from the `HostCallbacks` construction** + drop
  `null_validate_schema` (`lib.rs:433`). Per q-callbacks-shrinkage: bump `ABI_VERSION`
  2→3 for the field removal (bump freely — no reserved slot).
- **Drop `jit_name` derivation** (§5.2) if confirmed unused.

**The parser is kept, repointed at the generated artifact.** Today `Schema::parse`
(`schema.rs:167`) parses a **bespoke hand-authored schema dialect**. Under the third
convergence its input is the **`/platform-schema` artifact format** (the typed-field
`Map<FQTypeName, ...>` text, §5.5.2). Whether that is a grammar change or a near-verbatim
reuse depends on the artifact grammar settled at §2.2 q-schema-grammar — if the generator
emits an S-expr form the existing reader handles, the parser's grammar work shrinks
dramatically; if a bespoke line format, the tokenizer retargets. Either way the parser keeps
its structure (two-pass, ParseLoc diagnostics, name/field lookups) and stays
frontend-independent (Principle 3 — platform must not depend on frontend). `adt.rs`'s
schema-*declaration* half (`CLAdtType`, `GetSchema`-as-DSL marker plumbing) deletes; `CLAdt`'s
`read_field` reworks to **name-based** lookup against the parser's artifact-derived map (the
typed fields drive nested-ADT navigation, §5.5.2). This is `/dev (platform)` work once /arch
+ user ratify.

### 6.2 Backend (`cranelisp-backend`) — GOT export + dispatch + the schema generator

Today backend's `define_module_got_data` emits `__cranelisp_got_{M}` data symbols for
user/stdlib modules (`lib.rs:322`), and primitives' GOT is the exported static array
(0280). The platform's GOT is the **same mechanism, owned by the DLL** — backend does not
*emit* the platform GOT (the DLL exports it); backend's job is **dispatch**: a
`DefKind::PlatformEffect` call site emits GOT-indirect dispatch against
`__cranelisp_got_platform_<name>` at the entry's `got_slot`, replacing the current
direct-extern path (`apply.rs:209-227`, §9). This is **structurally identical** to how a
call to a user-module fn dispatches GOT-indirect against `__cranelisp_got_{other_M}`
(`lib.rs:489`). Backend references the platform's exported GOT as a `Linkage::Import`
data symbol — resolved by `dlsym` (JIT) or `ld` (`--link`).

### 6.3 The `--link` platform-dispatch verdict (suspected 0280-class hole — VERIFIED)

**Today, `--link` platform dispatch WORKS — but by a different, fragile mechanism than
GOT.** The verification walk:

- Platform fns are dispatched via `compile_extern_call` — a direct `Linkage::Import`
  against the mangled `jit_name` (e.g. `cranelisp_print`), NOT GOT-indirect
  (`apply.rs:209-227`). Platform entries carry `got_slot: None` (`worker.rs:2615`); the
  platform GOT atom is **not** emitted with fn relocations because platform fns have no
  `FuncId`s.
- In REPL/`--run` (JIT), the fn ptr reaches the JIT via `JITBuilder::symbol(jit_name,
  ptr)` (the `jit_symbols` vec from `register_platform_in_tc`, `src/platform.rs:311`),
  and the cache linker registers it identically.
- In `--link`, there is no `JITBuilder::symbol`. The direct `Linkage::Import` against
  `cranelisp_print` is instead resolved at `ld` time **because the platform rlib is
  `-force_load`ed** (`src/exe.rs:549`), so the DLL's `#[export_name]`/`extern "C"`
  symbols (`cranelisp_print`, …) are present in the link. **So it links and runs today.**

**The fragility (why the GOT export is the right fix, not just a tidy-up):**

1. **No redefinition / no GOT-swap.** A direct-extern call is baked at link; it cannot
   participate in the GOT copy-swap that `(trace …)` relies on (the primitives GOT
   rustdoc, `lib.rs:127`, documents the trace swap as a writability constraint on the
   GOT). Platform fns are simply outside that machinery — a latent inconsistency.
2. **Two dispatch paths for the same concept.** Platform fns dispatch by mangled-name
   direct extern; everything else (user, stdlib, primitives) dispatches GOT-indirect.
   That is a Principle 7 / Principle 11 smell — one concept, two code paths that age
   independently. The 0280 primitives fix removed exactly this divergence for primitives;
   this design removes it for platforms.
3. **The mangled-name namespace is a flat-namespace hazard — and worse than it looks.**
   `cranelisp_print` is a real as-built name (stdio's `jit_name`,
   `platforms/stdio/src/lib.rs:19` `#[export_name = "cranelisp_print"]`), and it exposes
   three defects at once: (i) it **squats in the compiler's own ABI prefix** —
   `cranelisp_*` is the runtime/intrinsics namespace (`cranelisp_panic`,
   `cranelisp_trace_*`), so a platform fn masquerades as a compiler intrinsic, with no
   platform component in the name to prevent platform-vs-compiler collision; (ii) two
   DLLs exporting the same name collide at link; (iii) the author must keep the
   `export_name` attribute and the descriptor's `jit_name` string identical **by hand,
   with no check** — JIT mode never exercises the export (it uses the manifest's fn
   pointer), so a typo surfaces only as a `--link` failure. Slot-indexed GOT dispatch
   under a per-platform-named GOT (`__cranelisp_got_platform_shapes`) retires all three:
   platform fns need no exported names at all, so `jit_name`, the `export_name`
   attributes, and the hand-agreement die together.

**Verdict: not broken today, but structurally unsound — the DLL-exported GOT makes it
sound** (emitted code references the platform's exported GOT directly, identical to
primitives and user modules, in all three modes). State this to the user plainly: the
fix is a *correctness/consistency* improvement, not a bug repair, so it can be sequenced
deliberately.

### 6.4 Int (`src/`) — load sequence

`load_platform_dll` + `register_platform_in_tc` (`src/platform.rs:148/247`) rework:

- **dlopen** the dylib; read the manifest (unchanged path, `manifest_to_descriptors`).
- **Resolve + compile the associated `.cl` type module(s)** through ordinary module
  resolution (`resolve_module_file` — project tree + `CRANELISP_LIB`, q-assoc-discovery
  (c)), into the symbol tables *before* the platform's sigs are parsed. These are
  **ordinary modules** (not `platform.<name>.*`-mounted); the FQ sig refs auto-load them
  per 0268.
- **Layout-hash check (§5.5.4):** regenerate the schema from the live tables (the backend
  generator, §6.0) and canonical-hash it; compare to `dlsym("__cranelisp_layout_hash_<name>")`.
  Mismatch → in the **REPL, warn-and-load** (the regeneration bootstrap, §5.5.1); in
  **`--run` (non-REPL), hard `PlatformError` refusal** (both hashes + "run /platform-schema
  and rebuild" guidance), abort the load.
- **dlsym the GOT** (`__cranelisp_got_platform_<name>`) and build the platform module's
  `GotTable::with_static_backing` **wrapping it in place** (answer 3 — no copy).
- **Build the SymbolTable** in host memory from the manifest: per fn, `got_slot = manifest
  index` (answer 1), scheme from the **FQ sig** (resolving `primitives/Int`,
  `shapes/Rectangle` directly), `DefKind::PlatformEffect`, metadata (§5.3). **No imports
  injected** — `inject_primitives_import_for_platform` (`src/platform.rs:325`) is
  **deleted**.
- The `jit_symbols` return vec (the old `JITBuilder::symbol` path) **goes away** — fn
  ptrs live in the GOT, not registered by name.

### 6.5 Cache (FIXME 0232) — what `.meta.json` needs

`SymbolTable.schema_literal: Option<String>` **already landed** (S76 W1b,
`cache/mod.rs:119`). **With ADTs as ordinary modules, this field retires** — the
platform's types are cached like any other module's `.cl` source; there is no schema
literal to round-trip. The cache-restore path for a platform module re-establishes the
GOT by `dlsym`-ing it at restore (the dylib is re-opened), exactly as JIT setup
does — no descriptor re-serialisation needed beyond what every cached module already
carries. **Net: `schema_literal` deletes; no new cache field is owed.**

### 6.6 Retirement list (each with disposition)

| Item | As-built site | Disposition |
|---|---|---|
| `schema:` macro **declaration arm** + `LazyLock<Schema>`-as-DSL static | `lib.rs:1456`, `:1475` | **RETIRE the declaration** — no hand-authored DLL-side schema. Replaced by the `schema:` **embed arm** taking the generated artifact (§6.1). |
| schema **hand-authored DIALECT** (the bespoke `(Type (CLInt …))` author grammar in `Schema::parse`) | `schema.rs:167` parse-arm | **RETIRE the hand-authored dialect** — the parser's input is now the `/platform-schema` artifact format (§5.5.2; grammar settled at §2.2 q-schema-grammar). |
| schema **PARSER** (`Schema::parse` two-pass structure + `lookup_field`/ParseLoc machinery) | `schema.rs` | **SURVIVES** — reads the generated artifact for name→index (§5.5.1). The struct family (`Schema`/`TypeShape`/`Variant`/`Field`) reshapes to the typed-field schema shape (§5.5.2); `SchemaParseError` repurposes to artifact-parse diagnostics. |
| `HostCallbacks::validate_schema` field + `validate_schema` host body (0229-step-2, unbuilt) | `lib.rs:394` | **RETIRE** — no schema to validate (the layout-hash check, §5.5.4, replaces validation); `ABI_VERSION` 2→3 bump (bump freely) |
| `null_validate_schema` placeholder | `lib.rs:433` | **RETIRE** — the gate's default value goes with the field |
| `inject_primitives_import_for_platform` (the platform-module primitives glob injection) | `src/platform.rs:325` | **RETIRE (NEW)** — sigs are FQ (q-sig-ref-style (a)); the platform module carries ZERO injected imports. Was a this-sprint 0233-step-1 bare-name convenience. The `parse_and_check_platform_type_sig` rustdoc (`:354–358`) that cites the injection is corrected to FQ-driven resolution. |
| `schema_literal` cache field | `cache/mod.rs:119` | **RETIRE** — platform types cache as ordinary modules |
| `CLAdtType`/`GetSchema`-as-DSL/declaration half of `CLAdt` | `adt.rs` | **RETIRE declaration lookup**; `CLAdt<T>` stays, `read_field` → **name-based** via the parser's artifact-derived map (§5.5.2) |
| `PlatformFn.jit_name` + `derive_jit_name` | `lib.rs:284`, `:1310` | **RETIRE** (candidate — confirm no consumer) — dispatch is slot-indexed |
| FIXME 0282 Option A (`schema_ptr` manifest fields) | proposed-only | **REJECTED** — never built (§8) |
| FIXME 0234 `/abi` per-type emitter + mangled-name naming convention (§1.3) | proposed-only | **SUBSUMED — NOT IMPLEMENTED** — its output target (the hand-authored schema arm) no longer exists; the structured-type-expression key supersedes the §1.3 mangle (§5.5.3, §8). FIXME retires when this design is actioned (do NOT delete doc-only). |
| `alloc_with_tag` (0229-step-1) | `HostCallbacks::alloc_with_tag`, `lib.rs:377` | **KEEP** — ADT *construction* across the FFI still needs the host allocator; unaffected by schema retirement |
| `/platform-schema <name>` REPL command + the backend schema generator | NEW (§5.5.1, §6.0) | **ADD** — the generator (closure-walk + substitution + canonical emit) in backend, shared with the trace `DisplayDescriptor` baker; the command in int/REPL dispatch. |
| `__cranelisp_layout_hash_<name>` export + dual gate | NEW (§5.5.4) | **ADD** — the layout-hash binding (data symbol; load warns-in-REPL/refuses-in-`--run`/refuses-in-`--link`) |

Note: `alloc_with_tag` stays — it is the heap-construction callback, orthogonal to the
schema. A platform fn that *constructs* a `Rectangle` to return still allocates a tagged
heap node via the host allocator; what changed is that `Rectangle`'s shape is declared in
`.cl`, not in a schema.

### 6.7 DEF-5 manifest-symbol namespacing (S86 — the coupled ABI rename) — GO

**The defect.** `declare_platform!` exports `cranelisp_platform_manifest`
**un-namespaced** (`#[unsafe(no_mangle)]`, `declare.rs:303-304`). Two
`--whole-archive`/`-force_load`'d platform rlibs each define that one symbol →
`cc: multiple definition of cranelisp_platform_manifest`. The GOT
(`__cranelisp_got_platform_<name>`) and layout-hash (`__cranelisp_layout_hash_<name>`)
exports are **already** per-platform namespaced; the manifest fn was the lone holdout.
This blocks the web exemplar `--link` (FIXME 0405 — it links `web` + transitively
`stdio`). `collect_platform_manifest_names` even documents the limitation in source
(`src/exe.rs:868-874`: "Multi-platform `--link` therefore needs per-platform mangled
manifest names").

**Scope confirmation — NAMING-ONLY.** This is a self-contained symbol-naming correction.
**No manifest *content* change** (the `#[repr(C)]` `PlatformManifest` / `PlatformFn`
structs are untouched), **no schema-model change**, **no three-exports-model change** —
the model of §1 is unchanged; only the manifest export's *name* is corrected to honour
the §5.5.5 invariant the other two exports already follow. It is therefore a pure rename
that must land **atomically across three crates + the platform rebuilds** (the sanctioned
exception to one-crate-per-`/dev`: a host that looks up the new name against a DLL still
exporting the old name finds nothing, and vice-versa — emit and consume MUST flip
together).

**The exact rename (old → new):**

| | Old export name | New export name |
|---|---|---|
| manifest fn | `cranelisp_platform_manifest` | `cranelisp_platform_manifest_<name>` |
| GOT (unchanged) | `__cranelisp_got_platform_<name>` | *(already namespaced — no change)* |
| layout-hash (unchanged) | `__cranelisp_layout_hash_<name>` | *(already namespaced — no change)* |

`<name>` = the raw `name:` literal verbatim (§5.5.5) — e.g. `cranelisp_platform_manifest_shapes`,
`cranelisp_platform_manifest_shapes-badabi`.

**Per-crate change list (one coordinated change-set):**

- **`/platform` — `cranelisp-platform`** (`src/declare.rs`, `src/lib.rs`):
  1. In `__declare_platform_body!`, change the manifest fn's `#[unsafe(no_mangle)]` to
     `#[unsafe(export_name = concat!("cranelisp_platform_manifest_", $platform_name))]`
     (`declare.rs:303-304`), matching the GOT/hash export-name form on the adjacent lines.
  2. Add `pub fn platform_manifest_symbol(name: &str) -> String` to the crate facade
     (`lib.rs`) — the shared emit/consume helper (§5.5.5). New `pub` item → the
     `public-api.txt` baseline regenerates + the crate-root rustdoc names it (the platform
     facade is retired → source rustdoc is the canonical surface; out-of-tree DLL authors
     consume this helper, so it is a legitimate boundary export — the external-audience
     exception).
  3. Add a unit test pinning `platform_manifest_symbol("shapes")` equal to the
     macro-expanded export name (defend against the concat-string vs helper-string drift).
  4. **Bump `pub const ABI_VERSION`** by one (`lib.rs` — currently `5`, so → `6`; the doc
     frames it as the v3→v4 step relative to the three-exports baseline, but the operative
     instruction is `current + 1`). Update the `ABI_VERSION` rustdoc bump-rule note +
     the `assert_eq!(ABI_VERSION, …)` unit test (`lib.rs:1724`).

- **`/backend` — `cranelisp-backend`** (`src/exe.rs`): the startup-stub emitter
  (`generate_startup_object_checked`) iterates `platform_manifest_names` and declares each
  `Linkage::Import` against the name string (`exe.rs:268-271`). **It is naming-agnostic —
  it imports whatever names the slice carries**, so the only change here is the test
  fixtures that hard-code `"cranelisp_platform_manifest"` (`exe.rs:440/448/467`) flip to
  the per-platform form (e.g. `cranelisp_platform_manifest_shapes`). The dispatch/import
  loop body needs no logic change. *(If a `platform_manifest_symbol` helper is wanted
  backend-side it imports from `cranelisp-platform`, but backend receives the names
  pre-computed from int, so it does not call the helper itself.)*

- **`/int` — `src/`** (`src/platform.rs`, `src/exe.rs`, `src/session_v4.rs`):
  1. **`src/platform.rs:218`** — the `--run` dlopen lookup
     `library.get(b"cranelisp_platform_manifest")` is the **read-before-name-known**
     problem: the manifest symbol now depends on `<name>`, but `<name>` *comes from* the
     manifest. **Two clean resolutions, pick one** (an implementation-detail decision for
     `/dev`, not an architectural fork): **(a)** the host already knows the platform name
     before dlopen — it is `resolve_platform_path`'s lookup key / the `(platform "<name>")`
     declaration — so thread that name in and `library.get(platform_manifest_symbol(name).as_bytes())`;
     **(b)** keep an additional bare-named **alias export** in the macro for the
     dlopen-discovery case only. **Recommend (a)** — the GOT and layout-hash dlsyms at
     `platform.rs:275/297` *already* depend on `name` and resolve it from the
     manifest-reported name, but the platform name is known at the call site from the
     declaration before the manifest is read; passing it in keeps a single namespacing rule
     with no alias-export special case. The lookup uses `platform_manifest_symbol(name)`,
     never an inline `format!`.
  2. **`src/exe.rs:860`** — `PLATFORM_MANIFEST_SYMBOL` const + `collect_platform_manifest_names`
     change from "N copies of the shared bare name" to **the per-platform suffixed names**.
     The function must therefore take the **platform names** (it currently takes only the
     count) and map each through `platform_manifest_symbol`. Update its doc comment (delete
     the "multi-platform needs mangled names — out of scope" limitation note; it is now
     resolved). Update its unit test (`exe.rs:1089`).
  3. **`src/session_v4.rs:2218-2219`** — `linked_platform_link_data` calls
     `collect_platform_manifest_names(platform_names.len())`; change to pass the deduped
     `platform_names` slice (it is right there at `:2209`) so the names, not the count,
     drive the manifest-symbol list. This is the single call-site adjustment for the new
     signature.

- **Platform DLL rebuilds:** every platform rebuilds against the new macro. In-tree members
  (`platforms/{stdio,test-capture,shapes,shapes-badabi,boom}` + `exemplar/platforms/web`)
  recompile with the workspace; `tests/scripts/build-link-prereqs.sh` already
  `cargo build -p`s the e2e platform set, so no script edit is needed.

**`--run`/dlopen path impact.** Yes — the `--run`/REPL dlopen of the manifest
(`src/platform.rs:218`) **must** use the new per-platform name (resolution (a) above);
this is the one consume-site that reads the manifest *to learn the name*, so the name has
to be sourced from the declaration, not the manifest. The GOT + layout-hash dlsyms
(`platform.rs:275/297`) are unaffected — they already namespace by `name`.

**Layout-hash / schema gate impact: NONE.** The layout-hash export, the schema generator,
the dual gate, the `--link` startup-stub hash bake — all unaffected. The hash symbol was
already namespaced; the schema model does not change. Only the manifest fn's name moves.

### 6.8.0 SINGLE-ABI CUTOVER — `ABI_VERSION` 7→8 (S96, user-directed; supersedes the dual-channel design below)

> **Status: RATIFIED target (S96 /arch), pre-`/dev`-migration.** User direction
> 2026-06-29: *"Jump to the latest ABI and ditch backward compatibility — there are
> no users."* This **retires the v6/v7 coexistence envelope** that the rest of §6.8
> (below) and the FIXME-0464 dual-manifest-merge ruling were built to preserve.
> Everything below from "§6.8 The ABI-v4 cascade" onward is **HISTORICAL** — it
> records how the additive, byte-identical-off, dormant-`concurrency`-feature
> coexistence worked. The target is now a single ABI; read §6.8.0 as authoritative
> and the rest as the path that led here.

**The target: ONE platform ABI (v8).** One manifest type, one macro, one GOT
export, one loader path. Each effect is **independently blocking or poll-shape via
its `ConcurrencyDescriptor`** — `blocking == 1` ⇒ a blocking `CLIO`-returning effect
fn; `blocking == 0` ⇒ a poll-shape async leaf (`PollFn`). There is no separate v7
channel, no either/or probe, no within-DLL-mixing problem (FIXME 0464 **dissolves** —
a single manifest naturally carries both shapes).

**1. The unified manifest entry — `PlatformFn` absorbs `ConcurrentPlatformFn`.** The
v6 `PlatformFn` and the v7 `ConcurrentPlatformFn` merge into ONE `#[repr(C)]`
manifest entry. Because GOT-indirect dispatch is **shape-agnostic** (the slot holds
a type-erased `*const u8`; the backend reads `poll_shape` off `DefKind` to decide
what *node* to build), the entry needs only one fn-pointer field plus the descriptor:

```rust
#[repr(C)]
pub struct PlatformFn {
    pub name: *const u8, pub name_len: usize,
    /// Blocking `extern "C"` effect fn (CLIO-returning) when `concurrency.blocking == 1`,
    /// or a `PollFn` when `concurrency.blocking == 0`. Type-erased; GOT-indirect
    /// dispatch is shape-agnostic — `DefKind::PlatformEffect.poll_shape` selects the node.
    pub ptr: *const u8,
    /// Poll-shape leaf state-teardown hook (the former ConcurrentPlatformFn.drop_state);
    /// `None` for blocking effects.
    pub drop_state: Option<unsafe extern "C" fn(state: *mut core::ffi::c_void)>,
    pub param_count: u32,
    pub type_sig: *const u8, pub type_sig_len: usize,
    pub docstring: *const u8, pub docstring_len: usize,
    pub param_names: *const *const u8, pub param_name_lens: *const usize, pub param_name_count: usize,
    /// REPLACES `scheduling_class: u32`. Carries token + cardinality + global_budget + blocking.
    pub concurrency: ConcurrencyDescriptor,
}
```

`PlatformManifest` is unchanged in shape (it already points at a `*const PlatformFn`
array) — only the element type's fields change. `ConcurrentPlatformManifest` is
**deleted** (merged into `PlatformManifest`).

**2. The ABI types become CORE (ungated).** `ConcurrencyDescriptor`, `Poll`,
`PollFn` (`cranelisp-types`) and `HostCtx`, `Waker`, `WakerVTable`, `PollFn`
(`cranelisp-platform`) graduate from the dormant `#[cfg(feature = "concurrency")]`
edge to the default public surface — the descriptor is part of every manifest entry
and any platform may declare a poll leaf. **The `concurrency` feature (layout-only)
is RETIRED**; the host **reactor** stays optional behind `concurrency-runtime`
(mio/futures, in `cranelisp-intrinsics`). **`/arch` has landed the `cranelisp-types`
half** (ungated `ConcurrencyDescriptor`/`Poll`/`PollFn`; `from_scheduling_class`
re-documented as the blocking-effect descriptor sugar, not a compat shim).

**3. ONE macro — `declare_platform!`; `declare_concurrent_platform!` is DELETED.**
The single macro emits one GOT (`__cranelisp_got_platform_<name>`), one namespaced
manifest fn (`cranelisp_platform_manifest_<name>`), the unified `PlatformFn` array,
and the optional `schema:`/layout-hash exports. Per-effect, the author writes EITHER
`scheduling: SchedulingClass` (blocking sugar → `ConcurrencyDescriptor::from_scheduling_class`,
`blocking = 1` — minimal churn for the 7 blocking platforms) OR `descriptor:
ConcurrencyDescriptor { … }` (full, for poll-shape, `blocking = 0`) + optional
`drop_state:`. This is a per-fn key choice inside one macro, **not** the rejected
two-top-level-macro convergence — strictly simpler.

**4. The loader is a SINGLE path.** `src/platform.rs::load_platform_dll` deletes the
`#[cfg(feature = "concurrency")]` either/or probe + the `cranelisp_concurrent_manifest`
symbol: it dlsyms `cranelisp_platform_manifest_<name>`, reads the unified manifest,
and `manifest_to_descriptors` (the lone lifter; `concurrent_manifest_to_descriptors`
is deleted) populates `OwnedPlatformFnDescriptor.concurrency` for every entry.
`register_platform_in_tc` computes — with NO cfg — `poll_shape = desc.concurrency.blocking == 0`
and `scheduling_class = desc.concurrency.nearest_scheduling_class()`, and builds
`DefKind::PlatformEffect { scheduling_class, poll_shape, got_slot }`. The exe-bundle
`--link` startup stub (`cranelisp_init_platform`) is unaffected in shape — it calls
the same namespaced manifest fn for its init side-effect; only the `PlatformManifest`
element type it transmutes against recompiles.

**5. The DEFAULT (non-reactor) host + poll effects — the key question, answered.**
The default build (no `concurrency-runtime`) fully understands the unified manifest:
it reads `blocking`, registers blocking effects for synchronous dispatch, and
registers poll-shape effects in the symbol table **but has no reactor to drive
them**. The resolution is **call-time, not load-time** (load-time whole-platform
refusal is wrong — it would break a mixed platform like stdio's `print` just because
the same DLL also carries a poll `read_line`):

- The platform **loads fully** in the default host; blocking effects work; a program
  that never invokes a poll effect runs unchanged. This is what makes mixed platforms
  (stdio = `print` blocking + `read_line` poll in ONE manifest) work in the default
  host — the exact wall FIXME 0464 hit, now structurally gone.
- The **backend is build-invariant** (no cargo feature): it always emits the
  `IO_TAG_EFFECT_POLL` node for a `poll_shape` effect — the same backend compiles for
  both the reactor and non-reactor binary, so it cannot know which it is in.
- The **earliest build-aware point is the trampoline** (`cranelisp-intrinsics`,
  `concurrency-runtime`-gated). The reactor build drives the poll node; the
  **non-reactor build gains a new `#[cfg(not(feature = "concurrency-runtime"))]`
  `IO_TAG_EFFECT_POLL` arm that returns a clean runtime error** — *"poll-shape effect
  invoked without a concurrency runtime; rebuild with `--features
  concurrency-runtime`"* — never a SIGSEGV, never a missing-arm panic. This is the one
  load-bearing `/dev` addition for the default-host story.
- Int MAY *additionally* surface a friendlier load-/codegen-time diagnostic when it
  can detect (poll effect reachable) ∧ (no reactor), but the **structural guarantee
  is the trampoline arm**.

**6. `concurrency-runtime` stays OPTIONAL.** The default build is lean (no
mio/futures, no reactor, blocking-only + the loud poll-error arm). This is
recommended-kept: the production default never pays for the reactor, and `--link`
output without `concurrency-runtime` links no executor (structural).

**7. The "byte-identical-off" invariant CHANGES MEANING → "reactor-free-off".** The
prior invariant (default build byte-identical because all v7 machinery is `#[cfg]`'d
out) no longer holds — the ABI types are core, so the manifest, loader, and descriptor
are present in every build. The NEW, narrower invariant: **the `concurrency-runtime`-off
build carries NO reactor (no mio/futures), drives only blocking effects, and produces a
clean error on poll-effect invocation.** This is a feature-presence guarantee, not a
byte-identity one. The `_neg`/frozen-edge guards that asserted "v7 types ABSENT from
the default `public-api.txt` edge" are **inverted** — those types are now present by
design — and are REPLACED by positive layout guards on the unified `PlatformFn` field
order + `ConcurrencyDescriptor` presence (a `/qa` rewrite; see SPRINT.md).

**8. ABI bump: 7 → 8.** The unified `PlatformFn` (drops `scheduling_class: u32`; adds
`drop_state` + `concurrency`) is a layout-affecting change (Principle 14). Stamp
`ABI_VERSION = 8`. With no out-of-tree DLLs, every in-tree platform rebuilds against
v8 in the cutover change-set. The `shapes-badabi` negative fixture's hard-coded wrong
version is re-pinned wrong-relative-to-8 (`/qa`).

---

### 6.8.0a FULL STREAMLINE — single trampoline + lazy reactor (S96 SCOPE PIVOT EXTENDED, user-directed)

> **Status: RATIFIED target (S96 /arch), pre-`/dev`-migration. Extends §6.8.0
> in the SAME A4c jump.** User direction 2026-06-29: *"are we still carrying two
> tramps or variations? would it make sense to cutover to the streamlined state
> in one jump? simple platform, simplest tramp?"* §6.8.0 above kept the host
> **reactor optional** behind `concurrency-runtime` — i.e. TWO `#[cfg]`-selected
> trampolines (a synchronous off-build stepper + the async on-build executor),
> and §6.8.0 point 5 even ADDED a poll-error arm to the off-build. Landing A4c on
> that dual-trampoline state would be a **Principle-8 interim** (migrate the
> platforms now, re-collapse the trampoline later). So A4c targets the genuine
> end-state in one jump: **ONE ABI + ONE (async) trampoline + NO
> `concurrency`/`concurrency-runtime` feature.** The reactor IS the runtime.

**The defuser is LAZY reactor init.** The async executor already drives the top
future on the **calling thread** (there is no dedicated reactor thread — `turn()`
blocks `mio::poll` on the same thread; only `rayon::spawn` uses other threads, via
rayon's own lazily-spun global pool). The only eager cost today is `Reactor::new()`
= `mio::Poll::new()` (epoll_create) + `mio::Waker::new()` (an eventfd). We **defer
those two syscalls** to the first time the program actually needs them — the first
poll-leaf that registers fd/timer interest, or the first `Par` blocking-bridge
spawn. A pure-blocking program (`(print "hello")`) then drains synchronously
through the one trampoline and constructs no mio Poll at all. **Lean-default
becomes a RUNTIME property, not a `#[cfg]` split.**

**Feasibility verdict: YES, with caveats** (verified against
`cranelisp-intrinsics/src/{io.rs,reactor.rs}` as-built):

1. **`block_on` drives pure-blocking to completion with no reactor activity.** The
   async stepper (`run_io_trampoline_inner_async`) forces `IO_TAG_EFFECT` thunks
   **synchronously** (`force_effect_node`, identical to the sync stepper) and
   walks `Pure`/`Bind` purely; only an `IO_TAG_EFFECT_POLL` that would-blocks, or a
   `Par` rayon-bridge, ever returns `Pending`. So for a Pure/Bind/blocking-Effect
   tree the FIRST `future.poll()` returns `Ready` — the executor loop returns
   before `turn()` is ever reached. **If a future never returns `Pending`, the mio
   `Poll` is never needed.** Confirmed.
2. **Lazy mio `Poll` is sound.** Make the `Poll` + bridge `Waker` a reactor-thread-
   local lazy singleton inside `Reactor` (a `OnceCell`/`RefCell<Option<…>>` field,
   NOT a process-global `LazyLock` — one reactor per `block_on` drive). Force it at
   the two register-callback bodies (`register_fd`/`register_timer`) and **before**
   the `rayon::spawn` in `run_blocking_branch`. The soundness obligation the prompt
   names — *the eventfd must exist before the first `Pending` parks* — holds **by
   single-thread happens-before**: a poll-fn can only register interest by calling
   `HostCtx::register_*` (forcing the `Poll` first, on the calling thread, before
   that call returns `Pending`); and the cross-thread `Par` wake races only after
   `rayon::spawn`, which we force the `Poll`+bridge-`Waker` ahead of. There is no
   window in which a wake targets a not-yet-built eventfd. The `HostCtx` *struct*
   (the register-callback vtable over `*mut Reactor`) is still built eagerly and
   cheaply — only the `Poll` it lazily touches is deferred — so a trivially-ready
   poll leaf (web `listen`/`send` returning `Poll::Ready` without registering)
   pays nothing.
3. **The blocking/rayon path works without the Poll for the sequential case.** A
   blocking effect runs inline via `force_effect_node` — no rayon, no reactor. Only
   a `Par` with a blocking branch spawns rayon, and that branch forces the lazy
   `Poll`+bridge before spawning (it needs the bridge to be woken back). The
   sync per-branch driver `run_io_trampoline` (sync) is **RETAINED** — it is the
   rayon-worker run-to-completion body; what is deleted is the `drive_io` `#[cfg]`
   split, not `run_io_trampoline` itself.
4. **`--link`/exe-bundle works with an always-linked-but-lazy reactor.** The
   startup stub calls `cranelisp_run_io` → `drive_io` → `block_on_reactor`
   unconditionally (today the `--link` build took the sync arm; post-cutover there
   is only the async arm). mio+futures+rayon are **always linked** into the binary
   (accepted per "no users" — rayon is already an unconditional intrinsics dep; mio
   +futures graduate from `dep:`-gated to plain deps). A `(print "hello")` linked
   binary still constructs no `Poll` at runtime (lazy). **No `HostCallbacks`/exe-
   bundle host-construction change** — the reactor `HostCtx` is built single-sited
   inside `block_on_reactor` (intrinsics), separate from the exe-bundle's
   `HostCallbacks{alloc, alloc_with_tag}`; **FIXME 0419 stays parked** (one reactor-
   construction site, divergence-proof, unchanged).

**Caveat / closest-feasible fallback.** The truly-lazy `Poll` is a bounded refactor
of `Reactor` (the `Poll`/`bridge_waker` fields, `register_fd`/`register_timer`,
`turn`, `ExecutorWaker`, `block_on_reactor_capped`). If it threatens A4c's already-
large blast radius, the **closest feasible alternative is "always-construct-but-
cheap"**: keep `Reactor::new()` eager (the two syscalls per top-level drive) but
never spawn a thread and never `turn()` for a pure-blocking program (already true).
That still delivers the one-trampoline collapse and the feature deletion; it merely
pays ~2 syscalls per `cranelisp_run_io`. This is a perf refinement, **not a
correctness interim** — eager-cheap is a permanently-valid behaviour. Recommended
sequencing: land the collapse green FIRST, then the lazy-`Poll` as the LAST step of
A4c (both in A4c, so the end-state is not split across sprints — Principle 8).

**What changes relative to §6.8.0 (the deltas of the extension):**

- **DELETE the `drive_io` `#[cfg]` split.** `drive_io` becomes the single async
  body unconditionally; the `#[cfg(not(feature = "concurrency-runtime"))] fn
  drive_io = run_io_trampoline` arm is removed.
- **DELETE the §6.8.0-point-5 trampoline poll-error arm before it is ever built.**
  There is no non-reactor build, so a poll-shape effect **always works** — no
  `IO_TAG_EFFECT_POLL` "rebuild with `--features concurrency-runtime`" error arm.
  (§6.8.0 point 5's call-time-error answer is mooted; the mixed-platform load story
  it protected still holds, but the resolution is "the reactor is always present,"
  not "error cleanly without it.")
- **RETIRE the `concurrency` AND `concurrency-runtime` features entirely** (§6.8.0
  retired only `concurrency`; this retires both). `reactor`/`strand` (in
  `cranelisp-intrinsics`) and the gated platform/types ABI items become
  unconditional. mio/futures move from `dep:`-gated to plain deps.
- **The regression guard changes again: "reactor-free-off" → a RUNTIME assertion.**
  With no off-state, there is no `#[cfg]` lane to police. The replacement invariant
  is a **runtime property**: *a pure-blocking program constructs no mio `Poll`
  (no epoll_create / eventfd) and drains synchronously through the one trampoline.*
  Guarded by (i) a lazy-init unit/e2e — drive a `(print …)`-shaped tree and assert
  the reactor's `Poll` was never built (a test-visible construction counter on
  `Reactor`); and (ii) the existing reactor/`Par`-overlap e2e rows, which now
  exercise the lazy construction path on first `Pending` (proving no lost-wake).
  The whole feature-off test lane (`#[cfg(not(feature = "concurrency-runtime"))]`
  rows, the `nt-concurrency`/`nt-concurrency-runtime`/`nt-reactor-e2e` aliases, the
  default-`nt` vs gated-lane split) **collapses into one lane** — the default `nt`
  now drives the lazy reactor.

**Added public-API consequence (beyond §6.8.0).** Retiring `concurrency-runtime`
ungates `cranelisp-intrinsics`'s `reactor` (+ `strand`) module ⇒ its `pub` items
(`Reactor`, `make_cabi_waker`, `monotonic_nanos`, `join_io_leaves`, the fixture
`AsyncReadState`/`async_read_pollfn`/`TimerWriteState`/`timer_write_pollfn`) now hit
the **default** `crates/cranelisp-intrinsics/public-api.txt` baseline (they were
off the default edge while feature-gated). `/dev` regenerates that baseline in the
cutover change-set; `/review` confirms each newly-default-public item is intended
(several fixtures may warrant `pub(crate)` downgrade during the ungate — a facade
cleanup, flagged not blocking). §6.8.0's `cranelisp-types`/`cranelisp-platform`
public-api deltas are unchanged.

**Knock-on to Chunks B/C: still NONE semantically.** The reactor + poll-leaf
substrate is identical; lazy init only defers WHEN the `Poll` is built. Launch-and-
continue/supervisor/backpressure (B) and cancellation/combinators (C) build on the
single async trampoline unchanged.

---

### 6.8.0b ABI v8→v9 — scheduling state moves off values into the `ctx` vtable handle model (S97, supersedes FIXME 0482; /arch-ruled)

> **Status: RATIFIED target (S97 /arch, 2026-06-30; supersedes FIXME 0482 + the
> Phase-2 value-header descriptor ruling).** The earlier S97 cut (the
> descriptor-as-representation-overhead model: a `ResourceDesc` value-header slot, a
> `desc_out` out-param on `PollFn`, a per-value `(token, capacity)`) is **RETIRED**.
> During Wave-2 implementation it hit a structural blocker — an opaque zero-field
> `Connection` minted *inside the DLL* (`CLAdt::construct` → 24-byte object) had no room
> for a 16-byte descriptor slot stamped at `value+24` (heap overrun), and reserving the
> slot at the DLL-mint→host-alloc boundary was an undesigned cross-crate interface. The
> ratified replacement **dissolves that blocker**: scheduling state never touches the
> value, so there is no slot to reserve. The canonical model statement is
> `effect-concurrency.md` §4.1.1; this section is its ABI cascade. **Deleted relative to
> the descriptor cut:** `ResourceDesc`, the value-header slot, `PollFn.desc_out`, the
> `AsRawFd`-style trait, and the backend's resource-handle layout marking. **Added:**
> `acquire` + `retire` fn-pointer entries on the `ctx` vtable (`HostCtx`) + an `Acquire`
> result enum. Cascade: /arch (this section + `effect-concurrency.md` §4.1.1/§8.1/§8.2 +
> BC §3/§5/§6 + `interfaces.md`) → /design re-cascade of `poll-support.md` /
> `io-trampoline.md` / `reactor.md` (they were written to the dead descriptor model;
> §6.8.0b cascade list below) → /platform (web + stdio leaves to the poll-fn skeleton) →
> /backend (uniform poll node, delete the positional bake) → /int (the ctx-vtable host
> impl: acquire/retire + tramp-owned release + the §4.1 single-step E2 hardening, FIXME
> 0478). The v9 cutover lands as **ONE change-set** (the `HostCtx` + `ConcurrencyDescriptor`
> layout change is atomic across `cranelisp-types`, `cranelisp-platform`, backend, int,
> and every in-tree platform DLL — "no users," so the bump is free). **It is a *simpler*
> bump than the descriptor cut.**

**The model (canonical: `effect-concurrency.md` §4.1.1).** Scheduling state never rides
on user values; it flows through a trampoline-owned `ctx` vtable the platform's poll-fns
call. Handles are **tramp-opaque, user-readable** ADTs carrying the platform's `r` in their
own field: the trampoline never introspects them (only the platform reads `r` back), but
the user program may read the handle's genuine fields by ordinary destructuring — "opaque"
is to the runtime, not the user (`effect-concurrency.md` §4.1.1). The poll-fn skeleton is
uniform:
`acquire(token,cap,waker)? → syscall → (would-block? register(waker)+Pending : Ready)`;
a commutative leaf omits `acquire`; `sleep` is the degenerate one-shot. Release is
trampoline-owned (fired on `Ready`/cancel; cancel never re-enters the poll-fn). The
token is a platform-computed projection of the handle (default `r`; split per-direction
for full-duplex; `0` ⇒ commutative). The **manifest** carries compile-time facts
(poll-shape, role, capacity default, serialization class) for inference + codegen; the
**`ctx` vtable** carries ALL runtime scheduling.

**The `cranelisp-platform` ABI surface (the `ctx` vtable = `HostCtx` generalized).**
`HostCtx` gains two fn-pointer entries beside the existing
`register_readable`/`register_writable`/`register_timer` + opaque `host`:

```rust
// in cranelisp-platform::concurrency (re-projected from cranelisp-types opaque c_void)
pub register_readable: unsafe extern "C" fn(host: *const c_void, fd: i32,  waker: *const Waker),
pub register_writable: unsafe extern "C" fn(host: *const c_void, fd: i32,  waker: *const Waker),
pub register_timer:    unsafe extern "C" fn(host: *const c_void, ns: u64,  waker: *const Waker),
// NEW v9 — the token-permit half of the ctx vtable:
pub acquire: unsafe extern "C" fn(host: *const c_void, token: u64, capacity: u32, waker: *const Waker) -> Acquire,
pub retire:  unsafe extern "C" fn(host: *const c_void, token: u64),
pub host: *const c_void,
```

```rust
/// C-ABI result of a permit acquisition. `#[repr(i32)]`.
#[repr(i32)]
pub enum Acquire { Acquired = 0, Parked = 1 }   // in cranelisp-types, re-exported here
```

- `acquire` takes the **waker** (refining the user-sketched `acquire(token,cap)`): on
  `Parked` the host enqueues that waker on the token's permit-wait queue so the strand is
  re-polled when a permit frees. The single reactor thread never blocks in `acquire` — it
  returns `Parked` immediately and the strand suspends `Pending` (cooperative); the
  permit-is-a-counter reasoning of §8.1 holds, **no deadlock** (pressure-test (f) PASS).
- `acquire` is **idempotent per in-flight effect** (host keys held permits by the waker's
  data identity), so a re-poll does not double-count a permit.
- There is **no `release` vtable entry** — release is trampoline-owned (on `Ready`/cancel).
- **`PollFn` is UNCHANGED** — `poll(state, *HostCtx, *Waker) -> Poll`. No `desc_out`. The
  poll-fn calls `acquire`/`register_*`/`retire` through the `*HostCtx` it already
  receives. (This is the chief simplification over the descriptor cut, which added a
  `desc_out` parameter.)

**The `cranelisp-types` ABI surface.** `ConcurrencyDescriptor` gains
`role: ResourceRole` (consuming one byte of the existing `_reserved: [u8; 3]` tail —
existing field offsets + size unchanged), a **compile-time-only** fact:

```rust
/// Per-EFFECT static leaf role — a compile-time manifest fact grounding inference E2
/// and documenting the leaf for the platform-writer's guide. The trampoline does NOT
/// branch on it at runtime (there is no stamp/read — the leaf does all scheduling via
/// the ctx vtable). `#[repr(u8)]`, governed by ABI_VERSION.
#[repr(u8)]
pub enum ResourceRole { None = 0, Produce = 1, Consume = 2, Retire = 3 }
```

`PollFn` (the `cranelisp-types` opaque-pointer projection) is **unchanged**. `Poll` is
unchanged. `Acquire` is the new result enum (above). **No `ResourceDesc` type exists.**

**Singleton resources** (stdin) declare a manifest-static serial token
(`read-line`: `{token != 0, cardinality 1, role Consume}`); the poll-fn acquires that
constant — single-in-flight by construction (resolves FIXME 0471).

**Leaf signatures slim identically to the descriptor cut.** `accept-conn : (Fn [Listener]
(IO Connection))` with `Connection` an ordinary user-readable ADT, tramp-opaque only
(`(deftype Connection [...])`, carrying the platform's `fd`/`r` in an ordinary field —
*not* a hidden slot, and *not* a sealed value); `read-conn :
(Fn [Connection] (IO Request))`; `send-conn : (Fn [Connection Response] (IO Int))`. The
user never writes `(read-conn fd 1 fd)`. The difference from the descriptor cut: the
`fd`/`r` is a **genuine opaque ADT field the platform reads back**, not a type-invisible
header slot the trampoline stamps — so `CLAdt::construct` mints a normal N-field object
and the Wave-2 24-vs-40-byte overrun never arises.

**Lifecycle: who calls what.**

| Operation | Caller | When |
|---|---|---|
| `acquire(token, cap, waker)` | platform poll-fn | start of each poll (token ≠ 0) |
| `register_readable/writable/timer` | platform poll-fn | on `WouldBlock` |
| `retire(token)` | platform poll-fn (a Retire/`close` leaf) | after `close(r)` |
| **release** (permit) | **host trampoline** | on the effect's `Ready` **or** cancel/drop |

`retire` is **idempotent** (remove-the-token's-pool-if-present); a double-`close` or a
`close`-while-parked retires once and wakes any token-parked waiters to observe the gone
resource via their own (now-`EBADF`) syscall — Unix-aligned, no drain barrier
(pressure-test (c)). Full-duplex is expressible because the platform projects **distinct
per-direction tokens** off one handle in its read vs write poll-fns; the manifest imposes
no shared-token constraint between distinct effects (pressure-test (d)).

**No v10 looming (Principle 8 — interim-risk PASS).** v9 *removes* the v8 positional-bake
convenience and is the model's end-state. The forward axis (slice-4 degree/backpressure)
rides the already-reserved `ConcurrencyDescriptor.global_budget` — no v9 reshape, no v10
bump. Nothing in v9 is built to be discarded.

**ABI bump: 8 → 9.** Stamp `ABI_VERSION = 9`. The `HostCtx` layout change (the two new
fn-pointers), the `ConcurrencyDescriptor.role` byte, and the new `Acquire` enum are
layout-affecting (Principle 14). Every in-tree platform rebuilds against v9 in the
cutover change-set; the `shapes-badabi` negative fixture re-pins wrong-relative-to-9
(`/qa`). The `cranelisp-types` + `cranelisp-platform` `public-api.txt` regen rides the
same change-set.

**/design re-cascade (the design docs written to the dead descriptor model — flag for
/design, do NOT edit from /arch):**
- `design/platform/poll-support.md` §3.1/§3.5/§3.6 — rewrite the leaf-authoring contract
  to the poll-fn skeleton (acquire/register/retire via `ctx`); delete the `desc_out`
  env contract and the resource-handle-header depiction; `Connection` opaque field holds
  `r` (not a slot); the two-module `web.cl`/`serve.cl` split + the load-order rule
  (§3.6.3) carry forward unchanged.
- `design/backend/io-trampoline.md` §17 — the poll node is **uniform** (no role bake, no
  `ResourceDesc` header slot, no `desc_out` slot, no resource-handle type set); the
  backend's only v9 delta is **deleting** `inject_poll_leading_pair` + the positional
  peel. Net *less* backend work than the descriptor cut. `ring2-rc.md` §3.5.10 (0474) is
  model-independent and stands.
- `design/intrinsics/reactor.md` §7 — the trampoline does **not** split by role / stamp / read;
  it drives the uniform poll node, and the host implements the `ctx` vtable's
  `acquire`/`retire` (the §8.1 permit map) + **tramp-owned release** on `Ready`/cancel,
  keyed by effect identity. §8 (0479 watchdog) + §9 (0475) are model-independent and
  stand. §7.5 singleton `read-line` acquires the manifest-static token (carries forward).

---

### 6.8 The ABI-v4 cascade — numeric `ABI_VERSION` 6→7 (S93, effect-concurrency slice 2) — HISTORICAL (superseded by §6.8.0)

**Framing — "v4" is a doc-label, the version is numeric.** The
`design/arch/effect-concurrency.md` §12 / §13 cascade is named the **A2
C-ABI-async-leaf model**, colloquially "ABI v4". The *operative* instruction is the
same `current + 1` rule §6.7 used: the numeric `ABI_VERSION` steps **6 → 7**. The
"v4" label denotes the async-leaf model relative to the three-exports baseline; it
is **not** the numeric stamp. (Recorded explicitly because the pre-implementation
`effect-concurrency.md` §13 still says "`ABI_VERSION` 3 → 4" — that was written when
the stamp was 3; the live stamp at this sprint is 6, so the bump is 6→7, sprint R5.)

**What v7 changes — the effect-call shape, not the deployment model.** The
three-exports model (GOT + manifest + schema+layout-hash), the dual-artifact
cdylib/rlib deployment, the GOT-indirect dispatch, the per-platform export
namespacing (§5.5.5 / §6.7) — all carry forward **unchanged**. Three additions, all
governed by Principle 14 (explicit ABI bump, not source-evolution guards):

1. **Poll-shape effect fns GO through the GOT (mechanism unchanged; signature
   shape changes).** A v6 effect fn is a blocking `extern "C" fn(...) -> i64`; a v7
   effect fn is the **poll-shape** `unsafe extern "C" fn(state, *HostCtx, *Waker)
   -> Poll` (`cranelisp_platform::PollFn`). It still lives in the platform GOT and is
   still dispatched GOT-indirect against `__cranelisp_got_platform_<name>` — only the
   slot's *signature* changes. Sync / non-blocking effects return `Poll::Ready`
   immediately, so blocking-style and poll-style coexist (§12). Cancellation is the
   host ceasing to poll + a `drop_state` export — the platform never truly blocks.

2. **The concurrency descriptor joins the manifest, subsuming `scheduling_class`.**
   The v6 `PlatformFn.scheduling_class: u32` is generalized by
   `cranelisp_types::ConcurrencyDescriptor` (token + cardinality + global_budget +
   blocking — §5). The v7 manifest entry is
   `cranelisp_platform::ConcurrentPlatformFn` (the poll-shape successor to
   `PlatformFn`: `ptr` → `poll: PollFn`, `scheduling_class: u32` → `concurrency:
   ConcurrencyDescriptor`). **The `global_budget` field is reserved-but-inert until
   slice 4** (backpressure; FIXME 0442) — present now solely so slice 4 does not force
   a second bump 7→8 (sprint R5/§6). `jit_name` was already retired at v3 (FIXME
   0288); there is nothing further to drop.

3. **The host-reactor C-ABI — the one genuinely new designed artifact.** A
   host-provided `cranelisp_platform::HostCtx` vtable (`register_readable` /
   `register_writable` / `register_timer` + an opaque host reactor handle) + a C-ABI
   `cranelisp_platform::Waker` (`(data, vtable)` fat-pointer pair projecting
   `std::task::Waker`). On `WouldBlock` the platform registers interest through these
   and returns `Poll::Pending`; the host's single reactor (epoll / io_uring / kqueue)
   owns the *when* and re-polls via the Waker. "Platforms own the *what*; the host
   owns the *when*" (§12). It is small, stable, Unix-reactor-shaped.

**Landed this sprint (S93) — the layout contracts only.** The v7 types
(`ConcurrencyDescriptor`, `Poll`, `PollFn` in `cranelisp-types`; `HostCtx`,
`Waker`, `WakerVTable`, `PollFn`, `ConcurrentPlatformFn` in `cranelisp-platform`;
`StrandId`, `StrandEvent` in `cranelisp-intrinsics`) are landed as code **gated
behind an off-by-default `concurrency` feature** — out of the default build and the
`public-api.txt` frozen edge (so the v6 `PlatformFn` / `PlatformManifest` /
`HostCallbacks` field-order tables in `tests/facade_pif_rows.rs` stay green), exactly
the "landed-and-dormant" pattern §6.2 used for the GOT-indirect dispatch arm at v3.
The numeric `ABI_VERSION` stamp is bumped to **7** now (the `declare_platform!` macro
+ host loader still emit / read the v6 `PlatformFn` shape; in-workspace host + DLLs
rebuild together, so the stamp stays consistent). **The wiring** — the macro emitting
poll-fns + descriptors, the host loader reading `ConcurrentPlatformFn` + adopting
`got_slot`, and the host reactor implementing the `HostCtx` vtable — **is the
slice-2 reactor implementation** (`/dev`, next sprint/stretch), feature-gated and
byte-identical-when-off.

**Per-crate change list when the wiring lands (not actioned this sprint):**

- **`/platform` — `cranelisp-platform`** (`src/declare.rs`, `src/concurrency.rs`):
  the `declare_platform!` macro emits each effect fn in poll-shape and a
  `ConcurrencyDescriptor` per fn; the manifest entry array switches `PlatformFn` →
  `ConcurrentPlatformFn`. The host-reactor C-ABI types are already landed in
  `src/concurrency.rs` (gated).
- **`/backend` — `cranelisp-backend`**: an additive **poll-construction arm** (NOT a
  direct poll call — the trampoline owns the call). For a poll-shape (`blocking == 0`)
  effect it loads the poll-fn from `__cranelisp_got_platform_<name>` (GOT-indirect
  dispatch preserved) and builds an `IO_TAG_EFFECT_POLL` node over a **host-built
  state-closure** (`code_ptr` = poll-fn, captures = the marshaled i64 args, a reserved
  result slot), reusing the existing closure-construction codegen; blocking effects
  keep the unchanged v6 arm (byte-identical-off). `HostCtx`/`Waker` are passed at
  *poll* time by the trampoline's `async fn`, not at the backend site
  (`effect-concurrency.md` §6 + Appendix B §"ratified backend↔intrinsics seam").
- **`/int` — `src/`** (host reactor): implements the `HostCtx` vtable over the host's
  single reactor + the feature-gated host async runtime; the loader reads
  `ConcurrentPlatformFn` and adopts `got_slot = manifest index` as today.

**Host substrate + feature topology (S93 Phase-5 Wave-3, /arch — the reactor-gate
decision).** The host that drives the v7 poll-fns is **`mio` (reactor) + `futures`
(`block_on` executor), NOT tokio** — `effect-concurrency.md` §6's
"tokio-or-equivalent" resolved to the *or-equivalent* because the landed
host-reactor C-ABI (`HostCtx` = "register a raw fd + a `std::task::Waker`
projection") is **mio-shaped, not tokio-shaped**, and the C-ABI insulates platforms
from the executor choice entirely (a later swap is gate-local + ABI-invisible). The
runtime is gated by a **new `concurrency-runtime` feature** in
`cranelisp-intrinsics` (`= ["concurrency", "dep:mio", "dep:futures"]`) — distinct
from the existing `concurrency` feature, which stays **layout-contracts-only / zero
runtime deps** so a *platform* enabling it pulls in **no executor** (the A2
"platforms carry no runtime" thesis, preserved structurally). The
`--link`-links-no-executor guarantee is structural (the runtime deps are
`dep:`-gated optional; the exe-bundle `--link` path never requests
`concurrency-runtime`). The reactor *implementation* is hosted in
`cranelisp-intrinsics` (not `src/`) so it links into `--link` output — int owns
construction-for-REPL/`--run` + policy + the dev sink + feature-gating. The full
implementable slice-2 plan (the one async await boundary, the demo `async-read`
leaf, the strand hook, the per-crate `/dev` step list + spill marker) lives at
`effect-concurrency.md` Appendix B §"Slice-2 reactor — the implementable plan."

**S94 R1 — node seam ratified + one ABI field reserved.** The backend↔intrinsics
poll-shape Effect-node representation (left undefined by the S93 platform↔host
contracts) is ratified as the **closure-env model** — full /dev contract in
`effect-concurrency.md` §13 "S94 R1" + Appendix B §"ratified backend↔intrinsics seam."
Its single platform-DLL consequence: a **`drop_state: Option<unsafe extern "C"
fn(*mut c_void)>`** field is appended to the still-dormant v7 `ConcurrentPlatformFn`
(`crates/cranelisp-platform/src/concurrency.rs`) **with NO `ABI_VERSION` bump** — v7
is not yet frozen (no real cdylib has shipped against it), so the field is reserved in
place under the same reserve-now discipline as `ConcurrencyDescriptor.global_budget`,
inert until the cancellation slice (≥ 7). State construction (backend-built, no
`make_state` export) and result extraction (generic offset read, no per-effect
`ResultReader`) stay host-internal — they add **no** platform-DLL field. The gated v7
layout guard (`crates/cranelisp-platform/src/tests.rs::concurrent_platform_fn_repr_c_field_order_v7`)
stays green because `drop_state` sits between `poll` and `param_count` (the listed
offsets stay strictly increasing; `concurrency` stays last); /qa should extend that
guard to pin `drop_state` explicitly.

**S94 R1 (FIXME 0457) — the manifest → loader → symbol-table → backend channel, RATIFIED.** R1 fixed the poll-node *runtime representation*; 0457 closes the *data channel* that carries the poll discriminator from a loaded platform to the backend's emission arm. The ratified channel, end to end:

1. **Symbol table (LANDED, /arch).** `DefKind::PlatformEffect` gains `poll_shape: bool` (`#[serde(default)]`, default `false` = the byte-identical v6 blocking world; a pre-S94 cache deserializes as blocking). It is the **orthogonal dispatch axis** beside `scheduling_class` (the conflict-domain axis) — the full `ConcurrencyDescriptor` is deliberately NOT put on `DefKind` because that type stays `#[cfg(feature="concurrency")]` (a dormant C-ABI contract off the frozen edge) while `DefKind` is core/ungated; graduating it is a later step gated on lifting that dormancy. `cranelisp-types/public-api.txt` regenerated (one line: `poll_shape: bool`); `ConcurrencyDescriptor` stays absent from the default edge (the `_neg` guard holds).
2. **Manifest channel (SPECIFIED for /dev, all `#[cfg(feature="concurrency")]`).** A v7 platform exposes poll-shape effects through a **separate manifest type + separate export symbol** (NOT a reinterpreted `PlatformFn` array — that would break v6 byte-identical layout): a gated `#[repr(C)] ConcurrentPlatformManifest { abi_version, name, name_len, version, version_len, functions: *const ConcurrentPlatformFn, function_count }` in `concurrency.rs`, exported by the v7 `declare_platform!` as `cranelisp_concurrent_manifest`. v6 platforms keep exporting only `cranelisp_platform_manifest` (PlatformFn array) — untouched.
3. **Loader (SPECIFIED for /dev).** The concurrency-built host (`src/platform.rs`) dlsym-probes `cranelisp_concurrent_manifest` FIRST; hit ⇒ `concurrent_manifest_to_descriptors` (gated sibling of `manifest_to_descriptors`); miss ⇒ the existing v6 path. `OwnedPlatformFnDescriptor` gains a gated `concurrency: Option<ConcurrencyDescriptor>` (`Some` for v7-lifted, `None`/absent for v6). The DefKind construction cfg-splits: ungated ⇒ `poll_shape: false`; `#[cfg(feature="concurrency")]` ⇒ `poll_shape: desc.concurrency.map_or(false, |c| c.blocking == 0)`. The v7 path derives the still-required `scheduling_class` from the descriptor via a gated `ConcurrencyDescriptor::nearest_scheduling_class` reverse map (token/cardinality → nearest class).
4. **Backend (SPECIFIED for /dev, NO cargo feature).** The effect-site codegen reads `DefKind::PlatformEffect { poll_shape, .. }`: `true` ⇒ the poll-construction arm (`IO_TAG_EFFECT_POLL` + host-built state-closure, the R1 seam); `false` ⇒ the unchanged blocking call. The default world only ever sees `poll_shape == false` (no v7 platform loaded) ⇒ byte-identical.

This refines §6.8's earlier loose "the manifest entry array switches `PlatformFn` → `ConcurrentPlatformFn`": the switch is via a separate v7 manifest type + a probed v7 export symbol, so v6 platforms + the default host stay byte-identical. **As-built (S94):** the channel shipped end-to-end (`ConcurrentPlatformManifest` + `cranelisp_concurrent_manifest` export + dlsym-probe loader + the `poll_shape` symbol-table field + backend poll-construction arm + intrinsics async Effect arm); the 5 reactor e2e rows (`tests/concurrency_reactor.rs`) are green (two real leaves overlap ≈max on one reactor thread). FIXME 0457 resolved + deleted S94.

**Status: ACTIONING (S93 → S94).** The pre-implementation §13 "flagged, not executed"
state is superseded — slice 2 has opened, the layout contracts are landed, the node
seam is ratified (S94 R1), and this §6.8 is the cascade record. The remaining wiring
is tracked by the slice-2 work in `sprints/ROADMAP.md`, not a separate FIXME (the
manifestation-site discipline: the cascade lives here at its natural home, actioned by
the open track).

**Within-DLL v6+v7 mixing — the boundary, and the deferred merge mechanism (S96 /arch
ruling, FIXME 0464). — SUPERSEDED by §6.8.0 (single-ABI cutover, 2026-06-29).** The
whole within-DLL-mixing *problem* dissolves under the single ABI: one manifest carries
both blocking and poll-shape entries natively, so the dual-manifest-merge mechanism
below is never built and FIXME 0464 is resolved-by-superseding-pivot (deleted). The
paragraph is retained as the record of the coexistence-era reasoning.

**The §6.8 byte-identical-off design supports **system-level
coexistence** — some platforms v6, some v7, the host loading each by the either/or probe
(`cranelisp_concurrent_manifest` first, else `cranelisp_platform_manifest_<name>`). It does
NOT, as built, support **within-DLL mixing** — a SINGLE DLL carrying both a v6 blocking
effect AND a v7 poll effect. Two structural walls: (1) both `declare_platform!` and
`declare_concurrent_platform!` export the same `__cranelisp_got_platform_<name>` GOT static
⇒ a crate invoking both fails to link; (2) the loader is strictly either/or per handle — a
v7 hit uses the v7 manifest *exclusively*, never also reading the v6 manifest from the same
handle. **This is a deliberate boundary, not a defect to fix on sight.** The S96 server demo
sidesteps it entirely: the exemplar **`web`** platform is **pure-v7 + concurrency-host-only**
(all leaves poll-shape — sync leaves via a trivially-ready `Poll::Ready` poll per point 1
above; `declare_concurrent_platform!` only ⇒ one GOT export, either/or loader suffices), and
**`stdio` stays fully v6** (`print` must stay default-host-loadable; its `read_line`-poll
ergonomics rewrite is descoped). **The merge mechanism, when a genuine within-DLL mixed
platform is needed (unmet trigger as of S96):** the ruled path is **dual-manifest merge** —
one DLL exports BOTH manifests over ONE shared GOT (disjoint slot ranges; GOT static emitted
once via the `declare_platform!`/`declare_concurrent_platform!` shared `@spine` macro
convergence), the `concurrency` host reading + merging both (blocking → v6 descriptors, poll
→ v7), the default host reading only the v6 subset (poll effects simply absent). It stays in
the §6.8 envelope: **no `cranelisp-types` touch, no `ABI_VERSION` bump, no `public-api.txt`
touch** — both manifest exports already exist; the change is macro-internal (GOT de-dup) +
int-internal (`src/platform.rs` loader merge), and the v7 manifest read is already
`#[cfg(feature="concurrency")]` so default-host byte-identical-off is preserved. The
rejected alternative (a unified v7 manifest carrying a blocking effect + a v6 *view*/shim for
the default host) couples the default load path to v7 types and re-opens the v7-unfrozen
posture — denied. Build the merge WITH the macro convergence when the trigger fires.

---

## 7. Data structures, functions & sequence

### 7.1 Shapes

```
__cranelisp_got_platform_<name> : [AtomicPtr<u8>; GOT_TABLE_SIZE]   ; the platform's GOT, exported by DLL
                                  ; slot i = fn pointer of manifest.functions[i]
                                  ; (manifest order IS GOT slot order — answer 1)
                                  ; entries linker-fixed-up via relocations — answer 2

cranelisp_platform_manifest_<name> : extern "C" fn(*const HostCallbacks) -> PlatformManifest
                                  ; the manifest entry point, exported by DLL
                                  ; NAMESPACED per §5.5.5 (was bare cranelisp_platform_manifest, DEF-5/§6.7, ABI v4)
                                  ; emit + consume agree via platform_manifest_symbol(name)

__cranelisp_layout_hash_<name> : <hash bytes>                       ; exported by DLL, ONE per
                                  ; platform (§5.5.4)
                                  ; = canonical hash of the generated schema artifact

embedded schema artifact (via schema: include_str!("<name>.platform-schema")):
  NOT a link symbol — the /platform-schema-generated text baked into the DLL,
  read by the schema parser DLL-side for read_field name→index (§5.5.1).
  Shape: Map<FQTypeName, Vec<(CtorName, tag, Vec<(Symbol, FieldType)>)>>
         + ";; layout-hash:" header line (§5.5.2/§5.5.4)

PlatformManifest (#[repr(C)], shrunk):
  abi_version: u32
  name, name_len; version, version_len
  functions: *const PlatformFn; function_count

PlatformFn (#[repr(C)], shrunk):
  name, name_len
  type_sig, type_sig_len
  docstring, docstring_len
  param_names, param_name_lens, param_name_count
  scheduling_class: u32
  ; (jit_name retired)
```

### 7.2 REPL / `--run` load sequence

```
int: dlopen(libcranelisp_<name>.dylib)
  → call cranelisp_platform_manifest(host_callbacks)   ; HostContext::init stores callbacks
  → manifest_to_descriptors(&manifest)                  ; UTF-8 → OwnedPlatformFnDescriptor[]
  → resolve + compile associated .cl type module(s)     ; q-assoc-discovery (c); BEFORE sigs
      → resolve_module_file(shapes) → shapes.cl          ; project tree / CRANELISP_LIB
      → register_module(shapes, …)                       ; ORDINARY module → TypeDef entries
  → layout-hash check (§5.5.4):                          ; staleness gate
      host_schema = backend_generate_schema(live tables)  ; one generator, §6.0
      host_hash   = canonical_hash(host_schema)
      dll_hash    = dlsym("__cranelisp_layout_hash_<name>")
      if host_hash != dll_hash:
        REPL    → warn + load (regeneration bootstrap, §5.5.1)
        --run   → PlatformError refusal + abort
  → dlsym("__cranelisp_got_platform_<name>")            ; GOT base (the DLL's exported GOT)
  → GotTable::with_static_backing(got)                   ; WRAP it in place — no copy (answer 3)
  → ensure_module_exists(platform.<name>)
  ; NO import injection — sigs are FQ
  → for i, desc in descriptors:                          ; HOST builds the table from the manifest
      scheme = check_type_expr(parse_type_expr(desc.type_sig))   ; resolves FQ refs (shapes/Rectangle)
      table.insert(desc.name, Def { scheme, PlatformEffect{sched}, got_slot=i, meta })  ; got_slot = manifest index (answer 1)
  → retain DLL handle on table.dll                       ; spec §8.9.3
  ; ready — call sites dispatch GOT-indirect through the GOT at got_slot
```

### 7.2a The schema generate cycle (`/platform-schema`)

```
author: write FQ sigs in declare_platform! + the .cl type module(s)
  → cargo build -p <platform>            ; first build — embedded schema absent/stale (tolerated)
  → cranelisp (REPL): load platform       ; hash mismatch → WARN + LOAD (bootstrap, §5.5.1)
  → /platform-schema <name>:              ; the generator (backend, §6.0):
      roots   = ADT types named in PlatformEffect sig schemes (scalars excluded)
      closure = transitive walk over field types (nested ADTs in; scalar leaves out)
      entries = for each (incl. concrete instantiations): substitute type args,
                emit (FQTypeName | structured-type-expr) → [(Ctor, tag, [(field, FieldType)])]
      emit    = ";; layout-hash: <hash>\n" + canonical schema text   → stdout
  → redirect text to <name>.platform-schema (the embed file)
  → cargo build -p <platform>            ; macro embeds artifact + exports __cranelisp_layout_hash_<name>
  → --run / --link now ACCEPT (host-recomputed hash matches)
```

### 7.3 `--link` sequence (no live load step)

```
compile time (has a SymbolTable): platform module built as 7.2 (FQ sigs, no
  injection), codegen emits GOT-indirect dispatch against
  __cranelisp_got_platform_<name> at got_slot, referenced as Linkage::Import
  data symbol. Associated .cl modules compiled like any source → their own .o + GOT.
  layout-hash check (§5.5.4): the compiler REGENERATES the schema from the modules
  it compiled (the same backend generator, §6.0), hashes it, and BAKES the hash into
  the startup object; the startup stub compares it against the statically-linked
  __cranelisp_layout_hash_<name> at process start — mismatch → abort with rebuild
  guidance. (A stale platform builds but refuses at run — the accepted trade vs
  teaching the compiler to read symbols out of rlib archives at build time; §1.)
link time: ld resolves __cranelisp_got_platform_<name> against the -force_load'd
  platform rlib (same as __cranelisp_got_primitives). No JITBuilder::symbol,
  no manifest read, no SymbolTable at runtime.
runtime: the GOT entries are already linker-fixed-up (relocations resolved at link, §5.1
  answer 2) — no runtime population; main() dispatches GOT-indirect. Works with zero session.
```

---

## 8. Appendix: superseded options

- **FIXME 0282 Option A** (add `schema_ptr`/`schema_len` to `PlatformManifest`,
  `ABI_VERSION` 2→3). Rejected: the schema itself retires, so there is no text to carry.
- **FIXME 0282 Option B** (reuse `validate_schema` callback's `schema_ptr`/`schema_len`
  to ferry the literal host-side; /design's recommendation in host-wiring-s76 §3).
  Rejected: same — no schema to ferry; `validate_schema` retires entirely.
- **The S71 schema DSL** (the `schema:` *declaration arm*, the `LazyLock<Schema>`-as-DSL
  marker types, host `validate_schema`). A self-contained DLL-only type *language* for
  ADTs. Superseded by "ADTs are ordinary `.cl` modules" — the language already has a type
  system; a second, weaker one in the DLL was duplication (Principle 7) and could not
  compose with constructors / `match` / traits. **Note:** only the *hand-authored
  declaration* is superseded; the schema *parser* survives (§5.5.1), now reading the
  machine-generated artifact; name-based field access is **recovered** by §5.5's
  compiler-generated-schema design — so the first convergence's "build-adjacent offset
  resolution is lost" cost is itself superseded.
- **JITBuilder-symbol / direct-extern dispatch** (today's as-built, §9). Superseded by
  GOT-indirect dispatch against the exported GOT — removes the two-path divergence and
  the flat-namespace collision hazard (§6.3).

### Third-convergence rejections (2026-06-07)

- **(B′) embed-the-`.cl` via `include_str!`** (the **second convergence's** recommendation —
  was the document's center until this session). The macro took `types: include_str!("shapes.cl")`
  — the very file the host compiled — and the repointed parser read the embedded `deftype`
  text DLL-side for name→index; a per-module canonical-`deftype`-hash bound it.
  **DISPROOF (user, 2026-06-07): "brittle."** `include_str!` captures **lexical file content**,
  but the layout the host actually uses is whatever the **resolved module graph** produces.
  The two diverge the moment the type module **imports or re-exports** its ADTs from another
  module: the lexical `shapes.cl` might be `(import [geom [Point]]) (deftype Rectangle [:Point origin ...])`,
  whose *layout* is only knowable after resolving `geom/Point` — the embedded text alone does
  not carry it, so the DLL-side parser cannot navigate the nested field, and the host-side
  hash (computed over the resolved forms) would never match the DLL-side hash (computed over
  lexical text). It also re-raised the **canonical-form/DAG problem**: the DLL side cannot
  call the frontend sexp printer (DAG ban platform→frontend), so "both sides hash the same
  canonical form" needed a fragile macro-build-time-printer or a duplicated canonicaliser.
  The compiler-generated schema (§5.5) reads the resolved graph directly and runs **one
  generator on both sides**, dissolving both problems.
- **FIXME 0234 `/abi` — SUBSUMED, NOT IMPLEMENTED.** 0234 specified a per-type
  paste-into-hand-authored-arm emitter (`/abi <type>` prints a schema-arm fragment the author
  pastes into the `schema:` declaration) plus a mangled-name naming convention (§1.3, e.g.
  `OptionInt`) for the human-pasted instantiation keys. Its **output target — the
  hand-authored schema arm — no longer exists** (retired with the S71 DSL above). The
  `/platform-schema` generator subsumes the per-type emit into a whole-platform machine emit,
  and the structured-type-expression map key (§5.5.3) supersedes the §1.3 mangle (no human in
  the loop → no human-readable mangle needed). The 0234 FIXME **retires when this design is
  actioned** — recorded here, not deleted doc-only (per the cross-skill FIXME protocol).

### Second-convergence rejections (2026-06-07)

- **q-assoc-discovery (a) — sibling-file convention + `platform.<name>.*` mounting.** The
  first convergence recommended (a)+(c): discover the type `.cl` on
  `CRANELISP_PLATFORM_PATH` and mount under a `platform.<name>.*` namespace. **REJECTED**
  in favour of pure (c) — the type modules are ordinary importable modules with no
  platform-specific discovery or mounting; FQ refs auto-load them per 0268 via ordinary
  module-file resolution (project tree / `CRANELISP_LIB`). The cost (no automatic
  dylib/`.cl` co-location) is accepted and mitigated by the §5.5 layout-hash.

- **q-sig-ref-style (b) — host injects an import.** The first convergence recommended the
  host inject `(import [platform.<name>.types [*]])` (mirroring the primitives injection)
  so sigs could stay short. **OVERRULED** — sigs are FQ (a); the platform module carries
  zero injected imports; the primitives injection itself retires.

- **Field-access (A) host-as-layout-oracle** (a `field_index` callback + a compiler-baked
  `--link` layout blob, trace `DisplayDescriptor` precedent). Rejected on cost: two new
  channels to avoid embedding one text blob; drift-proof but disproportionate (§5.5).

- **Field-access (B) codegen'd Rust bindings** (a build script turning the `.cl` into Rust
  accessors). Rejected: build tooling that creates the very drift it polices — a second
  maintained copy of the layout (§5.5).

---

## 9. Appendix: as-built archaeology

The current pipeline, compressed to what informs the design:

- **Load.** `load_platform_dll` (`src/platform.rs:148`) dlopens, reads the manifest,
  `manifest_to_descriptors` → `OwnedPlatformFnDescriptor[]`.
- **Register.** `register_platform_in_tc` (`src/platform.rs:247`) creates
  `platform.<name>`, injects `(import [primitives [*]])` via
  `inject_primitives_import_for_platform` (`:325` — **this injection retires** under FQ
  sigs, §2 q-sig-ref-style), parses each sig via `parse_type_expr`/`check_type_expr`,
  inserts `Def { PlatformEffect{sched}, got_slot: None }`, and returns `(jit_name, ptr)`
  pairs.
- **Dispatch.** Backend `apply.rs:209-227` emits a direct `Linkage::Import` against the
  mangled `jit_name` (`cranelisp_print`); fn ptr reaches the JIT via
  `JITBuilder::symbol(jit_name, ptr)`; cache linker registers identically.
- **`--link`.** Platform rlibs `-force_load`ed (`src/exe.rs:549`) so the mangled symbols
  resolve at `ld`. Works, but bypasses the GOT (§6.3).
- **Schema (S71).** `declare_platform!` `schema:` arm → DLL-local `LazyLock<Schema>`
  parsing a **bespoke schema dialect** (`Schema::parse`, `schema.rs:167` — its own
  grammar over `CLInt`/`CLBool`/… field types, byte-offset computation; it does NOT parse
  `deftype` source); `CLAdt::read_field` consults it for offsets; `validate_schema` host
  channel never wired (FIXME 0282 is the blocker that this redesign dissolves). **Note for
  §5.5:** the *parser's structure* (two-pass, ParseLoc, name/field lookups) is what
  survives, reading the **`/platform-schema`-generated artifact** instead of the
  hand-authored dialect; the *hand-authored dialect grammar* is what dies (the
  machine-generated artifact grammar is settled at §2.2 q-schema-grammar).
- **GOT precedent (0280).** `cranelisp-primitives::PRIMITIVES_GOT_SLAB` exported as
  `__cranelisp_got_primitives`, `GotTable::with_static_backing` over it; one GOT for JIT
  + cache + `--link`. This design generalises the pattern to platforms.

---

## 10. Change history

- **2026-06-18 (S86 — DEF-5 manifest-symbol namespacing, /arch GO)** — Blessed the
  DEF-5 fix: the `declare_platform!` manifest export is renamed
  `cranelisp_platform_manifest` → `cranelisp_platform_manifest_<name>`, extending the
  per-platform namespacing convention the GOT + layout-hash exports already followed (the
  manifest fn was the lone bare `#[unsafe(no_mangle)]` export → multi-platform `--link`
  collision). Recorded the **§5.5.5 binding invariant** (every per-platform C-ABI export
  is name-suffixed; shared `platform_manifest_symbol(name)` helper used by emit AND
  consume), the **ABI bump** (v3→v4 framing; operative = `ABI_VERSION` `current + 1` in
  `cranelisp-platform/src/lib.rs`; all DLLs rebuild), and the **§6.7 per-crate change
  list** (/platform macro + helper + bump; /backend test fixtures only — the startup-stub
  import loop is naming-agnostic; /int `collect_platform_manifest_names` takes names not
  count + dlopen-lookup uses the pre-known platform name). **Naming-only** — no manifest
  content, schema-model, or three-exports-model change; lands atomically (the sanctioned
  one-change-set ABI-rename exception). `--run`/dlopen path: the manifest dlsym must use
  the new name, resolved from the `(platform "<name>")` declaration (the name is known
  before the manifest is read). Layout-hash/schema gate: unaffected. Doc-only; cascade is
  the coordinated `/dev` change-set.
- **2026-06-07** — Authored. Resolves FIXME 0282 / S-PLAT-1 by the user's converged
  direction (DLL exports its GOT; platforms stop declaring ADTs → associated `.cl`
  modules; manifest shrinks to host-non-derivable facts). Supersedes host-wiring-s76 §3
  Options A/B and the S71 schema DSL. PENDING USER REVIEW — doc-only, no cascade.
- **2026-06-07 (second convergence)** — All five open questions ruled, and the
  field-by-name access problem the user posed this session settled by a new §5.5.
  **Rulings:** q-assoc-discovery **(c)** — type modules are plain importable modules
  found by ordinary `.cl` resolution (project tree / `CRANELISP_LIB`), NOT
  `CRANELISP_PLATFORM_PATH`; the (a) sibling-convention + `platform.<name>.*` mounting
  rejected (§8). q-sig-ref-style **(a)** — FQ sigs (`(Fn [primitives/Int]
  shapes/Rectangle)`); the (b) injection overruled and
  `inject_primitives_import_for_platform` (`src/platform.rs:325`) ruled DEAD WRONG and
  RETIRES (a this-sprint bare-name convenience). q-drift-mitigation **superseded by
  §5.5**. q-callbacks-shrinkage **bump freely** (`ABI_VERSION` 2→3, no reserved slot).
  q-symbol-table-content **confirmed** (name + FQ type_sig + got-index + scheduling_class
  + metadata; no injected imports). **New §5.5 (the doc's new center):** the DLL embeds
  the SAME `.cl` (`types: include_str!`), the schema **parser survives repointed** at the
  embedded `deftype` text (the **dialect/declaration arm dies**) so `read_field("w")`
  works by name; a **`layout_hash`** ABI binding (second axis, independent of repr(C)
  `abi_version`) — canonical hash of the embedded deftype forms (via the frontend sexp
  printer), exported as `__cranelisp_layout_hash_<module>` (one per module), checked at
  BOTH session load AND `--link` — catches deployment drift with a hard refusal. **One
  live question remains:** the user's re-read of the §5.5 recommendation (§2.1). Still
  PENDING USER REVIEW — doc-only, no cascade. **Flagged for the cascade when actioned:** a
  new `PlatformError` variant for the layout-hash refusal (Decision 0042).
- **2026-06-07 (third convergence)** — §5.5 **rewritten**: the embed-the-`.cl`
  (`include_str!`) design is **superseded** by a **compiler-generated schema**. The user
  disproved B′ as "brittle" — `include_str!` captures lexical file content, but layout truth
  lives in the **resolved module graph** (B′ breaks when the type module imports/re-exports
  its ADTs). **The converged design:** a new **`/platform-schema <name>` REPL command**
  (introspection-family sibling) derives the referenced-type set from the loaded platform's
  symbol table, takes the **transitive closure** over field types, and emits the schema as a
  **machine-written build artifact** the platform embeds (`schema: include_str!("<name>.platform-schema")`);
  the retained parser reads it verbatim. **Schema shape:** `Map<FQTypeName, Vec<(CtorName,
  tag, Vec<(Symbol, FieldType)>)>>` — ordered NAMED+TYPED fields; `FieldType` a recursive
  type-expr; typed fields make nesting work. **Concrete instantiations:** keyed by the
  **structured type expression** itself (machine-read) — **supersedes FIXME 0234 §1.3's
  mangled-name convention**; same substitution the trace `DisplayDescriptor` baker performs.
  **Layout hash:** ONE per platform (was per-module), `;; layout-hash:` artifact header +
  `__cranelisp_layout_hash_<name>` data symbol; the host **regenerates** the schema from live
  tables and re-hashes — **`--run`/`--link` REFUSE on mismatch, REPL WARNS-AND-LOADS** (the
  regeneration bootstrap). **One generator, one checker, both in the compiler** — the
  second-convergence canonical-form/DAG problem **dissolves** (no platform-crate
  canonicalization). **Generator placement: `cranelisp-backend`**, sharing the closure-walk +
  substitution logic with the trace descriptor baker (the `--link` host-recompute runs at
  link time inside backend; the sharing requirement is named — different consumers/lifetimes,
  one *walk*, not one serialized form). **0234 `/abi` SUBSUMED-NOT-IMPLEMENTED** (its
  hand-authored-arm output target no longer exists; retires when actioned). §2 is now
  near-empty (two genuine residual implementation questions: sum-type tag stability across
  regenerations; the artifact's textual grammar). Still PENDING USER READ — doc-only, no
  cascade. **Flagged for the cascade when actioned (unchanged):** the new `PlatformError`
  variant (Decision 0042); plus the FIXME 0234 retirement.
- **2026-06-07 (fourth convergence — editorial / terminology + precision reset)** — the
  user found the §1 overview language confusing and ordered a clarifying reset (no direction
  change; every third-convergence ruling stands). **Terminology normalised across the whole
  document:** the exported function-pointer table is the **GOT** (every prose use of "slab"
  for it struck; the exported symbol stays `__cranelisp_got_platform_<name>`; the code
  identifier `PRIMITIVES_GOT_SLAB` in `cranelisp-primitives` is kept as a factual precedent
  reference, not as a name for the platform table — 35 prose slab→GOT renames; the 4 retained
  occurrences are the real `PRIMITIVES_GOT_SLAB` identifier + the naming-directive sentence).
  The declarative function-data block is the **manifest** ("the data the host builds a symbol
  table from when it needs one"); the generated type-layout artifact is the **schema**
  (unchanged). **§1 rewritten** around the reset: a platform exports three things — its
  **GOT** (linker-fixed-up function pointers, manifest order), its **manifest** (what a
  session builds a symbol table from), its **schema + layout hash** (`/platform-schema`-
  generated, embedded, hash-checked at load); `--link` consumes only the GOT (+ hash to
  refuse a stale build), REPL/`--run` consume all three. **The four user confusions are now
  answered in plain language in §1** ("The four things the user asked, answered plainly") and
  reinforced at their construct sites: (1) ordering — manifest array order IS GOT slot order,
  one declared order, two derivations (§1 answer 1, §5.1, §5.3 `got_slot` row, §7.1/§7.2);
  (2) const-init vs relocations — both true at different levels, no runtime population, same
  mechanism as `define_module_got_data` (§1 answer 2, §5.1, §6.1, §7.3 runtime line);
  (3) wrap-not-copy — host builds the SymbolTable in its own memory from the manifest, its
  GotTable wraps the dlsym'd GOT in place under the dlopen handle (§1 answer 3, §5.1, §5.3,
  §6.4, §7.2); (4) naming (§1 answer 4). §5/§6/§7 swept for the same terminology. Still
  PENDING USER READ — doc-only, no cascade; all third-convergence cascade flags unchanged.
